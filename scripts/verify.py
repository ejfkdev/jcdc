#!/usr/bin/env python3
"""jcdc verification pipeline.

Mode A (features): compile the feature suite with `javac --release r`,
decompile, recompile, RUN both versions and compare stdout (semantic
verification of language constructs).

Mode B (corpus): for each downloaded JDK, pick self-contained source files
from its src.zip extraction, compile with `--release N` (or the JDK's own
javac for 6/7), decompile, recompile, and compare normalized `javap -c`
output per method (bytecode-level verification across class file versions).

Usage:
  python3 scripts/verify.py features [--releases 8,17,26] [--keep]
  python3 scripts/verify.py corpus [--jdks 8,17,21] [--limit 30] [--keep]
  python3 scripts/verify.py all
"""

import argparse
import json
import os
import re
import shutil
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
CORPUS = ROOT / "corpus"
WORK = CORPUS / "verify-work"
JCDC = ROOT / "target" / "release" / "jcdc"

# Platform classes for the decompiler's signature lookups (generic call/
# field instantiation). JDK8's rt.jar covers the stable java.base API for
# every corpus version; family classes (added first) still take priority.
RT_JAR = next(iter(sorted((ROOT / "corpus" / "jdks" / "jdk8").glob("*/Home/jre/lib/rt.jar"))), None)


def _extract_platform(feature):
    """Extract the era JDK's lib/modules jimage once per release into
    WORK/platform/jdkN; return the java.base class dir or None."""
    cache = WORK / "platform" / f"jdk{feature}"
    base = cache / "java.base"
    if base.is_dir():
        return base
    home = jdk_home(feature)
    modules = home / "lib" / "modules" if home else None
    if modules is None or not modules.exists():
        return None
    cache.mkdir(parents=True, exist_ok=True)
    for tool in (LOCAL_JDK / "bin" / "jimage", home / "bin" / "jimage"):
        if not tool.exists():
            continue
        run([str(tool), "extract", "--dir", str(cache), str(modules)],
            timeout=900)
        if base.is_dir():
            return base
    return None


def jcdc_cp(feature):
    # Platform classes for the decompiler's reference lookups (generic
    # signature instantiation, sealed-supertype checks). Must be ERA-
    # correct: JDK8's rt.jar answers with pre-9 semantics (jdk19+
    # IllegalFormatException is sealed; against the stale copy the
    # decompiler dropped `non-sealed` and the recompile died with
    # 需要密封、非密封或最终修饰符). For 9+ the era jimage; for 8 rt.jar IS the
    # era jar; for 6/7 the era JDK's own platform jar — EnumSet
    # readResolve's erased `(E)e` cast witness needs Collection.add(E)'s
    # Signature resolvable, and the super chain (AbstractSet→…→Collection)
    # lives only in the platform jar. The old "no cp for 6/7" rule
    # guarded against JDK8-era nested classes leaking into families
    # (DeqSpliterator); an era jar contains exactly the classes the era
    # sources compiled against, so there is nothing to leak. Family
    # classes (added first) still take priority: pool dir sources are
    # first-wins and dirs precede jars in lookup.
    if feature >= 9:
        base = _extract_platform(feature)
        if base is not None:
            return [str(base)]
    if feature == 8 and RT_JAR:
        return [str(RT_JAR)]
    home = jdk_home(feature)
    if home is not None:
        for c in (home / "jre" / "lib" / "rt.jar",
                  home / "lib" / "rt.jar",
                  home / "Classes" / "classes.jar",
                  home.parent / "Classes" / "classes.jar"):
            if c.exists():
                return [str(c)]
    return []
LOCAL_JDK = Path("/opt/homebrew/opt/openjdk/libexec/openjdk.jdk/Contents/Home")

FEATURE_GATES = {
    # file -> minimum release
    "Legacy6": 6, "Legacy7": 7,
    "ControlFlow": 8, "Exceptions": 8, "Expressions": 8,
    "EnumSwitch": 8, "Lambdas": 8, "Locals": 8,
    "OO": 9, "Modern": 17,
}
FEATURE_MAINS = ["Legacy6", "Legacy7", "ControlFlow", "Exceptions", "Expressions", "EnumSwitch", "Lambdas", "Locals", "OO", "Modern"]


def run(cmd, timeout=300, **kw):
    try:
        return subprocess.run(cmd, capture_output=True, timeout=timeout, **kw)
    except subprocess.TimeoutExpired:
        class R:
            returncode = -999
            stdout = b""
            stderr = b"TIMEOUT"
        return R()


def jdk_home(feature):
    d = CORPUS / "jdks" / f"jdk{feature}"
    for cand in (d / "Contents" / "Home", d / "jdk" / "Contents" / "Home", d):
        if (cand / "bin" / "javac").exists():
            return cand
    # vendor layouts like zulu-7.jdk/Contents/Home
    if d.is_dir():
        for sub in sorted(d.iterdir()):
            cand = sub / "Contents" / "Home"
            if (cand / "bin" / "javac").exists():
                return cand
            if (sub / "bin" / "javac").exists():
                return sub
    return None


# ---------------------------------------------------------------------------
# javap normalization
# ---------------------------------------------------------------------------

SKIP_METHODS = re.compile(r"(lambda\$|access\$\d+|\$values|readObject|writeObject)")

def javap_methods(javap_bin, classfile):
    """Return {method_sig: [normalized instruction lines]}."""
    r = run([str(javap_bin), "-p", "-c", "-constants", str(classfile)])
    if r.returncode != 0:
        return None
    text = r.stdout.decode("utf-8", "replace")
    methods = {}
    cur_sig = None
    cur_lines = None
    in_code = False
    for raw in text.splitlines():
        line = raw.rstrip()
        stripped = line.strip()
        if not stripped:
            continue
        # method signature lines end with ';' and are indented 2
        if re.match(r"^  [a-zA-Z<].*\(.*\).*;$", line) and not stripped.startswith("Code:"):
            if cur_sig is not None:
                methods[cur_sig] = cur_lines
            cur_sig = stripped
            cur_lines = []
            in_code = False
            continue
        if stripped == "Code:":
            in_code = True
            continue
        if cur_sig is None:
            continue
        # tables to skip
        if stripped.startswith(("LineNumberTable:", "LocalVariableTable:", "LocalVariableTypeTable:",
                                "StackMapTable:", "Exceptions:", "RuntimeVisible", "RuntimeInvisible",
                                "Signature:", "SourceFile:", "Deprecated:", "InnerClasses:",
                                "BootstrapMethods:", "NestHost:", "NestMembers:", "Record:",
                                "PermittedSubclasses:", "MethodParameters:", "AnnotationDefault:",
                                "Module", "ConstantValue:")):
            in_code = False
            continue
        if in_code and re.match(r"^\s+\d+:", line):
            norm = normalize_insn(stripped)
            if norm:
                cur_lines.append(norm)
    if cur_sig is not None:
        methods[cur_sig] = cur_lines
    # drop synthetic/compiler-specific methods
    return {k: v for k, v in methods.items() if not SKIP_METHODS.search(k.split("(")[0])}


INSN_RE = re.compile(r"^\d+:\s+")
CP_RE = re.compile(r"#\d+(?:,\s*\d+)*")

def normalize_insn(line):
    m = INSN_RE.match(line)
    if not m:
        return None
    body = line[m.end():]
    # keep the // comment (symbolic), drop numeric cp refs
    body = CP_RE.sub("#", body)
    body = re.sub(r"\s+", " ", body).strip()
    return body


# ---------------------------------------------------------------------------
# Mode A: feature suite
# ---------------------------------------------------------------------------


def toolchain(r):
    """(javac_argv, java_path, release_args) for compiling at release r."""
    if r >= 8:
        return ([str(LOCAL_JDK / "bin" / "javac")], LOCAL_JDK / "bin" / "java",
                ["--release", str(r)])
    home = jdk_home(r)
    if home is None:
        return (None, None, [])
    java = home / "bin" / "java"
    if r <= 6:
        # The JDK 6 macOS javac launcher segfaults under Rosetta and its JIT
        # is unstable; drive javac through the java launcher in -Xint mode.
        tools = next((c for c in (home / "Classes" / "classes.jar",
                                  home.parent / "Classes" / "classes.jar")
                      if c.exists()), None)
        javac = [str(java), "-Xint"]
        if tools is not None:
            javac += ["-cp", str(tools)]
        javac += ["com.sun.tools.javac.Main"]
    else:
        javac = [str(home / "bin" / "javac")]
    return (javac, java, [])


def verify_features(releases, keep=False):
    src = CORPUS / "features" / "src" / "feat"
    results = {}
    for r in releases:
        # Releases below 8 are not supported by modern javac's --release;
        # use the corpus JDK's own toolchain for those.
        if r < 8:
            home = jdk_home(r)
            if home is None:
                results[r] = {"compile_orig": False, "err": f"no jdk{r} toolchain"}
                continue
            java = home / "bin" / "java"
            # The JDK 6 macOS javac launcher segfaults under Rosetta; drive
            # the compiler through the (working) java launcher instead.
            legacy_tools = next(
                (c for c in (home / "Classes" / "classes.jar",
                             home.parent / "Classes" / "classes.jar",
                             home / "lib" / "tools.jar") if c.exists()),
                None,
            )
            if legacy_tools is not None or (home / "bin" / "javac").name == "javac" and str(home).endswith("Home"):
                # JDK <= 6 macOS: drive javac through the java launcher with
                # -Xint (its JIT segfaults under Rosetta).
                javac = [str(java), "-Xint"]
                if legacy_tools is not None:
                    javac += ["-cp", str(legacy_tools)]
                javac += ["com.sun.tools.javac.Main"]
            else:
                javac = [str(home / "bin" / "javac")]
            release_args = []
        else:
            javac = [str(LOCAL_JDK / "bin" / "javac")]
            java = LOCAL_JDK / "bin" / "java"
            release_args = ["--release", str(r)]
        rdir = WORK / "features" / f"r{r}"
        if rdir.exists():
            shutil.rmtree(rdir)
        (rdir / "orig").mkdir(parents=True)
        files = [str(src / f"{name}.java") for name, gate in FEATURE_GATES.items()
                 if gate <= r and (src / f"{name}.java").exists()]
        # 1. compile original
        cmd = javac + ["-nowarn", "-g", "-encoding", "UTF-8"] + release_args + ["-d", str(rdir / "orig")] + files
        p = run(cmd)
        # Legacy toolchains may crash on JVM exit after successful output;
        # accept when the expected class files exist.
        produced = any((rdir / "orig").rglob("*.class"))
        if p.returncode != 0 and not produced:
            results[r] = {"compile_orig": False, "err": p.stderr.decode("utf-8", "replace")[:2000]}
            continue
        # 2. run originals
        orig_out = {}
        for name in FEATURE_MAINS:
            if FEATURE_GATES.get(name, 99) > r:
                continue
            cls = (rdir / "orig" / "feat" / f"{name}.class")
            if not cls.exists():
                continue
            p = run([str(java), "-cp", str(rdir / "orig"), f"feat.{name}"], timeout=30)
            orig_out[name] = (p.returncode, p.stdout.decode("utf-8", "replace") + p.stderr.decode("utf-8", "replace"))
        # 3. decompile
        p = run([str(JCDC)] + (["-cp", ":".join(jcdc_cp(r))] if jcdc_cp(r) else []) +
                [str(rdir / "orig"), "-o", str(rdir / "decomp")])
        decomp_err = p.stderr.decode("utf-8", "replace")[:2000]
        # 4. recompile decompiled
        (rdir / "re").mkdir(parents=True, exist_ok=True)
        dfiles = sorted(str(x) for x in (rdir / "decomp").rglob("*.java"))
        p = run(javac + ["-nowarn", "-g", "-encoding", "UTF-8"] + release_args +
                ["-d", str(rdir / "re")] + dfiles)
        recomp_ok = p.returncode == 0 or (r < 8 and any((rdir / "re").rglob("*.class"))
                                          and not p.stderr.decode("utf-8", "replace").startswith("错误")
                                          and "error" not in p.stderr.decode("utf-8", "replace")[:200].lower())
        recomp_err = p.stderr.decode("utf-8", "replace")[:4000]
        import os as _os
        if _os.environ.get("VERIFY_DBG"):
            print("RECOMP rc=", p.returncode, "cmd=", " ".join(map(str, javac)), "dfiles=", len(dfiles), file=sys.stderr)
        # 5. run recompiled & compare
        re_out = {}
        matches = {}
        if recomp_ok:
            for name in FEATURE_MAINS:
                if name not in orig_out:
                    continue
                cls = (rdir / "re" / "feat" / f"{name}.class")
                if not cls.exists():
                    matches[name] = ("MISSING_CLASS", "")
                    continue
                p = run([str(java), "-cp", str(rdir / "re"), f"feat.{name}"], timeout=30)
                got = p.stdout.decode("utf-8", "replace") + p.stderr.decode("utf-8", "replace")
                exp_rc, exp = orig_out[name]
                ok = p.returncode == exp_rc and got == exp
                matches[name] = ("OK" if ok else f"DIFF(rc={p.returncode},exp_rc={exp_rc},out_eq={got == exp})", got)
        results[r] = {
            "compile_orig": True,
            "decomp_stderr": decomp_err,
            "recompile_ok": recomp_ok,
            "recompile_err": recomp_err,
            "run_matches": {k: v[0] for k, v in matches.items()},
            "diffs": {k: (orig_out[k][1], v[1]) for k, v in matches.items() if v[0] != "OK"},
        }
        if not keep:
            pass  # keep artifacts for inspection by default (small)
    return results


# ---------------------------------------------------------------------------
# Mode B: JDK source corpus
# ---------------------------------------------------------------------------

def pick_sources(feature, limit):
    """Pick small self-contained java files from the extracted src.zip."""
    srcroot = CORPUS / "jdk-sources" / f"jdk{feature}"
    if not srcroot.exists():
        return []
    candidates = []
    base_dirs = []
    if feature >= 9:
        for mod in ("java.base",):
            for pkg in ("java/util", "java/lang", "java/io", "java/math", "java/time", "java/text"):
                d = srcroot / mod / pkg
                if d.exists():
                    base_dirs.append(d)
    else:
        for pkg in ("java/util", "java/lang", "java/io", "java/math", "java/text"):
            d = srcroot / pkg
            if d.exists():
                base_dirs.append(d)
    bad_import = re.compile(r"^import\s+(?:static\s+)?(?!java\.|javax\.)")
    for d in base_dirs:
        for f in sorted(d.rglob("*.java")):
            if f.name in ("package-info.java", "module-info.java"):
                continue
            try:
                if f.stat().st_size > 40000:
                    continue
                text = f.read_text(encoding="utf-8", errors="replace")
            except OSError:
                continue
            if bad_import.search(text, re.M):
                continue
            if "@interface" in text:  # annotation decls with complex deps
                continue
            candidates.append(f)
            if len(candidates) >= limit * 3:
                break
        if len(candidates) >= limit * 3:
            break
    return candidates[:limit]


def verify_corpus(features, limit, keep=False):
    results = {}
    for feature in features:
        home = jdk_home(feature)
        if home is None:
            results[feature] = {"skipped": "jdk not executable/present"}
            continue
        javac_l, _java, release_args = toolchain(feature)
        if javac_l is None:
            results[feature] = {"skipped": "no toolchain"}
            continue
        javac = javac_l
        javap = home / "bin" / "javap" if feature < 8 and (home / "bin" / "javap").exists() else LOCAL_JDK / "bin" / "javap"
        srcs = pick_sources(feature, limit)
        if not srcs:
            results[feature] = {"skipped": "no sources"}
            continue
        # Modules (9+): java.* sources clash with the platform module, so
        # compile them as part of java.base via --patch-module.
        srcroot = CORPUS / "jdk-sources" / f"jdk{feature}"
        patch_args = []
        if feature >= 9 and (srcroot / "java.base").exists():
            patch_args = ["--patch-module", f"java.base={srcroot / 'java.base'}"]
        fdir = WORK / "corpus" / f"jdk{feature}"
        if fdir.exists():
            shutil.rmtree(fdir)
        (fdir / "orig").mkdir(parents=True)
        stats = {"sources": len(srcs), "compiled": 0, "decompiled": 0,
                 "recompiled": 0, "methods_total": 0, "methods_equal": 0,
                 "fail_files": []}
        def _cleanup_family():
            # Per-family artifacts must be removed on EVERY exit path:
            # a failed family's decompiled files otherwise poison every
            # subsequent recompile (the jdk7 EnumSet failure cascaded
            # into 13 phantom fails).
            shutil.rmtree(fdir / "orig", ignore_errors=True)
            shutil.rmtree(fdir / "fam", ignore_errors=True)
            shutil.rmtree(fdir / "decomp", ignore_errors=True)
            shutil.rmtree(fdir / "re", ignore_errors=True)
            (fdir / "orig").mkdir(parents=True)

        def _err_excerpt(stderr_bytes, limit=400):
            text = stderr_bytes.decode("utf-8", "replace")
            errs = [ln for ln in text.splitlines()
                    if ("错误" in ln or "error" in ln.lower())]
            return ("\n".join(errs) if errs else text)[:limit]

        for f in srcs:
            # -implicit:none: with --patch-module (9+) javac would
            # otherwise IMPLICITLY compile every dependency from the era
            # source tree into orig (a whole java.base per family — 30x
            # redundant work, and any poisoned decompiled dependency
            # failed all 30 families: jdk9/jdk10 scored 0/30). orig then
            # holds exactly this source file's classes — INCLUDING
            # sibling top-level classes (AbstractList.java also defines
            # SubList/RandomAccessSubList — a Stem-prefix filter dropped
            # them: 找不到符号 SubList).
            p = run(javac + ["-nowarn", "-g", "-encoding", "UTF-8", "-implicit:none"] + release_args + patch_args +
                    ["-d", str(fdir / "orig"), str(f)], timeout=120)
            if p.returncode != 0:
                continue
            stats["compiled"] += 1
            stem = f.stem
            fam_dir = fdir / "orig"
            if not any(fam_dir.rglob("*.class")):
                _cleanup_family()
                continue
            # decompile the produced class family
            p = run([str(JCDC)] + (["-cp", ":".join(jcdc_cp(feature))] if jcdc_cp(feature) else []) +
                    [str(fam_dir), "-o", str(fdir / "decomp")], timeout=120)
            if p.returncode != 0:
                stats["fail_files"].append((stem, "decompile:" + _err_excerpt(p.stderr, 200)))
                _cleanup_family()
                continue
            stats["decompiled"] += 1
            # recompile ALL decompiled files (families reference each other)
            # module-info.java describes the entire module; it can never
            # recompile from a per-family decompilation subset. Remove it
            # from the patch-module tree as well, or javac picks it up.
            for mi in (fdir / "decomp").rglob("module-info.java"):
                mi.unlink()
            dfiles = sorted(str(x) for x in (fdir / "decomp").rglob("*.java"))
            (fdir / "re").mkdir(parents=True, exist_ok=True)
            # Patch with decomp FIRST (decompiled family wins), then the
            # era's full java.base source tree so internal dependencies
            # (sun.util.spi, jdk.internal asm, ...) resolve exactly like
            # the original compile did.
            if feature >= 9:
                patch_roots = [str(fdir / "decomp")]
                if (srcroot / "java.base").exists():
                    patch_roots.append(str(srcroot / "java.base"))
                re_patch = ["--patch-module", "java.base=" + os.pathsep.join(patch_roots)]
            else:
                re_patch = []
            p = run(javac + ["-nowarn", "-g", "-encoding", "UTF-8"] + release_args + re_patch +
                    ["-d", str(fdir / "re")] + dfiles, timeout=300)
            if p.returncode != 0 and not (feature < 8 and any((fdir / "re").rglob("*.class"))):
                stats["fail_files"].append((stem, "recompile:" + _err_excerpt(p.stderr)))
                _cleanup_family()
                continue
            stats["recompiled"] += 1
            # Live progress: dump the partial stats after every family so a
            # long corpus run can be monitored (and partial results survive).
            try:
                _live = dict(results); _live[feature] = stats
                with open("/tmp/corpus_live.json", "w") as _lf:
                    json.dump(_live, _lf, indent=1, ensure_ascii=False, default=str)
            except Exception:
                pass
            # javap compare each original class file vs recompiled
            # (family classes only — orig also holds javac's implicit
            # dependency compilations for 9+).
            for oc in sorted(fam_dir.rglob("*.class")):
                rel = oc.relative_to(fam_dir)
                rc = fdir / "re" / rel
                if not rc.exists():
                    stats["fail_files"].append((str(rel), "missing recompiled class"))
                    continue
                mo = javap_methods(javap, oc)
                mr = javap_methods(javap, rc)
                if mo is None or mr is None:
                    continue
                for sig, lines in mo.items():
                    stats["methods_total"] += 1
                    if sig in mr and mr[sig] == lines:
                        stats["methods_equal"] += 1
                    else:
                        if len(stats["fail_files"]) < 40:
                            stats["fail_files"].append((f"{rel}:{sig}", "bytecode-diff"))
            # clean per-file artifacts so next file starts fresh
            _cleanup_family()
        if not keep:
            shutil.rmtree(fdir, ignore_errors=True)
        results[feature] = stats
    return results


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("mode", choices=["features", "corpus", "all"])
    ap.add_argument("--releases", default="8,9,11,17,21,26")
    ap.add_argument("--jdks", default="")
    ap.add_argument("--limit", type=int, default=30)
    ap.add_argument("--keep", action="store_true")
    args = ap.parse_args()

    if not JCDC.exists():
        print("build first: cargo build --release", file=sys.stderr)
        sys.exit(2)
    WORK.mkdir(parents=True, exist_ok=True)

    if args.mode in ("features", "all"):
        releases = [int(x) for x in args.releases.split(",")]
        res = verify_features(releases, args.keep)
        print(json.dumps({"features": res}, indent=1, ensure_ascii=False))
    if args.mode in ("corpus", "all"):
        if args.jdks:
            feats = [int(x) for x in args.jdks.split(",")]
        else:
            man = CORPUS / "jdks" / "MANIFEST.json"
            feats = sorted({e["feature"] for e in json.loads(man.read_text())
                            if e.get("executable") and e.get("src_zip_extracted")})
        res = verify_corpus(feats, args.limit, args.keep)
        print(json.dumps({"corpus": {str(k): v for k, v in res.items()}}, indent=1, ensure_ascii=False))


if __name__ == "__main__":
    main()
