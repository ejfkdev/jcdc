#!/usr/bin/env python3
"""jclassd corpus syntax check: decompile with jcdc, recompile with javac.

The corpus at corpus/jclassd/ (gitignored; offline third-party .class test
material) is decompiled wholesale, then every emitted .java is fed back
through javac. Failures are classified into

  syntax-bad      parse-level errors (the hard gate: an emitted file that
                  cannot exist as Java source)
  resolution-bad  symbols/types javac cannot resolve — corpus classpath or
                  fidelity issues, not parse errors
  other           everything else (preview-feature noise, module-info
                  collisions when a whole JDK image is compiled at once)

usage:
    python3 scripts/jclassd_syntax_check.py            # decompile + compile
    python3 scripts/jclassd_syntax_check.py --reuse    # reuse /tmp/jclassd-dec
    python3 scripts/jclassd_syntax_check.py --only cfr/java_8

Baselines (2026-09-15): 1,671 syntax-bad files before the sweep; 1 after —
asm's Artificial$()$Structures, whose name contains '()' and therefore
cannot be spelled in Java source at all (CFR emits the identical invalid
form).
"""
import os
import re
import subprocess
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
JCDC = ROOT / "target/release/jcdc"
JAVAC = Path(
    os.environ.get(
        "JAVAC",
        "/opt/homebrew/opt/openjdk/libexec/openjdk.jdk/Contents/Home/bin/javac",
    )
)
SRC = ROOT / "corpus/jclassd/testcases"
DEC = Path(os.environ.get("JCLASSD_DEC", "/tmp/jclassd-dec"))
RE = Path(os.environ.get("JCLASSD_RE", "/tmp/jclassd-re"))

SYNTAX = re.compile(
    r"';' expected|illegal start of|class, interface, enum, or record expected|"
    r"reached end of file while parsing|<identifier> expected|not a statement|"
    r"orphaned (case|default)|invalid method declaration|unclosed |"
    r"expected|illegal |malformed"
)
RESOLUTION = re.compile(
    r"cannot find symbol|does not exist|duplicate class|incompatible types|"
    r"no suitable (method|constructor)|is not abstract and does not override|"
    r"cannot be applied|is already defined|has private access|"
    r"cannot access|not a statement is unreachable|unreported exception|"
    r"is public, should be declared in a file named|non-static (variable|method)"
)


def decompile():
    DEC.mkdir(parents=True, exist_ok=True)
    t0 = time.time()
    r = subprocess.run(
        [str(JCDC), "-cp", str(SRC), str(SRC), "-o", str(DEC)],
        capture_output=True,
        text=True,
    )
    dt = time.time() - t0
    fails = [l for l in r.stderr.splitlines() if "failed to decompile" in l]
    n = sum(1 for _ in DEC.rglob("*.java"))
    print(f"[decompile] {dt:.1f}s rc={r.returncode} emitted={n} failed={len(fails)}")
    for l in fails:
        print("   !", l[:160])


def groups():
    """(name, emitted dir) pairs, compiled separately: the corpus nests each
    javac-era variant under its own prefix, and same-name classes across
    variants must not collide in one javac invocation."""
    g = [("root", DEC)]
    for d in sorted(DEC.iterdir()):
        if d.is_dir():
            g.append((d.name, d))
            if d.name == "cfr":
                g = [x for x in g if x[1] != d]
                for sub in sorted(d.iterdir()):
                    if sub.is_dir():
                        g.append((f"cfr/{sub.name}", sub))
    return g


def compile_group(name, d):
    files = sorted(
        str(p) for p in (d.glob("*.java") if name == "root" else d.rglob("*.java"))
    )
    if not files:
        return None
    out = RE / name.replace("/", "_")
    out.mkdir(parents=True, exist_ok=True)
    argf = out / "files.txt"
    argf.write_text("\n".join(files))
    # Classpath: the group's own package root — the corpus layout is not a
    # package tree rooted at SRC, so SRC alone cannot resolve the group's
    # own types — plus the emitted tree.
    src_root = SRC if name == "root" else SRC / name
    cp = f"{src_root}{os.pathsep}{SRC}{os.pathsep}{DEC}"
    # English messages: the classifier matches English diagnostics.
    env = dict(os.environ, LANG="en_US.UTF-8", LC_ALL="en_US.UTF-8")
    r = subprocess.run(
        [
            str(JAVAC),
            "-J-Duser.language=en",
            "-J-Duser.country=US",
            "--release",
            "26",
            "--enable-preview",
            "-nowarn",
            "-proc:none",
            "-implicit:none",
            "-Xmaxerrs",
            "1000000",
            "-J-Xmx4g",
            "-d",
            str(out),
            "-cp",
            cp,
            f"@{argf}",
        ],
        capture_output=True,
        text=True,
        cwd=str(DEC),
        env=env,
    )
    (out / "javac.stderr").write_text(r.stderr)
    return r


def classify(out):
    syntax_files, resolution_files, other = {}, {}, {}
    for line in out.splitlines():
        m = re.match(r"^(.+?\.java):(\d+): (error|warning): (.+)$", line)
        if m:
            path, ln, kind, msg = m.groups()
            if kind != "error":
                continue
            if SYNTAX.search(msg):
                syntax_files.setdefault(path, []).append(f"{ln}: {msg}")
            elif RESOLUTION.search(msg):
                resolution_files.setdefault(path, []).append(f"{ln}: {msg}")
            else:
                other.setdefault(path, []).append(f"{ln}: {msg}")
            continue
        m2 = re.match(r"^(error|warning): (.+)$", line)
        if m2 and m2.group(1) == "error":
            other.setdefault("<no-file>", []).append(m2.group(2)[:120])
    return syntax_files, resolution_files, other


def main():
    reuse = "--reuse" in sys.argv
    only = None
    if "--only" in sys.argv:
        only = sys.argv[sys.argv.index("--only") + 1]
    if not reuse:
        decompile()
    total_syntax = 0
    for name, d in groups():
        if only and only != name:
            continue
        r = compile_group(name, d)
        if r is None:
            continue
        sf, rf, of = classify(r.stderr)
        total_syntax += len(sf)
        nfiles = len(list(d.rglob("*.java")))
        print(
            f"\n=== group {name}: {nfiles} files, rc={r.returncode}, "
            f"syntax-bad={len(sf)} resolution-bad={len(rf)} other={len(of)}"
        )
        for p, msgs in sorted(sf.items())[:40]:
            print(f"  SYNTAX {p}")
            for m in msgs[:3]:
                print(f"         {m}")
        if of:
            for p, msgs in list(sorted(of.items()))[:10]:
                print(f"  OTHER  {p}: {msgs[0]}")
    print(f"\nTOTAL syntax-bad files: {total_syntax}")


if __name__ == "__main__":
    main()