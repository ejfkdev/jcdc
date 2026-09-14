#!/bin/zsh
# Benchmark jcdc against other open-source decompilers.
#
# usage: zsh scripts/bench.sh
#
# Workloads:
#   1. jdk8 rt.jar       — 20,413 class entries (12,609 top-level units)
#   2. jdk26 full image  — every class of the newest JDK, i.e. the post-JDK8
#      successor of rt.jar (JDK 9+ has no rt.jar: the boot classpath moved
#      into the module image lib/modules). Build it with:
#        jdk26/bin/jimage extract --dir X jdk26/lib/modules
#        for m in X/*/; do rsync -a --exclude module-info.class "$m" Y/; done
#        (cd Y && jar cf jdk26-full.jar .)     # 27,855 classes
#      (module-info.class is dropped: 68 modules share that one path.)
#
# Tools (jars in /tmp/bench_tools, or set BENCH_TOOLS):
#   vineflower-1.11.1.jar  cfr-0.152.jar  procyon-decompiler-0.6.0.jar
#   fernflower.jar (built from JetBrains/fernflower @2ceaf9f: javac with
#   org.jetbrains:annotations on the classpath, annotations merged in,
#   Main-Class ConsoleDecompiler)
#
# Every Java tool runs on the same JVM with -Xmx8g; each run is timed with
# /usr/bin/time -l (wall + peak RSS). jcdc additionally runs with
# JCDC_THREADS=1 for an honest single-thread comparison. fernflower emits a
# JAR of sources for jar input — it is unpacked (untimed) for counting.
# Vineflower exhausts an 8g heap on the jdk26 image (it catches the per-class
# OutOfMemoryError and writes nothing): it is retried up a heap ladder until
# a run logs no "Java heap space", and the row is labelled with the heap that
# finally worked. Each attempt is capped (it otherwise thrashes for tens of
# minutes), so a capped attempt counts as exhausted. Knobs:
#   VINE_HEAPS="8 16 32"        heap ladder in GB
#   VINE_ATTEMPT_TIMEOUT=900    seconds per attempt (alarm(2) via perl)
#
# Set BENCH_WORKLOADS to run a subset, e.g.:
#   BENCH_WORKLOADS=jdk26-all-modules zsh scripts/bench.sh

set -u
TOOLS=${BENCH_TOOLS:-/tmp/bench_tools}
JAVA=/opt/homebrew/opt/openjdk/libexec/openjdk.jdk/Contents/Home/bin/java
JCDC=/Users/e/Documents/project/jcdc/target/release/jcdc
RT8=/Users/e/Documents/project/jcdc/corpus/jdks/jdk8/Contents/Home/jre/lib/rt.jar
RT26=$TOOLS/jdk26-full.jar
WORK=/tmp/bench_run
XMX=-Xmx8g

echo "host: $(uname -m), $(sysctl -n hw.ncpu) cores, $(($(sysctl -n hw.memsize)/1073741824))GB"
echo "inputs: rt.jar(jdk8) $(unzip -l $RT8 | grep -c '\.class$') classes; jdk26-full.jar $(unzip -l $RT26 | grep -c '\.class$') classes"
echo

report() { # label timefile outdir
  local real=$(grep 'real' $2 | head -1 | awk '{print $1}')
  local rss=$(grep 'maximum resident' $2 | awk '{printf "%.0f", $1/1048576}')
  local files=$(find $3 -name '*.java' 2>/dev/null | wc -l | tr -d ' ')
  local kb=$(du -sk $3 2>/dev/null | awk '{print $1}')
  printf "%-28s %8ss %7sMB %7s files %9sKB\n" "$1" "$real" "$rss" "$files" "$kb"
}

bench_workload() { # workload-name input-jar
  local W=$1 IN=$2
  echo "================ workload: $W ================"

  rm -rf $WORK/$W-jcdc-par; mkdir -p $WORK/$W-jcdc-par
  /usr/bin/time -l $JCDC -cp $IN $IN -o $WORK/$W-jcdc-par > /dev/null 2> $WORK/$W-jcdc-par.time
  report "jcdc (parallel)" $WORK/$W-jcdc-par.time $WORK/$W-jcdc-par

  rm -rf $WORK/$W-jcdc-seq; mkdir -p $WORK/$W-jcdc-seq
  /usr/bin/time -l env JCDC_THREADS=1 $JCDC -cp $IN $IN -o $WORK/$W-jcdc-seq > /dev/null 2> $WORK/$W-jcdc-seq.time
  report "jcdc (JCDC_THREADS=1)" $WORK/$W-jcdc-seq.time $WORK/$W-jcdc-seq

  # Vineflower exhausts small heaps on the jdk26 image; climb the ladder
  # until a run logs no "Java heap space", and label the row.
  local vf_label="vineflower 1.11.1"
  local vf_cap=${VINE_ATTEMPT_TIMEOUT:-900}
  for heap in ${=VINE_HEAPS:-8 16 32}; do
    rm -rf $WORK/$W-vineflower; mkdir -p $WORK/$W-vineflower
    /usr/bin/time -l perl -e 'alarm shift; exec @ARGV' $vf_cap $JAVA -Xmx${heap}g -jar $TOOLS/vineflower-1.11.1.jar $IN $WORK/$W-vineflower > $WORK/$W-vineflower.log 2> $WORK/$W-vineflower.time
    if ! grep -q "Java heap space" $WORK/$W-vineflower.log; then break; fi
  done
  if [ $heap -ne 8 ]; then vf_label="vineflower 1.11.1 (${heap}g)"; fi
  report "$vf_label" $WORK/$W-vineflower.time $WORK/$W-vineflower

  rm -rf $WORK/$W-fernflower; mkdir -p $WORK/$W-fernflower
  /usr/bin/time -l $JAVA $XMX -jar $TOOLS/fernflower.jar $IN $WORK/$W-fernflower > $WORK/$W-fernflower.log 2> $WORK/$W-fernflower.time
  # fernflower writes a sources JAR for jar input; unpack (untimed) to count
  (cd $WORK/$W-fernflower && for j in *.jar; do [ -f "$j" ] && unzip -oq "$j" -d src_out && rm "$j"; done) 2>/dev/null
  report "fernflower (JetBrains)" $WORK/$W-fernflower.time $WORK/$W-fernflower

  rm -rf $WORK/$W-cfr; mkdir -p $WORK/$W-cfr
  /usr/bin/time -l $JAVA $XMX -jar $TOOLS/cfr-0.152.jar $IN --outputdir $WORK/$W-cfr > $WORK/$W-cfr.log 2> $WORK/$W-cfr.time
  report "cfr 0.152" $WORK/$W-cfr.time $WORK/$W-cfr

  rm -rf $WORK/$W-procyon; mkdir -p $WORK/$W-procyon
  /usr/bin/time -l $JAVA $XMX -jar $TOOLS/procyon-decompiler-0.6.0.jar -jar $IN -o $WORK/$W-procyon > $WORK/$W-procyon.log 2> $WORK/$W-procyon.time
  report "procyon 0.6.0" $WORK/$W-procyon.time $WORK/$W-procyon
}

for w in ${=BENCH_WORKLOADS:-rt-jar-jdk8 jdk26-all-modules}; do
  case $w in
    rt-jar-jdk8) bench_workload rt-jar-jdk8 $RT8 ;;
    jdk26-all-modules) bench_workload jdk26-all-modules $RT26 ;;
    *) echo "unknown workload: $w" >&2; exit 1 ;;
  esac
done
echo "done — logs in $WORK"
