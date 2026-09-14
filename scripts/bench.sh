#!/bin/zsh
# Benchmark jcdc against other open-source decompilers on a full SDK jar.
#
# usage: zsh scripts/bench.sh [rt.jar path]
#
# Tools (release jars, drop them in /tmp/bench_tools or set BENCH_TOOLS):
#   cfr-0.152.jar  procyon-decompiler-0.6.0.jar  vineflower-1.11.1.jar
# Each Java tool runs on the same JVM with -Xmx8g; every command is timed
# with /usr/bin/time -l (wall + peak RSS). jcdc runs twice: default
# (parallel, one worker per core) and JCDC_THREADS=1 (sequential) for an
# honest single-thread comparison. One timed run per tool (page cache is
# warm from the jcdc runs that go first).

set -u
RT=${1:-/Users/e/Documents/project/jcdc/corpus/jdks/jdk8/Contents/Home/jre/lib/rt.jar}
TOOLS=${BENCH_TOOLS:-/tmp/bench_tools}
JAVA=/opt/homebrew/opt/openjdk/libexec/openjdk.jdk/Contents/Home/bin/java
JCDC=/Users/e/Documents/project/jcdc/target/release/jcdc
WORK=/tmp/bench_run
XMX=-Xmx8g

echo "host: $(sysctl -n machdep.cpu.brand_string 2>/dev/null || uname -m), $(sysctl -n hw.ncpu) cores, $(($(sysctl -n hw.memsize)/1073741824))GB"
echo "input: $RT ($(unzip -l $RT 2>/dev/null | grep -c '\.class$') classes)"
echo

report() { # name timefile outdir
  local t=$2 o=$3
  local real=$(grep 'real' $t | head -1 | awk '{print $1}')
  local rss=$(grep 'maximum resident' $t | awk '{printf "%.0f", $1/1048576}')
  local files=$(find $o -name '*.java' 2>/dev/null | wc -l | tr -d ' ')
  local bytes=$(du -sk $o 2>/dev/null | awk '{print $1}')
  printf "%-22s %8ss  %6sMB  %6s files  %8sKB\n" "$1" "$real" "$rss" "$files" "$bytes"
}

run_timed() { # label cmd...  (single timed run; page cache already warm
              # from the jcdc runs that go first)
  local label=$1; shift
  rm -rf $WORK/$label; mkdir -p $WORK/$label
  /usr/bin/time -l "$@" > $WORK/$label.run.log 2> $WORK/$label.time
}

echo "=== jcdc (parallel, workers = $(sysctl -n hw.ncpu) cores) ==="
rm -rf $WORK/jcdc-par; mkdir -p $WORK/jcdc-par
/usr/bin/time -l $JCDC -cp $RT $RT -o $WORK/jcdc-par > /dev/null 2> $WORK/jcdc-par.time
report "jcdc (parallel)" $WORK/jcdc-par.time $WORK/jcdc-par

echo "=== jcdc (JCDC_THREADS=1, sequential) ==="
run_timed jcdc-seq env JCDC_THREADS=1 $JCDC -cp $RT $RT -o $WORK/jcdc-seq
report "jcdc (threads=1)" $WORK/jcdc-seq.time $WORK/jcdc-seq

echo "=== Vineflower ==="
run_timed vineflower $JAVA $XMX -jar $TOOLS/vineflower-1.11.1.jar $RT $WORK/vineflower
report "vineflower 1.11.1" $WORK/vineflower.time $WORK/vineflower

echo "=== CFR ==="
run_timed cfr $JAVA $XMX -jar $TOOLS/cfr-0.152.jar $RT --outputdir $WORK/cfr
report "cfr 0.152" $WORK/cfr.time $WORK/cfr

echo "=== Procyon ==="
run_timed procyon $JAVA $XMX -jar $TOOLS/procyon-decompiler-0.6.0.jar -jar $RT -o $WORK/procyon
report "procyon 0.6.0" $WORK/procyon.time $WORK/procyon

echo "done — logs in $WORK"
