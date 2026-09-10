#!/bin/zsh
# Re-run the three family censuses with the current debug binary (SESE path).
# usage: census_run.sh <dir> <release>
set -u
D=$1; R=$2
JCDC=/Users/e/Documents/project/jcdc/target/debug/jcdc
RT=/Users/e/Documents/project/jcdc/corpus/jdks/jdk8/Contents/Home/jre/lib/rt.jar
SRC=/Users/e/Documents/project/jcdc/corpus/jdk-sources/jdk$R/java.base
JAVAC=/opt/homebrew/opt/openjdk/libexec/openjdk.jdk/Contents/Home/bin/javac
rm -rf "$D/dec" "$D/re"
mkdir -p "$D/dec" "$D/re"
unset JCDC_SESE
"$JCDC" -cp "$RT" "$D/orig" -o "$D/dec" 2>"$D/dec_err.log"
find "$D/dec" -name module-info.java -delete
"$JAVAC" -nowarn -g -encoding UTF-8 --release "$R" -Xmaxerrs 10000 \
  --patch-module "java.base=$D/dec:$SRC" \
  -d "$D/re" $(find "$D/dec" -name '*.java') > "$D/re_walk.log" 2>&1
echo "jdk$R errors: $(grep -c ": 错误:" "$D/re_walk.log")"
