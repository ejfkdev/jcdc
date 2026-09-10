#!/bin/zsh
cd /Users/e/Documents/project/jcdc
cargo build --release --bin jcdc 2>&1 | grep -E '^error' && exit 1
cargo build --bin jcdc 2>&1 | grep -E '^error' && exit 1
PARSE='
import sys,json
raw=sys.stdin.read()
dec=json.JSONDecoder();i=0;n=len(raw);ok=0;tot=0;bad=[]
while i<n:
    while i<n and raw[i]!="{": i+=1
    if i>=n: break
    try: v,e=dec.raw_decode(raw,i);i=e
    except: i+=1
    if isinstance(v,dict) and "features" in v:
        for r,val in v["features"].items():
            rm=val.get("run_matches",{})
            for k,x in rm.items():
                tot+=1
                if x=="OK": ok+=1
                else: bad.append(f"{r}:{k}={x}")
            if not val.get("recompile_ok"): bad.append(f"{r}:recompile_fail")
print(f"{ok}/{tot} {bad}")
'
echo "walk $(python3 scripts/verify.py features --releases 6,7,8,9,11,17,21,26 2>&1 | python3 -c "$PARSE")"
echo "sese $(JCDC_SESE=1 python3 scripts/verify.py features --releases 6,7,8,9,11,17,21,26 2>&1 | python3 -c "$PARSE")"
