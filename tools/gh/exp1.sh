#!/usr/bin/env bash
# exp1.sh UNIT: agda-export the unit's modules into u/UNIT/out, its own files only at the end (export4's are symlinks to skip them)
U=$1; A=$HOME/src/agda2bend/run/a2b; X=$A/gcroot-agda-export-t/bin/agda-export
d=/tmp/bx/gh/u/$U; out=$d/out; ev=$d/ev; mkdir -p $out $ev; cd $ev || exit 1
[ -e $d/DONE ] && exit 0
export AGDA_DIR=$d/agda-dir AGDA_EXPORT_ATTEMPT_SECS=20 AGDA_EXPORT_MAX_BYTES=20000000 AGDA_EXPORT_MAX_DEF_BYTES=2000000
SECS=${SECS:-900}; t0=$(date +%s); left() { echo $(( SECS - ($(date +%s) - t0) )); }
cp -a /tmp/bx/gh/tmpl/. $out/
run() { timeout $(( $(left) < $2 ? $(left) : $2 )) nice -n 5 $X --export-dir=$out --export-skip-existing "$1" +RTS -M${MEMG:-4}g -RTS > last.log 2>&1; }
LF=$(cat $d/flags.txt 2>/dev/null)
rm -f part.* Chunk*.agda; split -l 30 -d -a 3 $d/mods.txt part.
for p in part.*; do [ "$(left)" -gt 10 ] || break; k=${p#part.}; { [ -n "$LF" ] && echo "{-# OPTIONS $LF #-}"; echo "module Chunk$k where"; sed 's/^/import /' $p; } > Chunk$k.agda; rm $p
  run Chunk$k.agda 1200; r=$?; rm -f $out/*.part $out/Chunk*.sexp; echo "chunk $k rc=$r" >> log; [ $r -ne 0 ] && tail -8 last.log | cut -c1-200 >> log.err
done
while read -r M; do
  [ -f "$out/$M.sexp" ] || [ -f "$out/$M.sexp.skip" ] && continue
  [ "$(left)" -gt 10 ] || break
  fp=$(printf '%s' "$M" | tr . /)
  src=; while read -r r; do for e in agda lagda lagda.md; do [ -f "$r/$fp.$e" ] && src="$r/$fp.$e"; done; done < $d/roots.txt
  opts=$(grep -m3 -o '{-#[[:space:]]*OPTIONS[^#]*#-}' "$src" 2>/dev/null | sed 's/--safe//g')
  { [ -n "$LF" ] && echo "{-# OPTIONS $LF #-}"; echo "$opts"; printf 'module Stub where\nimport %s\n' "$M"; } > Stub.agda
  run Stub.agda 300; r=$?; rm -f $out/*.part $out/Stub.sexp
  echo "$M rc=$r" >> log; [ $r -ne 0 ] && grep -m1 -A3 -i 'error\|Failed\|not found\|cannot' last.log | tr '\n' ' ' | cut -c1-240 >> log.err && echo >> log.err
done < $d/mods.txt
# own files only
find $out -type l -delete
n=$(ls $out | grep -c '\.sexp$'); echo "$U own=$n of $(wc -l < $d/mods.txt) secs=$(( $(date +%s) - t0 ))"
touch $d/DONE
