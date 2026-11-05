#!/usr/bin/env bash
# units.sh STATE TREE PORT N CMD...: CMD with BEND pointing at bendu and N daemons over TREE (a2bsrc.sh's module tree,
# TREE/mods/...), on ports PORT.., each restarted if it dies.  BEND: the real bend.
H=$(cd "$(dirname "$0")" && pwd)
S=$1; TREE=$(realpath "$2"); PORT=$3; N=$4; shift 4
BUN=${BUN:-$(ls -d /nix/store/*-bun-1.4.2/bin/bun | head -1)}
sups=
for ((i = 0; i < N; i++)); do
  d=$S.$i; mkdir -p "$d"
  "$H/gen.sh" "$BEND" "$d/g"
  echo $((PORT + i)) > "$d/port"
  ( while :; do "$BUN" "$d/g/checkd.js" $((PORT + i)) "$TREE" >> "$d/log" 2>&1 & echo $! > "$d/pid"; wait $!; sleep 1; done ) &
  sups="$sups $!"
done
trap 'for p in $sups; do kill $p 2>/dev/null; done; for ((i = 0; i < N; i++)); do kill "$(cat "$S.$i/pid")" 2>/dev/null; done' EXIT
sleep 3
export A2B_BEND=$BEND A2B_TREE=$TREE A2B_CHECKD_BASE=$S A2B_CHECKD_N=$N BEND=$H/bendu
"$@"
