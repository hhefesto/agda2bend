#!/usr/bin/env bash
# with.sh STATE SRC PORT CMD...: CMD with BEND pointing at tools/checkd's client and the
# daemon running, restarted if it dies, over SRC (the emit's OUT/src). BEND: the real bend.
H=$(cd "$(dirname "$0")" && pwd)
S=$1; SRC=$2; PORT=$3; shift 3
mkdir -p "$S" "$SRC"
BUN=${BUN:-$(ls -d /nix/store/*-bun-1.4.2/bin/bun | head -1)}
"$H/gen.sh" "$BEND" "$S/g"
echo "$PORT" > "$S/port"
( while :; do "$BUN" "$S/g/checkd.js" "$PORT" "$SRC" >> "$S/log" 2>&1 & echo $! > "$S/pid"; wait $!; sleep 1; done ) &
sup=$!
trap 'kill $sup $(cat "$S/pid") 2>/dev/null' EXIT
sleep 3
export A2B_CHECKD=$S A2B_BEND=$BEND BEND=$H/bendc
"$@"
