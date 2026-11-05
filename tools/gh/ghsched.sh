#!/usr/bin/env bash
# ghsched.sh: shards of the GitHub repositories' exported modules (shard.py), each an emit a2b-ghK on the same binary and flags as the libraries',
# while there is memory; run5c.sh takes them at the deadline like the others.  MAXJ in /tmp/bx/gh/maxj.  Ends at STOP or when run5c.sh has moved on.
G=/tmp/bx/gh; cd $G || exit 1
STOP=$(date -d "${STOPAT:-2026-11-05 18:30}" +%s); A=$HOME/src/agda2bend/run/a2b
say() { echo "$(date '+%F %T') $*"; }
k=${K0:-1}; while [ -e $A/export-gh$k ]; do k=$((k + 1)); done
BIN=${BIN:-k10}
while [ "$(date +%s)" -lt "$STOP" ]; do
  tail -n 1 $HOME/src/ana/run/v8/run5c.log | grep -q 'waiting for the emits' || { say "run5c.sh moved on"; exit 0; }
  systemctl --user is-active -q a2b-exp-gh || touch $G/export.ended
  run=$(systemctl --user list-units --type=service --state=active --no-legend --plain 'a2b-gh[0-9]*' | wc -l)
  av=$(awk '/^MemAvailable/ {print int($2/1048576)}' /proc/meminfo)
  mj=$(cat $G/maxj 2>/dev/null || echo 1)
  if [ "$run" -lt "$mj" ] && [ "$av" -ge 8 ]; then
    n=$(python3 -I $G/shard.py $k ${MAXM:-700} ${MINM:-250})
    if [ "$n" != 0 ]; then
      say "gh$k: $n modules of $(wc -l < $A/ev-gh$k/units.txt) units"
      cd $A; AUTO=6 WRAP=2000 /tmp/bx/a2p/go.sh gh$k 8G $BIN export-gh$k $((47200 + k)) $(cat ev-gh$k/own.txt) 2>&1 | cut -c1-60
      systemctl --user set-property --runtime a2b-gh$k CPUWeight=50
      cd $G; k=$((k + 1))
    fi
  fi
  sleep 120
done
say "stop time"
