#!/usr/bin/env bash
# ghsched2.sh (11-05 22:40, R5c's plan is 11 hours shorter): shards here beside delfos's, from the units reserved in delfos's assigned.tsv (tag olimpo), until GHCUT (run5c.sh, gh-cut.sh).  Numbers from 40: delfos counts from 12.
G=/tmp/bx/gh; cd $G || exit 1
STOP=$(date -d "${STOPAT:-2026-11-06 02:55}" +%s); A=$HOME/src/agda2bend/run/a2b
say() { echo "$(date '+%F %T') $*"; }
k=${K0:-40}; while [ -e $A/export-gh$k ]; do k=$((k + 1)); done
BIN=${BIN:-k12}
while [ "$(date +%s)" -lt "$STOP" ]; do
  run=$(systemctl --user list-units --type=service --state=active --no-legend --plain 'a2b-gh[0-9]*' | wc -l)
  av=$(awk '/^MemAvailable/ {print int($2/1048576)}' /proc/meminfo)
  mj=$(cat $G/maxj 2>/dev/null || echo 1)
  if [ "$run" -lt "$mj" ] && [ "$av" -ge ${AVMIN:-14} ]; then
    n=$(python3 -I $G/shard.py $k ${MAXM:-500} ${MINM:-100})
    if [ "$n" != 0 ]; then
      say "gh$k: $n modules of $(wc -l < $A/ev-gh$k/units.txt) units"
      cd $A; AUTO=6 WRAP=2000 /tmp/bx/a2p/go.sh gh$k 12G $BIN export-gh$k $((47200 + k)) $(cat ev-gh$k/own.txt) 2>&1 | cut -c1-60
      systemctl --user set-property --runtime a2b-gh$k CPUWeight=100
      cd $G; k=$((k + 1))
    fi
  fi
  sleep 120
done
say "stop time"
