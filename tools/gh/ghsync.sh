#!/usr/bin/env bash
# ghsync.sh: delfos exports (ana-help-gh); each unit it has finished comes back here, whole, and only then counts as DONE for shard.py
D=192.168.3.6; G=/tmp/bx/gh; cd $G || exit 1
say() { echo "$(date '+%F %T') $*"; }
R="ssh -o BatchMode=yes -o ServerAliveInterval=30 $D"
while :; do
  act=$($R 'systemctl --user is-active ana-help-gh2' 2>/dev/null)
  for U in $($R 'cd /tmp/bx/gh/u; ls -d */DONE 2>/dev/null' 2>/dev/null | sed 's|/DONE$||'); do
    [ -e "u/$U/DONE" ] && continue
    rsync -a --delete --timeout=300 "$D:/tmp/bx/gh/u/$U/out/" "u/$U/out/" && rsync -a --timeout=300 "$D:/tmp/bx/gh/u/$U/ev/log" "u/$U/ev.log" 2>/dev/null; touch "u/$U/DONE"
  done
  rsync -a --timeout=60 $D:/tmp/bx/gh/exp.log exp-delfos.log 2>/dev/null
  [ "$act" = active ] || [ "$act" = activating ] || { say "delfos: $act"; break; }
  sleep 60
done
