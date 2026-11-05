#!/usr/bin/env bash
# to-delfos.sh: the Agda exports on delfos (8 threads, 15 G), olimpo's memory is what its emits lack
D=192.168.3.6; G=/tmp/bx/gh; cd $G || exit 1
say() { echo "$(date '+%F %T') $*"; }
r() { ssh -o BatchMode=yes -o ServerAliveInterval=30 $D "$@"; }
XP=$(readlink -f $HOME/src/agda2bend/run/a2b/gcroot-agda-export-t)
LIBS=$(sed 's|/[^/]*$||' $HOME/src/agda2bend/run/a2b/libs/agda-dir/libraries)
say closures; nix copy --no-check-sigs --to ssh-ng://hhefesto@$D $XP $LIBS || { say "nix copy FAILED"; exit 1; }
systemctl --user stop a2b-exp-gh
find u -path '*/out/*' -type l -delete
r 'mkdir -p /tmp/bx/gh/tmpl; : > /tmp/bx/gh/empty'
ls tmpl | r 'cd /tmp/bx/gh/tmpl && while IFS= read -r f; do ln -sf /tmp/bx/gh/empty "$f"; done'
say sources; rsync -a --timeout=600 src u exp1.sh order.txt units.tsv $D:/tmp/bx/gh/ || { say "rsync FAILED"; exit 1; }
r "cd /tmp/bx/gh && systemctl --user reset-failed ana-help-gh 2>/dev/null; systemd-run --user --unit=ana-help-gh --collect -p WorkingDirectory=/tmp/bx/gh -p MemoryMax=13G -p MemorySwapMax=1G -p OOMPolicy=continue -p StandardOutput=append:/tmp/bx/gh/exp.log -p StandardError=append:/tmp/bx/gh/exp.log --setenv=X=$XP/bin/agda-export --setenv=MEMG=3 --setenv=SECS=900 --setenv=PATH=/run/current-system/sw/bin /bin/sh -c 'exec xargs -P 5 -n 1 ./exp1.sh < order.txt'"
say started
systemctl --user reset-failed ana-ghsync 2>/dev/null; systemd-run --user --unit=ana-ghsync --collect -p WorkingDirectory=$G -p StandardOutput=append:$G/sync.log -p StandardError=append:$G/sync.log $G/ghsync.sh
