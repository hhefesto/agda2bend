#!/usr/bin/env bash
# emit.sh NAME BIN EXPORT PORT [MOD...]: emit with the check daemon, in run/a2b, into corpus-NAME
N=$1; BIN=$2; EXP=$3; PORT=$4; shift 4
cd ~/src/agda2bend/run/a2b
export A2B_TIMES=1 BEND_NO_TELEMETRY=1 A2B_MAXLINE=100000 A2B_CORPUS_LINE=2000 BEND=/nix/store/xbgrvfxf4abkzr2nimnap7psmcdk0zih-bend/bin/bend
ulimit -s unlimited
O=${OUTD:-corpus-$N}
case $O in /*) A=$O;; *) A=$PWD/$O;; esac
exec ~/src/agda2bend/tools/checkd/with.sh $PWD/checkd-$N $A/src $PORT $BIN emit $EXP $O "$@"
