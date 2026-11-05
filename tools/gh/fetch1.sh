#!/usr/bin/env bash
# fetch1.sh REPO OID: the Agda sources and licence of owner__name at OID into src/REPO (no build files, no symlinks)
r=$1; oid=$2; o=${r%%__*}; n=${r#*__}; d=/tmp/bx/gh/src/$r
[ -e $d/.done ] && exit 0
rm -rf $d; mkdir -p $d
curl -sSfL --max-time 300 "https://codeload.github.com/$o/$n/tar.gz/$oid" | tar xz --no-same-owner --strip-components=1 -C $d --wildcards '*.agda' '*.lagda' '*.lagda.md' '*.agda-lib' '*LICENSE*' '*LICENCE*' '*COPYING*' 2>/dev/null
find $d -type l -delete
echo "$oid" > $d/.oid
touch $d/.done
echo "$r $(find $d -name '*.agda' -o -name '*.lagda' -o -name '*.lagda.md' | wc -l) $(du -sh $d | cut -f1)"
