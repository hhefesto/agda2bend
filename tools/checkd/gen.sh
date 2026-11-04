#!/usr/bin/env bash
# gen.sh BEND OUT: tools/checkd's daemon from the JS inside the binary of BEND (a bend
# wrapper's or the binary itself), so it checks exactly as that bend does: OUT/checkd.js,
# with OUT/base.bend beside it.
set -e
B=$(readlink -f "$1"); O=$2; mkdir -p "$O"
real=$(grep -ao '/nix/store/[a-z0-9]*-bend-[0-9.]*/bin/bend' "$B" | head -1); [ -n "$real" ] && B=$real
D=$(dirname "$(dirname "$B")")/libexec/bend
[ -d "$D" ] || D=$(dirname "$(dirname "$B")")
python3 -I - "$D/bin/bend" "$O/checkd.js" "$(dirname "$0")/server.js" <<'PY'
import sys
b=open(sys.argv[1],'rb').read()
i=b.find(b'function book_valid')
s=b.rfind(b'\x00',0,i); e=b.find(b'\x00',i)
js=b[s+1:e].decode()
k=js.rindex('var main_default = PLUGIN;')
open(sys.argv[2],'w').write(js[:k]+open(sys.argv[3]).read())
PY
cp "$D/bend2/base.bend" "$O/base.bend"
