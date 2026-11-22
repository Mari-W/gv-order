#!/bin/sh
# Screenshots of a map in headless Chrome: every section in every mode, light and dark.
# usage: shoot.sh <map.json> <out dir> [width] [height]
# The page reads the map from file:// with --allow-file-access-from-files, so no server is needed.
set -e
here=$(cd "$(dirname "$0")" && pwd)
map=$(cd "$(dirname "$1")" && pwd)/$(basename "$1")
out=$2; w=${3:-1400}; h=${4:-2000}
mkdir -p "$out"
rel=$(python3 -c 'import os,sys; print(os.path.relpath(sys.argv[1], sys.argv[2]))' "$map" "$here/page")
secs=$(node -e 'const m=require(process.argv[1]); console.log([...m.sections.map(s=>s.id), ...((m.examples||[]).length?["examples"]:[])].join(" "))' "$map")
modes=$(node -e 'const m=require(process.argv[1]); console.log(m.modes? m.modes.options.map(o=>o.id).join(" ") : "-")' "$map")
for theme in light dark; do for m in $modes; do for s in $secs; do
  q="map=$rel"; [ "$m" = "-" ] || q="$q&mode=$m"
  flag=""; [ "$theme" = dark ] && flag="--force-dark-mode --blink-settings=preferredColorScheme=0"
  timeout 90 google-chrome --headless=new --disable-gpu --hide-scrollbars --allow-file-access-from-files $flag \
    --virtual-time-budget=25000 --window-size=$w,$h --screenshot="$out/$theme-$m-$s.png" "file://$here/page/index.html?$q#$s" >/dev/null 2>&1 || true
done; done; done
ls "$out"
