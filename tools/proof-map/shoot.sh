#!/bin/sh
# Screenshots of a map in headless Chrome: every section in every mode, light and dark.
# usage: shoot.sh <map.json> <out dir> [width] [height] [zoom]
# width and height are screen pixels. A zoom of 2 shows the page as a browser at 200 % does, a CSS
# viewport of width/zoom at that device scale, and 0.67 as at 67 %. THEMES="light" limits the themes.
# The page reads the map from file:// with --allow-file-access-from-files, so no server is needed.
set -e
here=$(cd "$(dirname "$0")" && pwd)
map=$(cd "$(dirname "$1")" && pwd)/$(basename "$1")
out=$2; w=${3:-1400}; h=${4:-2000}; z=${5:-1}
cw=$(python3 -c "print(round($w / $z))"); ch=$(python3 -c "print(round($h / $z))")
tag=""; [ "$z" = 1 ] || tag="-z$z"
mkdir -p "$out"
rel=$(python3 -c 'import os,sys; print(os.path.relpath(sys.argv[1], sys.argv[2]))' "$map" "$here/page")
secs=$(node -e 'const m=require(process.argv[1]); console.log([...m.sections.map(s=>s.id), ...((m.examples||[]).length?["examples"]:[])].join(" "))' "$map")
modes=$(node -e 'const m=require(process.argv[1]); console.log(m.modes? m.modes.options.map(o=>o.id).join(" ") : "-")' "$map")
for theme in ${THEMES:-light dark}; do for m in $modes; do for s in $secs; do
  q="map=$rel"; [ "$m" = "-" ] || q="$q&mode=$m"
  flag=""; [ "$theme" = dark ] && flag="--force-dark-mode --blink-settings=preferredColorScheme=0"
  timeout 90 google-chrome --headless=new --disable-gpu --hide-scrollbars --allow-file-access-from-files $flag \
    --virtual-time-budget=25000 --window-size=$cw,$ch --force-device-scale-factor=$z --screenshot="$out/$theme-$m-$s$tag.png" "file://$here/page/index.html?$q#$s" >/dev/null 2>&1 || true
done; done; done
ls "$out"
