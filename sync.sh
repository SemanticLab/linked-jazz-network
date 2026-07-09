#!/bin/sh
# Sync the built viewer from the ch-jazz-mashup pipeline repo into site/.
# Run after any pipeline rebuild (layout, evidence, labels), then commit.
set -e
SRC="${1:-$HOME/git/ch-jazz-mashup/network/web}"
cd "$(dirname "$0")"
rsync -a --delete \
  --exclude ".DS_Store" \
  "$SRC/" site/
echo "synced $(find site -type f | wc -l | tr -d ' ') files, $(du -sh site | cut -f1)"
