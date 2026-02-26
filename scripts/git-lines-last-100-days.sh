#!/usr/bin/env bash

# Print some stats about code volume.

author="$(git config user.name)"

printf "%-12s %10s %10s %10s\n" "Date" "Added" "Removed" "Total"

for i in $(seq 0 99); do
  day=$(date -d "$i days ago" +%Y-%m-%d)
  next_day=$(date -d "$((i-1)) days ago" +%Y-%m-%d)

  if [ "$i" -eq 0 ]; then
    since="$day 00:00"
    until="now"
  else
    since="$day 00:00"
    until="$next_day 00:00"
  fi

  stats=$(git log \
    --since="$since" \
    --until="$until" \
    --author="$author" \
    --pretty=tformat: \
    --numstat)

  added=$(echo "$stats" | awk '{a+=$1} END {print a+0}')
  removed=$(echo "$stats" | awk '{r+=$2} END {print r+0}')
  total=$((added + removed))

  printf "%-12s %10d %10d %10d\n" "$day" "$added" "$removed" "$total"
done
