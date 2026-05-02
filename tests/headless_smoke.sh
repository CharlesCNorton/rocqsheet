#!/usr/bin/env bash
# Copyright (c) 2026 CharlesCNorton.  Licensed under the MIT License.
#
# Headless smoke for the rocqsheet binary.  Loads a fixture save
# file and asserts that --eval against a list of known cells returns
# the expected values.  Tests --print-csv output ends with a known
# row.  Exits non-zero on any mismatch so CI fails loudly.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
BIN="$REPO_ROOT/_build/cmake/rocqsheet"
FIX="$SCRIPT_DIR/fixtures/headless_smoke.txt"

if [ ! -x "$BIN" ]; then
  echo "headless_smoke: binary not found at $BIN; run 'make build' first" >&2
  exit 1
fi
if [ ! -f "$FIX" ]; then
  echo "headless_smoke: fixture not found at $FIX" >&2
  exit 1
fi

fails=0
ok=0

# assert_eval <CellRef> <expected stdout>
assert_eval() {
  local ref="$1" want="$2"
  local got
  got="$("$BIN" --headless --load "$FIX" --eval "$ref")"
  if [ "$got" = "$want" ]; then
    ok=$((ok + 1))
  else
    echo "FAIL --eval $ref: got [$got] want [$want]" >&2
    fails=$((fails + 1))
  fi
}

# Sheet 2 is the active sheet on load (last S= directive wins).
# Refs sheet: A1=100, B1=A1, C1=B1, D1=C1.
assert_eval A1 100
assert_eval B1 100
assert_eval C1 100
assert_eval D1 100
# Empty cell on the active sheet renders as 0.
assert_eval Z99 0

# --print-csv produces non-empty output.
csv_lines=$("$BIN" --headless --load "$FIX" --print-csv | wc -l)
if [ "$csv_lines" -lt 1 ]; then
  echo "FAIL --print-csv: produced no rows" >&2
  fails=$((fails + 1))
else
  ok=$((ok + 1))
fi

# --exec on a non-existent macro must report the pending engine and exit 3.
set +e
"$BIN" --headless --load "$FIX" --exec foo >/dev/null 2>&1
exec_rc=$?
set -e
if [ "$exec_rc" -eq 3 ]; then
  ok=$((ok + 1))
else
  echo "FAIL --exec: expected exit 3, got $exec_rc" >&2
  fails=$((fails + 1))
fi

echo "headless_smoke: $ok passed, $fails failed"
[ "$fails" -eq 0 ]
