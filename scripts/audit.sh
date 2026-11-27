#!/usr/bin/env bash
# Build, kernel-check, and audit the uniform odd-cycle (C_m) Lean 4 formalization.
# Usage: bash scripts/audit.sh
set -euo pipefail
cd "$(dirname "$0")/.."
export PATH="$HOME/.elan/bin:$PATH"

echo "== Checking project files for sorry/admit/axiom/unsafe"
python3 - <<'PY'
import pathlib, re, sys
root = pathlib.Path('.')
targets = [root / 'OddRoot.lean', root / 'OddCycleTarget.lean'] + sorted((root / 'OddCycleTarget').glob('*.lean'))
pat = re.compile(r'\bsorry\b|\badmit\b|^[ \t]*axiom |native_decide|implemented_by|@\[extern|\bunsafe\b', re.M)
bad = []
for p in targets:
    t = p.read_text(encoding='utf-8', errors='replace')
    t = re.sub(r'/-.*?-/', '', t, flags=re.S)
    t = re.sub(r'--.*$', '', t, flags=re.M)
    if pat.search(t):
        bad.append(str(p))
if bad:
    print('Forbidden token found in:', bad, file=sys.stderr)
    sys.exit(1)
print('(none)')
PY

echo "== lake build +OddCycleTarget.Equality"
lake build +OddCycleTarget.Equality

echo "== leanchecker OddRoot OddCycleTarget.Equality"
lake env leanchecker OddRoot OddCycleTarget.Equality

echo "== #print axioms (VerifyResults.lean)"
lake env lean VerifyResults.lean

echo "== audit passed"
