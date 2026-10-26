#!/usr/bin/env python3
"""Fetch pinned dependency sources and official Mathlib cache for local checking.

Only for hosts where standalone Lean cannot locate its application. No compiler
or kernel is changed. This does not establish independently replayed dependencies.
"""
import json
import os
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
TC = Path(os.environ['KMV_LEAN_ROOT']).resolve()
manifest = json.loads((ROOT / 'lake-manifest.json').read_text())
for p in manifest['packages']:
    target = ROOT / '.lake/packages' / p['name']
    if not target.exists():
        target.mkdir(parents=True)
        subprocess.run(['git', 'init', str(target)], check=True)
        subprocess.run(['git', '-C', str(target), 'remote', 'add', 'origin', p['url']], check=True)
        subprocess.run(['git', '-C', str(target), 'fetch', '--depth=1', 'origin', p['rev']], check=True)
        subprocess.run(['git', '-C', str(target), 'checkout', '--detach', p['rev']], check=True)
    actual = subprocess.check_output(['git', '-C', str(target), 'rev-parse', 'HEAD'], text=True).strip()
    if actual != p['rev']:
        raise RuntimeError('Dependency revision mismatch: ' + p['name'])

scratch = ROOT / '.lake/bootstrap'
bin_dir = scratch / 'bin'
bin_dir.mkdir(parents=True, exist_ok=True)
prefix_helper = bin_dir / 'lean'
prefix_helper.write_text('''#!/bin/sh
# Mathlib cache installation locator only; no replacement proof checker.
if [ "$#" -eq 1 ] && [ "$1" = "--print-prefix" ]; then
  printf '%s\\n' "$KMV_LEAN_ROOT"
else
  exec "$KMV_LEAN_ROOT/bin/lean" "$@"
fi
''')
prefix_helper.chmod(0o700)
os.environ['PATH'] = str(bin_dir) + os.pathsep + os.environ['PATH']
sys.path.insert(0, str(ROOT / 'scripts'))
import local_check
local_check.build('Cache.Requests')
fetch = scratch / 'Fetch.lean'
fetch.write_text('''import Cache.Requests
open Cache Cache.IO Cache.Hashing Cache.Requests
#eval do
  let sp : System.SearchPath := ((← IO.getEnv "LEAN_SRC_PATH").getD "").splitOn ":" |>.map System.FilePath.mk
  let action : CacheM Unit := do
    let roots ← parseArgs ["get", "Mathlib.Data.Finset.Card", "Mathlib.Analysis.SpecialFunctions.Pow.Real", "Mathlib.Combinatorics.Pigeonhole", "Mathlib.Tactic.IntervalCases", "Mathlib.Tactic.Linarith", "Mathlib.Tactic.Ring", "Mathlib.Data.Finset.Powerset", "Mathlib.Data.Finset.Max", "Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics", "Mathlib.Tactic.GCongr", "Mathlib.Algebra.Order.Floor.Semiring"]
    let memo ← getHashMemo roots
    let hashes ← memo.filterByRootModules roots.keys
    let curl ← validateCurl
    getFiles "leanprover-community/mathlib4" hashes false false curl true
  ReaderT.run action { mathlibDepPath := ".lake/packages/mathlib", srcSearchPath := sp }
''')
local_check.check(fetch, 'Fetch', cwd=ROOT)
