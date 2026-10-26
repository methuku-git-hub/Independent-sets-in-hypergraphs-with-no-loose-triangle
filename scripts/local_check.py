#!/usr/bin/env python3
"""Local Lean frontend host, using unmodified Lake/Lean at trustLevel=0.

This is development evidence only, not a substitute for Palomar preflight.
Set KMV_LEAN_ROOT to the pinned Lean installation. --deps bootstraps the
ordinary Cache helper modules from their pinned sources; no proof is assumed.
"""
import os
import pathlib
import re
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
TC = pathlib.Path(os.environ['KMV_LEAN_ROOT']).resolve()
PACKAGES = sorted((ROOT / '.lake/packages').glob('*'))
ROOTS = [ROOT, *PACKAGES]
ENV = os.environ.copy()
ENV.update(LAKE_HOME=str(TC), LEAN_SYSROOT=str(TC))
ENV['LEAN_PATH'] = ':'.join(str(p / '.lake/build/lib/lean') for p in ROOTS)
ENV['LEAN_SRC_PATH'] = ':'.join(str(p) for p in ROOTS)

def check(path, module, output=None, cwd=ROOT):
    if output:
        output.parent.mkdir(parents=True, exist_ok=True)
    command = [str(TC / 'bin/lake'), '-d', str(ROOT / 'tools/frontend'),
               'script', 'run', 'check', str(path), module,
               str(output) if output else '', str(cwd)]
    subprocess.run(command, env=ENV, check=True)

seen = set()
def build(module):
    if module in seen: return
    seen.add(module)
    relative = pathlib.Path(*module.split('.'))
    if (TC / 'lib/lean' / relative.with_suffix('.olean')).is_file(): return
    for base in ROOTS:
        src = base / relative.with_suffix('.lean')
        if src.is_file(): break
    else: raise RuntimeError('Missing source: ' + module)
    out = base / '.lake/build/lib/lean' / relative.with_suffix('.olean')
    if out.is_file(): return
    for line in src.read_text().splitlines():
        match = re.match(r'\s*(?:public |meta )*import\s+([\w.]+)', line)
        if match: build(match[1])
    print('CHECK', module, flush=True)
    check(src, module, out)

if __name__ == '__main__':
    if sys.argv[1] == '--deps':
        for module in sys.argv[2:]: build(module)
    else:
        module = sys.argv[1]
        source = ROOT / pathlib.Path(*module.split('.')).with_suffix('.lean')
        output = ROOT / '.lake/build/lib/lean' / pathlib.Path(*module.split('.')).with_suffix('.olean')
        check(source, module, output)
