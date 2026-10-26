#!/usr/bin/env python3
"""Rebuild this checkpoint's implemented modules and record exact evidence.

Default uses the standard Lean CLI under Lake. --local uses the documented
Lake frontend host for this execution environment. Neither is Palomar's
official reusable mechanical preflight. The main result is implemented; official preflight remains separate.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
from datetime import datetime, timezone

ROOT = Path(__file__).resolve().parents[1]
MODULES = ['KMV.Basic', 'KMV.Statements', 'KMV.Expansion', 'KMV.Compression',
           'KMV.Codegrees', 'KMV.Triangles', 'KMV.Coloring', 'KMV.Auxiliary', 'KMV.FiniteLaw', 'KMV.Entropy', 'KMV.SamplingProcess', 'KMV.SamplingIndependent', 'KMV.SamplingProducts', 'KMV.SamplingCap', 'KMV.SamplingEntropy', 'KMV.SamplingMarginals', 'KMV.Sampling', 'KMV.Packing', 'KMV.DensityStructure', 'KMV.DensityStars', 'KMV.DensityCounting', 'KMV.Density', 'KMV.Deletion', 'KMV.Trimming', 'KMV.AuxiliaryDegrees', 'KMV.ColoringSubset', 'KMV.TriangleCleaning', 'KMV.TriangleClassification', 'KMV.ConfigurationCounting', 'KMV.PairConfigurations', 'KMV.ConfigurationLoss', 'KMV.TriangleCover', 'KMV.IntersectionCounting', 'KMV.RandomDegrees', 'KMV.ConfigurationMonotone', 'KMV.Cleaning', 'KMV.TotalLoss', 'KMV.FiniteCleaning', 'KMV.GraphRestriction', 'KMV.RestrictedSampling', 'KMV.Reduction', 'KMV.SamplingCleaning', 'KMV.Scales', 'KMV.LossEnvelope', 'KMV.Parameters', 'KMV.SamplingParameters', 'KMV.ColorParameters', 'KMV.AssemblyBounds', 'KMV.ReducedAssembly', 'KMV.Main', 'KMV', 'Solution', 'Audit']

def hashes():
    paths = [*ROOT.glob('*.lean'), *ROOT.glob('KMV/*.lean'),
             *ROOT.glob('scripts/*.py'), ROOT / 'tools/frontend/lakefile.lean',
             ROOT / 'lean-toolchain', ROOT / 'lakefile.toml', ROOT / 'lake-manifest.json']
    return {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
            for p in sorted(paths)}

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--local', action='store_true')
    args = parser.parse_args()
    evidence = ROOT / 'evidence'
    evidence.mkdir(exist_ok=True)
    before = hashes()
    shutil.rmtree(ROOT / '.lake/build', ignore_errors=True)
    (evidence / 'declaration-audit.json').unlink(missing_ok=True)
    report = {'scope': 'full conditional main theorem and project proof development',
              'main_theorem_verified': False, 'official_preflight': 'not run',
              'checked_at_utc': datetime.now(timezone.utc).isoformat(),
              'host': 'Lake Lean.Elab.runFrontend trustLevel=0' if args.local else 'Lean CLI',
              'source_sha256': before, 'checks': []}
    for mod in [*MODULES, 'Challenge']:
        if args.local:
            cmd = [sys.executable, 'scripts/local_check.py', mod]
        else:
            source = mod.replace('.', '/') + '.lean'
            output = ROOT / '.lake/build/lib/lean' / (mod.replace('.', '/') + '.olean')
            output.parent.mkdir(parents=True, exist_ok=True)
            cmd = ['lake', 'env', 'lean', source, '-o', str(output)]
        run = subprocess.run(cmd, cwd=ROOT, capture_output=True, text=True)
        log = run.stdout + run.stderr
        (evidence / (mod.replace('.', '-') + '.log')).write_text(log)
        report['checks'].append({'module': mod, 'command': cmd, 'exit_code': run.returncode,
                                'contains_permitted_statement_placeholder': mod == 'Challenge'})
        print(mod, 'PASS' if run.returncode == 0 else 'FAIL', flush=True)
        (evidence / 'verification.json').write_text(json.dumps(report, indent=2) + '\n')
        if run.returncode:
            print(log)
            return 1
    if hashes() != before:
        raise RuntimeError('Sources changed during verification')
    report['all_implemented_modules_checked'] = True
    audit = json.loads((evidence / 'declaration-audit.json').read_text())
    if not audit['main_theorem_verified']:
        raise RuntimeError('Main theorem audit did not succeed')
    report['main_theorem_verified'] = True
    (evidence / 'verification.json').write_text(json.dumps(report, indent=2) + '\n')
    return 0

if __name__ == '__main__':
    raise SystemExit(main())
