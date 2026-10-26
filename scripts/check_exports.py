#!/usr/bin/env python3
"""Read-only validation of exports made from the checked local source.

Runs the pinned Lake comparison/axiom functions and the bundled kernels on
NDJSON proof data. This does not evaluate project configuration, build source
inside bubblewrap, or claim Palomar's complete official preflight.
"""
from pathlib import Path
import datetime
import hashlib
import json
import re
import subprocess
import sys
import local_check

ROOT = local_check.ROOT
OUT = ROOT / '.lake/exports'
OUT.mkdir(parents=True, exist_ok=True)
cfg = json.loads((ROOT/'comparator.json').read_text())
primitives = ['Nat.add','Nat.sub','Nat.mul','Nat.pow','Nat.gcd','Nat.div','Nat.mod',
 'Nat.beq','Nat.ble','Nat.land','Nat.lor','Nat.xor','Nat.shiftLeft','Nat.shiftRight',
 'String.ofList','Char.ofNat','List','eagerReduce','Nat','String','String.mk','Char',
 'optParam','autoParam','semiOutParam','outParam']
targets = ['Quot','Quot.mk','Quot.lift','Quot.ind'] + cfg['theorem_names'] + cfg['permitted_axioms'] + primitives + cfg.get('definition_names', [])
report = {'checked_at_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
 'scope':'Read-only exported-data checks; not sandboxed builds or official Palomar preflight',
 'toolchain':(ROOT/'lean-toolchain').read_text().strip(),
 'config_sha256':hashlib.sha256((ROOT/'comparator.json').read_bytes()).hexdigest(),
 'source_sha256': {str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest()
    for p in sorted([*ROOT.glob('*.lean'),*ROOT.glob('KMV/*.lean')])},
 'exports': [], 'checks': []}
def save():
    (ROOT/'evidence/export-validation.json').write_text(json.dumps(report,indent=2)+'\n')
def run(name, cmd):
    with (ROOT/'evidence'/f'{name}.log').open('w') as log:
        result=subprocess.run(cmd,cwd=ROOT,env=local_check.ENV,stdout=log,stderr=subprocess.STDOUT)
    report['checks'].append({'name':name,'command':cmd,'exit_code':result.returncode})
    save(); print(name,result.returncode,flush=True)
    return result.returncode
for mod in ['Challenge','Solution']:
    path=OUT/(mod+'.ndjson')
    cmd=[str(local_check.TC/'bin/leanexport'),mod,'--',*targets]
    with path.open('w') as f, (ROOT/'evidence'/f'{mod}-export.log').open('w') as log:
        result=subprocess.run(cmd,cwd=ROOT,env=local_check.ENV,stdout=f,stderr=log)
    report['exports'].append({'module':mod,'command':cmd,'exit_code':result.returncode,
      'path':str(path.relative_to(ROOT)),'sha256':hashlib.sha256(path.read_bytes()).hexdigest(),'bytes':path.stat().st_size})
    save(); print('export',mod,result.returncode,flush=True)
    if result.returncode:raise SystemExit(result.returncode)
def names(values):
    assert all(re.fullmatch(r'[A-Za-z_][A-Za-z_0-9.]*',v) for v in values)
    return '#['+', '.join('`'+v for v in values)+']'
reader=OUT/'CompareExports.lean'
reader.write_text('''module
public meta import Lake.Check.Compare
public meta import Lake.Check.Axioms
public meta import LeanExport.Parse
#eval do
  let challenge ← LeanExport.parseStream (.ofHandle (← IO.FS.Handle.mk ".lake/exports/Challenge.ndjson" .read))
  let solution ← LeanExport.parseStream (.ofHandle (← IO.FS.Handle.mk ".lake/exports/Solution.ndjson" .read))
  let theorems := '''+names(cfg['theorem_names'])+'''
  let legal := '''+names(cfg['permitted_axioms'])+'''
  let definitions := '''+names(cfg.get('definition_names', []))+'''
  let primitives := '''+names(primitives)+'''
  IO.ofExcept (Lake.Check.compareAt challenge solution (theorems ++ legal) definitions primitives)
  IO.ofExcept (Lake.Check.checkAxioms solution theorems definitions legal)
  IO.println "Pinned Lake comparison and axiom checks passed; definition bodies are compared recursively."
''')
compare=[str(local_check.TC/'bin/lake'),'-d',str(ROOT/'tools/frontend'),'script','run','check',str(reader),'CompareExports','',str(ROOT)]
if run('export-statement-comparison',compare):raise SystemExit(1)
solution=str(OUT/'Solution.ndjson')
nanoda=OUT/'nanoda.json';nanoda.write_text(json.dumps({'use_stdin':False,'export_file_path':solution,
 'permitted_axioms':cfg['permitted_axioms'],'unpermitted_axiom_hard_error':False,
 'num_threads':4,'nat_extension':True,'string_extension':True}))
failed=False
for name,args in [('nanoda',[str(local_check.TC/'bin/nanoda_bin'),str(nanoda)]),
                  ('con-ron',[str(local_check.TC/'bin/con-ron'),solution]),
                  ('lean-from-export',[str(local_check.TC/'bin/leanchecker'),'--from-export',solution])]:
    if run(name,args):failed=True
report['all_checks_passed']=not failed;save()
raise SystemExit(1 if failed else 0)
