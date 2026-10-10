




import argparse, gzip, hashlib, json, os, shutil, subprocess, time, sys
from pathlib import Path
from runtime_paths import root_path, relative, tool, run as native_run, check_output, entrypoint

ROOT=Path(__file__).resolve().parent
def read(p):return json.loads(p.read_text())
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def save(p,x):p.write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n')

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',required=True,help='A new directory relative to the extracted root.')
    parser.add_argument('--steps',default='lean,isabelle,recheck,statements,formal-support,auxiliary,native-metadata,survey',
        help='Comma-separated: lean,isabelle,recheck,statements,formal-support,auxiliary,native-metadata,survey. Recheck alone uses the supplied proof export.')
    args=parser.parse_args();steps=args.steps.split(',')
    assert set(steps)<={'lean','isabelle','recheck','statements','formal-support','auxiliary','native-metadata','survey'}
    if set(steps)&{'formal-support','native-metadata'}:assert 'lean' in steps,'Native metadata and auxiliary proofs require the lean build in this run'
    for line in (ROOT/'SHA256SUMS').read_text().splitlines():
        h,name=line.split('  ',1);assert digest(ROOT/name)==h,('File identity mismatch',name)
    output=root_path(args.output, '--output');output.mkdir(parents=True,exist_ok=False)
    results=[]
    def run(label,command,cwd=ROOT,env=None,stdin=None,expected=0):
        t=time.time();log=output/(label+'.stdout');err=output/(label+'.stderr')
        with log.open('wb') as o,err.open('wb') as e:
            p=native_run(command,cwd=cwd,env=env,stdin=stdin,stdout=o,stderr=e)
        row=dict(check=label,exit_code=p.returncode,expected_exit_code=expected,
            elapsed_s=round(time.time()-t,3),accepted=p.returncode==expected)
        results.append(row);save(output/'results.json',dict(results=results,complete=False))
        print(json.dumps(row),flush=True)
        if p.returncode!=expected:raise RuntimeError(label+': see '+relative(log)+' and '+relative(err))
        return log
    env=None;mathlib=None;lean=None
    if 'lean' in steps or 'statements' in steps:
        mathlib=root_path(os.environ['LCTR_MATHLIB'], 'LCTR_MATHLIB')
        want=read(ROOT/'environment/lean.json')
        commit=check_output(['git','rev-parse','HEAD'],cwd=mathlib,text=True).strip()
        assert commit==want['mathlib']['commit'],('Mathlib revision',commit)
        lean=tool('LCTR_LEAN','lean');lake=tool('LCTR_LAKE','lake')
        version=check_output([lean,'--version'],text=True)
        assert '4.33.1' in version,version
        lp=subprocess.check_output([lake,'env','printenv','LEAN_PATH'],cwd=mathlib,text=True).strip()
        build=output/'lean';build.mkdir()
        env=dict(os.environ,LEAN_PATH=str(build)+os.pathsep+lp)
    if 'lean' in steps:
        negatives={x['module']:x for x in read(ROOT/'inventory/lean-negative-controls.json')['controls']}
        for row in read(ROOT/'inventory/lean-modules.json')['modules']:
            name=row['module'];dst=build/Path(*name.split('.')).with_suffix('.olean');dst.parent.mkdir(parents=True,exist_ok=True)
            log=run('lean-'+name,[lean,'--root='+str(ROOT/'lean'),'-o',str(dst),str(ROOT/row['path'])],
                cwd=mathlib,env=env,expected=1 if name in negatives else 0)
            if name in negatives:
                text=log.read_text();control=negatives[name]
                assert text.count('error:')==1 and control['expected_diagnostic'] in text and control['expected_final_text'] in text
        run('lean-core',[lean,'--root='+str(ROOT/'lean'),'-o',str(build/'LCTRCore.olean'),str(ROOT/'lean/LCTRCore.lean')],cwd=mathlib,env=env)
    if 'isabelle' in steps:
        isabelle=tool('LCTR_ISABELLE','isabelle')
        assert check_output([isabelle,'version'],text=True).strip()=='Isabelle2025-2'
        groups=read(ROOT/'inventory/isabelle-grouped-builds.json')['groups']
        for group in groups:
            run('isabelle-group-'+str(group['group']).zfill(2),[isabelle,*group['arguments']])
    if 'recheck' in steps:
        proof=output/'proof.ndjson'
        if 'lean' in steps:
            exporter=tool('LCTR_LEAN4EXPORT','lean4export')
            roots=[r['lean'] for r in read(ROOT/'inventory/formal-root-pairs.json')['pairs']]
            generated=run('export',[exporter,'LCTRCore','--',*roots],cwd=mathlib,env=env)
            shutil.copyfile(generated,proof)
            assert digest(proof)==read(ROOT/'reports/independent/result.json')['export_sha256'],'Export identity mismatch'
        else:
            with gzip.open(ROOT/'reports/independent/proof.ndjson.gz','rb') as src,proof.open('wb') as dst:
                shutil.copyfileobj(src,dst)
        nanoda=tool('LCTR_NANODA','nanoda_bin');conleche=tool('LCTR_CON_LECHE','con-leche')
        with proof.open('rb') as src:run('nanoda',[nanoda,str(ROOT/'environment/nanoda.json')],stdin=src)
        run('con-leche',[conleche,'--verified',str(proof)])
    if 'statements' in steps:
        assert 'lean' in steps,'Statement output requires the lean step in this run'
        run('lean-statements',[lean,str(ROOT/'lean/RootStatements.lean')],cwd=mathlib,env=env)
    if 'formal-support' in steps:
        run('formal-support',[sys.executable,str(ROOT/'run_formal_support.py'),'--output',relative(output/'formal-support'),'--lean-build',relative(build)])
    if 'auxiliary' in steps:
        run('auxiliary',[sys.executable,str(ROOT/'run_auxiliary.py'),'--output',relative(output/'auxiliary')])
    if 'native-metadata' in steps:
        run('native-metadata',[sys.executable,str(ROOT/'run_native_metadata.py'),'--output',relative(output/'native-metadata'),'--lean-build',relative(build)])
    if 'survey' in steps:
        run('survey',[sys.executable,str(ROOT/'survey/verify.py'),'--output',str(output/'survey-results.json')])
    save(output/'results.json',dict(results=results,complete=True,steps=steps))

if __name__=='__main__':entrypoint(main)
