 
import argparse,json,os,shutil,subprocess,time
from pathlib import Path
from runtime_paths import root_path, tool, run as native_run, entrypoint
ROOT=Path(__file__).resolve().parent
def read(p):return json.loads(p.read_text())
def save(p,x):p.write_text(json.dumps(x,indent=2)+'\n')
def main():
    ap=argparse.ArgumentParser();ap.add_argument('--output',required=True);ap.add_argument('--lean-build',required=True);ap.add_argument('--steps',default='lean,isabelle,recheck')
    args=ap.parse_args();steps=args.steps.split(',');assert set(steps)<={'lean','isabelle','recheck'}
    out=root_path(args.output, '--output');out.mkdir(parents=True,exist_ok=False);build=root_path(args.lean_build, '--lean-build')
    pairs=read(ROOT/'inventory/auxiliary-formal-roots.json')['pairs'];results=[]
    def run(name,command,cwd=ROOT,env=None,stdin=None):
        start=time.monotonic();p=out/(name+'.stdout');e=out/(name+'.stderr')
        with p.open('wb') as stdout,e.open('wb') as stderr:r=native_run(command,cwd=cwd,env=env,stdin=stdin,stdout=stdout,stderr=stderr)
        results.append(dict(check=name,exit_code=r.returncode,accepted=r.returncode==0,elapsed_s=round(time.monotonic()-start,3)))
        save(out/'results.json',dict(complete=False,results=results));print(json.dumps(results[-1]),flush=True)
        assert r.returncode==0,name
        return p
    mathlib=root_path(os.environ['LCTR_MATHLIB'], 'LCTR_MATHLIB');lean=tool('LCTR_LEAN','lean');lake=tool('LCTR_LAKE','lake')
    lp=subprocess.check_output([lake,'env','printenv','LEAN_PATH'],cwd=mathlib,text=True).strip()
    env=dict(os.environ,LEAN_PATH=str(build)+os.pathsep+lp)
    if 'lean' in steps:
        for mod in dict.fromkeys(p['lean_module'] for p in pairs):
            run('lean-'+mod,[lean,'--root='+str(ROOT/'lean'),'-o',str(build/(mod+'.olean')),str(ROOT/'lean'/(mod+'.lean'))],cwd=mathlib,env=env)
        run('lean-auxiliary',[lean,'--root='+str(ROOT/'lean'),'-o',str(build/'LCTRAuxiliary.olean'),str(ROOT/'lean/LCTRAuxiliary.lean')],cwd=mathlib,env=env)
    if 'isabelle' in steps:
        original=read(ROOT/'inventory/isabelle-grouped-builds.json')['groups'][0]['arguments'];a=['build','-o','timeout=45','-j','2']
        for i,x in enumerate(original):
            if x=='-d':a+=['-d',original[i+1]]
        for p in sorted((ROOT/'isabelle').glob('core_*')):
            if p.name in {'core_smt_rewrite_rules','core_smt_boolean_rules','core_evaluation_smt_bridge','core_finite_margin_bridge'}:a+=['-d',str(p.relative_to(ROOT))]
        a+=list(dict.fromkeys(p['isabelle_session'] for p in pairs))
        run('isabelle-auxiliary',[tool('LCTR_ISABELLE','isabelle'),*a])
    if 'recheck' in steps:
        p=run('export',[tool('LCTR_LEAN4EXPORT','lean4export'),'LCTRAuxiliary','--',*[p['lean'] for p in pairs]],cwd=mathlib,env=env)
        with p.open('rb') as inp:run('nanoda',[tool('LCTR_NANODA','nanoda_bin'),str(ROOT/'environment/nanoda.json')],stdin=inp)
        run('con-leche',[tool('LCTR_CON_LECHE','con-leche'),'--verified',str(p)])
    save(out/'results.json',dict(complete=True,results=results,paired_roots=len(pairs),steps=steps))
if __name__=='__main__':entrypoint(main)
