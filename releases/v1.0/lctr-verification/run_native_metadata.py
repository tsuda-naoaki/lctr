 
import argparse,json,os,shutil,subprocess,time
from pathlib import Path
from runtime_paths import root_path, tool, run as native_run, entrypoint
ROOT=Path(__file__).resolve().parent
def read(p):return json.loads(p.read_text())
def save(p,x):p.write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n')
def main():
    ap=argparse.ArgumentParser();ap.add_argument('--output',required=True);ap.add_argument('--lean-build',required=True)
    ap.add_argument('--groups',default='1,2,3,4,5,6,7,8,9,10');ap.add_argument('--skip-lean',action='store_true')
    a=ap.parse_args();out=root_path(a.output, '--output');out.mkdir(parents=True,exist_ok=False);results=[]
    def run(label,cmd,cwd=ROOT,env=None):
        start=time.monotonic();p=out/(label+'.stdout');e=out/(label+'.stderr')
        with p.open('wb') as stdout,e.open('wb') as stderr:r=native_run(cmd,cwd=cwd,env=env,stdout=stdout,stderr=stderr)
        results.append(dict(check=label,exit_code=r.returncode,accepted=r.returncode==0,elapsed_s=round(time.monotonic()-start,3)))
        save(out/'results.json',dict(complete=False,results=results));print(json.dumps(results[-1]),flush=True);assert r.returncode==0,label
        return p
    if not a.skip_lean:
        mathlib=root_path(os.environ['LCTR_MATHLIB'], 'LCTR_MATHLIB');lake=tool('LCTR_LAKE','lake');lean=tool('LCTR_LEAN','lean')
        lp=subprocess.check_output([lake,'env','printenv','LEAN_PATH'],cwd=mathlib,text=True).strip()
        env=dict(os.environ,LEAN_PATH=str(root_path(a.lean_build, '--lean-build'))+os.pathsep+lp)
        p=run('lean-native-dependencies',[lean,str(ROOT/'lean/RootDependencies.lean')],cwd=mathlib,env=env)
        rows=[json.loads(s) for s in p.read_text().splitlines() if s.startswith('{')]
        assert len(rows)==1982 and all(r['has_native_value'] and not r['is_axiom'] and 'sorryAx' not in r['transitive_axioms'] for r in rows)
    wanted={int(x) for x in a.groups.split(',')};isabelle=tool('LCTR_ISABELLE','isabelle');total=0
    for g in read(ROOT/'inventory/native-metadata-queries.json')['groups']:
        if g['group'] not in wanted:continue
        run('isabelle-native-'+str(g['group']),[isabelle,*g['arguments']])
        group_dest=out/('isabelle-group-'+str(g['group']))
        run('isabelle-export-'+str(g['group']),[isabelle,'scala',str(ROOT/'queries/ExportNativeMetadata.scala'),str(group_dest),*[q['session'] for q in g['sessions']]])
        for query in g['sessions']:
            dest=group_dest/query['session']
            paths=list(dest.rglob('facts.json'));assert len(paths)==1,paths
            data=read(paths[0]);assert {r['name'] for r in data['records']}==set(query['names'])
            assert all(not r['oracle_dependencies'] for r in data['records'])
        total+=len(g['roots'])
    save(out/'results.json',dict(complete=True,results=results,core_roots=total,groups=sorted(wanted)))
if __name__=='__main__':entrypoint(main)
