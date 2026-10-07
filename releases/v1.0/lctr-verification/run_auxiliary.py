 
import argparse, hashlib, json, os, re, shutil, subprocess, time, xml.etree.ElementTree as ET
from pathlib import Path
from runtime_paths import root_path, tool, run as native_run, check_output, entrypoint

ROOT=Path(__file__).resolve().parent
def read(p):return json.loads(p.read_text())
def save(p,x):p.write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--output',required=True)
    args=ap.parse_args();out=root_path(args.output, '--output');out.mkdir(parents=True,exist_ok=False)
    results=[]
    def run(directory,label,command,timeout=90,cwd=ROOT):
        start=time.monotonic()
        proc=native_run(command,cwd=cwd,capture_output=True,text=True,timeout=timeout)
        (directory/(label+'.stdout')).write_text(proc.stdout)
        (directory/(label+'.stderr')).write_text(proc.stderr)
        assert proc.returncode==0,(label,proc.returncode,proc.stderr[-1000:])
        return proc.stdout
    cvc5=tool('LCTR_CVC5','cvc5');z3=tool('LCTR_Z3','z3');carcara=tool('LCTR_CARCARA','carcara')
    assert 'cvc5 1.3.4' in check_output([cvc5,'--version'],text=True)
    assert 'carcara 1.1.0 [git 0b38c86]' in check_output([carcara,'--version'],text=True)
    assert 'Z3 version 5.1.0' in check_output([z3,'--version'],text=True)
    python=tool('LCTR_CAS_PYTHON','python3');maxima=tool('LCTR_MAXIMA','maxima')
    java=tool('LCTR_JAVA','java');jar=root_path(os.environ['LCTR_MMT_JAR'], 'LCTR_MMT_JAR')
    foundation=root_path(os.environ['LCTR_MMT_FOUNDATION'], 'LCTR_MMT_FOUNDATION')
    assert sha(jar)=='e481c037e5785f3e6da4fa3110b683a98aced3ea9a0a7499f374a7d194565c3d'
    assert check_output(['git','rev-parse','HEAD'],cwd=foundation,text=True).strip()=='6ec8abac5e3bdab1eb6ee47dddbf8a7402934181'
    for c in read(ROOT/'inventory/auxiliary-checks.json')['cases']:
        start=time.monotonic();d=out/c['id'];d.mkdir(parents=True);inp=ROOT/c['input'];kind=c['kind'];extra={}
        if kind=='smt':
            flags=['--lang=smt2']
            if c['expected']=='unsat':flags+=['--dump-proofs','--proof-format-mode=alethe','--proof-granularity=dsl-rewrite','--proof-check=eager','--proof-alethe-res-pivots']
            s=run(d,'cvc5',[cvc5,*flags,str(inp)])
            assert s.splitlines()[0].strip()==c['expected'],c['id']
            z=run(d,'z3',[z3,str(inp)]);assert z.strip()==c['expected'],c['id']
            if 'native_input' in c:
                native=ROOT/c['native_input']
                assert run(d,'native-cvc5',[cvc5,'--lang=smt2',str(native)]).strip()==c['expected']
                assert run(d,'native-z3',[z3,str(native)]).strip()==c['expected']
            if c['expected']=='unsat':
                proof=s.split('\n',1)[1].strip()
                assert proof.startswith('(\n') and proof.endswith(')'), 'Expected the cvc5 outer proof-list wrapper'
                 
                original=d/'proof.original.alethe';original.write_text(proof+'\n')
                p=d/'proof.alethe';p.write_text(proof[1:-1].strip()+'\n')
                checked=run(d,'carcara',[carcara,'check',str(p),str(inp),'--rare-file',str(ROOT/c['required_rare'])])
                assert re.search(r'(?im)^valid\s*$',checked),checked[-1000:]
                stored=run(d,'carcara-supplied',[carcara,'check',str(ROOT/c['proof_alethe']),str(inp),'--rare-file',str(ROOT/c['required_rare'])])
                assert re.search(r'(?im)^valid\s*$',stored)
                extra=dict(proof_sha256=sha(p),rules_sha256=sha(ROOT/c['required_rare']))
        elif kind in {'sympy','pint','astropy'}:
            text=run(d,kind,[python,str(inp)]);obj=json.loads(text)
            versions={'sympy':'1.14.0','pint':'0.25.3','astropy':'8.0.1'}
            assert obj['version']==versions[kind]
            count=66 if c['group']=='finite_jet_polynomial_cas' else 9 if kind=='sympy' else 12
            assert len(obj['rows'])==count
            extra=dict(subchecks=count,version=obj['version'])
        elif kind=='maxima':
            text=run(d,kind,[maxima,'--very-quiet','-b',str(inp)])
            rows=dict(re.findall(r'^LCTR_CASE (\S+) (\S+)\s*$',text,re.M))
            if c['group']=='frequency_period_hz_cas':
                expected={'reciprocal_quotient':'0','frequency_period_product':'0','standard_normalization':'0','frequency_positive':'true','period_positive':'true','hz_unit_positive':'true','relative_hz_number_positive':'true','period_replaced_by_frequency':'-(5/9)','hz_unit_multiplied_instead_of_divided':'-(3/2)'}
            else:
                expected={**{f'basis_{i}_{j}':'0' for i in range(7) for j in range(8)},**{f'jet_{j}':'0' for j in range(7)},'above_degree':'0','negative_missing_factorial':'1','negative_reversed_displacement':'-2'}
            assert rows==expected,(c['id'],rows)
            assert '5.50.0' in text
            extra=dict(subchecks=len(rows),version='5.50.0')
        elif kind=='mmt':
            (d/'source').mkdir();(d/'META-INF').mkdir()
            shutil.copy2(inp,d/'source/test.mmt');archive='lctr-law-semantic-'+d.name
            (d/'META-INF/MANIFEST.MF').write_text('id: '+archive+'\nnarration-base: https://tsuda-naoaki.github.io/lctr/verification/law-candidate\n')
            script=d/'run.msl'
            foundation_relative=os.path.relpath(foundation.parent,d)
            script.write_text('log console\nmathpath archive '+foundation_relative+'\narchive add .\nbuild '+archive+' mmt-omdoc test.mmt\nexit\n')
            text=run(d,'mmt',[java,'-jar',str(jar),'file','run.msl'],cwd=d)
            text=re.sub(r'\x1b\[[0-9;]*m','',text+(d/'mmt.stderr').read_text())
            assert list(d.rglob('*.omdoc')), 'MMT produced no object'
            assert not re.search(r'parse error|parser error|syntax error|unexpected token|no backend applicable|no such file|no declaration|(unknown|undefined|unresolved).*(symbol|constant|name)',text,re.I)
            errors=[line for line in text.splitlines() if re.search(r'\b(error|invalid|failed)\b',line,re.I)]
            if c['expected']=='accepted':assert not errors,errors
            else:
                assert errors,'MMT accepted the negative control'
                assert all(re.search(r'invalid (?:unit|object): .*\?LawCandidate\?bad\?(?:type|definition): Judgment',line) for line in errors),errors
            extra=dict(type_diagnostics=len(errors))
        else:raise ValueError(kind)
        results.append(dict(id=c['id'],expected=c['expected'],accepted=True,input_sha256=sha(inp),elapsed_s=round(time.monotonic()-start,3),**extra))
        save(out/'results.json',dict(complete=False,cases=results))
        print(json.dumps(results[-1]),flush=True)
    controls=[]
    for name in ['missing_rules','false_ite_eq']:
        cmd=[carcara,'check',str(out/'graph/edge_rank/proof.alethe'),str(ROOT/'auxiliary/smt/graph/edge_rank/check.smt2')]
        if name=='false_ite_eq':cmd+=['--rare-file',str(ROOT/'auxiliary/smt/controls/false_ite_eq.rare')]
        proc=native_run(cmd,cwd=ROOT,capture_output=True,text=True,timeout=30)
        d=out/'trace-controls';d.mkdir(exist_ok=True)
        (d/(name+'.stdout')).write_text(proc.stdout);(d/(name+'.stderr')).write_text(proc.stderr)
        assert proc.returncode==1 and re.search(r'(?im)^invalid\s*$',proc.stdout)
        assert ('wasn`t found' in proc.stdout+proc.stderr) if name=='missing_rules' else ("isn't equal to" in proc.stdout+proc.stderr)
        controls.append(dict(case=name,exit_code=1,expected='invalid',accepted=True))
    serial=[];xslt=tool('LCTR_XSLTPROC','xsltproc');xml=tool('LCTR_XMLLINT','xmllint')
    def tree(ast):
        if ast[0]=='var':return ET.Element('var',name=ast[1])
        root=ET.Element(ast[0],name=ast[1])
        if ast[0]=='bind':
            vars=ET.SubElement(root,'vars')
            for name in ast[2]:ET.SubElement(vars,'var',name=name)
            root.append(tree(ast[3]))
        else:
            for child in ast[2:]:root.append(tree(child))
        return root
    def signature(node):return (node.tag,tuple(sorted(node.attrib.items())),tuple(signature(c) for c in node))
    for pair in read(ROOT/'inventory/semantic-expression-pairs.json')['expressions']:
        d=out/'serializations'/pair['id'];d.mkdir(parents=True)
        outputs=[]
        for key,style in [('openmath','openmath'),('content_mathml','mathml')]:
            p=ROOT/pair[key];run(d,key+'-parse',[xml,'--nonet','--noout',str(p)])
            outputs.append(ET.fromstring(run(d,key+'-expression',[xslt,'--nonet',str(ROOT/'queries'/(style+'-tree.xsl')),str(p)])))
        assert signature(outputs[0])==signature(outputs[1])==signature(tree(pair['reviewed_expression']))
        serial.append(dict(id=pair['id'],matching_reviewed_expression=True,accepted=True))
    save(out/'results.json',dict(complete=True,cases=results,groups=7,trace_controls=controls,serialization_pairs=serial))

if __name__=='__main__':entrypoint(main)
