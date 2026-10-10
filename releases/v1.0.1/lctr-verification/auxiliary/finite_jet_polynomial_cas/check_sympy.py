 
import json
import sympy as s
x,a=s.symbols('x a',real=True);v=s.symbols('v0:7',real=True)
rows=[]
def check(name,residual,expected=0):
    residual=s.expand(residual)
    assert residual==expected,(name,residual,expected)
    rows.append(dict(case=name,residual=str(residual)))
for i in range(7):
    for n in range(8):
        basis=(x-a)**i/s.factorial(i)
        check(f'basis_{i}_{n}',s.diff(basis,x,n).subs(x,a)-(1 if n==i else 0))
curve=sum((x-a)**i/s.factorial(i)*v[i] for i in range(7))
for n in range(7):check(f'jet_{n}',s.diff(curve,x,n).subs(x,a)-v[n])
check('above_degree',s.diff(curve,x,7))
check('negative_missing_factorial',s.diff((x-a)**2,x,2).subs(x,a)-1,1)
check('negative_reversed_displacement',s.diff(a-x,x).subs(x,a)-1,-2)
print(json.dumps(dict(tool='SymPy',version=s.__version__,rows=rows,
    scope='Symbolic real scalar polynomials: degrees 0..6, derivative orders 0..7.'),indent=2))
