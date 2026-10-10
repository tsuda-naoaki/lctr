 
import json
import sympy as s
n,d,v,u=s.symbols('n d v u',positive=True)
N=s.Symbol('N',integer=True,positive=True)
frequency=n/d;period=1/frequency;hz_unit=v/N;hz_number=v/hz_unit
identities={
 'reciprocal_quotient':period-d/n,
 'frequency_period_product':frequency*period-1,
 'standard_normalization':hz_number-N,
}
positivity={'frequency':frequency,'period':period,'hz_unit':hz_unit,'relative_hz_number':v/u}
rows=[]
for name,expression in identities.items():
 residual=s.cancel(expression);assert residual==0
 rows.append(dict(case=name,kind='rational_identity',residual=str(residual),passed=True))
for name,expression in positivity.items():
 assert expression.is_positive is True
 rows.append(dict(case=name,kind='positive_on_stated_domain',passed=True))
mutants={
 'period_replaced_by_frequency':(s.Rational(2,3)**2-1),
 'hz_unit_multiplied_instead_of_divided':s.Rational(10,10*2)-2,
}
for name,residual in mutants.items():
 assert residual!=0
 rows.append(dict(case=name,kind='false_identity_counterexample',residual=str(residual),passed=True))
print(json.dumps(dict(tool='SymPy',version=s.__version__,variables=dict(n='positive count difference',d='positive represented coordinate difference',v='positive frequency',u='positive frequency unit',N='positive integer normalization'),rows=rows,scope='Real scalar algebra under the stated positivity and nonzero conditions.'),indent=2))
