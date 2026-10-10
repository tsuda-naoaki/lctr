 
import json
import pint
u=pint.UnitRegistry()
u.define('lctr_coordinate = [lctr_coordinate]')
U=u.lctr_coordinate;one=u.dimensionless
n=2*one;d=3*U;N=5*one;standard=10/U
frequency=n/d;period=1/frequency;hz_unit=standard/N
cases={
 'count_difference':(n,one,0),'coordinate_difference':(d,U,1),
 'window_frequency':(frequency,1/U,-1),'window_period':(period,U,1),
 'frequency_period_product':(frequency*period,one,0),
 'standard_frequency':(standard,1/U,-1),'hz_unit':(hz_unit,1/U,-1),
 'hz_number':(frequency/hz_unit,one,0),'standard_normalization':(standard/hz_unit,one,0)}
rows=[]
for name,(q,target,power) in cases.items():
    q.to(target)
    dims=dict(q.dimensionality);expected={} if power==0 else {'[lctr_coordinate]':power}
    assert dims==expected,(name,dims)
    rows.append(dict(case=name,status='compatible',coordinate_power=power,dimensionality=dims))
negative={
 'add_frequency_and_period':lambda:frequency+period,
 'multiply_hz_normalization':lambda:(frequency*hz_unit).to(one),
 'frequency_as_period':lambda:frequency.to(U)}
for name,run in negative.items():
    try:run()
    except pint.DimensionalityError:rows.append(dict(case=name,status='dimension_rejected',exception='DimensionalityError'))
    else:raise AssertionError('Invalid unit assignment accepted: '+name)
print(json.dumps(dict(tool='Pint',version=pint.__version__,coordinate_unit='lctr_coordinate',
    physical_time_unit_assumed=False,numerical_identity_credit=False,rows=rows),indent=2))
