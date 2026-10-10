 
import json
import astropy
from astropy import units as u
U=u.def_unit('lctr_coordinate');one=u.dimensionless_unscaled
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
    reduced=q.unit.decompose();dims={str(base):exp for base,exp in zip(reduced.bases,reduced.powers)}
    expected={} if power==0 else {'lctr_coordinate':power}
    assert dims==expected,(name,dims)
    rows.append(dict(case=name,status='compatible',coordinate_power=power,dimensionality=dims))
negative={
 'add_frequency_and_period':lambda:frequency+period,
 'multiply_hz_normalization':lambda:(frequency*hz_unit).to(one),
 'frequency_as_period':lambda:frequency.to(U)}
for name,run in negative.items():
    try:run()
    except u.UnitConversionError:rows.append(dict(case=name,status='dimension_rejected',exception='UnitConversionError'))
    else:raise AssertionError('Invalid unit assignment accepted: '+name)
print(json.dumps(dict(tool='Astropy',version=astropy.__version__,coordinate_unit='lctr_coordinate',
    physical_time_unit_assumed=False,numerical_identity_credit=False,rows=rows),indent=2))
