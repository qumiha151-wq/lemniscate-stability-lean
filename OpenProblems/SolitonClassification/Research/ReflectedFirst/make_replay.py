"""Materialize individual kernel reductions, with concrete inputs at each step."""
from pathlib import Path
import argparse
import json
from mesh_replay import H, STEPS

here=Path(__file__).resolve().parent

def box(row):
    return '⟨#['+','.join(f'⟨{c},{r}⟩' for c,r in row)+'],rfl⟩'

def source(label,start,count,name):
    rows=json.loads((here/(label+'.json')).read_bytes())
    text=['import SolitonClassification.Reflected.TaylorStep',
          'namespace SolitonClassification.Reflected.'+name,
          'set_option maxHeartbeats 0','set_option maxRecDepth 10000000',
          'set_option Elab.async false',
          f'def h : ℚ := {H.numerator}/{H.denominator}']
    for j in range(start,start+count+1):
        text.append(f'def b{j} : Box := {box(rows[j])}')
    for j in range(start,start+count):
        text.append(f'theorem step{j} : advance h b{j} = b{j+1} := by decide +kernel')
    text+=['end SolitonClassification.Reflected.'+name,
           '#print axioms SolitonClassification.Reflected.'+name+f'.step{start}']
    (here/(name+'.lean')).write_text('\n'.join(text)+'\n',encoding='utf8')

if __name__=='__main__':
    p=argparse.ArgumentParser()
    p.add_argument('--label',default='all')
    p.add_argument('--start',type=int,default=0)
    p.add_argument('--count',type=int,default=1)
    p.add_argument('--name',default='ReplayFirst')
    a=p.parse_args()
    source(a.label,a.start,a.count,a.name)
