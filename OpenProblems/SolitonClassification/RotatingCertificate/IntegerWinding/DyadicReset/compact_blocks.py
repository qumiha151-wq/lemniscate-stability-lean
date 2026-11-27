"""Produce compact signed polynomial witnesses for independent kernel reflection."""
import json
import sys
from reset_tape import HERE,seed,path
from node_blocks import rows

def encode(p):
    value=0
    for a in reversed(p):
        z=2*a if a>=0 else -2*a-1
        k=z.bit_length()
        assert k<256
        value=(value<<(k+8)) + (z<<8) + k
    return hex(value)

def source(sign,first,count,tape=None):
    label=('Plus' if sign>0 else 'Minus')+str(first).zfill(4)
    if tape is None: tape=list(rows(HERE/('plus4000.jsonl.gz' if sign>0 else 'minus4000.jsonl.gz')))
    n= 'Middle.hn' if sign>0 else '(-Middle.hn)'
    h=seed(sign)[1]
    src=['import SolitonClassification.Rotating.ResetCompactCell',
         'namespace SolitonClassification.Rotating.DyadicReset.Compact'+label,
         'set_option Elab.async false','set_option maxRecDepth 200000','set_option maxHeartbeats 0']
    for i in range(first,first+count):
        P=path(tape[i],h)
        assert [sum(p) for p in P]==tape[i+1]
        src.extend([f'def p{i} : PackedCell := #['+','.join(encode(p) for p in P)+']',
                    f'def begin{i} : Node := #['+','.join(map(str,tape[i]))+']',
                    f'def end{i} : Node := #['+','.join(map(str,tape[i+1]))+']',
                    f'theorem checked{i} : SignedCheck {n} (packedData p{i}) := by',
                    f'  apply signedOfAll;decide +kernel',
                    f'theorem small{i} : Small (packedData p{i}) := by unfold Small;decide +kernel',
                    f'theorem nodes{i} : sampleStart p{i}=begin{i} ∧ sampleEnd p{i}=end{i} := by decide +kernel'])
    src+=[f'end SolitonClassification.Rotating.DyadicReset.Compact{label}']
    (HERE/'cellblocks').mkdir(exist_ok=True)
    (HERE/'cellblocks'/f'ResetPacked{label}.lean').write_text('\n'.join(src)+'\n',encoding='utf8')
if __name__=='__main__':
    if sys.argv[1]=='full':
        for sign in (1,-1):
            tape=list(rows(HERE/('plus4000.jsonl.gz' if sign>0 else 'minus4000.jsonl.gz')))
            for j in range(0,4000,16):
                source(sign,j,16,tape)
                if j%400==0: print(sign,j,flush=True)
    else: source(*(int(v) for v in sys.argv[1:]))
