"""Produce rational node/inverse witnesses for reflection in the Lean kernel."""
import gzip
import json
import sys
from pathlib import Path
from reset_tape import D,HERE,ROWS
from nodes import B,fmpz_mat

def get_inverses(n):
    Z=[[0]*6 for _ in range(6)]
    for a,i in enumerate(ROWS):
        for j in range(5):
            Z[i][j]=n[6+5*j+a]
    Z[4][4]=Z[5][5]=D
    q=fmpz_mat(Z).inv()
    return [int(q[i,j]*(D*B)) for j in range(6) for i in range(6)]

def rows(path):
    with gzip.open(path,'rt',encoding='utf8') as fp:
        next(fp)
        for i,line in enumerate(fp):
            data=json.loads(line)
            yield data[2] if i else data

def write_block(key,nodes):
    def vec(row):
        return '#['+','.join(map(str,row))+']'
    head=['import SolitonClassification.Rotating.ResetFastNode',
          f'namespace SolitonClassification.Rotating.DyadicReset.Node{key}',
          'set_option Elab.async false','set_option maxRecDepth 200000','set_option maxHeartbeats 0']
    for i,n in enumerate(nodes):
        head.extend([f'def n{i} : Node := '+vec(n),f'def w{i} : Node := '+vec(get_inverses(n)),
                     f'theorem bounds{i} : CheckedNode n{i} w{i} := fastNode_sound (by decide +kernel : fastNode n{i} w{i}=true)'])
    head.extend(['def nodes : Array Node := #['+','.join(f'n{i}' for i in range(len(nodes)))+']',
                 'def witnesses : Array Node := #['+','.join(f'w{i}' for i in range(len(nodes)))+']',
                 f'end SolitonClassification.Rotating.DyadicReset.Node{key}'])
    (HERE/'nodeblocks'/f'ResetNode{key}.lean').write_text('\n'.join(head)+'\n',encoding='utf8')

if __name__=='__main__':
    (HERE/'nodeblocks').mkdir(exist_ok=True)
    for sign in ['plus','minus']:
        tape=list(rows(HERE/f'{sign}4000.jsonl.gz'))
        for b in range(0,len(tape),64):
            write_block(sign.title()+str(b//64).zfill(2),tape[b:b+64])
        print(sign,len(tape),flush=True)
