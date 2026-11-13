"""Untrusted small-block proposals for the forthcoming 42/22 grid.

This staging script is deliberately capped at two segments. It performs
no Lean validation and does not assert a trajectory or a root. Each leaf
will be checked against independent point-node data, avoiding imports of
its predecessor's heavy coefficient table.
"""
from pathlib import Path
import argparse,hashlib,json,sys,time

ROOT=Path(__file__).resolve().parent.parent
sys.path.insert(0,str(ROOT/'performance'))
from reference import Q,S,ZERO,ofq,add,neg,scale,div,conv,endpoint,state_coefficients

def full_variation(c,q,initial,N=22):
    w=[initial]
    cc=lambda i:[row[i] for row in c]
    for n in range(N):
        ww=lambda i:[row[i] for row in w]
        rhs=[scale(8,w[n][1]),
             add(neg(div(scale(3,conv(q,ww(0),n)),16)),
                 add(neg(div(w[n][2],8)),
                     add(neg(div(conv(cc(4),ww(3),n),8)),neg(div(conv(cc(3),ww(4),n),8))))),
             add(neg(conv(cc(0),ww(3),n)),neg(conv(cc(3),ww(0),n))),
             add(conv(cc(0),ww(2),n),conv(cc(2),ww(0),n)),ZERO,w[n][0]]
        w.append([div(z,n+1) for z in rhs])
    return w

def midpoint_inverse(B):
    # Exact rational Gaussian elimination only proposes C. Lean must
    # independently check both C*B and B*C integer residuals below.
    A=[[Q(B[j][i],S) for j in range(6)]+[Q(int(i==j)) for j in range(6)] for i in range(6)]
    for j in range(6):
        pivot=next(i for i in range(j,6) if A[i][j])
        A[j],A[pivot]=A[pivot],A[j]
        d=A[j][j];A[j]=[z/d for z in A[j]]
        for i in range(6):
            if i!=j:
                d=A[i][j];A[i]=[v-d*w for v,w in zip(A[i],A[j])]
    return [[int((A[i][6+j]*S).__floor__()) for i in range(6)] for j in range(6)]

def product_defect(A,B):
    return [[sum(A[k][i]*B[j][k] for k in range(6))-S*S*int(i==j)
             for i in range(6)] for j in range(6)]

def row_bound(A):
    return max(sum(abs(A[j][i]) for j in range(6)) for i in range(6))

def point_node(index,a,B):
    C=midpoint_inverse(B)
    left=product_defect(C,B);right=product_defect(B,C)
    checks={'B_row_numerator':row_bound(B),'C_row_numerator':row_bound(C),
            'CB_defect_row_numerator':row_bound(left),'BC_defect_row_numerator':row_bound(right)}
    # These Python assertions are proposal diagnostics, not a certificate.
    assert checks['B_row_numerator']<=2000*S
    assert checks['C_row_numerator']<=3999*S
    assert checks['CB_defect_row_numerator']<=10**100
    assert checks['BC_defect_row_numerator']<=10**100
    for value,cap in zip(a[:5],[Q(407,50),Q(33,8),Q(731,100),Q(731,100),Q(1,100)]):
        assert abs(value)<=cap
    return {'index':index,'state_rationals':[[z.numerator,z.denominator] for z in a],
            'matrix_integer_columns':B,'inverse_proposal_integer_columns':C,
            'untrusted_integer_check_diagnostics':checks}

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--steps',type=int,default=2)
    ap.add_argument('--sign',type=int,choices=[-1,1],default=1)
    args=ap.parse_args()
    if not 1<=args.steps<=2:
        ap.error('Only the bounded one/two-segment staging run is enabled; no 4000/8000 run is authorized here.')
    cap=ROOT.parent/'next_research/classification_odd_branch_interval/shooting_certificate.json'
    r=json.loads(cap.read_text());x=list(map(Q,r['center_exact_decimal']));e=list(map(Q,r['phase_exact_decimal']))
    a=[x[0],x[3]*e[0]/8,x[1],x[3]*e[1],x[4],Q(0)]
    B=[[S*int(i==j) for i in range(6)] for j in range(6)]
    h=x[2]/4000;t=ofq(args.sign*h)
    nodes=[point_node(0,a,B)];leaves=[]
    started=time.perf_counter()
    for j in range(args.steps):
        start=list(map(ofq,a)) if j==0 else [(int(z*S),0) for z in a]
        c,q=state_coefficients(start,42)
        W=[full_variation(c,q,[(v,0) for v in col]) for col in B]
        aout=endpoint(c,t);Bout=[endpoint(w,t) for w in W]
        leaves.append({'index':j,'state_coefficients':c,'curvature_square_coefficients':q,
                       'variation_columns_coefficients':W,'state_endpoint':aout,'matrix_endpoint_columns':Bout})
        a=[Q(v[0],S) for v in aout];B=[[z[0] for z in col] for col in Bout]
        nodes.append(point_node(j+1,a,B))
    out=ROOT/'pipeline/proposals'/('positive' if args.sign==1 else 'negative')/f'n{args.steps:04d}'
    out.mkdir(parents=True,exist_ok=True)
    metadata={'state_order':42,'matrix_order':22,'mesh':S,'sign':args.sign,'steps':args.steps,
              'positive_step':[h.numerator,h.denominator],'full_candidate_steps_per_sign':4000,
              'CAP_seed_sha256':hashlib.sha256(cap.read_bytes()).hexdigest(),
              'status':'UNTRUSTED PROPOSALS; no Lean table validation, true ODE, global bound, or root conclusion',
              'terminal_design':'Nominal nodes only. Extended grid terminal must use last polynomial at Nh+2r with zero reset; central Nh has separate numerical endpoint comparison.'}
    (out/'nodes.json').write_text(json.dumps({'metadata':metadata,'nodes':nodes},indent=2)+'\n')
    for leaf in leaves:
        (out/f"leaf{leaf['index']:04d}.json").write_text(json.dumps({'metadata':metadata,**leaf},indent=2)+'\n')
    record={'metadata':metadata,'untrusted_generation_wall_seconds':time.perf_counter()-started,
            'max_state_endpoint_radius':max(z[1] for l in leaves for z in l['state_endpoint']),
            'max_matrix_endpoint_radius':max(z[1] for l in leaves for col in l['matrix_endpoint_columns'] for z in col),
            'files':[{ 'name':p.name,'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'bytes':p.stat().st_size}
                     for p in sorted(out.glob('*.json')) if p.name!='proposal_manifest.json']}
    (out/'proposal_manifest.json').write_text(json.dumps(record,indent=2)+'\n')
    print(json.dumps({'directory':str(out),'seconds':record['untrusted_generation_wall_seconds'],
                      'max_state_radius':record['max_state_endpoint_radius'],'max_matrix_radius':record['max_matrix_endpoint_radius'],
                      'status':metadata['status']}))

if __name__=='__main__':main()
