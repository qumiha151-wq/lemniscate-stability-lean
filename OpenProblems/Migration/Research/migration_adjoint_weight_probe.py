"""Exact checks of the projected expander identity and rational jet obstructions.

The finite-dimensional search concerns uniform pointwise multipliers on ALL
local initial jets of the ODE. The selected jets need not be on a closed orbit.
"""
from itertools import product
import json
from pathlib import Path


from flint import fmpq, fmpq_mat, fmpq_mpoly_ctx
import numpy as np
from scipy.optimize import linprog

C = fmpq_mpoly_ctx.get(('k', 'v', 'p', 'q'))
k, v, p, q = C.gens()
field = (v, -k**3/2-p, -k*q, 1+k*p)


def ds(f):
    return sum(g*f.derivative(i) for i,g in enumerate(field))


def adj(f):
    return ds(ds(ds(ds(f)))) + ds(3*k**2*ds(f)/2) + ds(q*f) + f


def powers(N):
    # Average under ambient reflection and reversal of orientation.
    return [e for e in product(range(N+1), repeat=4) if sum(e) <= N and
            (e[0]+e[1]+e[2])%2 == 0 and (e[0]+e[2]+e[3])%2 == 0]


def multiplier(e):
    f = k**0
    for x,j in zip((k,v,p,q),e):
        f *= x**j
    return f


def test(N):
    basis = powers(N)
    funcs = [adj(multiplier(e)) for e in basis]
    grid = list(product((-4,-3,-2,-1,0,1,2,3,4), repeat=4))
    grid = [x for x in grid if x[0] >= 0 and x[3] >= 0]
    # Include reflected-sign combinations at k=0 or q=0 as separate samples.
    columns = [[f(*x) for f in funcs] for x in grid]
    M = np.array([[float(y) for y in col] for col in columns]).T
    M /= np.maximum(1,np.max(np.abs(M),axis=1))[:,None]
    result = linprog(np.arange(len(grid))*1e-4,A_eq=np.vstack((np.ones(len(grid)),M)),
        b_eq=[1]+[0]*len(funcs),bounds=(0,None),method='highs')
    if not result.success:
        return dict(degree=N, columns=len(basis), status=result.message)
    active = np.flatnonzero(result.x>1e-9).tolist()
    # Some sampled moment rows can be dependent. Pick a maximal independent
    # subset exactly by RREF on the transposed system.
    exact_rows = [[fmpq(1) for _ in active]] + [
        [columns[i][j] for i in active] for j in range(len(funcs))]
    system = fmpq_mat(exact_rows)
    rref, rank = system.transpose().rref()
    pivot_rows = [next(j for j in range(rref.ncols()) if rref[i,j] != 0) for i in range(rank)]
    assert rank == len(active) == len(funcs)+1 and pivot_rows[0]==0
    coefficients = fmpq_mat([exact_rows[j] for j in pivot_rows]).solve(
        fmpq_mat([[int(j==0)] for j in pivot_rows]))
    rhs = system*coefficients
    assert all(rhs[i,0] == int(i==0) for i in range(rhs.nrows()))
    assert all(coefficients[i,0] > 0 for i in range(rank))
    return dict(degree=N, basis_exponents=basis, status='exact positive annihilator',
        atoms=[dict(jet=grid[j],weight=str(coefficients[i,0])) for i,j in enumerate(active)])


def main():
    r2 = p**2+q**2
    assert adj(k**0) == 2+k*p
    assert adj(r2/2) == k**2/2+2*q**2+k*p*r2/2
    H = -k**3/2-p
    assert ds(H) == -(3*k**2*v)/2+k*q
    results = [test(i) for i in (2,3,4,5)]
    print([(r['degree'],r['status'],len(r.get('atoms',[]))) for r in results])
    target = Path(__file__).with_name('migration_adjoint_weight_probe.json')
    target.write_text(json.dumps(results,indent=2)+'\n',encoding='utf-8')


if __name__ == '__main__':
    main()
