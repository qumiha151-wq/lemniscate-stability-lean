"""Independent floating-point check; the proof is in the companion .txt file."""
import sys
sys.path.insert(0, r'C:\Users\17815\Documents\Codex\2026-11-11\w\work\pydeps')
import numpy as np
from scipy.special import ellipj, ellipk, ellipe
from scipy.integrate import quad

m = 2/3
Ke, Ee = ellipk(m), ellipe(m)
omega, L = 2*Ke/np.pi, 2*np.pi
lam = omega**2/3

def K(s):
    return 2*omega*np.sqrt(m)*ellipj(omega*s, m)[1]

A2 = quad(lambda s: K(s)**2, 0, L, epsabs=1e-11)[0]
A4 = quad(lambda s: K(s)**4, 0, L, epsabs=1e-10)[0]
print(f'omega={omega:.14g}; lambda={lam:.14g}; Eell/Kell={Ee/Ke:.14g}')
print(f'A2={A2:.14g}; A4={A4:.14g}')
print(f'A2 identity residual={A2-4*L*omega**2*(Ee/Ke-1/3):.3g}')
print(f'positive gap={A2/(2*L)-lam:.14g}; rigorous bound={omega**2/7:.14g}')

# High-resolution trapezoidal quadrature is used only as an independent
# numerical cross-check of closure and the exact symbolic integral expansions.
for q, N in [(1, 12), (1, 24), (-1, 12), (2, 24), (3, 36)]:
    s = np.linspace(0, L, 131072, endpoint=False)
    sn, cn, dn, ph = ellipj(omega*N*s, m)
    theta = q*s+2*np.arcsin(np.sqrt(m)*sn)
    curvature_wave = 2*omega*np.sqrt(m)*cn
    k = q+N*curvature_wave
    kss = N**3*(lam*curvature_wave-curvature_wave**3/2)
    F = kss+k**3/2
    E_num = L*np.mean(k*k)/2
    D_num = L*np.mean(F*F)
    Lp_num = L*np.mean(k*F)
    Up_num = -L*D_num+E_num*Lp_num
    Up_formula = (lam*A2*(A2/2-L*lam)*N**6
                  + q*q*(1.5*A2*A2-2.5*L*lam*A2-2.25*L*A4)*N**4
                  -2*q**4*L*A2*N*N)
    closure = abs(L*np.mean(np.exp(1j*theta)))
    print(f'q={q} N={N}: closure={closure:.3g}; EL={E_num*L:.14g}; '
          f'Up={Up_num:.14g}; relative polynomial error='
          f'{abs(Up_num-Up_formula)/abs(Up_formula):.3g}')
    assert closure < 1e-10
    assert Up_num > 0
    assert abs(Up_num-Up_formula)/abs(Up_formula) < 1e-10
print('Floating-point checks passed. These are not interval certificates.')
