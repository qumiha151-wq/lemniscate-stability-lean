import Migration.AngularSpectralExample

namespace MigrationGeometry.AngularGauge.FourierExample

/-- Sparse polynomials in exp(ix) and normalized slab time. Each leaf
uses exclusively real or exclusively imaginary Fourier coefficients, so
one signed integer per term and one common denominator suffice. -/
abbrev Poly := List ((Int × Nat) × Int)

/-- Merge two lists sorted by (time degree, Fourier mode).
The fuel drops whenever at least one list discards a head. -/
def merge : Nat → Poly → Poly → Poly
  | 0, p, q => p ++ q
  | _ + 1, [], q => q
  | _ + 1, p, [] => p
  | k + 1, (i,a) :: p, (j,b) :: q =>
    if i = j then (i,a+b) :: merge k p q
    else if i.2 < j.2 || (i.2 == j.2 && i.1 < j.1)
         then (i,a) :: merge k p ((j,b)::q)
         else (j,b) :: merge k ((i,a)::p) q

def plus (p q : Poly) := merge (p.length+q.length) p q
def scale (a : Int) (p : Poly) : Poly := p.map fun (k,v) => (k,a*v)
def times (p q : Poly) : Poly :=
  p.foldl (fun r (k,a) => plus r (q.map fun (l,b) => ((k.1+l.1,k.2+l.2),a*b))) []

def D : Int := 4800000000000
/-- This multiple of 1,...,40 clears the nonconstant spatial primitive. -/
def C : Int := 5342931457063200
def firstRhs : List (Int × Int) := [(2,1918824),(4,-346160),(6,-13973),(8,190),(10,3)]
def mirrored (j : Nat) (source : List (Int × Int)) : Poly :=
  (source.reverse.map fun (n,a) => ((-n,j),-a)) ++ source.map fun (n,a) => ((n,j),a)
def angleCoeffs : Poly := mirrored 0 [(2,-D/20)] ++ mirrored 1 firstRhs
def vCoeffs : Poly := plus [((0,0),D)] (angleCoeffs.map fun ((n,j),a) => ((n,j),-n*a))
def wCoeffs : Poly := vCoeffs.map fun ((n,j),a) => ((n,j),n*a)

/-- Integer numerators of the full, untruncated imaginary residual at
denominator 2 D^5 C. Products of two imaginary factors enter with a
minus sign. The zero spatial mode of the periodic primitive vanishes. -/
def residual : Poly := Id.run do
  let v := vCoeffs
  let w := wCoeffs
  let v2 := times v v
  let s := plus (scale (-2*D^2) (times w w)) (scale (-1) (times v2 v2))
  let prim : Poly := s.map fun ((n,j),a) => ((n,j),if n=0 then 0 else -(C/n)*a)
  let dt := scale 1000000 (mirrored 0 firstRhs)
  let dx4 : Poly := angleCoeffs.map fun ((n,j),a) => ((n,j),n^4*a)
  return plus (plus (scale (2*D^4*C) (plus dt dx4)) (scale (5*D^2*C) (times v2 w)))
    (scale (-1) (times v prim))

def absSum (p : Poly) : Nat := p.foldl (fun acc e => acc+e.2.natAbs) 0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
theorem residual_certificate :
    ((List.range 40).all (fun k => C % (k+1 : Nat)=0)) = true ∧
    (residual.all (fun e => e.1.2≠0 ∨ e.2=0)) = true ∧
    ((residual.filter (fun e=>e.2≠0)).length=170) ∧
    (absSum residual : Int)*10^9 ≤ 47091*(2*D^5*C) := by
  decide +kernel

set_option maxRecDepth 10000 in
theorem derivative_certificate :
    (absSum vCoeffs : Int)*10^8 ≤ 120000222*D ∧
    (absSum wCoeffs : Int)*10^8 ≤ 40000573*D := by decide +kernel

end MigrationGeometry.AngularGauge.FourierExample
#print axioms MigrationGeometry.AngularGauge.FourierExample.residual_certificate
#print axioms MigrationGeometry.AngularGauge.FourierExample.derivative_certificate
