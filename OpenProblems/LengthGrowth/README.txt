LengthGrowth: static estimates and actual forward-flow variation laws

This independent Lean 4.33.1 project imports Mathlib and its own LengthGrowth
modules. It does not import the other open-problem formalizations.

The ActualFlow addition starts with a genuine smooth periodic planar position
family on an open time domain, with nonzero spatial derivative. It defines
speed, frame, curvature, elastic force, stress, length, energy, dissipation
and velocity using actual derivatives and integrals. Their regularity,
Frenet identities, mixed-partial consequences and periodicity are proved.
For the actual normal velocity equation gamma_t = -F N it proves
  L'(t) = integral k F ds,       E'(t) = -integral F^2 ds,
and the corresponding length secant estimate on compact intervals contained
in the open time domain. No metric or curvature variation law is a field.

FourJetForce separately identifies the intrinsic elastic force with its
formula in the first four position derivatives and proves continuity along
any filter when the limiting first derivative is nonzero.

ForwardGeometry and ForwardDissipation extend the integral laws to initial
time using continuous actual spatial jets, without assuming a backward flow.
For a global forward classical normal FEF with the stated initial regularity,
they prove L(t)/sqrt(t) tends to zero. This is not a global existence theorem.
The batch does not prove uniform normalized energy, bounded total absolute
curvature, or the unrestricted quarter-power length growth conjecture. The existing
scalar conditional results and static coercivity remain separate theorems.
See ActualFlowScope.txt for the assumptions and exported interfaces.

Build from this directory using the pinned lean-toolchain and lake-manifest:
  lake build
The default target also includes LengthGrowth.AxiomAudit. The audit recursively
permits only propext, Classical.choice and Quot.sound in the project namespaces.

ActualFlowEvidence records successful author module logs and the independent
local integration of the updated entry point with the unchanged project audit.
Integration reused checked leaf objects; it was not a fresh rebuild of every
leaf. No compiled objects are included in this source publication.
