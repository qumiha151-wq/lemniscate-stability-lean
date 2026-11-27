import SolitonClassification.MeromorphicOrdinaryPole
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

noncomputable section
open Complex Set Filter Metric
open scoped Topology
namespace ClosedSimilarity.RamifiedBounded

def puncturedDisk (d:ℝ) : Set ℂ := {z | z≠0 ∧ ‖z‖<d}

theorem puncturedDisk_preconnected (d:ℝ) : IsPreconnected (puncturedDisk d) := by
  let F (p : ℝ × ℂ) := (p.1:ℂ)*p.2
  have continuous : Continuous F := by dsimp [F];fun_prop
  let S:=(Ioo (0:ℝ) d) ×ˢ (sphere (0:ℂ) 1)
  have hs : IsPreconnected S := isPreconnected_Ioo.prod (isPreconnected_sphere (by simp) _ _)
  have eq : F '' S=puncturedDisk d := by
    ext w
    constructor
    · rintro ⟨⟨r,v⟩,⟨hr,hv⟩,rfl⟩
      have vn : ‖v‖=1 := by simpa only [mem_sphere,dist_zero_right] using hv
      have rn : ‖F (r,v)‖=r := by simp [F,vn,Real.norm_eq_abs,abs_of_pos hr.1]
      exact ⟨norm_pos_iff.mp (by rw [rn];exact hr.1),by rw [rn];exact hr.2⟩
    · rintro ⟨nw,hw⟩
      have hn := norm_pos_iff.mpr nw
      have rn : (‖w‖:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hn.ne'
      refine ⟨(‖w‖,w/(‖w‖:ℂ)),⟨⟨hn,hw⟩,?_⟩,?_⟩
      · simp [hn.ne']
      · dsimp only [F];field_simp
  rw [←eq]
  exact hs.image _ continuous.continuousOn

theorem punctured_identity {f g:ℂ→ℂ} {d:ℝ} {p:ℂ} (hp:p∈puncturedDisk d)
    (mf:∀z∈puncturedDisk d,MeromorphicNFAt f z)
    (mg:∀z∈puncturedDisk d,MeromorphicNFAt g z)
    (localEq:f=ᶠ[𝓝[≠] p] g) : ∀z∈puncturedDisk d,f z=g z := by
  have eq0 : meromorphicOrderAt (fun w=>f w-g w) p=⊤ :=
    meromorphicOrderAt_eq_top_iff.mpr (localEq.mono (fun _ e=>sub_eq_zero.mpr e))
  have md : MeromorphicOn (fun w=>f w-g w) (puncturedDisk d) :=
    fun z hz=>(mf z hz).meromorphicAt.sub (mg z hz).meromorphicAt
  intro z hz
  have high : meromorphicOrderAt (fun w=>f w-g w) z=⊤ := by
    by_contra ne
    exact (md.meromorphicOrderAt_ne_top_of_isPreconnected (puncturedDisk_preconnected d) hz hp ne) eq0
  exact (((mf z hz).eventuallyEq_nhdsNE_iff_eventuallyEq_nhds (mg z hz)).mp
    ((meromorphicOrderAt_eq_top_iff.mp high).mono (fun _ e=>sub_eq_zero.mp e))).eq_of_nhds

theorem neg_normal {f:ℂ→ℂ} {z:ℂ} (h:MeromorphicNFAt f z) : MeromorphicNFAt (fun t=> -f t) z := by
  have e:=h.smul_analytic (analyticAt_const (v:=(-1:ℂ))) (by norm_num)
  convert! e using 1
  ext t
  exact (neg_one_mul (f t)).symm

#print axioms punctured_identity
end ClosedSimilarity.RamifiedBounded
