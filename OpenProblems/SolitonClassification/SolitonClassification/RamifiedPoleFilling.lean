import SolitonClassification.RamifiedMirrorDisk
import SolitonClassification.RamifiedLocalMirror

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Complex Set Filter Metric
open scoped Topology
namespace ClosedSimilarity.RamifiedBounded
open MeromorphicCurvature

/-- One sufficiently close ordinary pole is enough to fill the branch
value by reflecting a germ at an ordinary point. Ordinary poles may be
present elsewhere on the punctured cover. -/
theorem descends_of_nearby_pole {q:ℕ} (hq:0<q) {r:ℝ} {s₀ p:ℂ} (np:p≠0)
    (near:4*‖p‖≤r) {f:ℂ→ℂ} (nf:∀w:ℂ,w≠0 → ‖w‖<r → MeromorphicNFAt f w)
    {a b:ℝ} (ap:0<a) (k:ℂ→ℂ) (nk:MeromorphicNFAt k (s₀+p^q))
    (sing:¬AnalyticAt ℂ k (s₀+p^q))
    (rep:f=ᶠ[𝓝 p] fun w=>k (s₀+w^q))
    (law:ordinaryResidual a b k=ᶠ[𝓝[≠] (s₀+p^q)] fun _=>0) :
    ∃G:ℂ→ℂ,MeromorphicAt G s₀ ∧ f=ᶠ[𝓝[≠] 0] fun w=>G (s₀+w^q) := by
  obtain ⟨d,d1,d2,dq⟩ := exists_mirror_radius q
  have dp := zero_lt_one.trans d1
  have pn := norm_pos_iff.mpr np
  let R:=d*‖p‖
  have Rp : 0<R := mul_pos dp pn
  have pR : p∈puncturedDisk R :=
    ⟨np,by dsimp [R];simpa only [one_mul] using mul_lt_mul_of_pos_right d1 pn⟩
  have Rr : R<r := by
    dsimp [R]
    exact (mul_lt_mul_of_pos_right (d2.trans (by norm_num : (2:ℝ)<4)) pn).trans_le near
  let J (w:ℂ) := mirrorLift q p (w^q)
  let F (s:ℂ) := -f (mirrorLift q p s)
  let g (w:ℂ) := F (w^q)
  have geom {w:ℂ} (hw:‖w‖<R) := mirrorLift_geometry hq np dq hw
  have gNF {w:ℂ} (hw:‖w‖<R) : MeromorphicNFAt g w := by
    obtain ⟨an,nz,bd⟩ := geom hw
    exact neg_normal ((nf _ nz (bd.trans_le near)).comp_analyticAt (g:=J)
      ((an.comp (f:=fun z:ℂ=>z^q) (analyticAt_id.pow q))))
  have j0 : J p=p := mirrorLift_center q np
  have ja : AnalyticAt ℂ J p := (geom pR.2).1.comp (f:=fun z:ℂ=>z^q) (analyticAt_id.pow q)
  have jt : Tendsto J (𝓝 p) (𝓝 p) := by simpa only [j0] using ja.continuousAt.tendsto
  have t : Tendsto (fun w:ℂ=>s₀+w^q) (𝓝 p) (𝓝 (s₀+p^q)) :=
    (show ContinuousAt (fun w:ℂ=>s₀+w^q) p by fun_prop).tendsto
  have odd := ordinary_pole_odd_germ ap nk sing law
  have seed : f=ᶠ[𝓝 p] g := by
    filter_upwards [rep,jt.eventually rep,t.eventually odd] with w ew ej eodd
    change f w= -f (J w)
    rw [ew,ej,eodd]
    change -k (2*(s₀+p^q)-(s₀+w^q))= -k (s₀+(mirrorLift q p (w^q))^q)
    rw [mirrorLift_power hq np]
    congr 2
    ring
  have ident := punctured_identity pR (fun w hw=>nf w hw.1 (hw.2.trans Rr))
    (fun _ hw=>gNF hw.2) (seed.filter_mono nhdsWithin_le_nhds)
  have igeom := geom (w:=0) (by simpa using Rp)
  have at0 : MeromorphicAt F 0 := by
    obtain ⟨an,nz,bd⟩ := igeom
    rw [zero_pow hq.ne'] at an nz bd
    exact ((nf _ nz (bd.trans_le near)).meromorphicAt.comp_analyticAt an).neg
  let G (s:ℂ) := F (s-s₀)
  have base : MeromorphicAt G s₀ := by
    apply meromorphicAt_fun_comp_sub_const_iff_meromorphicAt.mpr
    simpa only [sub_self] using at0
  refine ⟨G,base,?_⟩
  filter_upwards [eventually_nhdsWithin_of_eventually_nhds (ball_mem_nhds (0:ℂ) Rp),
    eventually_mem_nhdsWithin] with w hw nw
  simpa only [G,g,add_sub_cancel_left] using ident w ⟨nw,by simpa only [mem_ball,dist_zero_right] using hw⟩

#print axioms descends_of_nearby_pole
end ClosedSimilarity.RamifiedBounded
