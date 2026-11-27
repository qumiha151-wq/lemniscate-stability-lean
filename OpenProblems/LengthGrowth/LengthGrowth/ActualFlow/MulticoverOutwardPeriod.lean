import LengthGrowth.ActualFlow.MulticoverOutwardFields
import Mathlib.Topology.Instances.AddCircle.Defs

noncomputable section
open Set Filter Topology Function
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false
namespace LengthGrowth.Multicover.Outward

def repeatCurve (P:ℝ) (hp:0<P) (g:ℝ→ℝ) (s:ℝ):=g (toIcoMod hp 0 s)

theorem repeat_periodic (P:ℝ) (hp:0<P) (g:ℝ→ℝ) : Periodic (repeatCurve P hp g) P:=by
  intro x;unfold repeatCurve;rw [toIcoMod_add_right]

theorem repeat_eq {P:ℝ} (hp:0<P) (g:ℝ→ℝ) {s:ℝ} (hs:s∈Ico 0 P):repeatCurve P hp g s=g s:=by
  unfold repeatCurve
  rw [(toIcoMod_eq_self hp).mpr (by simpa using hs)]

theorem repeat_flat (P:ℝ) (hp:1<P) (g:ℝ→ℝ) (flat : (∀x,x≤1/4→g x=1) ∧ (∀x,P-1/4≤x→g x=1)) :
    repeatCurve P (by linarith) g=ᶠ[𝓝 0](fun _=>1):=by
  have pp : 0<P:=by linarith
  filter_upwards [Ioo_mem_nhds (by norm_num : -(1/4:ℝ)<0) (by norm_num : (0:ℝ)<1/4)] with x hx
  by_cases sign : 0≤x
  · rw [repeat_eq pp g (show x∈Ico 0 P from ⟨sign,by linarith only [hx.2,hp]⟩)]
    exact flat.1 x hx.2.le
  rw [←repeat_periodic P pp g x,repeat_eq pp g (show x+P∈Ico 0 P from ⟨by linarith only [hx.1,hp],by linarith⟩)]
  exact flat.2 _ (by linarith only [hx.1])

theorem repeat_agrees {P:ℝ} (hp:1<P) (g:ℝ→ℝ) (flat : (∀x,x≤1/4→g x=1) ∧ (∀x,P-1/4≤x→g x=1))
    {s:ℝ} (hs:s∈Icc 0 P) : repeatCurve P (by linarith) g=ᶠ[𝓝 s] g:=by
  have pp : 0<P:=by linarith
  rcases eq_or_lt_of_le hs.1 with eq|sl
  · subst s
    apply (repeat_flat P hp g flat).trans
    filter_upwards [gt_mem_nhds (by norm_num : (0:ℝ)<1/4)] with x hx
    exact (flat.1 x hx.le).symm
  rcases lt_or_eq_of_le hs.2 with sr|eq
  · filter_upwards [Ioo_mem_nhds sl sr] with y hy
    exact repeat_eq pp g ⟨hy.1.le,hy.2⟩
  subst s
  have shifted : (fun x:ℝ=>x-P) P=0:=sub_self _
  have tr : Tendsto (fun x:ℝ=>x-P) (𝓝 P) (𝓝 0):=shifted ▸ ((continuous_id.sub continuous_const).continuousAt (x:=P)).tendsto
  filter_upwards [tr.eventually (repeat_flat P hp g flat),lt_mem_nhds (show P-1/4<P by linarith)] with x hx ha
  change repeatCurve P pp g (x-P)=1 at hx
  have per:=repeat_periodic P pp g (x-P)
  rw [sub_add_cancel] at per
  exact per.trans (hx.trans (flat.2 _ ha.le).symm)

theorem repeat_smooth {P:ℝ} (hp:1<P) (g:ℝ→ℝ) (cg:ContDiff ℝ ∞ g)
    (flat : (∀x,x≤1/4→g x=1) ∧ (∀x,P-1/4≤x→g x=1)) :
    ContDiff ℝ ∞ (repeatCurve P (by linarith) g):=by
  have pp : 0<P:=by linarith
  apply contDiff_iff_contDiffAt.mpr
  intro x
  obtain ⟨n,hn,_⟩:=existsUnique_add_zsmul_mem_Ico pp x 0
  have hin : x+n • P∈Icc 0 P:=by simpa using Ico_subset_Icc_self hn
  have loc : ContDiffAt ℝ ∞ (repeatCurve P pp g) (x+n • P):=
    cg.contDiffAt.congr_of_eventuallyEq (repeat_agrees hp g flat hin)
  have trans:=loc.comp x (show ContDiffAt ℝ ∞ (fun y:ℝ=>y+n • P) x by fun_prop)
  have eq : (repeatCurve P pp g) ∘ (fun y:ℝ=>y+n • P)=repeatCurve P pp g:=funext ((repeat_periodic P pp g).zsmul n)
  exact eq ▸ trans

end LengthGrowth.Multicover.Outward
#print axioms LengthGrowth.Multicover.Outward.repeat_smooth
