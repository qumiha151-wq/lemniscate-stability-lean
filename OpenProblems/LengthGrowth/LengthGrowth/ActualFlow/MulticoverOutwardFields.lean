import LengthGrowth.ActualFlow.MulticoverOutwardWave
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.Deriv.Shift

noncomputable section
open Set Function MeasureTheory Filter Topology
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false
namespace LengthGrowth.Multicover.Outward

inductive Moment
  | turn | square | rate | diss
deriving DecidableEq

def Moment.apply : Moment→ℝ→ℝ→ℝ
  | .turn,k,_=>k
  | .square,k,_=>k^2
  | .rate,k,f=>k*f
  | .diss,_,f=>f^2

def Moment.val : Moment→Integrals→ℝ
  | .turn,v=>v.turn
  | .square,v=>v.square
  | .rate,v=>v.rate
  | .diss,v=>v.diss

def density (i:Moment) (k:ℝ→ℝ) (s:ℝ):=i.apply (k s) (deriv (deriv k) s+(k s)^3/2)

theorem density_congr (i:Moment) {k l:ℝ→ℝ} {s:ℝ} (h:k=ᶠ[𝓝 s] l) : density i k s=density i l s:=by
  unfold density
  rw [h.eq_of_nhds,h.deriv.deriv.eq_of_nhds]

theorem density_shift (i:Moment) (k:ℝ→ℝ) (a s:ℝ) :
    density i (fun x=>k (x+a)) s=density i k (s+a):=by
  unfold density
  rw [show deriv (fun x=>k (x+a))=(fun x=>deriv k (x+a)) by funext x;exact deriv_comp_add_const ..,
    deriv_comp_add_const]

theorem joint_density {k:ℝ→ℝ→ℝ} (sk:ContDiff ℝ ∞ (fun p:ℝ×ℝ=>k p.1 p.2)) (i:Moment) :
    Continuous (fun p:ℝ×ℝ=>density i (k p.1) p.2):=by
  have der {g:ℝ→ℝ→ℝ} (hg:ContDiff ℝ ∞ (fun p:ℝ×ℝ=>g p.1 p.2)):
      ContDiff ℝ ∞ (fun p:ℝ×ℝ=>deriv (g p.1) p.2):=by
    have h:=LengthGrowth.ActualFlow.joint_smooth_deriv_space (I:=univ) isOpen_univ (f:=g)
      (hf:=hg.contDiffOn)
    simpa only [univ_prod_univ,contDiffOn_univ] using h
  have ck:=sk.continuous
  have c2:=(der (g:=fun u=>deriv (k u)) (der sk)).continuous
  cases i <;> simp only [density,Moment.apply] <;> fun_prop

def cutoff (s:ℝ):=Real.smoothTransition (2*s-1/2)
theorem cutoff_smooth : ContDiff ℝ ∞ cutoff:=Real.smoothTransition.contDiff.comp (by fun_prop)
theorem cutoff_one {s:ℝ} (h:3/4≤s) : cutoff s=1:=Real.smoothTransition.one_of_one_le (by linarith)
theorem cutoff_zero {s:ℝ} (h:s≤1/4) : cutoff s=0:=Real.smoothTransition.zero_of_nonpos (by linarith)

def block (u s:ℝ):=1+cutoff s*cutoff (u+2-s)*(wave s-1)
def leftEnd (s:ℝ):=1+cutoff s*(wave s-1)
def rightEnd (u r:ℝ):=1+cutoff (1-r)*(wave (r+(u+1))-1)

theorem wave_smooth : ContDiff ℝ ∞ (fun s=>wave s):=by
  change ContDiff ℝ ∞ (fun s:ℝ=>(3/2)*Real.cos (1*(3/4*s)));fun_prop

theorem block_smooth : ContDiff ℝ ∞ (fun p:ℝ×ℝ=>block p.1 p.2):=by
  unfold block
  exact contDiff_const.add (((cutoff_smooth.comp contDiff_snd).mul (cutoff_smooth.comp (by fun_prop))).mul ((wave_smooth.comp contDiff_snd).sub contDiff_const))

theorem left_smooth : ContDiff ℝ ∞ leftEnd:=by
  unfold leftEnd
  exact contDiff_const.add (cutoff_smooth.mul (wave_smooth.sub contDiff_const))

theorem right_smooth : ContDiff ℝ ∞ (fun p:ℝ×ℝ=>rightEnd p.1 p.2):=by
  unfold rightEnd
  exact contDiff_const.add ((cutoff_smooth.comp (by fun_prop)).mul ((wave_smooth.comp (by fun_prop)).sub contDiff_const))

theorem wave_per : Periodic (fun s=>wave s) (8*Real.pi/3):=by
  intro x
  change 3/2*Real.cos (1*(3/4*(x+8*Real.pi/3)))=3/2*Real.cos (1*(3/4*x))
  rw [show 1*(3/4*(x+8*Real.pi/3))=1*(3/4*x)+2*Real.pi by ring,Real.cos_add_two_pi]

theorem middle_density (i:Moment) {u s:ℝ} (hs: s∈Icc 1 (u+1)) :
    density i (block u) s=density i (fun x=>wave x) s:=by
  apply density_congr
  filter_upwards [lt_mem_nhds (show 3/4<s by linarith only [hs.1]),
    gt_mem_nhds (show s<u+2-3/4 by linarith only [hs.2])] with x hx ht
  simp [block,cutoff_one hx.le,cutoff_one (show 3/4≤u+2-x by linarith)]

theorem left_density (i:Moment) {u s:ℝ} (hu:2≤u) (hs:s≤1) :
    density i (block u) s=density i leftEnd s:=by
  apply density_congr
  filter_upwards [gt_mem_nhds (show s<u+2-3/4 by linarith)] with x hx
  simp [block,leftEnd,cutoff_one (show 3/4≤u+2-x by linarith)]

theorem right_density (i:Moment) {u r:ℝ} (hu:2≤u) (hr:0≤r) :
    density i (block u) (r+(u+1))=density i (rightEnd u) r:=by
  rw [←density_shift]
  apply density_congr
  filter_upwards [lt_mem_nhds (show -(u+1)+3/4<r by linarith)] with x hx
  simp [block,rightEnd,cutoff_one (show 3/4≤x+(u+1) by linarith),
    show u+2-(x+(u+1))=1-x by ring]

theorem uniform_ends (i:Moment) : ∃B:ℝ,0≤B ∧ ∀u:ℝ,2≤u →
    (∀s∈Icc 0 1,|density i (block u) s|≤B) ∧
    (∀s∈Icc (u+1) (u+2),|density i (block u) s|≤B):=by
  have cl : Continuous (density i leftEnd):=by
    have j:=joint_density (k:=fun _ s=>leftEnd s) (left_smooth.comp contDiff_snd) i
    exact j.comp (show Continuous (fun s:ℝ=>((0:ℝ),s)) by fun_prop)
  have cr:=joint_density right_smooth i
  let P:=8*Real.pi/3
  have pp : 0<P:=by dsimp [P];positivity
  have per (r:ℝ): Periodic (fun u=>density i (rightEnd u) r) P:=by
    intro u
    have eq : rightEnd (u+P)=rightEnd u:=by
      funext x;unfold rightEnd
      have wp : wave (x+(u+1)+P)=wave (x+(u+1)):=wave_per _
      rw [show x+(u+P+1)=x+(u+1)+P by ring,wp]
    change density i (rightEnd (u+P)) r=density i (rightEnd u) r
    rw [eq]
  obtain ⟨l,_,hl⟩:=isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr (by norm_num : (0:ℝ)≤1)) cl.abs.continuousOn
  have ne : ((Icc 0 P) ×ˢ (Icc (0:ℝ) 1)).Nonempty:=⟨(0,0),⟨le_rfl,pp.le⟩,le_rfl,by norm_num⟩
  obtain ⟨z,_,hz⟩:=(isCompact_Icc.prod isCompact_Icc).exists_isMaxOn ne cr.abs.continuousOn
  refine ⟨max |density i leftEnd l| |density i (rightEnd z.1) z.2|,(abs_nonneg _).trans (le_max_left ..),fun u hu=>⟨?_,?_⟩⟩
  · intro s hs
    rw [left_density i hu hs.2]
    exact (hl hs).trans (le_max_left ..)
  · intro s hs
    let r:=s-(u+1)
    have hr : r∈Icc 0 1:=⟨by dsimp [r];linarith only [hs.1],by dsimp [r];linarith only [hs.2]⟩
    obtain ⟨t,ht,eq⟩:=(per r).exists_mem_Ioc pp u 0
    have term:=hz (show (t,r)∈((Icc 0 P) ×ˢ Icc 0 1) from ⟨⟨ht.1.le,by simpa using ht.2⟩,hr⟩)
    rw [←show r+(u+1)=s by dsimp [r];ring,right_density i hu hr.1,eq]
    exact term.trans (le_max_right ..)
end LengthGrowth.Multicover.Outward
#print axioms LengthGrowth.Multicover.Outward.uniform_ends
