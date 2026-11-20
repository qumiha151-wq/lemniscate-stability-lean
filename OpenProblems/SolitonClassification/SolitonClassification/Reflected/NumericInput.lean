import SolitonClassification.Reflected.ActualEvent
namespace SolitonClassification.Reflected
open SolitonClassification.Rotating Set
set_option linter.unnecessarySeqFocus false
def minusStart : Box := ⟨#[⟨0,0⟩,⟨899083403241250000000000000,1⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩],rfl⟩
def minusEnd : Box := ⟨#[⟨-22397058260227757089513176061,8091828064780187⟩,⟨43454555039407446896,2737074991314226⟩,⟨6568491194487444587908864374,6842028916651563⟩,⟨-195932084406579597121,7848487629168832⟩,⟨0,740000001480⟩,⟨30870600613342038391586818013,4074818004269293⟩],rfl⟩
def allStart : Box := ⟨#[⟨0,0⟩,⟨899083415741250000000000000,12500000000000000001⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩],rfl⟩
def allEnd : Box := ⟨#[⟨-22397058125870749886231973286,726890571495826620234207⟩,⟨32300089656605,245958577230559375367128⟩,⟨6568491369363681052557042089,617301577296264617813310⟩,⟨-131616384891436,707689714227866366468761⟩,⟨0,740000001480⟩,⟨30870600726223617547586139692,365626610944613036253865⟩],rfl⟩
def plusStart : Box := ⟨#[⟨0,0⟩,⟨899083428241250000000000000,1⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩],rfl⟩
def plusEnd : Box := ⟨#[⟨-22397057991513740422788470751,8091827695992804⟩,⟨-43454490722397853471,2737074824347681⟩,⟨6568491544239913609027588521,6842028632896460⟩,⟨195931825154615140184,7848487263845589⟩,⟨0,740000001480⟩,⟨30870600839105200568429287014,4074817895075142⟩],rfl⟩

theorem allInitial {b : ℝ} (hb : b ∈ slopes) : BoxContains allStart (initial b) := by
  obtain ⟨hl,hu⟩ := hb
  norm_num [leftSlope,rightSlope] at hl hu
  intro i
  fin_cases i <;> norm_num [initial,allStart,boxFn,FixedBall.Contains,FixedBall.toRational,
    RationalBall.Contains,mesh,abs_le] <;> constructor <;> linarith

theorem minusInitial : BoxContains minusStart (initial leftSlope) := by
  intro i
  fin_cases i <;> norm_num [initial,leftSlope,minusStart,boxFn,FixedBall.Contains,FixedBall.toRational,
    RationalBall.Contains,mesh,abs_le]
theorem plusInitial : BoxContains plusStart (initial rightSlope) := by
  intro i
  fin_cases i <;> norm_num [initial,rightSlope,plusStart,boxFn,FixedBall.Contains,FixedBall.toRational,
    RationalBall.Contains,mesh,abs_le]

theorem midData_of_trajectories (wide : Segment traceStep allStart allEnd center)
    (lo : Segment traceStep minusStart minusEnd center)
    (hi : Segment traceStep plusStart plusEnd center) : MidData := by
  have wideEnd {b : ℝ} (hb : b∈slopes) : BoxContains allEnd (shot b center) :=
    wide.endpoint _ (allInitial hb)
  have loEnd : BoxContains minusEnd (shot leftSlope center) := lo.endpoint _ minusInitial
  have hiEnd : BoxContains plusEnd (shot rightSlope center) := hi.endpoint _ plusInitial
  constructor
  · intro b hb
    have hp:=fixedBall_contains_lower_upper (wideEnd hb 0)
    norm_num [FixedBall.toRational,boxFn,allEnd,mesh,velocity,tangentSupport,abs_le,Set.mem_Icc] at hp ⊢
    constructor <;> linarith
  · intro b hb
    have hp:=fixedBall_contains_lower_upper (wideEnd hb 2)
    norm_num [FixedBall.toRational,boxFn,allEnd,mesh,velocity,tangentSupport,abs_le,Set.mem_Icc] at hp ⊢
    constructor <;> linarith
  · intro b hb
    have hp:=fixedBall_contains_lower_upper (wideEnd hb 1)
    norm_num [FixedBall.toRational,boxFn,allEnd,mesh,velocity,tangentSupport,abs_le,Set.mem_Icc] at hp ⊢
    rcases le_or_gt 0 (shot b center 1) with hs | hs
    · rw [abs_of_nonneg hs]; linarith
    · rw [abs_of_neg hs]; linarith
  · intro b hb
    have hp:=fixedBall_contains_lower_upper (wideEnd hb 3)
    norm_num [FixedBall.toRational,boxFn,allEnd,mesh,velocity,tangentSupport,abs_le,Set.mem_Icc] at hp ⊢
    constructor <;> linarith
  · have hp:=fixedBall_contains_lower_upper (loEnd 1)
    norm_num [FixedBall.toRational,boxFn,minusEnd,mesh,velocity,tangentSupport,abs_le,Set.mem_Icc] at hp ⊢
    rcases le_or_gt 0 (shot leftSlope center 1) with hs | hs
    · rw [abs_of_nonneg hs]; linarith
    · rw [abs_of_neg hs]; linarith
  · have hp:=fixedBall_contains_lower_upper (hiEnd 1)
    norm_num [FixedBall.toRational,boxFn,plusEnd,mesh,velocity,tangentSupport,abs_le,Set.mem_Icc] at hp ⊢
    rcases le_or_gt 0 (shot rightSlope center 1) with hs | hs
    · rw [abs_of_nonneg hs]; linarith
    · rw [abs_of_neg hs]; linarith
  · have hp:=fixedBall_contains_lower_upper (loEnd 3)
    norm_num [FixedBall.toRational,boxFn,minusEnd,mesh,velocity,tangentSupport,abs_le,Set.mem_Icc] at hp ⊢
    linarith
  · have hp:=fixedBall_contains_lower_upper (hiEnd 3)
    norm_num [FixedBall.toRational,boxFn,plusEnd,mesh,velocity,tangentSupport,abs_le,Set.mem_Icc] at hp ⊢
    linarith

theorem trajectory_event (wide : Segment traceStep allStart allEnd center)
    (lo : Segment traceStep minusStart minusEnd center)
    (hi : Segment traceStep plusStart plusEnd center) :
    ∃b∈slopes, ∃t∈times, velocity (b,t)=0 ∧ tangentSupport (b,t)=0 ∧
      ∀x∈Icc 0 t, shot b x ∈ outerTube := by
  have h:=midData_of_trajectories wide lo hi
  obtain ⟨b,hb,t,ht,hv,hq⟩:=zero_from_midData h
  refine ⟨b,hb,t,ht,hv,hq,fun x hx => ?_⟩
  by_cases he : x≤center
  · exact wide.tube _ (allInitial hb) x ⟨hx.1,he⟩
  · apply (actual_event_derivatives h hb _).1
    exact ⟨by linarith [show 0≤width by norm_num [width]],hx.2.trans ht.2⟩
end SolitonClassification.Reflected
#print axioms SolitonClassification.Reflected.trajectory_event
