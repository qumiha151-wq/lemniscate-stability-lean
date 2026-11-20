import SolitonClassification.FrozenDyadicChain
import SolitonClassification.FrozenEndpointSigns

noncomputable section
namespace ClosedSimilarity.FrozenStress.Endpoint
open Set
set_option exponentiation.threshold 2048

def negativeStart : Mark := ⟨(-13093562431584567480052758787310396608866568184172259157933165472384535185618698219533080369303616628603546736510240284036869026183541572213314110357504),0,52374249726338269920211035149241586435466272736689036631732661889538140742474792878132321477214466514414186946040961136147476104734166288853256441430016,0⟩
def negativeFinish : Mark := ⟨178779580508608869566247713777730258117727926001156538290664696003664624616435780267905590384400957496362430760574297371724652479061435051829375890156335,635183880152618440335951934729127530649741988360045443689612393454781752932464622019202444769219101350304284235166468580269906957803391977999454319498905,(-47747442678633460125264594105837867641335780086809300000451738981615511972215636212927958653340509899418882122059991583292155657969921687854423473074014),(-21523098105232348912549201395355557308390712990778217560431403003305245496419847704941661723600582831679437050639080872850730639473501981876927073647931)⟩

theorem negative_from_transport (replay : Transports 0 640 negativeStart negativeFinish)
    (z : Orbit) (hk : z.k 0=(-1/4)) (hv : z.v 0=0) (hp : z.p 0=1) (hq : z.q 0=0) :
    13 < -z.radial 20 ∧ -0.10 < correctedImpact z.root z.shape z.slope z.along z.across 20 ∧ correctedImpact z.root z.shape z.slope z.along z.across 20 < -0.09 ∧ |z.root 20*z.across 20| < 0.25 := by
  have zr : z.radial 0=0 := by simp [Orbit.radial,hq,hv]
  have zb : |z.transverse 0|≤1 := by norm_num [Orbit.transverse,hk,hp,hq,hv]
  have ini : state z 0=markState negativeStart := by
    funext i
    fin_cases i <;> norm_num [state,markState,negativeStart,S,hk,hv,hp,hq]
  have err := zero_to_twenty replay z zr zb ini
  have coordinate (i : Fin 4) : |state z 20 i-markState negativeFinish i| ≤ 1/2^20 :=
    (norm_le_pi_norm _ i).trans err
  apply EndpointSigns.negative_box z 20
  · have h := abs_le.mp (coordinate 0)
    change -_ ≤ z.k 20-(negativeFinish.k:ℝ)/S ∧ z.k 20-(negativeFinish.k:ℝ)/S ≤ _ at h
    norm_num [negativeFinish,S] at h
    constructor <;> linarith [h.1,h.2]
  · have h := abs_le.mp (coordinate 1)
    change -_ ≤ z.v 20/8-(negativeFinish.v:ℝ)/(8*S) ∧ z.v 20/8-(negativeFinish.v:ℝ)/(8*S) ≤ _ at h
    norm_num [negativeFinish,S] at h
    constructor <;> linarith [h.1,h.2]
  · have h := abs_le.mp (coordinate 2)
    change -_ ≤ z.p 20-(negativeFinish.p:ℝ)/S ∧ z.p 20-(negativeFinish.p:ℝ)/S ≤ _ at h
    norm_num [negativeFinish,S] at h
    constructor <;> linarith [h.1,h.2]
  · have h := abs_le.mp (coordinate 3)
    change -_ ≤ z.q 20-(negativeFinish.q:ℝ)/S ∧ z.q 20-(negativeFinish.q:ℝ)/S ≤ _ at h
    norm_num [negativeFinish,S] at h
    constructor <;> linarith [h.1,h.2]

def positiveStart : Mark := ⟨52374249726338269920211035149241586435466272736689036631732661889538140742474792878132321477214466514414186946040961136147476104734166288853256441430016,0,52374249726338269920211035149241586435466272736689036631732661889538140742474792878132321477214466514414186946040961136147476104734166288853256441430016,0⟩
def positiveFinish : Mark := ⟨(-150496231212480689008753227791347345220143676715606499317136332211053729634035309760887218277397702481148683828530979389819681625757823118990849343179754),630872809851935874666458041159753723877872021812835830467718726409689002744876817859812997331604149085904081516633868821245751626741697872914022228625591,(-43754922016443450616227503019675631765701781854845174374360249042680484115991203203306741804801880365220871789471033860055101921602745189967016194567975),(-28784871612216660069460959770464750960038433591376304365176673133935591872650587656749822711264706863613192109982569669710730041717916669099531731464858)⟩

theorem positive_from_transport (replay : Transports 0 640 positiveStart positiveFinish)
    (z : Orbit) (hk : z.k 0=1) (hv : z.v 0=0) (hp : z.p 0=1) (hq : z.q 0=0) :
    12 < -z.radial 20 ∧ 0.8 < correctedImpact z.root z.shape z.slope z.along z.across 20 := by
  have zr : z.radial 0=0 := by simp [Orbit.radial,hq,hv]
  have zb : |z.transverse 0|≤1 := by norm_num [Orbit.transverse,hk,hp,hq,hv]
  have ini : state z 0=markState positiveStart := by
    funext i
    fin_cases i <;> norm_num [state,markState,positiveStart,S,hk,hv,hp,hq]
  have err := zero_to_twenty replay z zr zb ini
  have coordinate (i : Fin 4) : |state z 20 i-markState positiveFinish i| ≤ 1/2^20 :=
    (norm_le_pi_norm _ i).trans err
  apply EndpointSigns.positive_box z 20
  · have h := abs_le.mp (coordinate 0)
    change -_ ≤ z.k 20-(positiveFinish.k:ℝ)/S ∧ z.k 20-(positiveFinish.k:ℝ)/S ≤ _ at h
    norm_num [positiveFinish,S] at h
    constructor <;> linarith [h.1,h.2]
  · have h := abs_le.mp (coordinate 1)
    change -_ ≤ z.v 20/8-(positiveFinish.v:ℝ)/(8*S) ∧ z.v 20/8-(positiveFinish.v:ℝ)/(8*S) ≤ _ at h
    norm_num [positiveFinish,S] at h
    constructor <;> linarith [h.1,h.2]
  · have h := abs_le.mp (coordinate 2)
    change -_ ≤ z.p 20-(positiveFinish.p:ℝ)/S ∧ z.p 20-(positiveFinish.p:ℝ)/S ≤ _ at h
    norm_num [positiveFinish,S] at h
    constructor <;> linarith [h.1,h.2]
  · have h := abs_le.mp (coordinate 3)
    change -_ ≤ z.q 20-(positiveFinish.q:ℝ)/S ∧ z.q 20-(positiveFinish.q:ℝ)/S ≤ _ at h
    norm_num [positiveFinish,S] at h
    constructor <;> linarith [h.1,h.2]

end ClosedSimilarity.FrozenStress.Endpoint
#print axioms ClosedSimilarity.FrozenStress.Endpoint.negative_from_transport
#print axioms ClosedSimilarity.FrozenStress.Endpoint.positive_from_transport
