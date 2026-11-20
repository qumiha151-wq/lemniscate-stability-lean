import Lean
import SolitonClassification.FrozenRowInput

/-! An untrusted elaborator reconstructs polynomial witnesses. The emitted
terms contain only literal natural numbers and the public coefficient decoder. -/
namespace ClosedSimilarity.FrozenStress.Endpoint
open Lean Meta Elab Term

private def decodeSigned (z : ℕ) : ℤ :=
  if z % 2=0 then Int.ofNat (z/2) else Int.negSucc (z/2)

private def encodeSigned : ℤ → ℕ
  | .ofNat n => 2*n
  | .negSucc n => 2*n+1

private def packColumn (v : Array ℤ) : List ℕ := Id.run do
  let mut payload := 0
  for c in v.reverse do
    let code := encodeSigned c
    let width := if code=0 then 0 else code.log2+1
    payload := (((payload <<< width)+code) <<< 10)+width
  let mut blocks := #[]
  while payload≠0 do
    blocks := blocks.push (payload % (1 <<< 2048))
    payload := payload >>> 2048
  return blocks.toList

private def conv (a b : Array ℤ) (n : ℕ) : ℤ := Id.run do
  let mut total := 0
  for j in [:n+1] do
    total := total+a[j]!*b[n-j]!
  return total

private def approximate (degree : ℕ) (point : Array ℤ) : Array (Array ℤ) := Id.run do
  let scale : ℤ := Int.ofNat (1 <<< 504)
  let mut k := #[point[0]!]
  let mut v := #[point[1]!]
  let mut p := #[point[2]!]
  let mut q := #[point[3]!]
  let mut square := #[]
  for n in [:degree] do
    square := square.push (conv k k n / scale)
    let den : ℤ := (n+1)*32
    let dk := v[n]!
    let dv := -(conv square k n / (2*scale))-p[n]!
    let dp := -(conv k q n / scale)
    let dq := conv k p n / scale
    k := k.push (dk/den)
    v := v.push (dv/den)
    p := p.push (dp/den)
    q := q.push (dq/den)
  return #[k,v,p,q]

syntax "frozenRows% " "[" num,* "]" num num num num : term

elab_rules : term
  | `(frozenRows% [$ds:num,*] $k:num $v:num $p:num $q:num) => do
    let mut point := #[k.getNat,v.getNat,p.getNat,q.getNat].map decodeSigned
    let mut rows := #[]
    for deg in ds.getElems do
      let columns := approximate deg.getNat point
      let terms := columns.map fun col =>
        mkApp2 (mkConst ``coefficients) (toExpr col.size) (toExpr (packColumn col))
      rows := rows.push (mkAppN (mkConst ``Row.mk) terms)
      point := columns.map fun col => col.foldl (·+·) 0
    mkListLit (mkConst ``Row) rows.toList

end ClosedSimilarity.FrozenStress.Endpoint
