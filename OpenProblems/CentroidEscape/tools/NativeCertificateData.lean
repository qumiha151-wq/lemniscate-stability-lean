import CentroidEscape.CertificateSeedParameters
import CentroidEscape.BallStep

/- Untrusted data generation and cost/width preflight only. No theorem is
   established by this executable. Every generated arithmetic assertion
   must still be replayed by the trusted Lean kernel. -/
open CentroidEscape
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000

namespace NativeCertificateData

def ballJson (b : FixedBall) : String := s!"[\"{b.center}\",\"{b.radius}\"]"
def vectorJson (v : Vector FixedBall 7) : String :=
  "[" ++ String.intercalate "," (v.toList.map ballJson) ++ "]"
def stateJson (j : Nat) (st : FixedTaylorState) (ep : Vector FixedBall 7) : String :=
  "{\"step\":" ++ toString j ++ ",\"coefficients\":[" ++
    String.intercalate "," (st.coeffs.toList.map vectorJson) ++ "],\"squares\":[" ++
    String.intercalate "," (st.squares.toList.map ballJson) ++
    "],\"endpoint\":" ++ vectorJson ep ++ "}\n"

def runCase (name : String) (outRoot : System.FilePath) (first count : Nat) : IO Unit := do
  if !(#["center","a_plus","a_minus","b_plus","b_minus"].contains name) then
    throw <| IO.userError "Unknown preview case"
  let δ : ℚ := 1/10^25
  let a := actualBenchA + (if name="a_plus" then δ else if name="a_minus" then -δ else 0)
  let b := actualBenchB + (if name="b_plus" then δ else if name="b_minus" then -δ else 0)
  let L := actualBenchL
  let h := L/750
  let S : ℕ := 10^80
  let outDir := outRoot / name
  IO.FS.createDirAll outDir
  let started ← IO.monoMsNow
  IO.FS.writeFile (outDir / "status.json")
    "{\"status\":\"native_generation_running\",\"kernel_verified\":false}\n"
  let initial : Fin 7 → ℚ := ![a,0,0,1/4,b/16,0,0]
  let mut seed : Vector FixedBall 7 := Vector.ofFn (fun i=>FixedBall.ofRat S (initial i))
  let initialJson := vectorJson seed
  let mut largestRadius : ℤ := 0
  let mut dataBytes : Nat := 0
  let mut minMargin : ℚ := 100
  for j in [:first+count] do
    let marginOk := checkBallCanonicalMargin (fun i=>(seed[i.val]).toRational S)
    if !marginOk then
      IO.FS.writeFile (outDir / "status.json")
        ("{\"status\":\"native_margin_failed\",\"kernel_verified\":false,\"step\":" ++ toString j ++ "}\n")
      throw <| IO.userError s!"Native margin failed at step {j}"
    for i in [:6] do
      let q := (seed.toList[i]?.getD FixedBall.zero).toRational S
      let r := (rationalTubeRadius ⟨i%7,Nat.mod_lt _ (by decide)⟩)-(|q.center|+q.radius)
      minMargin := min minMargin r
    let st := computeFixedTaylor S (fun i=>seed[i.val]) 60
    let ep := evaluateFixedTaylorOrder S 60 h st
    let src := stateJson j st ep
    if first ≤ j then
      dataBytes := dataBytes+src.toUTF8.size
      IO.FS.writeFile (outDir / s!"step{j}.json") src
    for c in ep.toList do
      if c.radius<0 then throw <| IO.userError s!"Negative radius at {j}"
      largestRadius := max largestRadius c.radius
    seed := ep
    if (j+1)%50=0 then
      IO.println s!"Native-only {name}: {j+1}/750, elapsed {(← IO.monoMsNow)-started}ms, largest radius numerator {largestRadius}."
  let epMargin := checkBallCanonicalMargin (fun i=>(seed[i.val]).toRational S)
  let elapsed := (← IO.monoMsNow)-started
  let complete := first=0 && count=750
  let status := if complete then "native_preview_complete" else "native_partial_complete"
  let summary := "{\"status\":\"" ++ status ++ "\",\"kernel_verified\":false," ++
    "\"case\":\"" ++ name ++ "\",\"steps\":" ++ toString count ++ ",\"start\":" ++ toString first ++
    ",\"mesh_steps\":750,\"order\":60,\"mesh\":\"" ++ toString S ++
    "\",\"a\":\"" ++ toString a ++ "\",\"b\":\"" ++ toString b ++ "\",\"L\":\"" ++ toString L ++
    "\",\"h\":\"" ++ toString h ++ "\",\"initial\":" ++ initialJson ++
    ",\"endpoint\":" ++ vectorJson seed ++ ",\"final_margin_check\":" ++ toString epMargin ++
    ",\"minimum_input_margin\":\"" ++ toString minMargin ++
    "\",\"largest_radius_numerator\":\"" ++ toString largestRadius ++
    "\",\"data_bytes\":" ++ toString dataBytes ++ ",\"elapsed_ms\":" ++ toString elapsed ++ "}\n"
  IO.FS.writeFile (outDir / "status.json") summary
  IO.println s!"Native-only {name} finished: {elapsed}ms; {dataBytes} bytes. KERNEL VERIFICATION STILL REQUIRED."

end NativeCertificateData

def main (args : List String) : IO UInt32 := do
  let [name, outPath, firstText, countText] := args
    | throw <| IO.userError "usage: lean --run NativeCertificateData.lean CASE OUTPUT_DIR START COUNT"
  let some first := firstText.toNat?
    | throw <| IO.userError "START must be a natural number"
  let some count := countText.toNat?
    | throw <| IO.userError "COUNT must be a natural number"
  if count=0 || first+count>750 then
    throw <| IO.userError "Require COUNT>0 and START+COUNT<=750"
  let names := if name="all" then #["center","a_plus","a_minus","b_plus","b_minus"] else #[name]
  for caseName in names do
    NativeCertificateData.runCase caseName (System.FilePath.mk outPath) first count
  return 0
