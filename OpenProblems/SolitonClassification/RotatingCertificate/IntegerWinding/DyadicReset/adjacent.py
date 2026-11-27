"""Generate adjacent-cell proofs with the reusable full-polynomial residual test."""
from reset_tape import *
COUNT=4
START=1999
def go():
    with gzip.open(HERE/'plus4000.jsonl.gz','rt',encoding='utf8') as fp:
        next(fp)
        tape=[json.loads(l) for l in fp]
    d=seed(1)[1]
    z=lambda a:'['+','.join(map(str,a))+']'
    for j in range(START,START+COUNT):
        polys=path(tape[j][2],d)
        assert [sum(p) for p in polys]==tape[j+1][2]
        lines=['import SolitonClassification.Rotating.ResetCellChecker',
               'import Mathlib.Data.Fintype.Fin',
               'import Mathlib.Tactic.FinCases',
               'namespace SolitonClassification.Rotating.DyadicReset.Cell'+str(j),
               'open Middle CellCheck','set_option maxHeartbeats 2000000','set_option maxRecDepth 100000']
        if j==2000:
            lines.append('def inputs := Middle.rows')
        else:
            for i,p in enumerate(polys):lines.append(f'def a{i} : List ℤ := '+z(p))
            lines.append('def inputs : Array (List ℤ) := #['+','.join('a'+str(i) for i in range(31))+']')
        lines.extend(['def table (i : Nat) := (inputs[i]?).getD []',
                      'def test (i : Nat) := sufficient (defectTerm table den hn hd i)'])
        for i in range(31):
            lines.append(f'theorem row{i} : test {i}=true := by decide +kernel')
        lines.append('theorem checked : ∀i : Fin 31, test i=true := by\n  intro i\n  fin_cases i')
        lines.extend(f'  · exact row{i}' for i in range(31))
        lines+=['def startNode : Array ℤ := #'+z(tape[j][2]),
                'def endNode : Array ℤ := #'+z(tape[j+1][2]),
                'theorem matching : inputs.map (fun p => p.head?.getD 0)=startNode ∧ inputs.map List.sum=endNode := by decide +kernel',
                'end SolitonClassification.Rotating.DyadicReset.Cell'+str(j),
                f'#print axioms SolitonClassification.Rotating.DyadicReset.Cell{j}.checked']
        (HERE/f'ResetCell{j}.lean').write_bytes(('\n'.join(lines)+'\n').encode())
if __name__=='__main__':go()
