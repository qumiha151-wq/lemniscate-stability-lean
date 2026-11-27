"""Create the two total PolynomialTape witnesses from the independently checked numeric blocks."""
from pathlib import Path
from reset_tape import HERE
OUT=HERE/'fullassembly'
OUT.mkdir(exist_ok=True)
HEAD='SolitonClassification.Rotating.'
NS=HEAD+'DyadicReset.'
def write(name,lines):
    (OUT/(name+'.lean')).write_text('\n'.join(lines)+'\n',encoding='utf8')
def pre(imports,ns):
    return ['import '+HEAD+i for i in imports]+['namespace '+NS+ns,'noncomputable section',
      'set_option Elab.async false','set_option maxRecDepth 200000','set_option maxHeartbeats 10000000']
def footer(ns):return ['end','end '+NS+ns]

for sign in ('Plus','Minus'):
    n='Middle.hn' if sign=='Plus' else '(-Middle.hn)'
    namespace='Grid'+sign
    header=pre(['ResetNode'+sign+str(b).zfill(2) for b in range(63)],namespace)
    body=['def chunk : ℕ→Array Node']+[f'  | {b}=>Node{sign}{b:02d}.nodes' for b in range(63)]
    body+=['  | _=>#[]','def atNode (i : ℕ) : Node := ((chunk (i/64))[i%64]?).getD #[]']
    write('ResetGrid'+sign,header+body+footer(namespace))
    for b in range(63):
        begin=64*b
        size=min(64,4000-begin)
        pref=f'Tile{sign}{b:02d}'
        chunk=[f'ResetPacked{sign}{k:04d}' for k in range(begin,begin+size,16)]
        lines=pre(['ResetRows','ResetGrid'+sign]+chunk,pref)
        for j in range(size):
            i=begin+j
            col=f'Compact{sign}{i//16*16:04d}'
            node=f'Node{sign}{i//64:02d}'
            end=f'Grid{sign}.atNode {i+1}'
            lines.extend([f'def r{j} : TapeRow {n} :=',
              f'  ⟨{col}.p{i},Grid{sign}.atNode {i},{end},{node}.w{j},{col}.checked{i},{col}.small{i},{col}.nodes{i},{node}.bounds{j}⟩'])
        lines+=['def entries : Array (TapeRow '+n+') := #['+','.join(f'r{j}' for j in range(size))+']',
          'def atRow (j : ℕ) := (entries[j]?).getD r0',
          f'theorem at_index (j : ℕ) (hj : j<{size}) : (atRow j).left=Grid{sign}.atNode ({begin}+j) ∧',
          f'    (atRow j).right=Grid{sign}.atNode ({begin}+j+1) := by interval_cases j <;> exact ⟨rfl,rfl⟩']
        write('Reset'+pref,lines+footer(pref))
    ns='Complete'+sign
    lines=pre([f'ResetTile{sign}{b:02d}' for b in range(63)],ns)
    lines+=['def cellBlock : ℕ→ℕ→TapeRow '+n]+[f'  | {b}=>Tile{sign}{b:02d}.atRow' for b in range(63)]
    lines+=['  | _=>Tile'+sign+'00.atRow',
      f'theorem indexes (b j : ℕ) (hb : b<63) (hj : j<64) (total : 64*b+j<4000) :',
      f'    (cellBlock b j).left=Grid{sign}.atNode (64*b+j) ∧ (cellBlock b j).right=Grid{sign}.atNode (64*b+j+1) := by',
      '  interval_cases b']
    for b in range(63):
        lines.append(f'  · exact Tile{sign}{b:02d}.at_index j '+('hj' if b<62 else '(by omega)'))
    lines+=['def atRow (i : ℕ) := cellBlock (i/64) (i%64)',
      f'theorem range (i : ℕ) (hi : i<4000) : (atRow i).left=Grid{sign}.atNode i ∧ (atRow i).right=Grid{sign}.atNode (i+1) := by',
      '  have sub : i%64<64 := Nat.mod_lt _ (by decide)',
      '  have eq : 64*(i/64)+i%64=i := Nat.div_add_mod i 64',
      '  have b:=indexes (i/64) (i%64) (by omega) sub (by omega)',
      '  simpa only [atRow,eq] using b',
      'theorem links (i : ℕ) (hi : i+1<4000) : (atRow i).right=(atRow (i+1)).left :=',
      '  (range i (by omega)).2.trans (range (i+1) hi).1.symm',
      'def tape : PolynomialTape '+n+' 4000 := assemble atRow links']
    write('Reset'+ns,lines+footer(ns))
