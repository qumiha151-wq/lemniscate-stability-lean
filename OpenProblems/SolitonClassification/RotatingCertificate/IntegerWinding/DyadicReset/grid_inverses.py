"""Assemble both finite certified inverse grids without reevaluating their integers."""
from pathlib import Path

HERE = Path(__file__).resolve().parent
OUT = HERE / 'fullassembly'
OUT.mkdir(exist_ok=True)
for sign in ('Plus', 'Minus'):
    ns = 'SolitonClassification.Rotating.DyadicReset.AllInverses' + sign
    grid = 'Grid' + sign
    lines = [
        'import SolitonClassification.Rotating.ResetGrid' + sign,
        'namespace ' + ns, 'set_option Elab.async false',
        'set_option maxRecDepth 50000', 'set_option maxHeartbeats 7000000',
        'structure Entry where', '  node : Node', '  inv : Node',
        '  verified : CheckedNode node inv',
    ]
    for b in range(63):
        entries = []
        for j in range(min(64, 4001-64*b)):
            name = f'Node{sign}{b:02d}'
            entries.append(f'  ⟨{name}.n{j},{name}.w{j},{name}.bounds{j}⟩')
        lines += [f'def block{b} : Array Entry := #[', ',\n'.join(entries) + ']']
    lines += ['def block : ℕ → Array Entry']
    lines += [f'  | {b} => block{b}' for b in range(63)]
    lines += ['  | _ => #[]',
        'theorem projection (b : ℕ) (hb : b<63) :',
        f'    (block b).map Entry.node = {grid}.chunk b := by interval_cases b <;> decide +kernel',
        'theorem length (b : ℕ) (hb : b<63) :',
        '    (block b).size = if b<62 then 64 else 33 := by interval_cases b <;> rfl',
        f'theorem every_node (i : ℕ) (hi : i≤4000) : ∃ w, CheckedNode ({grid}.atNode i) w := by',
        '  have hb : i/64<63 := by omega',
        '  have len : i%64<(block (i/64)).size := by',
        '    rw [length _ hb]; split <;> omega',
        '  let e := (block (i/64))[i%64]',
        '  refine ⟨e.inv,?_⟩',
        f'  have eq : {grid}.atNode i = e.node := by',
        f'    rw [{grid}.atNode,←projection _ hb,Array.getElem?_map,Array.getElem?_eq_getElem len]',
        '    rfl',
        '  exact eq.symm ▸ e.verified', 'end ' + ns,
        '#print axioms ' + ns + '.every_node']
    (OUT / ('ResetAllInverses'+sign+'.lean')).write_text('\n'.join(lines)+'\n',encoding='utf8')
