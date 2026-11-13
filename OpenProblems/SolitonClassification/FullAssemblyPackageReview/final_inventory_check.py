"""Terminal exact-file-set/hash check; no imports from either package."""
from pathlib import Path
import hashlib
import json

HERE = Path(__file__).resolve()
FORMAL = HERE.parents[1]
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
prepared = json.loads((HERE.parent / 'preparation.json').read_bytes())
result = {'status': 'checked', 'new_Lean_calls': 0, 'full_certificate_proved': False, 'packages': [],
          'checker_sha256': sha(HERE)}
specs = [
    ('full_assembly_tools_package_v1', 'FullAssemblyToolsInventory.json', prepared['inventory_sha256']),
    ('first_four_partial_metadata_package_v1', 'PartialEvidenceInventory.json', prepared['partial_inventory_sha256'])]
for folder, index, pin in specs:
    root = FORMAL / folder
    assert sha(root / index) == pin
    inventory = json.loads((root / index).read_bytes())
    actual = {p.relative_to(root).as_posix() for p in root.rglob('*') if p.is_file()}
    assert actual == set(inventory['files']) | {index}
    for name, row in inventory['files'].items():
        assert sha(root / name) == row['sha256'] and (root / name).stat().st_size == row['bytes']
    result['packages'].append({'directory': folder, 'inventory_sha256': pin,
                               'actual_files_including_inventory': len(actual),
                               'actual_bytes': sum((root / name).stat().st_size for name in actual)})
assert all(sha(path) == digest for path, digest in prepared['original_input_pins'].items())
result['original_selected_inputs_rehashed'] = len(prepared['original_input_pins'])
out = HERE.with_suffix('.json')
assert not out.exists()
out.write_text(json.dumps(result, indent=2) + '\n', encoding='utf-8')
print(json.dumps(result))
print(sha(out))
