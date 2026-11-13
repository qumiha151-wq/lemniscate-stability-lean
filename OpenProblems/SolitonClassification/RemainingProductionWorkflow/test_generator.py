"""Synthetic gate/structure tests only; zero GitHub/Lean/numeric execution."""
from pathlib import Path
import argparse, ast, copy, json
import generate_workflow as g


def main():
    parser = argparse.ArgumentParser()
    for name in ('basis-generator', 'basis-report', 'plan', 'output'):
        parser.add_argument('--' + name, type=Path, required=True)
    a = parser.parse_args()
    basis = g.load_basis(a.basis_generator)
    assert g.digest(a.basis_report) == g.BASIS_REPORT and g.digest(a.plan) == basis.PLAN
    pins = g.read_json(a.basis_report)['pins']; plan = g.read_json(a.plan)
    required = ['Fresh private audit and Arctan import from the restored core',
                'Check actual completion and retain the conditional scope',
                'Recheck all pinned source bytes and absence of fallback cache',
                'Actually compile all 47 modules and pack the complete checked shard',
                'Actually import the validated complete bundle using public project inputs only',
                'Actually compile final48 and fresh conditional2205 audit on Linux']
    run = {'id': g.FIRST_RUN, 'head_sha': g.FIRST_REVISION, 'repository': {'full_name': g.REPO},
           'status': 'completed', 'conclusion': 'success', 'run_attempt': 1}
    jobs = {'total_count': 5, 'jobs': [{'name': name, 'id': i + 1, 'run_id': g.FIRST_RUN,
            'head_sha': g.FIRST_REVISION, 'status': 'completed', 'conclusion': 'success',
            'steps': [{'name': label, 'status': 'completed', 'conclusion': 'success'} for label in required]}
            for i, name in enumerate(sorted(g.EXPECTED_NAMES))]}
    passed = []
    def reject(label, call):
        try:
            call()
        except (ValueError, KeyError) as error:
            passed.append({'name': label, 'rejected': True, 'reason': str(error)})
        else:
            raise AssertionError('Unexpected acceptance: ' + label)
    for label, field, value in [('wrong_run', 'id', 1), ('wrong_revision', 'head_sha', '0' * 40),
                                 ('unfinished_run', 'status', 'in_progress'), ('failed_run', 'conclusion', 'failure'),
                                 ('missing_attempt', 'run_attempt', 0)]:
        bad = copy.deepcopy(run); bad[field] = value
        reject(label, lambda bad=bad: g.validate_first(bad, jobs))
    bad = copy.deepcopy(run); bad['repository']['full_name'] = 'other/repo'
    reject('foreign_repository', lambda: g.validate_first(bad, jobs))
    for label, mutate in [('missing_job', lambda j: j['jobs'].pop()),
                           ('duplicate_job', lambda j: j['jobs'].__setitem__(0, copy.deepcopy(j['jobs'][1]))),
                           ('wrong_job_revision', lambda j: j['jobs'][0].update(head_sha='0' * 40)),
                           ('failed_job', lambda j: j['jobs'][0].update(conclusion='failure')),
                           ('skipped_compile', lambda j: j['jobs'][0]['steps'][3].update(conclusion='skipped')),
                           ('no_audit', lambda j: j['jobs'][0]['steps'].pop(0))]:
        badjobs = copy.deepcopy(jobs); mutate(badjobs)
        reject(label, lambda badjobs=badjobs: g.validate_first(run, badjobs))
    first = g.validate_first(run, jobs)
    for label, mutate in [('missing_source_job', lambda p: p['jobs'].pop()),
                           ('duplicate_source_job', lambda p: p['jobs'].__setitem__(0, copy.deepcopy(p['jobs'][1]))),
                           ('reordered_source_jobs', lambda p: p['jobs'].reverse()),
                           ('wrong_plan_revision', lambda p: p.update(revision='0' * 40))]:
        badplan = copy.deepcopy(plan); mutate(badplan)
        reject(label, lambda badplan=badplan: g.render(basis, pins, first, badplan, 'rotating-remaining-production.yml'))
    reject('duplicate_json', lambda: json.loads('{"a":1,"a":2}', object_pairs_hook=g.unique_pairs))
    reject('unsafe_workflow_path', lambda: g.render(basis, pins, first, plan, '../unsafe.yml'))
    doc = g.render(basis, pins, first, plan, 'rotating-remaining-production.yml')
    job = doc['jobs']['checked']; matrix = job['strategy']['matrix']['include']
    assert len(matrix) == len({row['key'] for row in matrix}) == 246
    assert {row['key'] for row in matrix} | set(g.FIRST_KEYS) == {row['key'] for row in plan['jobs']}
    assert not {row['key'] for row in matrix} & set(g.FIRST_KEYS)
    assert all(row['kind'] == 'shard' and row['timeout'] == 120 for row in matrix)
    assert job['strategy']['max-parallel'] == 12 and job['strategy']['fail-fast'] is False
    assert doc['permissions'] == {'contents': 'read', 'actions': 'read'}
    assert job['runs-on'] == 'ubuntu-24.04'
    original = basis.workflow(pins, 'rotating-first-production.yml')
    original_steps = {step.get('name'): step for step in original['jobs']['checked']['steps']}
    for step in job['steps']:
        name = step.get('name')
        if name is not None and name in original_steps and name != 'Set the isolated output path using the runner shell environment':
            assert step == original_steps[name], 'Existing execution step changed: ' + str(name)
    assert [step for step in job['steps'] if 'name' not in step] == [
        step for step in original['jobs']['checked']['steps'] if 'name' not in step]
    uploads = [step for step in job['steps'] if step.get('uses') == 'actions/upload-artifact@v4']
    assert len(uploads) == 2
    assert uploads[0]['if'] == 'always()' and '/job/*.tar.xz' in uploads[0]['with']['path']
    assert '/job/generated' not in uploads[0]['with']['path']
    assert uploads[1]['if'] == 'failure()' and uploads[1]['with']['path'].endswith('/job/generated')
    embedded = 0
    for step in job['steps']:
        script = step.get('run', '')
        if "<<'PY'\n" in script:
            source = script.split("<<'PY'\n", 1)[1].split('\nPY\n', 1)[0]
            ast.parse(source); embedded += 1
    ast.parse(Path(g.__file__).read_text(encoding='utf-8'))
    ast.parse(Path(__file__).read_text(encoding='utf-8'))
    assert not a.output.exists()
    a.output.mkdir(parents=True)
    report = {'schema': 'rotating.remaining-workflow-synthetic-tests.v1', 'status': 'passed',
              'test_fixture': True, 'generator_sha256': g.digest(g.__file__), 'test_sha256': g.digest(__file__),
              'negative_count': len(passed), 'negative_cases': passed, 'embedded_Python_AST_count': embedded,
              'matrix_entries': len(matrix), 'unchanged_proof_execution_steps': True,
              'actual_first_five_success_observed_by_this_test': False,
              'workflow_installed': False, 'workflow_executed': False, 'Lean_calls': 0,
              'numeric_generation_calls': 0, 'real_GitHub_requests': 0, 'full_certificate_proved': False}
    (a.output / 'review.json').write_text(json.dumps(report, indent=2) + '\n', encoding='utf-8', newline='\n')
    print(json.dumps(report))


if __name__ == '__main__':
    main()
