"""Narrow fresh-audit binding patch checks; no new Lean invocation."""
from pathlib import Path
import ast,hashlib,json,sys
import production_full_assembly_plan as v

def main():
    root=Path(__file__).resolve().parent.parent
    old=root/'assembly_plan_fixture_v2/validator_source.py'
    assert v.sha(old)=='c8cb7c4402c8b01e11c3c4b9083694b27126367cd9a480d91df7c0245765d4f8'
    oldtree=ast.parse(old.read_bytes());newtree=ast.parse(Path(v.__file__).read_bytes())
    oldfunc={n.name:n for n in oldtree.body if isinstance(n,ast.FunctionDef)}
    newfunc={n.name:n for n in newtree.body if isinstance(n,ast.FunctionDef)}
    assert set(newfunc)==set(oldfunc)|{'validate_fresh_audit'}
    for name in oldfunc:
        updated=newfunc[name]
        if name=='validate':
            statements=[n for n in updated.body if not (isinstance(n,ast.Expr) and isinstance(n.value,ast.Call)
                and isinstance(n.value.func,ast.Name) and n.value.func.id=='validate_fresh_audit')]
            assert len(statements)==len(updated.body)-1
            updated=ast.FunctionDef(name=updated.name,args=updated.args,body=statements,
                decorator_list=updated.decorator_list,returns=updated.returns,type_comment=updated.type_comment,
                type_params=getattr(updated,'type_params',[]))
        assert ast.dump(updated,include_attributes=False)==ast.dump(oldfunc[name],include_attributes=False),name
    oldconstants={ast.dump(n,include_attributes=False) for n in oldtree.body if isinstance(n,ast.Assign)}
    newconstants={ast.dump(n,include_attributes=False) for n in newtree.body if isinstance(n,ast.Assign)}
    assert oldconstants <= newconstants and len(newconstants-oldconstants)==1
    v.load_helpers()
    runner=Path(__file__).parent/'production_compile_final_supplement.py'
    tree=ast.parse(runner.read_bytes())
    function=next(n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name=='compile_supplement')
    assignment=next(n for n in function.body if isinstance(n,ast.Assign) and
        any(isinstance(t,ast.Name) and t.id=='audit' for t in n.targets))
    text=next(x.value for x in assignment.value.keywords if x.arg=='text')
    assert isinstance(text,ast.JoinedStr)
    assert all(isinstance(x,ast.Constant) and isinstance(x.value,str) or
        isinstance(x,ast.FormattedValue) and isinstance(x.value,ast.Name) and x.value.id=='main'
        and x.format_spec is None and x.conversion==-1 for x in text.values)
    rendered=eval(compile(ast.Expression(text),str(runner),'eval'),
        {'__builtins__':{},'main':'SolitonClassification.Rotating.FullPathFinalGeometry'})
    assert hashlib.sha256(rendered.encode()).hexdigest()==v.FINAL_AUDIT_SOURCE_SHA
    portable=root/'pipeline/final_supplement_portable_check'
    source=portable/'source/SolitonClassification/Rotating/FinalSupplementFreshAudit.lean'
    log=portable/'logs/SolitonClassification_Rotating_FinalSupplementFreshAudit.log'
    assert source.read_bytes()==rendered.encode()
    v.validate_fresh_audit(source,log.read_text(encoding='utf-8'))
    out=root/'assembly_plan_audit_patch_check'
    assert not out.exists();out.mkdir()
    rejected=[]
    def bad(name,fn):
        try:fn()
        except ValueError as e:rejected.append({'name':name,'rejected':True,'reason':str(e)})
        else:raise AssertionError('Unexpected acceptance')
    bad('absent_actual_audit_marker',lambda:v.validate_fresh_audit(source,'Completed report claims 2205.'))
    bad('wrong_actual_audit_count',lambda:v.validate_fresh_audit(source,'FINAL_SUPPLEMENT_CONDITIONAL_AUDIT 2204'))
    changed=out/'changed_audit.lean';changed.write_bytes(source.read_bytes()+b'\n-- changed source\n')
    bad('changed_fixed_audit_source',lambda:v.validate_fresh_audit(changed,log.read_text(encoding='utf-8')))
    report={'schema':'rotating.assembly-fresh-audit-patch-check.v1','status':'passed',
        'validator_sha256':v.sha(v.__file__),'patch_test_sha256':v.sha(__file__),
        'previous_actual_tiny_validator_sha256':v.sha(old),
        'previous_actual_tiny_report_sha256':v.sha(root/'assembly_plan_fixture_v2/report.json'),
        'all_previous_helper_functions_AST_unchanged':True,
        'validate_only_added_one_fresh_audit_guard':True,
        'fixed_audit_source_sha256':v.FINAL_AUDIT_SOURCE_SHA,'pinned_runner_sha256':v.sha(runner),
        'fixed_source_matches_actual_Windows_source_and_pinned_runner_literal':True,
        'scope':'Pure patch guards plus existing portable artifact read; not actual Linux48 verification',
        'negative_cases':rejected,'new_Lean_calls':0,'actual_full250_validation':False,'full_certificate_proved':False}
    v.save(out/'report.json',report);print(json.dumps(report),flush=True)

if __name__=='__main__':main()

