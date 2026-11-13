"""Bounded real 42/22 shard generator, with independent <=8-step headers.

The numerical proposals are untrusted. Every emitted finite check uses
`decide +kernel`; the mathematical result is a real PolynomialPointGridBlock.
This generator intentionally caps execution at 32 steps until resource tests
authorize the full 4000+4000 pipeline. Frozen pilot sources are only templates.
"""
from pathlib import Path
import argparse, hashlib, json, re, sys, time
import propose_grid42x22 as g
ROOT=Path(__file__).resolve().parent.parent
OLD=ROOT/'SolitonClassification/Rotating'
sys.path.insert(0,str(ROOT/'performance'))
from reference import vec,ball
import reference
PREFIX='SolitonClassification.Rotating.'
v=lambda xs:'!['+','.join(map(str,xs))+']'
m=lambda xs:'!['+','.join(v(col) for col in xs)+']'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()

def audit(marker):
 return f'''open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name,_) in (← getEnv).constants do
    if (`SolitonClassification.Rotating).isPrefixOf (privateToUserName name) then
      for ax in (← collectAxioms name) do
        unless #[`propext,`Classical.choice,`Quot.sound].contains ax do
          throwError "Production shard audit failed: {{name}} depends on {{ax}}"
      count := count+1
  logInfo m!"{marker}: {{count}} declarations; standard axioms only."
'''

def main():
 p=argparse.ArgumentParser()
 p.add_argument('--key',required=True)
 p.add_argument('--count',type=int,required=True)
 p.add_argument('--sign',type=int,choices=[1,-1],required=True)
 p.add_argument('--output',type=Path,required=True)
 p.add_argument('--module',action='store_true')
 p.add_argument('--input-node',type=Path)
 p.add_argument('--seed',type=Path,default=ROOT.parent/'next_research/classification_odd_branch_interval/shooting_certificate.json')
 p.add_argument('--candidate-source',type=Path,default=OLD/'CandidateInitial.lean')
 p.add_argument('--template-root',type=Path,default=OLD)
 args=p.parse_args()
 if not re.fullmatch('[A-Za-z][A-Za-z0-9_]*',args.key):p.error('key must start with ASCII letter and contain only alphanumeric/underscore')
 if not 1<=args.count<=32:p.error('this checkpoint permits only 1..32 steps')
 out=args.output.resolve();out.mkdir(parents=True,exist_ok=True)
 if (out/'manifest.json').exists():p.error('refusing to overwrite an existing shard manifest')
 sources={'seed':args.seed.resolve(),'candidate_initial':args.candidate_source.resolve(),
  'state_template':(args.template_root/'Block16Leaf08State.lean').resolve(),
  'matrix_template':(args.template_root/'Block16Leaf08Matrix.lean').resolve(),
  'generator':Path(__file__).resolve(),'proposal_arithmetic':Path(g.__file__).resolve(),
  'interval_arithmetic':Path(reference.__file__).resolve()}
 source_bytes={k:path.read_bytes() for k,path in sources.items()}
 fingerprints={k:{'sha256':hashlib.sha256(data).hexdigest(),'bytes':len(data)} for k,data in source_bytes.items()}
 candidate_hash=fingerprints['candidate_initial']['sha256']
 # Match the previous Path.read_text universal-newline behavior exactly.
 template_text=lambda data:data.decode('utf-8-sig').replace('\r\n','\n').replace('\r','\n')
 templates={'Block16Leaf08State':template_text(source_bytes['state_template']),
            'Block16Leaf08Matrix':template_text(source_bytes['matrix_template'])}
 capdata=json.loads(source_bytes['seed'].decode('utf-8-sig'));x=list(map(g.Q,capdata['center_exact_decimal']));e=list(map(g.Q,capdata['phase_exact_decimal']))
 if len(x)!=5 or len(e)!=2:p.error('seed must contain five parameters and two phase coordinates')
 h=x[2]/4000;start=0
 if h<=0:p.error('nominal step must be positive')
 input_bytes=args.input_node.read_bytes() if args.input_node else None
 if args.input_node:
  old=json.loads(input_bytes.decode('utf-8-sig'))
  if old['sign']!=args.sign or old['mesh']!=str(g.S) or old['candidate_hash']!=candidate_hash:
   p.error('input checkpoint candidate/sign/mesh mismatch')
  if old.get('orders')!={'state':42,'matrix':22} or old.get('step')!={'num':str(h.numerator),'den':str(h.denominator)}:
   p.error('input checkpoint orders/step mismatch')
  start=old['index'];a=[g.Q(n,d) for n,d in old['state_exact_rational']];B=old['matrix_integer_columns']
  if not isinstance(start,int) or isinstance(start,bool) or start<0:p.error('input index must be a nonnegative integer')
  if len(a)!=6 or any((z*g.S).denominator!=1 for z in a):p.error('input state must have six exact mesh-grid coordinates')
  if len(B)!=6 or any(len(col)!=6 or any(not isinstance(z,int) or isinstance(z,bool) for z in col) for col in B):p.error('input matrix must be six integer columns of length six')
 else:
  a=[x[0],x[3]*e[0]/8,x[1],x[3]*e[1],x[4],g.Q(0)]
  B=[[g.S*int(i==j) for i in range(6)] for j in range(6)]
 if start+args.count>4000:p.error('path range exceeds 4000')
 started=time.perf_counter();nodes=[g.point_node(start,a,B)];leaves=[]
 for local in range(args.count):
  j=start+local
  initial=list(map(g.ofq,a)) if j==0 else [(int(z*g.S),0) for z in a]
  c,q=g.state_coefficients(initial,42)
  W=[g.full_variation(c,q,[(z,0) for z in col]) for col in B]
  X=g.endpoint(c,g.ofq(args.sign*h));M=[g.endpoint(w,g.ofq(args.sign*h)) for w in W]
  leaves.append({'index':j,'state_coefficients':c,'curvature_square_coefficients':q,
                 'variation_columns_coefficients':W,'state_endpoint':X,'matrix_endpoint_columns':M})
  a=[g.Q(z[0],g.S) for z in X];B=[[z[0] for z in col] for col in M]
  nodes.append(g.point_node(j+1,a,B))
 proposal=out/'untrusted_proposal.json'
 proposal.write_text(json.dumps({'nodes':nodes,'leaves':leaves,'generation_wall_seconds':time.perf_counter()-started},indent=2)+'\n')
 endpoint={'index':start+args.count,'sign':args.sign,'mesh':str(g.S),'candidate_hash':candidate_hash,
           'orders':{'state':42,'matrix':22},'step':{'num':str(h.numerator),'den':str(h.denominator)},
           'state_exact_rational':[[z.numerator,z.denominator] for z in a],'matrix_integer_columns':B}
 (out/'output_node.json').write_text(json.dumps(endpoint,indent=2)+'\n')
 modules=[];coverage=[]
 marker=f'Production_{args.key}_audit'
 def write(name,imports,text,public_generic=False,private_computation=False):
  head=('module\n' if args.module else '')+'\n'.join(('public ' if args.module else '')+'import '+PREFIX+n for n in imports)+'\n\n'
  core_imports=['Init.Data.Vector.Basic','Init.Data.Array.DecidableEq'] if args.module and private_computation else []
  if core_imports:head+='\n'.join('import all '+n for n in core_imports)+'\n\n'
  if args.module and public_generic:head+='@[expose] public section\n\n'
  content=head+text+('\nend\n' if args.module and public_generic else '')+'\n'+audit(marker)
  relative=Path(*(PREFIX+name).split('.')).with_suffix('.lean');dest=out/relative
  dest.parent.mkdir(parents=True,exist_ok=True);dest.write_text(content,encoding='utf-8')
  modules.append({'name':PREFIX+name,'source':relative.as_posix(),'sha256':sha(dest),'imports':[PREFIX+n for n in imports]+core_imports})
 def namespace(name):
  return f'''namespace {PREFIX}{name}
open Candidate
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
'''
 blocks=[]
 for base in range(0,args.count,8):
  count=min(8,args.count-base);header=f'{args.key}B{base//8:02d}Nodes'
  text=namespace(header)
  for j in range(count+1):
   index=base+j
   centers=[z[0] for z in (leaves[index]['state_coefficients'][0] if index<args.count else leaves[-1]['state_endpoint'])]
   text+=f'def centers{j} : Fin 6 → ℤ := {v(centers)}\n'
   text+=f'def B{j} : PointMatrix := {m(nodes[index]["matrix_integer_columns"])}\n'
   text+=f'def C{j} : PointMatrix := {m(nodes[index]["inverse_proposal_integer_columns"])}\n'
  for field,typ,prefix in [('centers','Fin 6 → ℤ','centers'),('matrix','PointMatrix','B'),('inverseProposal','PointMatrix','C')]:
   text+=f'def {field} : ℕ → {typ}\n'+''.join(f'  | {j} => {prefix}{j}\n' for j in range(count+1))+f'  | _ => {prefix}{count}\n'
  initial=(start+base==0)
  text+=f'def signedStep : ℚ := ({args.sign}:ℚ)*step\n'
  text+='def rawState (j : ℕ) (i : Fin 6) : ℚ := '+('if j=0 then rawInitial i else ' if initial else '')+'(centers j i:ℚ)/mesh\n'
  text+='def state (j : ℕ) : State := fun i => (rawState j i:ℝ)\n'
  text+='def operator (j : ℕ) : FlowEnd := pointMatrixOperator mesh (matrix j)\n'
  text+='def startBalls (j : ℕ) (i : Fin 6) : FixedBall := '+('if j=0 then initialBalls i else ' if initial else '')+'⟨centers j i,0⟩\n'
  text+='''theorem start_contains (j : ℕ) (i : Fin 6) : (startBalls j i).Contains mesh (state j i) := by
'''
  if initial:
   text+='''  by_cases hj : j=0
  · subst j; exact initial_enclosed i
  · simp [startBalls,state,rawState,hj,FixedBall.Contains,FixedBall.toRational,RationalBall.Contains]
'''
  else:text+='  simp [startBalls,state,rawState,FixedBall.Contains,FixedBall.toRational,RationalBall.Contains]\n'
  text+='''theorem start_column_contains (j : ℕ) (c i : Fin 6) :
    (⟨matrix j c i,0⟩:FixedBall).Contains mesh (operator j (coordinateBasis c) i) := by
  change (⟨matrix j c i,0⟩:FixedBall).Contains mesh (pointMatrixOperator mesh (matrix j) (coordinateBasis c) i)
  rw [pointMatrixOperator_basis]
  simp [FixedBall.Contains,FixedBall.toRational,RationalBall.Contains]
'''
  for j in range(count+1):text+=f'theorem valid{j} : PointNodeValid (matrix {j}) (inverseProposal {j}) := by decide +kernel\n'
  text+=f'''theorem bounds (j : ℕ) (hj : j≤{count}) : ‖operator j‖≤2000 ∧ IsUnit (operator j) ∧ ‖Ring.inverse (operator j)‖≤4000 := by
  have hv : PointNodeValid (matrix j) (inverseProposal j) := by
    interval_cases j
'''+''.join(f'    · exact valid{j}\n' for j in range(count+1))+'''  exact hv.sound
'''
  text+=f'''theorem raw_inner (j : ℕ) (hj : j≤{count}) : |rawState j 0|≤407/50 ∧ |rawState j 1|≤33/8 ∧
    |rawState j 2|≤731/100 ∧ |rawState j 3|≤731/100 ∧ |rawState j 4|≤1/100 := by
  interval_cases j <;> decide +kernel
theorem inner (j : ℕ) (hj : j≤{count}) : state j∈innerTube := by
  have lift (q r : ℚ) (hq : |q|≤r) : |(q:ℝ)|≤(r:ℝ) := by
    rw [←Rat.cast_abs]; exact Rat.cast_le.mpr hq
  rcases raw_inner j hj with ⟨h0,h1,h2,h3,h4⟩
  change |(rawState j 0:ℝ)|≤407/50 ∧ |(rawState j 1:ℝ)|≤33/8 ∧
    |(rawState j 2:ℝ)|≤731/100 ∧ |(rawState j 3:ℝ)|≤731/100 ∧ |(rawState j 4:ℝ)|≤1/100
  exact ⟨by simpa only [Rat.cast_div,Rat.cast_ofNat] using lift _ _ h0,
    by simpa only [Rat.cast_div,Rat.cast_ofNat] using lift _ _ h1,
    by simpa only [Rat.cast_div,Rat.cast_ofNat] using lift _ _ h2,
    by simpa only [Rat.cast_div,Rat.cast_ofNat] using lift _ _ h3,
    by simpa only [Rat.cast_div,Rat.cast_ofNat,Rat.cast_one] using lift _ _ h4⟩
'''
  if initial:
   text+='theorem state_initial : state 0=initial := rfl\n'
   text+='''theorem operator_initial : operator 0=1 := by
  have hb (j : Fin 6) : operator 0 (coordinateBasis j)=coordinateBasis j := by
    ext i
    change pointMatrixOperator mesh (matrix 0) (coordinateBasis j) i=coordinateBasis j i
    rw [pointMatrixOperator_basis]
    fin_cases j <;> fin_cases i <;> norm_num [matrix,B0,mesh,coordinateBasis]
  apply ContinuousLinearMap.ext
  intro v
  change operator 0 v=v
  conv_lhs => rw [state_basis_expansion v]
  simp only [map_sum,map_smul,hb]
  exact (state_basis_expansion v).symm
'''
  text+=f'end {PREFIX}{header}\n'
  write(header,['PointMatrixGridBudget','FlowTube'],text,True)
  leaf_names=[]
  for j in range(count):
   d=leaves[base+j];name=f'{args.key}L{base+j:04d}';state_ns=name+'State';matrix_ns=name+'Matrix'
   def body(old_name,new_name):
    t=templates[old_name]
    t=t[t.index('namespace SolitonClassification.'):t.index('open Lean Elab Command in')]
    t=t.replace('Block16Leaf08State',state_ns).replace('Block16Leaf08Matrix',matrix_ns)
    for field in ['state','operator','startBalls','matrix','centers','start_contains','start_column_contains']:
     t=t.replace(f'Block16Nodes.{field} 8',f'{header}.{field} {j}')
     t=t.replace(f'Block16Nodes.{field} 9',f'{header}.{field} {j+1}')
    t=t.replace('Block16Nodes.operator',header+'.operator')
    t=re.sub(r'\bstep\b',header+'.signedStep',t)
    return t
   s=body('Block16Leaf08State',state_ns);mt=body('Block16Leaf08Matrix',matrix_ns)
   for n,row in enumerate(d['state_coefficients']):s=re.sub(rf'(?m)^def c{n} : Vector FixedBall 6 := .*$',f'def c{n} : Vector FixedBall 6 := {vec(row)}',s)
   for n,z in enumerate(d['curvature_square_coefficients']):s=re.sub(rf'(?m)^def q{n} : FixedBall := .*$',f'def q{n} : FixedBall := {ball(z)}',s)
   s=re.sub(r'(?m)^def endpointData : Vector FixedBall 6 := .*$',f'def endpointData : Vector FixedBall 6 := {vec(d["state_endpoint"])}',s)
   for col,w in enumerate(d['variation_columns_coefficients']):
    for n,row in enumerate(w):mt=re.sub(rf'(?m)^def w{col}_{n} : Vector FixedBall 6 := .*$',f'def w{col}_{n} : Vector FixedBall 6 := {vec(row)}',mt)
    mt=re.sub(rf'(?m)^def endpoint{col} : Vector FixedBall 6 := .*$',f'def endpoint{col} : Vector FixedBall 6 := {vec(d["matrix_endpoint_columns"][col])}',mt)
   # The exported statement uses the actual polynomial operator at signed time.
   mt=mt.replace(f'referencePolynomialMatrix 1 ({header}.state {j}) 22 ({header}.operator {j}) ({header}.signedStep:ℝ)',
                 f'(variationPolynomialMap ({header}.state {j}) 22 ({header}.signedStep:ℝ)).comp ({header}.operator {j})')
   mt=mt.replace('  simp only [referencePolynomialMatrix,one_mul]\n','')
   if args.module:
    s=s.replace('theorem state_reset :','public theorem state_reset :')
    mt=mt.replace('theorem matrix_reset :','public theorem matrix_reset :')
   write(name,[header,'TaylorDataCertificate','FixedEndpointReset','MixedOrderVariation','VariationLinearity'],s+'\n'+mt,private_computation=True)
   leaf_names.append(name);coverage.append({'global_step':d['index'],'state_module':PREFIX+name,'matrix_module':PREFIX+name,'header_module':PREFIX+header})
  block=f'{args.key}B{base//8:02d}Block';text=namespace(block)+'noncomputable section\n'
  text+=f'''def state (j : ℕ) : State := {header}.state j
def matrix (j : ℕ) : FlowEnd := {header}.operator j
theorem state_reset (j : ℕ) (hj : j<{count}) :
    ‖polynomialPath (taylorPolynomial (state j) 42) (({args.sign}:ℝ)*(step:ℝ))-state (j+1)‖≤1/10^55 := by
  interval_cases j
'''
  for j,name in enumerate(leaf_names):text+=f'  · simpa only [state,{header}.signedStep,Rat.cast_mul,Rat.cast_neg,Rat.cast_one,one_mul,neg_one_mul] using {name}State.state_reset\n'
  text+=f'''theorem matrix_reset (j : ℕ) (hj : j<{count}) :
    ‖referencePolynomialMatrix ({args.sign}:ℝ) (state j) 22 (matrix j) (step:ℝ)-matrix (j+1)‖≤1/10^55 := by
  interval_cases j
'''
  for j,name in enumerate(leaf_names):text+=f'  · simpa only [state,matrix,referencePolynomialMatrix,{header}.signedStep,Rat.cast_mul,Rat.cast_neg,Rat.cast_one,one_mul,neg_one_mul] using {name}Matrix.matrix_reset\n'
  text+=f'''def certificate : PolynomialPointGridBlock ({args.sign}:ℝ) (step:ℝ) (1/10^55) (1/10^55) {count} where
  state := state
  matrix := matrix
  inner j hj := {header}.inner j hj
  nodeUnit j hj := ({header}.bounds j hj).2.1
  nodeNorm j hj := ({header}.bounds j hj).1
  nodeInverse j hj := ({header}.bounds j hj).2.2
  stateResetNonneg := by norm_num
  matrixResetNonneg := by norm_num
  stateReset := state_reset
  matrixReset := matrix_reset
theorem state_start : certificate.state 0={header}.state 0 := rfl
theorem matrix_start : certificate.matrix 0={header}.operator 0 := rfl
theorem state_last : certificate.state {count}={header}.state {count} := rfl
theorem matrix_last : certificate.matrix {count}={header}.operator {count} := rfl
attribute [irreducible] certificate
end
end {PREFIX}{block}
'''
  write(block,leaf_names+['PolynomialPointGridBlock'],text,True)
  blocks.append({'name':block,'count':count,'first_header':header,'last_header':header,'last_index':count})
 # Balanced append; a separate node seam module performs literal equality checks.
 level=0
 while len(blocks)>1:
  new=[]
  for pair in range(0,len(blocks),2):
   if pair+1==len(blocks):new.append(blocks[pair]);continue
   left,right=blocks[pair:pair+2];ln,rn=left['name'],right['name'];lh,rh=left['last_header'],right['first_header'];li=left['last_index']
   seam=f'{args.key}Seam{level}_{pair//2}'
   text=namespace(seam)+f'''theorem centers_equal : {lh}.centers {li}={rh}.centers 0 := by
  funext i; fin_cases i <;> decide +kernel
theorem matrices_equal : {lh}.matrix {li}={rh}.matrix 0 := by
  funext c i; fin_cases c <;> fin_cases i <;> decide +kernel
theorem state_equal : {lh}.state {li}={rh}.state 0 := by
  funext i
  change ((({lh}.centers {li} i:ℚ)/mesh:ℚ):ℝ)=((({rh}.centers 0 i:ℚ)/mesh:ℚ):ℝ)
  rw [centers_equal]
theorem operator_equal : {lh}.operator {li}={rh}.operator 0 := by
  exact congrArg (pointMatrixOperator mesh) matrices_equal
end {PREFIX}{seam}
'''
   write(seam,[lh,rh],text,True)
   name=f'{args.key}Join{level}_{pair//2}';n=left['count']+right['count']
   text=namespace(name)+f'''noncomputable section
theorem state_seam : {ln}.certificate.state {left['count']}={rn}.certificate.state 0 := by
  rw [{ln}.state_last,{rn}.state_start]; exact {seam}.state_equal
theorem matrix_seam : {ln}.certificate.matrix {left['count']}={rn}.certificate.matrix 0 := by
  rw [{ln}.matrix_last,{rn}.matrix_start]; exact {seam}.operator_equal
def certificate : PolynomialPointGridBlock ({args.sign}:ℝ) (step:ℝ) (1/10^55) (1/10^55) {n} :=
  PolynomialPointGridBlock.append {ln}.certificate {rn}.certificate state_seam matrix_seam
theorem state_start : certificate.state 0={left['first_header']}.state 0 := by
  rw [certificate,PolynomialPointGridBlock.append_state_zero,{ln}.state_start]
theorem matrix_start : certificate.matrix 0={left['first_header']}.operator 0 := by
  rw [certificate,PolynomialPointGridBlock.append_matrix_zero,{ln}.matrix_start]
theorem state_last : certificate.state {n}={right['last_header']}.state {right['last_index']} := by
  change (PolynomialPointGridBlock.append _ _ state_seam matrix_seam).state ({left['count']}+{right['count']})=_
  rw [PolynomialPointGridBlock.append_state_last,{rn}.state_last]
theorem matrix_last : certificate.matrix {n}={right['last_header']}.operator {right['last_index']} := by
  change (PolynomialPointGridBlock.append _ _ state_seam matrix_seam).matrix ({left['count']}+{right['count']})=_
  rw [PolynomialPointGridBlock.append_matrix_last,{rn}.matrix_last]
attribute [irreducible] certificate
end
end {PREFIX}{name}
'''
   write(name,[ln,rn,seam],text,True)
   new.append({'name':name,'count':n,'first_header':left['first_header'],'last_header':right['last_header'],'last_index':right['last_index']})
  blocks=new;level+=1
 root=blocks[0]['name'];audit_name=args.key+'Audit'
 write(audit_name,[root],f'#print axioms {PREFIX}{root}.certificate\n')
 if any(path.read_bytes()!=source_bytes[k] for k,path in sources.items()):
  raise ValueError('Pinned generator input source changed during generation')
 if args.input_node and args.input_node.read_bytes()!=input_bytes:
  raise ValueError('Input checkpoint changed during generation')
 manifest={'schema':'rotating.production-shard.v1','key':args.key,
  'candidate_id':'nonzero_rotation_minus56_over57','candidate_hash':candidate_hash,
  'sign':args.sign,'start':start,'count':args.count,'orders':{'state':42,'matrix':22},'mesh':str(g.S),
  'step':{'num':str(h.numerator),'den':str(h.denominator)},'modules':modules,'root_module':PREFIX+root,
  'audit_module':PREFIX+audit_name,'audit_marker':marker,'total_path_steps':4000,'local_block_size':8,
  'reset_bounds':{k:{'num':'1','den':str(10**55)} for k in ['state','matrix']},'leaf_coverage':coverage,
  'checked_constant':PREFIX+root+'.certificate','output_node':'output_node.json',
  'attachments':[{'source':'output_node.json','sha256':sha(out/'output_node.json')}],
  'input_node_sha256':hashlib.sha256(input_bytes).hexdigest() if input_bytes is not None else None,
  'generator_sha256':fingerprints['generator']['sha256'],'source_fingerprints':fingerprints,'module_system':args.module,
  'status':'Generated untrusted proposals and Lean source only; no successful compile or trajectory/root claim.'}
 (out/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
 print(json.dumps({'source_modules':len(modules),'count':args.count,'sign':args.sign,'manifest':str(out/'manifest.json')}))

if __name__=='__main__':main()
