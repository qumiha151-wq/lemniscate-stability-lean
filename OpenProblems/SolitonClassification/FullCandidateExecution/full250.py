"""Project complete original release assets and build the exact 250-shard ledger."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile

REPO = "qumiha151-wq/lemniscate-stability-lean"
SOURCE = "cff971bcac7ac2d83aba04596ce09e44fda1ac29"
PLAN = "a62ef654ec4f2fd01d55b6dae19c28483dba137c424c3068a372c514b89559c1"
BASE = "dcf9b162c42c30f387803fc9f395fcb1183f0e8179f5b46004782ba4bbf1f10d"
FINAL48 = "23e73ccbac0d8d374ff23634eb67967ac41ae3f8bc5594e24e3f53fb3b26d9af"
TOOLS = {
 "production_public_projection.py":"b206b8a43a3e1b9a47a31ab33b038ca2ac351a461b810d9265f183019c56708d",
 "production_projection_transport.py":"784bf78a8cf0d0be458553f4ed82eb9b096d36681fcda2622e152fd92f5adf34",
 "production_projection_merge.py":"b0508cb0168b01077f2d90bc341daeca756cb6c3b43aec3c7ebbf2013c5f5625",
 "production_full_assembly_compile.py":"a0e2b19e60ebefdf1b35ac162df0a5a7f9b67188b4eb26d604d0664a1186456a"}
FIRST = {
 "RP0000":"92ae696c5c11fc8097253534778747500a775e534522d61e86c40b6a14e4e910",
 "RP3968":"4830497e721f832848aa615bffaeafd0a19b0c9446a672ec746862dd30a5953c",
 "RM0000":"70d343fa118e6b96ca07a9a35421417849ccec3a732f42afb2e4340daaf5ce4b",
 "RM3968":"5cbc08318f2a272e4b957dcbdd0cae1212cdac17eb0ab36e6364ead2ff4c5e13"}
REQUESTS = (
 "7ad7c023e8aaedef5878f2d8309295df3bfb28302850c239b0865e12070d6cde",
 "3f47d2d452800877dcccb548337b3747d285e999ba75ade58d6a644a9a9bf579",
 "bfea0fea6de890be95a151f852712097717bea2b99376bffce797a19adf28ce4",
 "e1e5c25c41b4905a4bd5829da61694fbcea75b590bf4278d81fae9ebb7ea8fa0",
 "9a48e2d12a96f64feb2dc59254ee5762f51405ce11148846142de57e417555ac",
 "906b9c886672bfe54730c8922b31fe896a0989dc6770759ef1d545401fe2b7df",
 "abfaa94c0f2e2f3bc8d214607a13324467fcc4a7615fd73a52ee1cc930d71397",
 "4ac483ebb2cdaf3704d7383d76b9b83175f7ef638226e1f071bb96f9db797a8b")

def require(ok, message):
    if not ok:
        raise ValueError(message)

def sha(path):
    with path.open("rb") as f:
        return hashlib.file_digest(f,"sha256").hexdigest()

def read(path):
    return json.loads(path.read_bytes())

def save(path,obj):
    with path.open("x",encoding="utf-8",newline="\n") as f:
        json.dump(obj,f,indent=2,sort_keys=True)
        f.write("\n")

def tool(args,name,*params):
    subprocess.run([sys.executable,"-B",str(args.tools/name),*map(str,params)],check=True)

def request_for(args,batch):
    p=args.requests/f"batch{batch:02}.json"
    require(sha(p)==REQUESTS[batch-1],"wrong numbered request")
    return read(p)["original_request"]

def bound_record(args,key,batch,job):
    file=args.records/(key+".json")
    digest=sha(file)
    record=read(file)
    require(record["schema"]=="rotating.durable-release-record.v1" and record["status"]=="remote_verified"
            and record["test_fixture"] is False and record["remote_durability_verified"] is True
            and record["key"]==key and record["release"]["draft"] is False and record["release"]["published_at"]
            and record["repository"]==REPO and record["revision"]==SOURCE and record["plan_sha256"]==PLAN
            and record["base_lock_sha256"]==BASE,"wrong durable record for "+key)
    if batch==0:
        require(digest==FIRST[key],"wrong original first-four record")
    else:
        require(record["publisher"]["request_sha256"]==REQUESTS[batch-1]
                and record["publisher"]["origin_catalog_sha256"]=="647a4e70ebf7b8a5c6d0436bf097e2edbb9678d750feeb0101480fbe24d427ad"
                and record["release"]["tag"]==f"soliton-rotating-cff971bcac7a-original-run43359142508-b{batch:02}"
                and record["asset"]["name"]==job["asset_name"]
                and record["asset"]["digest"]=="sha256:"+job["archive_sha256"]
                and record["asset"]["size"]==job["archive_bytes"],"publisher record/origin request mismatch "+key)
    if args.index_jobs:
        bound=args.index_jobs[key]
        expected=dict(key=key, source_revision=SOURCE, release_id=record["release"]["id"],
            asset_id=record["asset"]["id"],asset_name=record["asset"]["name"],
            archive_sha256=record["asset"]["digest"][7:],archive_bytes=record["asset"]["size"],
            record_sha256=digest)
        require(all(bound[k]==v for k,v in expected.items()),"durable index disagrees with "+key)
    return record,digest

def project(args,plan):
    require(0<=args.batch<=8,"invalid batch")
    jobs={j["key"]:j for j in plan["jobs"]}
    batch={key:None for key in FIRST} if args.batch==0 else {j["key"]:j for j in request_for(args,args.batch)["jobs"]}
    local=read(args.local_archives) if args.local_archives else {}
    if args.local_archives:
        require(set(local)==set(batch),"local archive list differs from batch")
    args.out.mkdir(parents=True,exist_ok=False)
    require(shutil.disk_usage(args.out).free>=2*1024**3,"projection worker needs 2 GiB free")
    rows=[]
    for key,job in batch.items():
        rec,rsha=bound_record(args,key,args.batch,job)
        a=rec["asset"]
        want=a["digest"].removeprefix("sha256:")
        require(re.fullmatch("[0-9a-f]{64}",want),"invalid archive digest")
        with tempfile.TemporaryDirectory(prefix="project-",dir=args.out.parent) as tmp:
            scratch=Path(tmp)
            if args.local_archives:
                original=Path(local[key])
            else:
                incoming=scratch/"original"
                incoming.mkdir()
                original=incoming/(key+".tar.xz")
                subprocess.run(["gh","release","download",rec["release"]["tag"],"--repo",REPO,
                    "--pattern",a["name"],"--output",str(original)],check=True)
            require(original.stat().st_size==a["size"] and sha(original)==want,"original archive bytes differ")
            common=["--plan",args.plan,"--plan-sha256",PLAN,"--revision",SOURCE,"--key",key,
                "--archive-sha256",want,"--base-lock-sha256",BASE,"--require-durable","--durable-record-sha256",rsha]
            projected=scratch/"projection"
            tool(args,"production_public_projection.py","project",*common,"--archive",original,"--output",projected,
                "--durable-record",args.records/(key+".json"))
            receipt=projected/"projection.json"
            r=read(receipt)
            receipt_sha=sha(receipt)
            transport=args.out/(key+".public.tar.xz")
            tool(args,"production_projection_transport.py","pack",*common,"--projection",projected,
                "--receipt-sha256",receipt_sha,"--archive",transport)
            row={k:jobs[key][k] for k in ("key","sign","start","count","input_node_sha256","output_node_sha256")}
            row.update(full_archive_sha256=want,full_archive_bytes=a["size"],receipt_sha256=receipt_sha,
                durable_record_sha256=rsha,transport_file=transport.name,transport_sha256=sha(transport),
                transport_bytes=transport.stat().st_size,public_bytes=r["public_bytes"],metadata_bytes=r["metadata_bytes"],
                receipt_bytes=receipt.stat().st_size)
            rows.append(row)
            print("Projected",key,row["transport_sha256"],flush=True)
    save(args.out/"rows.json",rows)

def merge(args,plan,merger):
    require(re.fullmatch("[a-f0-9]{40}",args.publication_revision),"invalid execution revision")
    args.out.mkdir(parents=True,exist_ok=False)
    transports=args.out/"transports"
    transports.mkdir()
    rows={}
    for batch in (range(9) if args.mode=="full" else [0]):
        folder=args.parts/f"batch{batch:02}"
        jobs={k:None for k in FIRST} if batch==0 else {j["key"]:j for j in request_for(args,batch)["jobs"]}
        records=read(folder/"rows.json")
        require(len(records)==len(jobs) and {r["key"] for r in records}==set(jobs),"batch coverage mismatch")
        for row in records:
            key=row["key"]
            require(key not in rows and row["transport_file"]==key+".public.tar.xz","duplicate or unsafe transport name")
            rec,rsha=bound_record(args,key,batch,jobs[key])
            require(row["durable_record_sha256"]==rsha and row["full_archive_bytes"]==rec["asset"]["size"]
                and "sha256:"+row["full_archive_sha256"]==rec["asset"]["digest"],"unbound worker receipt")
            source=folder/row["transport_file"]
            require(source.stat().st_size==row["transport_bytes"] and sha(source)==row["transport_sha256"],"transport changed")
            shutil.copyfile(source,transports/source.name)
            rows[key]=row
    ledger=dict(schema=merger.SCHEMA,mode=args.mode,source_revision=SOURCE,
        publication_revision=args.publication_revision,plan_sha256=PLAN,base_lock_sha256=BASE,
        **{k:plan[k] for k in ("candidate_id","candidate_hash","orders","mesh","step")},
        projection_helper_sha256=merger.p.helpers(),transport_helper_sha256=merger.transport.helpers(),
        jobs=[rows[j["key"]] for j in plan["jobs"] if j["key"] in rows])
    merger.validate_ledger(ledger,plan,args.mode)
    path=args.out/"ledger.json"
    save(path,ledger)
    tool(args,"production_projection_merge.py","--ledger",path,"--ledger-sha256",sha(path),
        "--plan",args.plan,"--plan-sha256",PLAN,"--revision",SOURCE,"--base-lock",args.base,
        "--base-lock-sha256",BASE,"--archive-root",transports,"--output",args.out/"merged","--mode",args.mode)
    receipt=args.out/"merged/merge_receipt.json"
    result=read(receipt)
    require(result["mode"]==args.mode and result["all_250_projections_validated"]==(args.mode=="full")
        and len(result["modules"])==47*len(rows),"unexpected merge result")
    save(args.out/"merge_pins.json",dict(ledger_sha256=sha(path),merge_receipt_sha256=sha(receipt),
        mode=args.mode,modules=len(result["modules"])))

def assemble(args):
    pins=read(args.merge/"merge_pins.json")
    require(pins["mode"]=="full" and pins["modules"]==11750,"complete 250-shard merge required")
    a=args.tools.parent
    p=args.pipeline
    tool(args,"production_full_assembly_compile.py","--ledger",args.merge/"ledger.json",
        "--ledger-sha256",pins["ledger_sha256"],"--merged",args.merge/"merged",
        "--merge-receipt-sha256",pins["merge_receipt_sha256"],"--pipeline-package",p,
        "--core-project",args.core_project,"--final-package",args.final_package,"--final-output",args.final_output,
        "--final-report-sha256",FINAL48,"--assembly-root",a/"uncompiled/assembly","--endpoint-root",
        a/"uncompiled/endpoints","--candidate-source",p/"future/uncompiled/FullCandidate.lean","--census",
        a/"inputs/FullAssemblyDesignCensus.json","--base-lock",args.restored/"base_lock.json",
        "--base-lock-sha256",BASE,"--base-args",args.restored/"base_args.json","--output",args.out,
        "--seconds","600","--memory-mb","4096")

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--tools",required=True,type=Path)
    subs=parser.add_subparsers(dest="command",required=True)
    project_cli=subs.add_parser("project")
    merge_cli=subs.add_parser("merge")
    asm=subs.add_parser("assemble")
    for sub in (project_cli,merge_cli,asm):
        sub.add_argument("--out",type=Path,required=True)
    for sub in (project_cli,merge_cli):
        for arg in ("plan","records","requests"):
            sub.add_argument("--"+arg,type=Path,required=True)
        sub.add_argument("--index",type=Path,help="Execution-commit index of all 250 published records")
    project_cli.add_argument("--batch",type=int,required=True)
    project_cli.add_argument("--local-archives",type=Path,help="JSON mapping keys to predownloaded original assets")
    merge_cli.add_argument("--parts",type=Path,required=True)
    merge_cli.add_argument("--base",type=Path,required=True)
    merge_cli.add_argument("--publication-revision",required=True)
    merge_cli.add_argument("--mode",choices=["pilot","full"],required=True)
    for arg in ("merge","pipeline","core-project","final-package","final-output","restored"):
        asm.add_argument("--"+arg,type=Path,required=True)
    args=parser.parse_args()
    for k,v in vars(args).items():
        if isinstance(v,Path):
            setattr(args,k,v.resolve())
    for filename,digest in TOOLS.items():
        require(sha(args.tools/filename)==digest,"wrong frozen tool "+filename)
    if args.command=="assemble":
        return assemble(args)
    require(sha(args.plan)==PLAN,"wrong 250-shard plan")
    plan=read(args.plan)
    args.index_jobs={}
    if args.index:
        rows=read(args.index)["jobs"]
        require([row["key"] for row in rows]==[row["key"] for row in plan["jobs"]],"bound index plan order")
        args.index_jobs={row["key"]:row for row in rows}
    else:
        require((args.command=="project" and args.batch==0 and args.local_archives) or
            (args.command=="merge" and args.mode=="pilot"),"production requires a bound 250-record index")
    if args.command=="project":
        return project(args,plan)
    sys.path.insert(0,str(args.tools))
    import production_projection_merge as merger
    return merge(args,plan,merger)

if __name__=="__main__":
    main()
