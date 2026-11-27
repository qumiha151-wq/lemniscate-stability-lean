"""Run with Python and python-flint. All four b85 files are wrapped ASCII."""
from pathlib import Path
import base64, json, zlib, tempfile
from shape import checks
here=Path(__file__).resolve().parent
def main():
    data=json.loads((here/"header.json").read_bytes())
    data["rows"]={}
    for name in ("k","v","p","q"):
        text=b"".join((here/(name+".b85")).read_bytes().split())
        data["rows"][name]=json.loads(zlib.decompress(base64.b85decode(text)))
    with tempfile.TemporaryDirectory() as folder:
        path=Path(folder)/"reference.json"
        path.write_bytes((json.dumps(data,separators=(",",":"))+"\n").encode())
        report=checks(path,here.parent/"center.json")
    expected=json.loads((here/"shape_report.json").read_bytes())
    assert all(report[k]==expected[k] for k in ("packet_sha256","center_sha256","grid_size","transfer_radius","residual_bound","crossing_cells","counts"))
    print(report["counts"])
if __name__=="__main__":
    main()
