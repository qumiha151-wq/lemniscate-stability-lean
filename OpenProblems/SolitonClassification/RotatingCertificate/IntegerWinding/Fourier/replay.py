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
        from caps import cap_check
        cap=cap_check(path,report)
        assert cap["unique_critical_cell"]==49217
        print("Unique outer cap, angular separation in turns > 1/200")
        from annuli import check_annuli
        annuli=check_annuli(path,report)
        assert annuli["inner_critical_cell"]==49
        print("Inner and outer radial-band apertures in revolutions:",annuli)
        from density_geometry import check_density
        from density_upper import check_density_upper
        lower=check_density(path,report)
        upper=check_density_upper(path,report)
        assert lower["distinct_critical_radii"]==72
        assert lower["variation_lower_numerator"] >= 1009779369 and lower["variation_lower_denominator"]==10**8
        assert upper["strict_density_upper"]==14
        print("Whole-image crossing-density enclosure:",lower,upper)
        from crossings import count
        for mesh,num in ((32768,42),(49152,45)):
            result=count(path,mesh)
            assert result["eligible_pairs"]==num and result["clusters"]==2
            assert len(result["roots"])==2 and result["failures"]==[]
            print(mesh,"two transverse ordinary double points")
    expected=json.loads((here/"shape_report.json").read_bytes())
    assert all(report[k]==expected[k] for k in ("packet_sha256","center_sha256","grid_size","transfer_radius","residual_bound","crossing_cells","counts"))
    print(report["counts"])
if __name__=="__main__":
    main()
