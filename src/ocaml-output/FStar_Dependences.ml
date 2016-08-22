
open Prims
# 24 "FStar.Dependences.fst"
let find_deps_if_needed : FStar_Parser_Dep.verify_mode  ->  Prims.string Prims.list  ->  Prims.string Prims.list = (fun verify_mode files -> if (FStar_Options.explicit_deps ()) then begin
files
end else begin
(
# 33 "FStar.Dependences.fst"
let _87_8 = (FStar_Parser_Dep.collect verify_mode files)
in (match (_87_8) with
| (_87_4, deps, _87_7) -> begin
(match (deps) with
| [] -> begin
(
# 36 "FStar.Dependences.fst"
let _87_10 = (FStar_Util.print_error "Dependency analysis failed; reverting to using only the files provided")
in files)
end
| _87_13 -> begin
(
# 39 "FStar.Dependences.fst"
let deps = (FStar_List.rev deps)
in (
# 40 "FStar.Dependences.fst"
let deps = if ((let _179_5 = (FStar_List.hd deps)
in (FStar_Util.basename _179_5)) = "prims.fst") then begin
(FStar_List.tl deps)
end else begin
(
# 44 "FStar.Dependences.fst"
let _87_15 = (FStar_Util.print_error "dependency analysis did not find prims.fst?!")
in (FStar_All.exit 1))
end
in deps))
end)
end))
end)




