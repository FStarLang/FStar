
open Prims
# 29 "FStar.Dependences.fst"
let find_deps_if_needed : FStar_Parser_Dep.verify_mode  ->  Prims.string Prims.list  ->  Prims.string Prims.list = (fun verify_mode files -> if (FStar_Options.explicit_deps ()) then begin
files
end else begin
(
# 33 "FStar.Dependences.fst"
let _88_8 = (FStar_Parser_Dep.collect verify_mode files)
in (match (_88_8) with
| (_88_4, deps, _88_7) -> begin
(match (deps) with
| [] -> begin
(
# 36 "FStar.Dependences.fst"
let _88_10 = (FStar_Util.print_error "Dependency analysis failed; reverting to using only the files provided")
in files)
end
| _88_13 -> begin
(
# 39 "FStar.Dependences.fst"
let deps = (FStar_List.rev deps)
in (
# 40 "FStar.Dependences.fst"
let deps = if ((let _181_5 = (FStar_List.hd deps)
in (FStar_Util.basename _181_5)) = "prims.fst") then begin
(FStar_List.tl deps)
end else begin
(
# 44 "FStar.Dependences.fst"
let _88_15 = (FStar_Util.print_error "dependency analysis did not find prims.fst?!")
in (FStar_All.exit 1))
end
in deps))
end)
end))
end)




