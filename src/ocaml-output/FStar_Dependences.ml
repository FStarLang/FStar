
open Prims

let find_deps_if_needed : Prims.string Prims.list  ->  Prims.string Prims.list = (fun files -> if (FStar_Options.explicit_deps ()) then begin
files
end else begin
(

let _85_7 = (FStar_Parser_Dep.collect files)
in (match (_85_7) with
| (_85_3, deps, _85_6) -> begin
(match (deps) with
| [] -> begin
(

let _85_9 = (FStar_Util.print_error "Dependency analysis failed; reverting to using only the files provided")
in files)
end
| _85_12 -> begin
(

let deps = (FStar_List.rev deps)
in (

let deps = if ((let _175_3 = (FStar_List.hd deps)
in (FStar_Util.basename _175_3)) = "prims.fst") then begin
(FStar_List.tl deps)
end else begin
(

let _85_14 = (FStar_Util.print_error "dependency analysis did not find prims.fst?!")
in (FStar_All.exit 1))
end
in deps))
end)
end))
end)




