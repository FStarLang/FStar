
open Prims

let find_deps_if_needed : Prims.string Prims.list  ->  Prims.string Prims.list = (fun files -> if (FStar_Options.explicit_deps ()) then begin
files
end else begin
(

let _86_7 = (FStar_Parser_Dep.collect files)
in (match (_86_7) with
| (_86_3, deps, _86_6) -> begin
(match (deps) with
| [] -> begin
(

let _86_9 = (FStar_Util.print_error "Dependency analysis failed; reverting to using only the files provided")
in files)
end
| _86_12 -> begin
(

let deps = (FStar_List.rev deps)
in (

let deps = if ((let _177_3 = (FStar_List.hd deps)
in (FStar_Util.basename _177_3)) = "prims.fst") then begin
(FStar_List.tl deps)
end else begin
(

let _86_14 = (FStar_Util.print_error "dependency analysis did not find prims.fst?!")
in (FStar_All.exit 1))
end
in deps))
end)
end))
end)




