
open Prims
# 28 "FStar.Dependences.fst"
let find_deps_if_needed : Prims.string Prims.list  ->  (Prims.string Prims.list * Prims.string Prims.list) = (fun files -> if (FStar_ST.read FStar_Options.explicit_deps) then begin
(files, [])
end else begin
(
# 32 "FStar.Dependences.fst"
let _84_5 = (FStar_Parser_Dep.collect files)
in (match (_84_5) with
| (_84_3, deps) -> begin
(match (deps) with
| [] -> begin
(
# 35 "FStar.Dependences.fst"
let _84_7 = (FStar_Util.print_error "Dependency analysis failed; reverting to using only the files provided")
in (files, []))
end
| _84_10 -> begin
(
# 38 "FStar.Dependences.fst"
let deps = (FStar_List.rev deps)
in (
# 39 "FStar.Dependences.fst"
let deps = if ((let _173_3 = (FStar_List.hd deps)
in (FStar_Util.basename _173_3)) = "prims.fst") then begin
(FStar_List.tl deps)
end else begin
(
# 43 "FStar.Dependences.fst"
let _84_12 = (FStar_Util.print_error "dependency analysis did not find prims.fst?!")
in (FStar_All.exit 1))
end
in (
# 47 "FStar.Dependences.fst"
let admit_fsi = (FStar_ST.alloc [])
in (
# 48 "FStar.Dependences.fst"
let _84_18 = (FStar_List.iter (fun d -> (
# 49 "FStar.Dependences.fst"
let d = (FStar_Util.basename d)
in if ((FStar_Util.get_file_extension d) = "fsti") then begin
(let _173_7 = (let _173_6 = (FStar_Util.substring d 0 ((FStar_String.length d) - 5))
in (let _173_5 = (FStar_ST.read admit_fsi)
in (_173_6)::_173_5))
in (FStar_ST.op_Colon_Equals admit_fsi _173_7))
end else begin
if ((FStar_Util.get_file_extension d) = "fsi") then begin
(let _173_10 = (let _173_9 = (FStar_Util.substring d 0 ((FStar_String.length d) - 4))
in (let _173_8 = (FStar_ST.read admit_fsi)
in (_173_9)::_173_8))
in (FStar_ST.op_Colon_Equals admit_fsi _173_10))
end else begin
()
end
end)) deps)
in (let _173_11 = (FStar_ST.read admit_fsi)
in (deps, _173_11))))))
end)
end))
end)




