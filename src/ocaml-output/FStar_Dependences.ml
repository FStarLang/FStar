
open Prims
# 28 "FStar.Dependences.fst"
let find_deps_if_needed : Prims.string Prims.list  ->  (Prims.string Prims.list * Prims.string Prims.list) = (fun files -> if (FStar_ST.read FStar_Options.explicit_deps) then begin
(files, [])
end else begin
(
# 32 "FStar.Dependences.fst"
let _80_5 = (FStar_Parser_Dep.collect files)
in (match (_80_5) with
| (_80_3, deps) -> begin
(
# 33 "FStar.Dependences.fst"
let deps = (FStar_List.rev deps)
in (
# 34 "FStar.Dependences.fst"
let deps = if ((let _165_3 = (FStar_List.hd deps)
in (FStar_Util.basename _165_3)) = "prims.fst") then begin
(FStar_List.tl deps)
end else begin
(
# 38 "FStar.Dependences.fst"
let _80_7 = (FStar_Util.print_error "dependency analysis did not find prims.fst?!")
in (FStar_All.exit 1))
end
in (
# 42 "FStar.Dependences.fst"
let admit_fsi = (FStar_ST.alloc [])
in (
# 43 "FStar.Dependences.fst"
let _80_13 = (FStar_List.iter (fun d -> (
# 44 "FStar.Dependences.fst"
let d = (FStar_Util.basename d)
in if ((FStar_Util.get_file_extension d) = "fsti") then begin
(let _165_7 = (let _165_6 = (FStar_Util.substring d 0 ((FStar_String.length d) - 5))
in (let _165_5 = (FStar_ST.read admit_fsi)
in (_165_6)::_165_5))
in (FStar_ST.op_Colon_Equals admit_fsi _165_7))
end else begin
if ((FStar_Util.get_file_extension d) = "fsi") then begin
(let _165_10 = (let _165_9 = (FStar_Util.substring d 0 ((FStar_String.length d) - 4))
in (let _165_8 = (FStar_ST.read admit_fsi)
in (_165_9)::_165_8))
in (FStar_ST.op_Colon_Equals admit_fsi _165_10))
end else begin
()
end
end)) deps)
in (let _165_11 = (FStar_ST.read admit_fsi)
in (deps, _165_11))))))
end))
end)




