
open Prims
# 28 "FStar.Dependences.fst"
let find_deps_if_needed : Prims.string Prims.list  ->  (Prims.string Prims.list * Prims.string Prims.list) = (fun files -> if (FStar_ST.read FStar_Options.explicit_deps) then begin
(files, [])
end else begin
(
# 32 "FStar.Dependences.fst"
let _79_5 = (FStar_Parser_Dep.collect files)
in (match (_79_5) with
| (_79_3, deps) -> begin
(
# 33 "FStar.Dependences.fst"
let deps = (FStar_List.rev deps)
in (
# 34 "FStar.Dependences.fst"
let deps = if ((let _163_3 = (FStar_List.hd deps)
in (FStar_Util.basename _163_3)) = "prims.fst") then begin
(FStar_List.tl deps)
end else begin
(
# 38 "FStar.Dependences.fst"
let _79_7 = (FStar_Util.print_error "dependency analysis did not find prims.fst?!")
in (FStar_All.exit 1))
end
in (
# 42 "FStar.Dependences.fst"
let admit_fsi = (FStar_ST.alloc [])
in (
# 43 "FStar.Dependences.fst"
let _79_13 = (FStar_List.iter (fun d -> (
# 44 "FStar.Dependences.fst"
let d = (FStar_Util.basename d)
in if ((FStar_Util.get_file_extension d) = "fsti") then begin
(let _163_7 = (let _163_6 = (FStar_Util.substring d 0 ((FStar_String.length d) - 5))
in (let _163_5 = (FStar_ST.read admit_fsi)
in (_163_6)::_163_5))
in (FStar_ST.op_Colon_Equals admit_fsi _163_7))
end else begin
if ((FStar_Util.get_file_extension d) = "fsi") then begin
(let _163_10 = (let _163_9 = (FStar_Util.substring d 0 ((FStar_String.length d) - 4))
in (let _163_8 = (FStar_ST.read admit_fsi)
in (_163_9)::_163_8))
in (FStar_ST.op_Colon_Equals admit_fsi _163_10))
end else begin
()
end
end)) deps)
in (let _163_11 = (FStar_ST.read admit_fsi)
in (deps, _163_11))))))
end))
end)




