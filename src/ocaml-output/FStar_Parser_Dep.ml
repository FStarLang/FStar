
open Prims
let check_and_strip_suffix = (fun f -> (let suffixes = (".fsti")::(".fst")::(".fsi")::(".fs")::[]
in (let matches = (FStar_List.map (fun ext -> (let lext = (FStar_String.length ext)
in (let l = (FStar_String.length f)
in if ((l > lext) && ((let _115_4 = (FStar_String.substring f (l - lext) lext)
in (FStar_Util.compare _115_4 ext)) = 0)) then begin
(let _115_5 = (FStar_String.substring f 0 (l - lext))
in Some (_115_5))
end else begin
None
end))) suffixes)
in (match ((FStar_List.filter FStar_Util.is_some matches)) with
| Some (m)::_49_12 -> begin
Some (m)
end
| _49_17 -> begin
None
end))))

let is_interface = (fun f -> ((FStar_String.get f ((FStar_String.length f) - 1)) = 'i'))

let print_map = (fun m -> (let _115_13 = (FStar_Util.smap_keys m)
in (FStar_List.iter (fun k -> (let _115_12 = (let _115_11 = (FStar_Util.smap_try_find m k)
in (FStar_Util.must _115_11))
in (FStar_Util.fprint2 "%s: %s\n" k _115_12))) _115_13)))

let build_map = (fun _49_21 -> (match (()) with
| () -> begin
(let include_directories = (let _115_16 = (FStar_Util.getcwd ())
in (FStar_Options.get_include_path _115_16))
in (let map = (FStar_Util.smap_create 41)
in (let _49_39 = (FStar_List.iter (fun d -> if (FStar_Util.file_exists d) then begin
(let files = (FStar_Util.readdir d)
in (FStar_List.iter (fun f -> (let f = (FStar_Util.basename f)
in (match ((check_and_strip_suffix f)) with
| Some (longname) -> begin
(let key = (FStar_String.lowercase longname)
in (match ((FStar_Util.smap_try_find map key)) with
| Some (existing_file) -> begin
(let _49_33 = if ((FStar_String.lowercase existing_file) = (FStar_String.lowercase f)) then begin
(let _115_20 = (let _115_19 = (FStar_Util.format1 "I\'m case insensitive, and I found the same file twice (%s)" f)
in FStar_Absyn_Syntax.Err (_115_19))
in (Prims.raise _115_20))
end else begin
()
end
in (let _49_35 = if ((is_interface existing_file) = (is_interface f)) then begin
(let _115_22 = (let _115_21 = (FStar_Util.format1 "Found both a .fs and a .fst (or both a .fsi and a .fsti) (%s)" f)
in FStar_Absyn_Syntax.Err (_115_21))
in (Prims.raise _115_22))
end else begin
()
end
in if (not ((is_interface existing_file))) then begin
(FStar_Util.smap_add map key f)
end else begin
()
end))
end
| None -> begin
(FStar_Util.smap_add map key f)
end))
end
| None -> begin
()
end))) files))
end else begin
()
end) include_directories)
in map)))
end))

let enter_namespace = (fun original_map working_map prefix -> (let found = (FStar_ST.alloc false)
in (let prefix = (Prims.strcat prefix ".")
in (let _49_51 = (let _115_28 = (FStar_Util.smap_keys original_map)
in (FStar_List.iter (fun k -> if (FStar_Util.starts_with k prefix) then begin
(let suffix = (FStar_String.substring k (FStar_String.length prefix) ((FStar_String.length k) - (FStar_String.length prefix)))
in (let filename = (let _115_27 = (FStar_Util.smap_try_find original_map k)
in (FStar_Util.must _115_27))
in (let _49_49 = (FStar_Util.smap_add working_map suffix filename)
in (FStar_ST.op_Colon_Equals found true))))
end else begin
()
end) _115_28))
in (FStar_ST.read found)))))

let lowercase_join_longident = (fun l last -> (let suffix = if last then begin
(l.FStar_Absyn_Syntax.ident.FStar_Absyn_Syntax.idText)::[]
end else begin
[]
end
in (let names = (let _115_34 = (FStar_List.map (fun x -> x.FStar_Absyn_Syntax.idText) l.FStar_Absyn_Syntax.ns)
in (FStar_List.append _115_34 suffix))
in (let names = (FStar_List.map FStar_String.lowercase names)
in (FStar_String.concat "." names)))))

let check_module_declaration_against_filename = (fun lid filename -> (let k' = (lowercase_join_longident lid true)
in if ((let _115_41 = (let _115_40 = (let _115_39 = (FStar_Util.basename filename)
in (check_and_strip_suffix _115_39))
in (FStar_Util.must _115_40))
in (FStar_Util.compare _115_41 k')) <> 0) then begin
(FStar_Util.fprint2 "Warning: the module declaration \"module %s\" found in file %s does not match its filename\n" k' filename)
end else begin
()
end))

let collect_one = (fun original_map filename -> (let deps = (FStar_ST.alloc [])
in (let add_dep = (fun d -> (let _115_49 = (let _115_48 = (FStar_ST.read deps)
in (d)::_115_48)
in (FStar_ST.op_Colon_Equals deps _115_49)))
in (let working_map = (FStar_Util.smap_copy original_map)
in (let rec collect_fragment = (fun _49_1 -> (match (_49_1) with
| FStar_Util.Inl (file) -> begin
(collect_file file)
end
| FStar_Util.Inr (decls) -> begin
(collect_decls decls)
end))
and collect_file = (fun _49_2 -> (match (_49_2) with
| modul::[] -> begin
(collect_module modul)
end
| _49_82 -> begin
(let _115_58 = (let _115_57 = (FStar_Util.format1 "File %s does not respect the one module per file convention" filename)
in FStar_Absyn_Syntax.Err (_115_57))
in (Prims.raise _115_58))
end))
and collect_module = (fun _49_3 -> (match (_49_3) with
| (FStar_Parser_AST.Module (lid, decls)) | (FStar_Parser_AST.Interface (lid, decls, _)) -> begin
(let _49_92 = (check_module_declaration_against_filename lid filename)
in (collect_decls decls))
end))
and collect_decls = (fun decls -> (FStar_List.iter (fun x -> (collect_decl x.FStar_Parser_AST.d)) decls))
and collect_decl = (fun _49_4 -> (match (_49_4) with
| FStar_Parser_AST.Open (lid) -> begin
(let key = (lowercase_join_longident lid true)
in (match ((FStar_Util.smap_try_find original_map key)) with
| Some (filename) -> begin
(add_dep filename)
end
| None -> begin
(let r = (enter_namespace original_map working_map key)
in if (not (r)) then begin
(FStar_Util.fprint1 "Warning: no modules in namespace %s\n" key)
end else begin
()
end)
end))
end
| _49_105 -> begin
()
end))
in (let ast = (FStar_Parser_Driver.parse_file_raw filename)
in (let _49_107 = (collect_file ast)
in (FStar_ST.read deps))))))))

let collect = (fun filenames -> (let m = (build_map ())
in (FStar_List.map (fun f -> (let deps = (collect_one m f)
in (f, deps))) filenames)))

let print = (fun deps -> (FStar_List.iter (fun _49_116 -> (match (_49_116) with
| (f, deps) -> begin
(let deps = (FStar_List.map (fun s -> (FStar_Util.replace_string s " " "\\ ")) deps)
in (FStar_Util.fprint2 "%s: %s\n" f (FStar_String.concat " " deps)))
end)) deps))




