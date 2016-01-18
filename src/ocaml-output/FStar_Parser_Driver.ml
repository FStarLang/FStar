
open Prims
let print_error = (fun msg r -> (let _114_6 = (let _114_5 = (FStar_Range.string_of_range r)
in (FStar_Util.format2 "ERROR %s: %s\n" _114_5 msg))
in (FStar_Util.print_string _114_6)))

let is_cache_file = (fun fn -> ((FStar_Util.get_file_extension fn) = ".cache"))

type fragment =
| Empty
| Modul of (FStar_Parser_DesugarEnv.env * FStar_Absyn_Syntax.modul)
| Decls of (FStar_Parser_DesugarEnv.env * FStar_Absyn_Syntax.sigelts)

let is_Empty = (fun _discr_ -> (match (_discr_) with
| Empty -> begin
true
end
| _ -> begin
false
end))

let is_Modul = (fun _discr_ -> (match (_discr_) with
| Modul (_) -> begin
true
end
| _ -> begin
false
end))

let is_Decls = (fun _discr_ -> (match (_discr_) with
| Decls (_) -> begin
true
end
| _ -> begin
false
end))

let ___Modul____0 = (fun projectee -> (match (projectee) with
| Modul (_48_6) -> begin
_48_6
end))

let ___Decls____0 = (fun projectee -> (match (projectee) with
| Decls (_48_9) -> begin
_48_9
end))

let parse_fragment = (fun curmod env frag -> (match ((FStar_Parser_ParseIt.parse (FStar_Util.Inr (frag)))) with
| FStar_Util.Inl (FStar_Util.Inl ([])) -> begin
Empty
end
| FStar_Util.Inl (FStar_Util.Inl (modul::[])) -> begin
(let _48_22 = (FStar_Parser_Desugar.desugar_partial_modul curmod env modul)
in (match (_48_22) with
| (env, modul) -> begin
Modul ((env, modul))
end))
end
| FStar_Util.Inl (FStar_Util.Inr (decls)) -> begin
(let _114_41 = (FStar_Parser_Desugar.desugar_decls env decls)
in Decls (_114_41))
end
| FStar_Util.Inl (FStar_Util.Inl (_48_27)) -> begin
(Prims.raise (FStar_Absyn_Syntax.Err ("Refusing to check more than one module at a time incrementally")))
end
| FStar_Util.Inr (msg, r) -> begin
(Prims.raise (FStar_Absyn_Syntax.Error ((msg, r))))
end))

let parse_file_raw = (fun fn -> (match ((FStar_Parser_ParseIt.parse (FStar_Util.Inl (fn)))) with
| FStar_Util.Inl (FStar_Util.Inl (ast)) -> begin
ast
end
| FStar_Util.Inl (FStar_Util.Inr (_48_39)) -> begin
(let _48_42 = (FStar_Util.print1 "%s: Expected a module\n" fn)
in (FStar_All.exit 1))
end
| FStar_Util.Inr (msg, r) -> begin
(let _48_48 = (let _114_44 = (FStar_Absyn_Print.format_error r msg)
in (FStar_All.pipe_left FStar_Util.print_string _114_44))
in (FStar_All.exit 1))
end))

let parse_file = (fun env fn -> if (is_cache_file fn) then begin
(let full_name = (let _114_52 = (let _114_51 = (let _114_50 = (let _114_49 = (FStar_Options.get_fstar_home ())
in (Prims.strcat _114_49 "/"))
in (Prims.strcat _114_50 FStar_Options.cache_dir))
in (Prims.strcat _114_51 "/"))
in (Prims.strcat _114_52 fn))
in (let m = (let _114_53 = (FStar_Util.get_oreader full_name)
in (FStar_Absyn_SSyntax.deserialize_modul _114_53))
in (let _114_54 = (FStar_Parser_Desugar.add_modul_to_env m env)
in (_114_54, (m)::[]))))
end else begin
(let _114_55 = (parse_file_raw fn)
in (FStar_Parser_Desugar.desugar_file env _114_55))
end)

let read_build_config = (fun file -> (FStar_Parser_ParseIt.read_build_config file true))




