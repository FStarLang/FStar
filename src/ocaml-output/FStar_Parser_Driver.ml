
open Prims
let print_error = (fun msg r -> (let _113_6 = (let _113_5 = (FStar_Range.string_of_range r)
in (FStar_Util.format2 "ERROR %s: %s\n" _113_5 msg))
in (FStar_Util.print_string _113_6)))

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
(let _113_41 = (FStar_Parser_Desugar.desugar_decls env decls)
in Decls (_113_41))
end
| FStar_Util.Inl (FStar_Util.Inl (_48_27)) -> begin
(Prims.raise (FStar_Absyn_Syntax.Err ("Refusing to check more than one module at a time incrementally")))
end
| FStar_Util.Inr (msg, r) -> begin
(Prims.raise (FStar_Absyn_Syntax.Error ((msg, r))))
end))

let parse_file = (fun env fn -> if (is_cache_file fn) then begin
(let full_name = (let _113_49 = (let _113_48 = (let _113_47 = (let _113_46 = (FStar_Options.get_fstar_home ())
in (Prims.strcat _113_46 "/"))
in (Prims.strcat _113_47 FStar_Options.cache_dir))
in (Prims.strcat _113_48 "/"))
in (Prims.strcat _113_49 fn))
in (let m = (let _113_50 = (FStar_Util.get_oreader full_name)
in (FStar_Absyn_SSyntax.deserialize_modul _113_50))
in (let _113_51 = (FStar_Parser_Desugar.add_modul_to_env m env)
in (_113_51, (m)::[]))))
end else begin
(match ((FStar_Parser_ParseIt.parse (FStar_Util.Inl (fn)))) with
| FStar_Util.Inl (FStar_Util.Inl (ast)) -> begin
(FStar_Parser_Desugar.desugar_file env ast)
end
| FStar_Util.Inl (FStar_Util.Inr (_48_42)) -> begin
(let _48_45 = (FStar_Util.fprint1 "%s: Expected a module\n" fn)
in (FStar_All.exit 1))
end
| FStar_Util.Inr (msg, r) -> begin
(let _48_51 = (let _113_52 = (FStar_Absyn_Print.format_error r msg)
in (FStar_All.pipe_left FStar_Util.print_string _113_52))
in (FStar_All.exit 1))
end)
end)

let read_build_config = (fun file -> (FStar_Parser_ParseIt.read_build_config file))




