
let print_error = (fun msg r -> (let _113_6 = (let _113_5 = (Microsoft_FStar_Range.string_of_range r)
in (Microsoft_FStar_Util.format2 "ERROR %s: %s\n" _113_5 msg))
in (Microsoft_FStar_Util.print_string _113_6)))

let is_cache_file = (fun fn -> ((Microsoft_FStar_Util.get_file_extension fn) = ".cache"))

let parse_fragment = (fun curmod env frag -> (match ((Microsoft_FStar_Parser_ParseIt.parse (Microsoft_FStar_Util.Inr (frag)))) with
| Microsoft_FStar_Util.Inl (Microsoft_FStar_Util.Inl (modul::[])) -> begin
(let _47_13 = (Microsoft_FStar_Parser_Desugar.desugar_partial_modul curmod env modul)
in (match (_47_13) with
| (env, modul) -> begin
Microsoft_FStar_Util.Inl ((env, modul))
end))
end
| Microsoft_FStar_Util.Inl (Microsoft_FStar_Util.Inr (decls)) -> begin
(let _113_13 = (Microsoft_FStar_Parser_Desugar.desugar_decls env decls)
in (All.pipe_left (fun _113_12 -> Microsoft_FStar_Util.Inr (_113_12)) _113_13))
end
| Microsoft_FStar_Util.Inl (Microsoft_FStar_Util.Inl (_47_18)) -> begin
(Prims.raise (Microsoft_FStar_Absyn_Syntax.Err ("Refusing to check more than one module at a time incrementally")))
end
| Microsoft_FStar_Util.Inr (msg, r) -> begin
(Prims.raise (Microsoft_FStar_Absyn_Syntax.Error ((msg, r))))
end))

let parse_file = (fun env fn -> (match ((is_cache_file fn)) with
| true -> begin
(let full_name = (let _113_21 = (let _113_20 = (let _113_19 = (let _113_18 = (Microsoft_FStar_Options.get_fstar_home ())
in (Prims.strcat _113_18 "/"))
in (Prims.strcat _113_19 Microsoft_FStar_Options.cache_dir))
in (Prims.strcat _113_20 "/"))
in (Prims.strcat _113_21 fn))
in (let m = (let _113_22 = (Microsoft_FStar_Util.get_oreader full_name)
in (Microsoft_FStar_Absyn_SSyntax.deserialize_modul _113_22))
in (let _113_23 = (Microsoft_FStar_Parser_Desugar.add_modul_to_env m env)
in (_113_23, (m)::[]))))
end
| false -> begin
(match ((Microsoft_FStar_Parser_ParseIt.parse (Microsoft_FStar_Util.Inl (fn)))) with
| Microsoft_FStar_Util.Inl (Microsoft_FStar_Util.Inl (ast)) -> begin
(Microsoft_FStar_Parser_Desugar.desugar_file env ast)
end
| Microsoft_FStar_Util.Inl (Microsoft_FStar_Util.Inr (_47_33)) -> begin
(let _47_36 = (Microsoft_FStar_Util.fprint1 "%s: Expected a module\n" fn)
in (All.exit 1))
end
| Microsoft_FStar_Util.Inr (msg, r) -> begin
(let _47_42 = (let _113_24 = (Microsoft_FStar_Absyn_Print.format_error r msg)
in (All.pipe_left Microsoft_FStar_Util.print_string _113_24))
in (All.exit 1))
end)
end))

let read_build_config = (fun file -> (Microsoft_FStar_Parser_ParseIt.read_build_config file))




