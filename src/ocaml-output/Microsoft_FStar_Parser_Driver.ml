
let print_error = (fun ( msg ) ( r ) -> (let _70_20341 = (let _70_20340 = (Support.Microsoft.FStar.Range.string_of_range r)
in (Support.Microsoft.FStar.Util.format2 "ERROR %s: %s\n" _70_20340 msg))
in (Support.Microsoft.FStar.Util.print_string _70_20341)))

let is_cache_file = (fun ( fn ) -> ((Support.Microsoft.FStar.Util.get_file_extension fn) = ".cache"))

let parse_fragment = (fun ( curmod ) ( env ) ( frag ) -> (match ((Microsoft_FStar_Parser_ParseIt.parse (Support.Microsoft.FStar.Util.Inr (frag)))) with
| Support.Microsoft.FStar.Util.Inl (Support.Microsoft.FStar.Util.Inl (modul::[])) -> begin
(let _47_13 = (Microsoft_FStar_Parser_Desugar.desugar_partial_modul curmod env modul)
in (match (_47_13) with
| (env, modul) -> begin
Support.Microsoft.FStar.Util.Inl ((env, modul))
end))
end
| Support.Microsoft.FStar.Util.Inl (Support.Microsoft.FStar.Util.Inr (decls)) -> begin
(let _70_20348 = (Microsoft_FStar_Parser_Desugar.desugar_decls env decls)
in (Support.All.pipe_left (fun ( _70_20347 ) -> Support.Microsoft.FStar.Util.Inr (_70_20347)) _70_20348))
end
| Support.Microsoft.FStar.Util.Inl (Support.Microsoft.FStar.Util.Inl (_47_18)) -> begin
(raise (Microsoft_FStar_Absyn_Syntax.Err ("Refusing to check more than one module at a time incrementally")))
end
| Support.Microsoft.FStar.Util.Inr ((msg, r)) -> begin
(raise (Microsoft_FStar_Absyn_Syntax.Error ((msg, r))))
end))

let parse_file = (fun ( env ) ( fn ) -> (match ((is_cache_file fn)) with
| true -> begin
(let full_name = (let _70_20356 = (let _70_20355 = (let _70_20354 = (let _70_20353 = (Microsoft_FStar_Options.get_fstar_home ())
in (Support.String.strcat _70_20353 "/"))
in (Support.String.strcat _70_20354 Microsoft_FStar_Options.cache_dir))
in (Support.String.strcat _70_20355 "/"))
in (Support.String.strcat _70_20356 fn))
in (let m = (let _70_20357 = (Support.Microsoft.FStar.Util.get_oreader full_name)
in (Microsoft_FStar_Absyn_SSyntax.deserialize_modul _70_20357))
in (let _70_20358 = (Microsoft_FStar_Parser_Desugar.add_modul_to_env m env)
in (_70_20358, (m)::[]))))
end
| false -> begin
(match ((Microsoft_FStar_Parser_ParseIt.parse (Support.Microsoft.FStar.Util.Inl (fn)))) with
| Support.Microsoft.FStar.Util.Inl (Support.Microsoft.FStar.Util.Inl (ast)) -> begin
(Microsoft_FStar_Parser_Desugar.desugar_file env ast)
end
| Support.Microsoft.FStar.Util.Inl (Support.Microsoft.FStar.Util.Inr (_47_33)) -> begin
(let _47_36 = (Support.Microsoft.FStar.Util.fprint1 "%s: Expected a module\n" fn)
in (Support.All.exit 1))
end
| Support.Microsoft.FStar.Util.Inr ((msg, r)) -> begin
(let _47_42 = (let _70_20359 = (Microsoft_FStar_Absyn_Print.format_error r msg)
in (Support.All.pipe_left Support.Microsoft.FStar.Util.print_string _70_20359))
in (Support.All.exit 1))
end)
end))

let read_build_config = (fun ( file ) -> (Microsoft_FStar_Parser_ParseIt.read_build_config file))




