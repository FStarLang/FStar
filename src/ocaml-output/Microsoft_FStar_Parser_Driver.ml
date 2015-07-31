
let print_error = (fun ( msg ) ( r ) -> (let _68_20190 = (let _68_20189 = (Support.Microsoft.FStar.Range.string_of_range r)
in (Support.Microsoft.FStar.Util.format2 "ERROR %s: %s\n" _68_20189 msg))
in (Support.Microsoft.FStar.Util.print_string _68_20190)))

let is_cache_file = (fun ( fn ) -> ((Support.Microsoft.FStar.Util.get_file_extension fn) = ".cache"))

let parse_fragment = (fun ( curmod ) ( env ) ( frag ) -> (match ((Microsoft_FStar_Parser_ParseIt.parse (Support.Microsoft.FStar.Util.Inr (frag)))) with
| Support.Microsoft.FStar.Util.Inl (Support.Microsoft.FStar.Util.Inl (modul::[])) -> begin
(let _45_13 = (Microsoft_FStar_Parser_Desugar.desugar_partial_modul curmod env modul)
in (match (_45_13) with
| (env, modul) -> begin
Support.Microsoft.FStar.Util.Inl ((env, modul))
end))
end
| Support.Microsoft.FStar.Util.Inl (Support.Microsoft.FStar.Util.Inr (decls)) -> begin
(let _68_20197 = (Microsoft_FStar_Parser_Desugar.desugar_decls env decls)
in (Support.Prims.pipe_left (fun ( _68_20196 ) -> Support.Microsoft.FStar.Util.Inr (_68_20196)) _68_20197))
end
| Support.Microsoft.FStar.Util.Inl (Support.Microsoft.FStar.Util.Inl (_)) -> begin
(raise (Microsoft_FStar_Absyn_Syntax.Err ("Refusing to check more than one module at a time incrementally")))
end
| Support.Microsoft.FStar.Util.Inr ((msg, r)) -> begin
(raise (Microsoft_FStar_Absyn_Syntax.Error ((msg, r))))
end))

let parse_file = (fun ( env ) ( fn ) -> (match ((is_cache_file fn)) with
| true -> begin
(let full_name = (let _68_20205 = (let _68_20204 = (let _68_20203 = (let _68_20202 = (Microsoft_FStar_Options.get_fstar_home ())
in (Support.String.strcat _68_20202 "/"))
in (Support.String.strcat _68_20203 Microsoft_FStar_Options.cache_dir))
in (Support.String.strcat _68_20204 "/"))
in (Support.String.strcat _68_20205 fn))
in (let m = (let _68_20206 = (Support.Microsoft.FStar.Util.get_oreader full_name)
in (Microsoft_FStar_Absyn_SSyntax.deserialize_modul _68_20206))
in (let _68_20207 = (Microsoft_FStar_Parser_Desugar.add_modul_to_env m env)
in (_68_20207, (m)::[]))))
end
| false -> begin
(match ((Microsoft_FStar_Parser_ParseIt.parse (Support.Microsoft.FStar.Util.Inl (fn)))) with
| Support.Microsoft.FStar.Util.Inl (Support.Microsoft.FStar.Util.Inl (ast)) -> begin
(Microsoft_FStar_Parser_Desugar.desugar_file env ast)
end
| Support.Microsoft.FStar.Util.Inl (Support.Microsoft.FStar.Util.Inr (_)) -> begin
(let _45_36 = (Support.Microsoft.FStar.Util.fprint1 "%s: Expected a module\n" fn)
in (exit (1)))
end
| Support.Microsoft.FStar.Util.Inr ((msg, r)) -> begin
(let _45_42 = (let _68_20208 = (Microsoft_FStar_Absyn_Print.format_error r msg)
in (Support.Prims.pipe_left Support.Microsoft.FStar.Util.print_string _68_20208))
in (exit (1)))
end)
end))

let read_build_config = (fun ( file ) -> (Microsoft_FStar_Parser_ParseIt.read_build_config file))




