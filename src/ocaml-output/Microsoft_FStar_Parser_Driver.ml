
let print_error = (fun msg r -> (Support.Microsoft.FStar.Util.print_string (Support.Microsoft.FStar.Util.format2 "ERROR %s: %s\n" (Support.Microsoft.FStar.Range.string_of_range r) msg)))

let is_cache_file = (fun fn -> ((Support.Microsoft.FStar.Util.get_file_extension fn) = ".cache"))

let parse_fragment = (fun curmod env frag -> (match ((Microsoft_FStar_Parser_ParseIt.parse (Support.Microsoft.FStar.Util.Inr (frag)))) with
| Support.Microsoft.FStar.Util.Inl (Support.Microsoft.FStar.Util.Inl (modul::[])) -> begin
(let _414607 = (Microsoft_FStar_Parser_Desugar.desugar_partial_modul curmod env modul)
in (match (_414607) with
| (env, modul) -> begin
Support.Microsoft.FStar.Util.Inl ((env, modul))
end))
end
| Support.Microsoft.FStar.Util.Inl (Support.Microsoft.FStar.Util.Inr (decls)) -> begin
(Support.Microsoft.FStar.Util.Inr (Microsoft_FStar_Parser_Desugar.desugar_decls env decls))
end
| Support.Microsoft.FStar.Util.Inl (Support.Microsoft.FStar.Util.Inl (_)) -> begin
(raise (Microsoft_FStar_Absyn_Syntax.Err ("Refusing to check more than one module at a time incrementally")))
end
| Support.Microsoft.FStar.Util.Inr ((msg, r)) -> begin
(raise (Microsoft_FStar_Absyn_Syntax.Error ((msg, r))))
end))

let parse_file = (fun env fn -> if (is_cache_file fn) then begin
(let full_name = (Support.String.strcat (Support.String.strcat (Support.String.strcat (Support.String.strcat (Microsoft_FStar_Options.get_fstar_home ()) "/") Microsoft_FStar_Options.cache_dir) "/") fn)
in (let m = (Microsoft_FStar_Absyn_SSyntax.deserialize_modul (Support.Microsoft.FStar.Util.get_oreader full_name))
in ((Microsoft_FStar_Parser_Desugar.add_modul_to_env m env), (m)::[])))
end else begin
(match ((Microsoft_FStar_Parser_ParseIt.parse (Support.Microsoft.FStar.Util.Inl (fn)))) with
| Support.Microsoft.FStar.Util.Inl (Support.Microsoft.FStar.Util.Inl (ast)) -> begin
(Microsoft_FStar_Parser_Desugar.desugar_file env ast)
end
| Support.Microsoft.FStar.Util.Inl (Support.Microsoft.FStar.Util.Inr (_)) -> begin
(let _414630 = (Support.Microsoft.FStar.Util.fprint1 "%s: Expected a module\n" fn)
in (exit (1)))
end
| Support.Microsoft.FStar.Util.Inr ((msg, r)) -> begin
(let _414636 = (Support.Microsoft.FStar.Util.print_string (Microsoft_FStar_Absyn_Print.format_error r msg))
in (exit (1)))
end)
end)

let read_build_config = (fun file -> (Microsoft_FStar_Parser_ParseIt.read_build_config file))




