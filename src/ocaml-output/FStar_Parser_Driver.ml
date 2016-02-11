
open Prims
# 28 "FStar.Parser.Driver.fst"
let print_error : Prims.string  ->  FStar_Range.range  ->  Prims.unit = (fun msg r -> (let _135_6 = (let _135_5 = (FStar_Range.string_of_range r)
in (FStar_Util.format2 "ERROR %s: %s\n" _135_5 msg))
in (FStar_Util.print_string _135_6)))

# 31 "FStar.Parser.Driver.fst"
let is_cache_file : Prims.string  ->  Prims.bool = (fun fn -> ((FStar_Util.get_file_extension fn) = ".cache"))

# 33 "FStar.Parser.Driver.fst"
type fragment =
| Empty
| Modul of (FStar_Parser_DesugarEnv.env * FStar_Absyn_Syntax.modul)
| Decls of (FStar_Parser_DesugarEnv.env * FStar_Absyn_Syntax.sigelts)

# 34 "FStar.Parser.Driver.fst"
let is_Empty = (fun _discr_ -> (match (_discr_) with
| Empty (_) -> begin
true
end
| _ -> begin
false
end))

# 35 "FStar.Parser.Driver.fst"
let is_Modul = (fun _discr_ -> (match (_discr_) with
| Modul (_) -> begin
true
end
| _ -> begin
false
end))

# 36 "FStar.Parser.Driver.fst"
let is_Decls = (fun _discr_ -> (match (_discr_) with
| Decls (_) -> begin
true
end
| _ -> begin
false
end))

# 35 "FStar.Parser.Driver.fst"
let ___Modul____0 : fragment  ->  (FStar_Parser_DesugarEnv.env * FStar_Absyn_Syntax.modul) = (fun projectee -> (match (projectee) with
| Modul (_56_6) -> begin
_56_6
end))

# 36 "FStar.Parser.Driver.fst"
let ___Decls____0 : fragment  ->  (FStar_Parser_DesugarEnv.env * FStar_Absyn_Syntax.sigelts) = (fun projectee -> (match (projectee) with
| Decls (_56_9) -> begin
_56_9
end))

# 38 "FStar.Parser.Driver.fst"
let parse_fragment : FStar_Absyn_Syntax.modul Prims.option  ->  FStar_Parser_DesugarEnv.env  ->  Prims.string  ->  fragment = (fun curmod env frag -> (match ((FStar_Parser_ParseIt.parse (FStar_Util.Inr (frag)))) with
| FStar_Util.Inl (FStar_Util.Inl ([])) -> begin
Empty
end
| FStar_Util.Inl (FStar_Util.Inl (modul::[])) -> begin
(
# 44 "FStar.Parser.Driver.fst"
let _56_22 = (FStar_Parser_Desugar.desugar_partial_modul curmod env modul)
in (match (_56_22) with
| (env, modul) -> begin
Modul ((env, modul))
end))
end
| FStar_Util.Inl (FStar_Util.Inr (decls)) -> begin
(let _135_44 = (FStar_Parser_Desugar.desugar_decls env decls)
in Decls (_135_44))
end
| FStar_Util.Inl (FStar_Util.Inl (_56_27)) -> begin
(Prims.raise (FStar_Absyn_Syntax.Err ("Refusing to check more than one module at a time incrementally")))
end
| FStar_Util.Inr (msg, r) -> begin
(Prims.raise (FStar_Absyn_Syntax.Error ((msg, r))))
end))

# 57 "FStar.Parser.Driver.fst"
let parse_file_raw : Prims.string  ->  FStar_Parser_AST.modul Prims.list = (fun fn -> (match ((FStar_Parser_ParseIt.parse (FStar_Util.Inl (fn)))) with
| FStar_Util.Inl (FStar_Util.Inl (ast)) -> begin
ast
end
| FStar_Util.Inl (FStar_Util.Inr (_56_39)) -> begin
(
# 63 "FStar.Parser.Driver.fst"
let _56_42 = (FStar_Util.print1 "%s: Expected a module\n" fn)
in (FStar_All.exit 1))
end
| FStar_Util.Inr (msg, r) -> begin
(
# 67 "FStar.Parser.Driver.fst"
let _56_48 = (let _135_47 = (FStar_Absyn_Print.format_error r msg)
in (FStar_All.pipe_left FStar_Util.print_string _135_47))
in (FStar_All.exit 1))
end))

# 73 "FStar.Parser.Driver.fst"
let parse_file : FStar_Parser_DesugarEnv.env  ->  Prims.string  ->  (FStar_Parser_DesugarEnv.env * FStar_Absyn_Syntax.modul Prims.list) = (fun env fn -> if (is_cache_file fn) then begin
(
# 75 "FStar.Parser.Driver.fst"
let full_name = (let _135_55 = (let _135_54 = (let _135_53 = (let _135_52 = (FStar_Options.get_fstar_home ())
in (Prims.strcat _135_52 "/"))
in (Prims.strcat _135_53 FStar_Options.cache_dir))
in (Prims.strcat _135_54 "/"))
in (Prims.strcat _135_55 fn))
in (
# 76 "FStar.Parser.Driver.fst"
let m = (let _135_56 = (FStar_Util.get_oreader full_name)
in (FStar_Absyn_SSyntax.deserialize_modul _135_56))
in (let _135_57 = (FStar_Parser_Desugar.add_modul_to_env m env)
in (_135_57, (m)::[]))))
end else begin
(let _135_58 = (parse_file_raw fn)
in (FStar_Parser_Desugar.desugar_file env _135_58))
end)




