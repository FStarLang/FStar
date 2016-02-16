
open Prims
# 29 "FStar.Parser.Driver.fst"
let is_cache_file : Prims.string  ->  Prims.bool = (fun fn -> ((FStar_Util.get_file_extension fn) = ".cache"))

# 31 "FStar.Parser.Driver.fst"
type fragment =
| Empty
| Modul of (FStar_Parser_DesugarEnv.env * FStar_Absyn_Syntax.modul)
| Decls of (FStar_Parser_DesugarEnv.env * FStar_Absyn_Syntax.sigelts)

# 32 "FStar.Parser.Driver.fst"
let is_Empty = (fun _discr_ -> (match (_discr_) with
| Empty (_) -> begin
true
end
| _ -> begin
false
end))

# 33 "FStar.Parser.Driver.fst"
let is_Modul = (fun _discr_ -> (match (_discr_) with
| Modul (_) -> begin
true
end
| _ -> begin
false
end))

# 34 "FStar.Parser.Driver.fst"
let is_Decls = (fun _discr_ -> (match (_discr_) with
| Decls (_) -> begin
true
end
| _ -> begin
false
end))

# 33 "FStar.Parser.Driver.fst"
let ___Modul____0 : fragment  ->  (FStar_Parser_DesugarEnv.env * FStar_Absyn_Syntax.modul) = (fun projectee -> (match (projectee) with
| Modul (_56_4) -> begin
_56_4
end))

# 34 "FStar.Parser.Driver.fst"
let ___Decls____0 : fragment  ->  (FStar_Parser_DesugarEnv.env * FStar_Absyn_Syntax.sigelts) = (fun projectee -> (match (projectee) with
| Decls (_56_7) -> begin
_56_7
end))

# 36 "FStar.Parser.Driver.fst"
let parse_fragment : FStar_Absyn_Syntax.modul Prims.option  ->  FStar_Parser_DesugarEnv.env  ->  Prims.string  ->  fragment = (fun curmod env frag -> (match ((FStar_Parser_ParseIt.parse (FStar_Util.Inr (frag)))) with
| FStar_Util.Inl (FStar_Util.Inl ([])) -> begin
Empty
end
| FStar_Util.Inl (FStar_Util.Inl (modul::[])) -> begin
(
# 42 "FStar.Parser.Driver.fst"
let _56_20 = (FStar_Parser_Desugar.desugar_partial_modul curmod env modul)
in (match (_56_20) with
| (env, modul) -> begin
Modul ((env, modul))
end))
end
| FStar_Util.Inl (FStar_Util.Inr (decls)) -> begin
(let _135_38 = (FStar_Parser_Desugar.desugar_decls env decls)
in Decls (_135_38))
end
| FStar_Util.Inl (FStar_Util.Inl (_56_25)) -> begin
(Prims.raise (FStar_Absyn_Syntax.Err ("Refusing to check more than one module at a time incrementally")))
end
| FStar_Util.Inr (msg, r) -> begin
(Prims.raise (FStar_Absyn_Syntax.Error ((msg, r))))
end))

# 55 "FStar.Parser.Driver.fst"
let parse_file_raw : Prims.string  ->  FStar_Parser_AST.modul Prims.list = (fun fn -> (match ((FStar_Parser_ParseIt.parse (FStar_Util.Inl (fn)))) with
| FStar_Util.Inl (FStar_Util.Inl (ast)) -> begin
ast
end
| FStar_Util.Inl (FStar_Util.Inr (_56_37)) -> begin
(
# 61 "FStar.Parser.Driver.fst"
let _56_40 = (FStar_Util.print1_error "%s: expected a module\n" fn)
in (FStar_All.exit 1))
end
| FStar_Util.Inr (msg, r) -> begin
(
# 65 "FStar.Parser.Driver.fst"
let _56_46 = (let _135_41 = (FStar_Absyn_Print.format_error r msg)
in (FStar_All.pipe_left FStar_Util.print_string _135_41))
in (FStar_All.exit 1))
end))

# 71 "FStar.Parser.Driver.fst"
let parse_file : FStar_Parser_DesugarEnv.env  ->  Prims.string  ->  (FStar_Parser_DesugarEnv.env * FStar_Absyn_Syntax.modul Prims.list) = (fun env fn -> if (is_cache_file fn) then begin
(
# 73 "FStar.Parser.Driver.fst"
let full_name = (let _135_49 = (let _135_48 = (let _135_47 = (let _135_46 = (FStar_Options.get_fstar_home ())
in (Prims.strcat _135_46 "/"))
in (Prims.strcat _135_47 FStar_Options.cache_dir))
in (Prims.strcat _135_48 "/"))
in (Prims.strcat _135_49 fn))
in (
# 74 "FStar.Parser.Driver.fst"
let m = (let _135_50 = (FStar_Util.get_oreader full_name)
in (FStar_Absyn_SSyntax.deserialize_modul _135_50))
in (let _135_51 = (FStar_Parser_Desugar.add_modul_to_env m env)
in (_135_51, (m)::[]))))
end else begin
(let _135_52 = (parse_file_raw fn)
in (FStar_Parser_Desugar.desugar_file env _135_52))
end)




