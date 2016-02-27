
open Prims
# 29 "FStar.Parser.Driver.fst"
let is_cache_file : Prims.string  ->  Prims.bool = (fun fn -> ((FStar_Util.get_file_extension fn) = ".cache"))

# 31 "FStar.Parser.Driver.fst"
type fragment =
| Empty
| Modul of FStar_Parser_AST.modul
| Decls of FStar_Parser_AST.decl Prims.list

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
let ___Modul____0 : fragment  ->  FStar_Parser_AST.modul = (fun projectee -> (match (projectee) with
| Modul (_55_4) -> begin
_55_4
end))

# 34 "FStar.Parser.Driver.fst"
let ___Decls____0 : fragment  ->  FStar_Parser_AST.decl Prims.list = (fun projectee -> (match (projectee) with
| Decls (_55_7) -> begin
_55_7
end))

# 36 "FStar.Parser.Driver.fst"
let parse_fragment : Prims.string  ->  fragment = (fun frag -> (match ((FStar_Parser_ParseIt.parse (FStar_Util.Inr (frag)))) with
| FStar_Util.Inl (FStar_Util.Inl ([])) -> begin
Empty
end
| FStar_Util.Inl (FStar_Util.Inl (modul::[])) -> begin
Modul (modul)
end
| FStar_Util.Inl (FStar_Util.Inr (decls)) -> begin
Decls (decls)
end
| FStar_Util.Inl (FStar_Util.Inl (_55_20)) -> begin
(Prims.raise (FStar_Absyn_Syntax.Err ("Refusing to check more than one module at a time incrementally")))
end
| FStar_Util.Inr (msg, r) -> begin
(Prims.raise (FStar_Absyn_Syntax.Error ((msg, r))))
end))

# 62 "FStar.Parser.Driver.fst"
let parse_file : Prims.string  ->  FStar_Parser_AST.modul Prims.list = (fun fn -> (match ((FStar_Parser_ParseIt.parse (FStar_Util.Inl (fn)))) with
| FStar_Util.Inl (FStar_Util.Inl (ast)) -> begin
ast
end
| FStar_Util.Inl (FStar_Util.Inr (_55_32)) -> begin
(
# 68 "FStar.Parser.Driver.fst"
let _55_35 = (FStar_Util.print1_error "%s: expected a module\n" fn)
in (FStar_All.exit 1))
end
| FStar_Util.Inr (msg, r) -> begin
(
# 72 "FStar.Parser.Driver.fst"
let _55_41 = (let _137_36 = (FStar_Absyn_Print.format_error r msg)
in (FStar_All.pipe_left FStar_Util.print_string _137_36))
in (FStar_All.exit 1))
end))




