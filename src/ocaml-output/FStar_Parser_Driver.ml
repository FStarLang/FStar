
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
let ___Modul____0 = (fun projectee -> (match (projectee) with
| Modul (_50_4) -> begin
_50_4
end))

# 34 "FStar.Parser.Driver.fst"
let ___Decls____0 = (fun projectee -> (match (projectee) with
| Decls (_50_7) -> begin
_50_7
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
| FStar_Util.Inl (FStar_Util.Inl (_50_20)) -> begin
if (FStar_ST.read FStar_Options.universes) then begin
(Prims.raise (FStar_Syntax_Syntax.Err ("Refusing to check more than one module at a time incrementally")))
end else begin
(Prims.raise (FStar_Absyn_Syntax.Err ("Refusing to check more than one module at a time incrementally")))
end
end
| FStar_Util.Inr (msg, r) -> begin
if (FStar_ST.read FStar_Options.universes) then begin
(Prims.raise (FStar_Syntax_Syntax.Error ((msg, r))))
end else begin
(Prims.raise (FStar_Absyn_Syntax.Error ((msg, r))))
end
end))

# 66 "FStar.Parser.Driver.fst"
let parse_file : Prims.string  ->  FStar_Parser_AST.modul Prims.list = (fun fn -> (match ((FStar_Parser_ParseIt.parse (FStar_Util.Inl (fn)))) with
| FStar_Util.Inl (FStar_Util.Inl (ast)) -> begin
ast
end
| FStar_Util.Inl (FStar_Util.Inr (_50_32)) -> begin
(
# 72 "FStar.Parser.Driver.fst"
let msg = (FStar_Util.format1 "%s: expected a module\n" fn)
in (
# 73 "FStar.Parser.Driver.fst"
let r = FStar_Range.dummyRange
in if (FStar_ST.read FStar_Options.universes) then begin
(Prims.raise (FStar_Syntax_Syntax.Error ((msg, r))))
end else begin
(Prims.raise (FStar_Absyn_Syntax.Error ((msg, r))))
end))
end
| FStar_Util.Inr (msg, r) -> begin
if (FStar_ST.read FStar_Options.universes) then begin
(Prims.raise (FStar_Syntax_Syntax.Error ((msg, r))))
end else begin
(Prims.raise (FStar_Absyn_Syntax.Error ((msg, r))))
end
end))




