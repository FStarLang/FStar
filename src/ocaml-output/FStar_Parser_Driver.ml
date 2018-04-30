
open Prims
open FStar_Pervasives

let is_cache_file : Prims.string  ->  Prims.bool = (fun fn -> (

let uu____6 = (FStar_Util.get_file_extension fn)
in (Prims.op_Equality uu____6 ".cache")))

type fragment =
| Empty
| Modul of FStar_Parser_AST.modul
| Decls of FStar_Parser_AST.decl Prims.list


let uu___is_Empty : fragment  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Empty -> begin
true
end
| uu____24 -> begin
false
end))


let uu___is_Modul : fragment  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Modul (_0) -> begin
true
end
| uu____31 -> begin
false
end))


let __proj__Modul__item___0 : fragment  ->  FStar_Parser_AST.modul = (fun projectee -> (match (projectee) with
| Modul (_0) -> begin
_0
end))


let uu___is_Decls : fragment  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Decls (_0) -> begin
true
end
| uu____47 -> begin
false
end))


let __proj__Decls__item___0 : fragment  ->  FStar_Parser_AST.decl Prims.list = (fun projectee -> (match (projectee) with
| Decls (_0) -> begin
_0
end))


let parse_fragment : FStar_Parser_ParseIt.input_frag  ->  fragment = (fun frag -> (

let uu____66 = (FStar_Parser_ParseIt.parse (FStar_Parser_ParseIt.Toplevel (frag)))
in (match (uu____66) with
| FStar_Parser_ParseIt.ASTFragment (FStar_Util.Inl (modul), uu____68) -> begin
Modul (modul)
end
| FStar_Parser_ParseIt.ASTFragment (FStar_Util.Inr ([]), uu____83) -> begin
Empty
end
| FStar_Parser_ParseIt.ASTFragment (FStar_Util.Inr (decls), uu____99) -> begin
Decls (decls)
end
| FStar_Parser_ParseIt.ParseError (e, msg, r) -> begin
(FStar_Errors.raise_error ((e), (msg)) r)
end
| FStar_Parser_ParseIt.Term (uu____119) -> begin
(failwith "Impossible: parsing a Toplevel always results in an ASTFragment")
end)))


let parse_file : Prims.string  ->  (FStar_Parser_AST.file * (Prims.string * FStar_Range.range) Prims.list) = (fun fn -> (

let uu____135 = (FStar_Parser_ParseIt.parse (FStar_Parser_ParseIt.Filename (fn)))
in (match (uu____135) with
| FStar_Parser_ParseIt.ASTFragment (FStar_Util.Inl (ast), comments) -> begin
((ast), (comments))
end
| FStar_Parser_ParseIt.ASTFragment (FStar_Util.Inr (uu____168), uu____169) -> begin
(

let msg = (FStar_Util.format1 "%s: expected a module\n" fn)
in (

let r = FStar_Range.dummyRange
in (FStar_Errors.raise_error ((FStar_Errors.Fatal_ModuleExpected), (msg)) r)))
end
| FStar_Parser_ParseIt.ParseError (e, msg, r) -> begin
(FStar_Errors.raise_error ((e), (msg)) r)
end
| FStar_Parser_ParseIt.Term (uu____211) -> begin
(failwith "Impossible: parsing a Filename always results in an ASTFragment")
end)))




