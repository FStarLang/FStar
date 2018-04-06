
open Prims
open FStar_Pervasives

let is_cache_file : Prims.string  ->  Prims.bool = (fun fn -> (

let uu____4 = (FStar_Util.get_file_extension fn)
in (Prims.op_Equality uu____4 ".cache")))

type fragment =
| Empty
| Modul of FStar_Parser_AST.modul
| Decls of FStar_Parser_AST.decl Prims.list


let uu___is_Empty : fragment  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Empty -> begin
true
end
| uu____18 -> begin
false
end))


let uu___is_Modul : fragment  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Modul (_0) -> begin
true
end
| uu____23 -> begin
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
| uu____37 -> begin
false
end))


let __proj__Decls__item___0 : fragment  ->  FStar_Parser_AST.decl Prims.list = (fun projectee -> (match (projectee) with
| Decls (_0) -> begin
_0
end))


let parse_fragment : FStar_Parser_ParseIt.input_frag  ->  fragment = (fun frag -> (

let uu____54 = (FStar_Parser_ParseIt.parse (FStar_Parser_ParseIt.Toplevel (frag)))
in (match (uu____54) with
| FStar_Parser_ParseIt.ASTFragment (FStar_Util.Inl (modul), uu____56) -> begin
Modul (modul)
end
| FStar_Parser_ParseIt.ASTFragment (FStar_Util.Inr ([]), uu____77) -> begin
Empty
end
| FStar_Parser_ParseIt.ASTFragment (FStar_Util.Inr (decls), uu____99) -> begin
Decls (decls)
end
| FStar_Parser_ParseIt.ParseError (e, msg, r) -> begin
(FStar_Errors.raise_error ((e), (msg)) r)
end
| FStar_Parser_ParseIt.Term (uu____125) -> begin
(failwith "Impossible: parsing a Toplevel always results in an ASTFragment")
end)))


let parse_file : FStar_Parser_ParseIt.filename  ->  (FStar_Parser_AST.file * (Prims.string * FStar_Range.range) Prims.list) = (fun fn -> (

let uu____139 = (FStar_Parser_ParseIt.parse (FStar_Parser_ParseIt.Filename (fn)))
in (match (uu____139) with
| FStar_Parser_ParseIt.ASTFragment (FStar_Util.Inl (ast), comments) -> begin
((ast), (comments))
end
| FStar_Parser_ParseIt.ASTFragment (FStar_Util.Inr (uu____178), uu____179) -> begin
(

let msg = (FStar_Util.format1 "%s: expected a module\n" fn)
in (

let r = FStar_Range.dummyRange
in (FStar_Errors.raise_error ((FStar_Errors.Fatal_ModuleExpected), (msg)) r)))
end
| FStar_Parser_ParseIt.ParseError (e, msg, r) -> begin
(FStar_Errors.raise_error ((e), (msg)) r)
end
| FStar_Parser_ParseIt.Term (uu____227) -> begin
(failwith "Impossible: parsing a Filename always results in an ASTFragment")
end)))




