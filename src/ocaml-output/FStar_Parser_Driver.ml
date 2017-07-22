
open Prims
open FStar_Pervasives

let is_cache_file : Prims.string  ->  Prims.bool = (fun fn -> (

let uu____5 = (FStar_Util.get_file_extension fn)
in (uu____5 = ".cache")))

type fragment =
| Empty
| Modul of FStar_Parser_AST.modul
| Decls of FStar_Parser_AST.decl Prims.list


let uu___is_Empty : fragment  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Empty -> begin
true
end
| uu____20 -> begin
false
end))


let uu___is_Modul : fragment  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Modul (_0) -> begin
true
end
| uu____26 -> begin
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
| uu____42 -> begin
false
end))


let __proj__Decls__item___0 : fragment  ->  FStar_Parser_AST.decl Prims.list = (fun projectee -> (match (projectee) with
| Decls (_0) -> begin
_0
end))


let parse_fragment : FStar_Parser_ParseIt.input_frag  ->  fragment = (fun frag -> (

let uu____61 = (FStar_Parser_ParseIt.parse (FStar_Util.Inr (frag)))
in (match (uu____61) with
| FStar_Util.Inl (FStar_Util.Inl ([]), uu____80) -> begin
Empty
end
| FStar_Util.Inl (FStar_Util.Inl ((modul)::[]), uu____128) -> begin
Modul (modul)
end
| FStar_Util.Inl (FStar_Util.Inr (decls), uu____176) -> begin
Decls (decls)
end
| FStar_Util.Inl (FStar_Util.Inl (uu____219), uu____220) -> begin
(FStar_Pervasives.raise (FStar_Errors.Err ("Refusing to check more than one module at a time incrementally")))
end
| FStar_Util.Inr (msg, r) -> begin
(FStar_Pervasives.raise (FStar_Errors.Error (((msg), (r)))))
end)))


let parse_file : FStar_Parser_ParseIt.filename  ->  (FStar_Parser_AST.file * (Prims.string * FStar_Range.range) Prims.list) = (fun fn -> (

let uu____291 = (FStar_Parser_ParseIt.parse (FStar_Util.Inl (fn)))
in (match (uu____291) with
| FStar_Util.Inl (FStar_Util.Inl (ast), comments) -> begin
((ast), (comments))
end
| FStar_Util.Inl (FStar_Util.Inr (uu____368), uu____369) -> begin
(

let msg = (FStar_Util.format1 "%s: expected a module\n" fn)
in (

let r = FStar_Range.dummyRange
in (FStar_Pervasives.raise (FStar_Errors.Error (((msg), (r)))))))
end
| FStar_Util.Inr (msg, r) -> begin
(FStar_Pervasives.raise (FStar_Errors.Error (((msg), (r)))))
end)))




