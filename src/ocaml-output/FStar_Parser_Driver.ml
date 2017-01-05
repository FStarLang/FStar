
open Prims

let is_cache_file : Prims.string  ->  Prims.bool = (fun fn -> ((FStar_Util.get_file_extension fn) = ".cache"))


type fragment =
| Empty
| Modul of FStar_Parser_AST.modul
| Decls of FStar_Parser_AST.decl Prims.list


let is_Empty = (fun _discr_ -> (match (_discr_) with
| Empty (_) -> begin
true
end
| _ -> begin
false
end))


let is_Modul = (fun _discr_ -> (match (_discr_) with
| Modul (_) -> begin
true
end
| _ -> begin
false
end))


let is_Decls = (fun _discr_ -> (match (_discr_) with
| Decls (_) -> begin
true
end
| _ -> begin
false
end))


let ___Modul____0 = (fun projectee -> (match (projectee) with
| Modul (_72_4) -> begin
_72_4
end))


let ___Decls____0 = (fun projectee -> (match (projectee) with
| Decls (_72_7) -> begin
_72_7
end))


let parse_fragment : FStar_Parser_ParseIt.input_frag  ->  fragment = (fun frag -> (match ((FStar_Parser_ParseIt.parse (FStar_Util.Inr (frag)))) with
| FStar_Util.Inl (FStar_Util.Inl ([]), _72_12) -> begin
Empty
end
| FStar_Util.Inl (FStar_Util.Inl ((modul)::[]), _72_19) -> begin
Modul (modul)
end
| FStar_Util.Inl (FStar_Util.Inr (decls), _72_25) -> begin
Decls (decls)
end
| FStar_Util.Inl (FStar_Util.Inl (_72_29), _72_32) -> begin
if (FStar_Options.universes ()) then begin
(Prims.raise (FStar_Syntax_Syntax.Err ("Refusing to check more than one module at a time incrementally")))
end else begin
(Prims.raise (FStar_Absyn_Syntax.Err ("Refusing to check more than one module at a time incrementally")))
end
end
| FStar_Util.Inr (msg, r) -> begin
if (FStar_Options.universes ()) then begin
(Prims.raise (FStar_Syntax_Syntax.Error (((msg), (r)))))
end else begin
(Prims.raise (FStar_Absyn_Syntax.Error (((msg), (r)))))
end
end))


let parse_file : FStar_Parser_ParseIt.filename  ->  (FStar_Parser_AST.modul Prims.list * (Prims.string * FStar_Range.range) Prims.list) = (fun fn -> (match ((FStar_Parser_ParseIt.parse (FStar_Util.Inl (fn)))) with
| FStar_Util.Inl (FStar_Util.Inl (ast), comments) -> begin
((ast), (comments))
end
| FStar_Util.Inl (FStar_Util.Inr (_72_46), _72_49) -> begin
(

let msg = (FStar_Util.format1 "%s: expected a module\n" fn)
in (

let r = FStar_Range.dummyRange
in if (FStar_Options.universes ()) then begin
(Prims.raise (FStar_Syntax_Syntax.Error (((msg), (r)))))
end else begin
(Prims.raise (FStar_Absyn_Syntax.Error (((msg), (r)))))
end))
end
| FStar_Util.Inr (msg, r) -> begin
if (FStar_Options.universes ()) then begin
(Prims.raise (FStar_Syntax_Syntax.Error (((msg), (r)))))
end else begin
(Prims.raise (FStar_Absyn_Syntax.Error (((msg), (r)))))
end
end))




