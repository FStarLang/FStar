
open Prims

let one_toplevel : FStar_Parser_AST.decl Prims.list  ->  (FStar_Parser_AST.decl * FStar_Parser_AST.decl Prims.list) Prims.option = (fun decls -> (

let uu____10 = (FStar_List.partition (fun d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.TopLevelModule (uu____16) -> begin
true
end
| uu____17 -> begin
false
end)) decls)
in (match (uu____10) with
| (top, nontops) -> begin
(match (top) with
| (t)::[] -> begin
Some (((t), (nontops)))
end
| uu____37 -> begin
None
end)
end)))

type mforest =
| Leaf of (Prims.string * Prims.string)
| Branch of mforest FStar_Util.smap


let uu___is_Leaf : mforest  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Leaf (_0) -> begin
true
end
| uu____57 -> begin
false
end))


let __proj__Leaf__item___0 : mforest  ->  (Prims.string * Prims.string) = (fun projectee -> (match (projectee) with
| Leaf (_0) -> begin
_0
end))


let uu___is_Branch : mforest  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Branch (_0) -> begin
true
end
| uu____76 -> begin
false
end))


let __proj__Branch__item___0 : mforest  ->  mforest FStar_Util.smap = (fun projectee -> (match (projectee) with
| Branch (_0) -> begin
_0
end))


let htree : mforest FStar_Util.smap = (FStar_Util.smap_create (Prims.parse_int "50"))


let string_of_optiont = (fun f y xo -> (match (xo) with
| Some (x) -> begin
(f x)
end
| None -> begin
y
end))


let string_of_fsdoco : FStar_Syntax_Syntax.fsdoc Prims.option  ->  Prims.string = (fun d -> (string_of_optiont (fun x -> (

let uu____121 = (

let uu____122 = (FStar_Syntax_Syntax.string_of_fsdoc x)
in (Prims.strcat uu____122 "*)"))
in (Prims.strcat "(*" uu____121))) "" d))


let string_of_termo : FStar_Parser_AST.term Prims.option  ->  Prims.string = (fun t -> (string_of_optiont FStar_Parser_AST.term_to_string "" t))


let code_wrap : Prims.string  ->  Prims.string = (fun s -> (Prims.strcat "```fsharp\n" (Prims.strcat s "\n```\n")))


let string_of_tycon : FStar_Parser_AST.tycon  ->  Prims.string = (fun tycon -> (match (tycon) with
| FStar_Parser_AST.TyconAbstract (uu____134) -> begin
"abstract"
end
| FStar_Parser_AST.TyconAbbrev (uu____140) -> begin
"abbrev"
end
| FStar_Parser_AST.TyconRecord (id, _bb, _ko, fields) -> begin
(

let uu____165 = (

let uu____166 = (

let uu____167 = (

let uu____168 = (FStar_All.pipe_right fields (FStar_List.map (fun uu____180 -> (match (uu____180) with
| (id1, t, doco) -> begin
(

let uu____190 = (string_of_fsdoco doco)
in (

let uu____191 = (

let uu____192 = (

let uu____193 = (FStar_Parser_AST.term_to_string t)
in (Prims.strcat ":" uu____193))
in (Prims.strcat id1.FStar_Ident.idText uu____192))
in (Prims.strcat uu____190 uu____191)))
end))))
in (FStar_All.pipe_right uu____168 (FStar_String.concat "; ")))
in (Prims.strcat uu____167 " }"))
in (Prims.strcat " = { " uu____166))
in (Prims.strcat id.FStar_Ident.idText uu____165))
end
| FStar_Parser_AST.TyconVariant (id, _bb, _ko, vars) -> begin
(

let uu____217 = (

let uu____218 = (

let uu____219 = (FStar_All.pipe_right vars (FStar_List.map (fun uu____235 -> (match (uu____235) with
| (id1, trmo, doco, u) -> begin
(

let uu____250 = (string_of_fsdoco doco)
in (

let uu____251 = (

let uu____252 = (

let uu____253 = (string_of_optiont FStar_Parser_AST.term_to_string "" trmo)
in (Prims.strcat ":" uu____253))
in (Prims.strcat id1.FStar_Ident.idText uu____252))
in (Prims.strcat uu____250 uu____251)))
end))))
in (FStar_All.pipe_right uu____219 (FStar_String.concat " | ")))
in (Prims.strcat " = " uu____218))
in (Prims.strcat id.FStar_Ident.idText uu____217))
end))


let string_of_decl' : FStar_Parser_AST.decl'  ->  Prims.string = (fun d -> (match (d) with
| FStar_Parser_AST.TopLevelModule (l) -> begin
(Prims.strcat "module " l.FStar_Ident.str)
end
| FStar_Parser_AST.Open (l) -> begin
(Prims.strcat "open " l.FStar_Ident.str)
end
| FStar_Parser_AST.Include (l) -> begin
(Prims.strcat "include " l.FStar_Ident.str)
end
| FStar_Parser_AST.ModuleAbbrev (i, l) -> begin
(Prims.strcat "module " (Prims.strcat i.FStar_Ident.idText (Prims.strcat " = " l.FStar_Ident.str)))
end
| FStar_Parser_AST.TopLevelLet (uu____263, pats) -> begin
(

let termty = (FStar_List.map (fun uu____279 -> (match (uu____279) with
| (p, t) -> begin
(

let uu____286 = (FStar_Parser_AST.pat_to_string p)
in (

let uu____287 = (FStar_Parser_AST.term_to_string t)
in ((uu____286), (uu____287))))
end)) pats)
in (

let termty' = (FStar_List.map (fun uu____292 -> (match (uu____292) with
| (p, t) -> begin
(Prims.strcat p (Prims.strcat ":" t))
end)) termty)
in (Prims.strcat "let " (FStar_String.concat ", " termty'))))
end
| FStar_Parser_AST.Main (uu____297) -> begin
"main ..."
end
| FStar_Parser_AST.Assume (i, t) -> begin
(

let uu____300 = (

let uu____301 = (

let uu____302 = (FStar_Parser_AST.term_to_string t)
in (Prims.strcat ":" uu____302))
in (Prims.strcat i.FStar_Ident.idText uu____301))
in (Prims.strcat "assume " uu____300))
end
| FStar_Parser_AST.Tycon (uu____303, tys) -> begin
(

let uu____313 = (

let uu____314 = (FStar_All.pipe_right tys (FStar_List.map (fun uu____324 -> (match (uu____324) with
| (t, d1) -> begin
(

let uu____332 = (string_of_tycon t)
in (

let uu____333 = (

let uu____334 = (string_of_fsdoco d1)
in (Prims.strcat " " uu____334))
in (Prims.strcat uu____332 uu____333)))
end))))
in (FStar_All.pipe_right uu____314 (FStar_String.concat " and ")))
in (Prims.strcat "type " uu____313))
end
| FStar_Parser_AST.Val (i, t) -> begin
(

let uu____338 = (

let uu____339 = (

let uu____340 = (FStar_Parser_AST.term_to_string t)
in (Prims.strcat ":" uu____340))
in (Prims.strcat i.FStar_Ident.idText uu____339))
in (Prims.strcat "val " uu____338))
end
| FStar_Parser_AST.Exception (i, uu____342) -> begin
(Prims.strcat "exception " i.FStar_Ident.idText)
end
| (FStar_Parser_AST.NewEffect (FStar_Parser_AST.DefineEffect (i, _, _, _))) | (FStar_Parser_AST.NewEffect (FStar_Parser_AST.RedefineEffect (i, _, _))) -> begin
(Prims.strcat "new_effect " i.FStar_Ident.idText)
end
| FStar_Parser_AST.SubEffect (uu____354) -> begin
"sub_effect"
end
| FStar_Parser_AST.Pragma (uu____355) -> begin
"pragma"
end
| FStar_Parser_AST.Fsdoc (comm, uu____357) -> begin
comm
end))


let decl_documented : FStar_Parser_AST.decl  ->  Prims.bool = (fun d -> (

let tycon_documented = (fun tt -> (

let tyconvars_documented = (fun tycon -> (match (tycon) with
| (FStar_Parser_AST.TyconAbstract (_)) | (FStar_Parser_AST.TyconAbbrev (_)) -> begin
false
end
| FStar_Parser_AST.TyconRecord (uu____385, uu____386, uu____387, fields) -> begin
(FStar_List.existsb (fun uu____407 -> (match (uu____407) with
| (_id, _t, doco) -> begin
(FStar_Util.is_some doco)
end)) fields)
end
| FStar_Parser_AST.TyconVariant (uu____417, uu____418, uu____419, vars) -> begin
(FStar_List.existsb (fun uu____445 -> (match (uu____445) with
| (_id, _t, doco, _u) -> begin
(FStar_Util.is_some doco)
end)) vars)
end))
in (FStar_List.existsb (fun uu____463 -> (match (uu____463) with
| (tycon, doco) -> begin
((tyconvars_documented tycon) || (FStar_Util.is_some doco))
end)) tt)))
in (match (d.FStar_Parser_AST.doc) with
| Some (uu____471) -> begin
true
end
| uu____472 -> begin
(match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Fsdoc (uu____474) -> begin
true
end
| FStar_Parser_AST.Tycon (uu____475, ty) -> begin
(tycon_documented ty)
end
| uu____485 -> begin
false
end)
end)))


let document_decl : (Prims.string  ->  Prims.unit)  ->  FStar_Parser_AST.decl  ->  Prims.unit = (fun w d -> (match ((decl_documented d)) with
| true -> begin
(

let uu____497 = d
in (match (uu____497) with
| {FStar_Parser_AST.d = decl; FStar_Parser_AST.drange = uu____499; FStar_Parser_AST.doc = fsdoc; FStar_Parser_AST.quals = uu____501; FStar_Parser_AST.attrs = uu____502} -> begin
((

let uu____505 = (

let uu____506 = (string_of_decl' d.FStar_Parser_AST.d)
in (code_wrap uu____506))
in (w uu____505));
(match (fsdoc) with
| Some (doc1, _kw) -> begin
(w (Prims.strcat "\n" doc1))
end
| uu____521 -> begin
()
end);
(w "");
)
end))
end
| uu____523 -> begin
()
end))


let document_toplevel = (fun name topdecl -> (match (topdecl.FStar_Parser_AST.d) with
| FStar_Parser_AST.TopLevelModule (uu____540) -> begin
(match (topdecl.FStar_Parser_AST.doc) with
| Some (doc1, kw) -> begin
(

let uu____558 = (FStar_List.tryFind (fun uu____564 -> (match (uu____564) with
| (k, v1) -> begin
(k = "summary")
end)) kw)
in (match (uu____558) with
| None -> begin
((None), (Some (doc1)))
end
| Some (uu____577, summary) -> begin
((Some (summary)), (Some (doc1)))
end))
end
| None -> begin
((None), (None))
end)
end
| uu____585 -> begin
(Prims.raise (FStar_Errors.Err ("Not a TopLevelModule")))
end))


let document_module : FStar_Parser_AST.modul  ->  FStar_Ident.lid = (fun m -> (

let uu____593 = (match (m) with
| FStar_Parser_AST.Module (n1, d) -> begin
((n1), (d), ("module"))
end
| FStar_Parser_AST.Interface (n1, d, uu____609) -> begin
((n1), (d), ("interface"))
end)
in (match (uu____593) with
| (name, decls, _mt) -> begin
(

let uu____618 = (one_toplevel decls)
in (match (uu____618) with
| Some (top_decl, other_decls) -> begin
(

let on = (FStar_Options.prepend_output_dir (Prims.strcat name.FStar_Ident.str ".md"))
in (

let fd = (FStar_Util.open_file_for_writing on)
in (

let w = (FStar_Util.append_to_file fd)
in (

let no_summary = "fsdoc: no-summary-found"
in (

let no_comment = "fsdoc: no-comment-found"
in (

let uu____637 = (document_toplevel name top_decl)
in (match (uu____637) with
| (summary, comment) -> begin
(

let summary1 = (match (summary) with
| Some (s) -> begin
s
end
| None -> begin
no_summary
end)
in (

let comment1 = (match (comment) with
| Some (s) -> begin
s
end
| None -> begin
no_comment
end)
in ((

let uu____653 = (FStar_Util.format "# module %s" ((name.FStar_Ident.str)::[]))
in (w uu____653));
(

let uu____655 = (FStar_Util.format "%s\n" ((summary1)::[]))
in (w uu____655));
(

let uu____657 = (FStar_Util.format "%s\n" ((comment1)::[]))
in (w uu____657));
(FStar_List.iter (document_decl w) other_decls);
(FStar_Util.close_file fd);
name;
)))
end)))))))
end
| None -> begin
(

let uu____663 = (

let uu____664 = (FStar_Util.format1 "No singleton toplevel in module %s" name.FStar_Ident.str)
in FStar_Errors.Err (uu____664))
in (Prims.raise uu____663))
end))
end)))


let generate : Prims.string Prims.list  ->  Prims.unit = (fun files -> (

let modules = (FStar_List.collect (fun fn -> (

let uu____673 = (FStar_Parser_Driver.parse_file fn)
in (Prims.fst uu____673))) files)
in (

let mods = (FStar_List.map document_module modules)
in (

let on = (FStar_Options.prepend_output_dir "index.md")
in (

let fd = (FStar_Util.open_file_for_writing on)
in ((FStar_List.iter (fun m -> (

let uu____688 = (FStar_Util.format "%s\n" ((m.FStar_Ident.str)::[]))
in (FStar_Util.append_to_file fd uu____688))) mods);
(FStar_Util.close_file fd);
))))))




