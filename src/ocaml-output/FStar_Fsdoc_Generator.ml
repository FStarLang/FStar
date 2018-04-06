
open Prims
open FStar_Pervasives

let one_toplevel : FStar_Parser_AST.decl Prims.list  ->  (FStar_Parser_AST.decl * FStar_Parser_AST.decl Prims.list) FStar_Pervasives_Native.option = (fun decls -> (

let uu____16 = (FStar_List.partition (fun d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.TopLevelModule (uu____28) -> begin
true
end
| uu____29 -> begin
false
end)) decls)
in (match (uu____16) with
| (top, nontops) -> begin
(match (top) with
| (t)::[] -> begin
FStar_Pervasives_Native.Some (((t), (nontops)))
end
| uu____65 -> begin
FStar_Pervasives_Native.None
end)
end)))

type mforest =
| Leaf of (Prims.string * Prims.string)
| Branch of mforest FStar_Util.smap


let uu___is_Leaf : mforest  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Leaf (_0) -> begin
true
end
| uu____96 -> begin
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
| uu____122 -> begin
false
end))


let __proj__Branch__item___0 : mforest  ->  mforest FStar_Util.smap = (fun projectee -> (match (projectee) with
| Branch (_0) -> begin
_0
end))


let htree : mforest FStar_Util.smap = (FStar_Util.smap_create (Prims.parse_int "50"))


let string_of_optiont : 'Auu____143 'Auu____144 . ('Auu____143  ->  'Auu____144)  ->  'Auu____144  ->  'Auu____143 FStar_Pervasives_Native.option  ->  'Auu____144 = (fun f y xo -> (match (xo) with
| FStar_Pervasives_Native.Some (x) -> begin
(f x)
end
| FStar_Pervasives_Native.None -> begin
y
end))


let string_of_fsdoco : (Prims.string * (Prims.string * Prims.string) Prims.list) FStar_Pervasives_Native.option  ->  Prims.string = (fun d -> (string_of_optiont (fun x -> (

let uu____217 = (

let uu____218 = (FStar_Parser_AST.string_of_fsdoc x)
in (Prims.strcat uu____218 "*)"))
in (Prims.strcat "(*" uu____217))) "" d))


let string_of_termo : FStar_Parser_AST.term FStar_Pervasives_Native.option  ->  Prims.string = (fun t -> (string_of_optiont FStar_Parser_AST.term_to_string "" t))


let code_wrap : Prims.string  ->  Prims.string = (fun s -> (Prims.strcat "```fsharp\n" (Prims.strcat s "\n```\n")))


let string_of_tycon : FStar_Parser_AST.tycon  ->  Prims.string = (fun tycon -> (match (tycon) with
| FStar_Parser_AST.TyconAbstract (uu____232) -> begin
"abstract"
end
| FStar_Parser_AST.TyconAbbrev (uu____243) -> begin
"abbrev"
end
| FStar_Parser_AST.TyconRecord (id1, _bb, _ko, fields) -> begin
(

let uu____288 = (

let uu____289 = (

let uu____290 = (

let uu____291 = (FStar_All.pipe_right fields (FStar_List.map (fun uu____330 -> (match (uu____330) with
| (id2, t, doco) -> begin
(

let uu____376 = (string_of_fsdoco doco)
in (

let uu____377 = (

let uu____378 = (

let uu____379 = (FStar_Parser_AST.term_to_string t)
in (Prims.strcat ":" uu____379))
in (Prims.strcat id2.FStar_Ident.idText uu____378))
in (Prims.strcat uu____376 uu____377)))
end))))
in (FStar_All.pipe_right uu____291 (FStar_String.concat "; ")))
in (Prims.strcat uu____290 " }"))
in (Prims.strcat " = { " uu____289))
in (Prims.strcat id1.FStar_Ident.idText uu____288))
end
| FStar_Parser_AST.TyconVariant (id1, _bb, _ko, vars) -> begin
(

let uu____422 = (

let uu____423 = (

let uu____424 = (FStar_All.pipe_right vars (FStar_List.map (fun uu____472 -> (match (uu____472) with
| (id2, trmo, doco, u) -> begin
(

let uu____527 = (string_of_fsdoco doco)
in (

let uu____528 = (

let uu____529 = (

let uu____530 = (string_of_optiont FStar_Parser_AST.term_to_string "" trmo)
in (Prims.strcat ":" uu____530))
in (Prims.strcat id2.FStar_Ident.idText uu____529))
in (Prims.strcat uu____527 uu____528)))
end))))
in (FStar_All.pipe_right uu____424 (FStar_String.concat " | ")))
in (Prims.strcat " = " uu____423))
in (Prims.strcat id1.FStar_Ident.idText uu____422))
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
| FStar_Parser_AST.TopLevelLet (uu____541, pats) -> begin
(

let termty = (FStar_List.map (fun uu____575 -> (match (uu____575) with
| (p, t) -> begin
(

let uu____586 = (FStar_Parser_AST.pat_to_string p)
in (

let uu____587 = (FStar_Parser_AST.term_to_string t)
in ((uu____586), (uu____587))))
end)) pats)
in (

let termty' = (FStar_List.map (fun uu____598 -> (match (uu____598) with
| (p, t) -> begin
(Prims.strcat p (Prims.strcat ":" t))
end)) termty)
in (Prims.strcat "let " (FStar_String.concat ", " termty'))))
end
| FStar_Parser_AST.Main (uu____605) -> begin
"main ..."
end
| FStar_Parser_AST.Assume (i, t) -> begin
(

let uu____608 = (

let uu____609 = (

let uu____610 = (FStar_Parser_AST.term_to_string t)
in (Prims.strcat ":" uu____610))
in (Prims.strcat i.FStar_Ident.idText uu____609))
in (Prims.strcat "assume " uu____608))
end
| FStar_Parser_AST.Tycon (uu____611, tys) -> begin
(

let uu____629 = (

let uu____630 = (FStar_All.pipe_right tys (FStar_List.map (fun uu____664 -> (match (uu____664) with
| (t, d1) -> begin
(

let uu____707 = (string_of_tycon t)
in (

let uu____708 = (

let uu____709 = (string_of_fsdoco d1)
in (Prims.strcat " " uu____709))
in (Prims.strcat uu____707 uu____708)))
end))))
in (FStar_All.pipe_right uu____630 (FStar_String.concat " and ")))
in (Prims.strcat "type " uu____629))
end
| FStar_Parser_AST.Val (i, t) -> begin
(

let uu____714 = (

let uu____715 = (

let uu____716 = (FStar_Parser_AST.term_to_string t)
in (Prims.strcat ":" uu____716))
in (Prims.strcat i.FStar_Ident.idText uu____715))
in (Prims.strcat "val " uu____714))
end
| FStar_Parser_AST.Exception (i, uu____718) -> begin
(Prims.strcat "exception " i.FStar_Ident.idText)
end
| FStar_Parser_AST.NewEffect (FStar_Parser_AST.DefineEffect (i, uu____724, uu____725, uu____726)) -> begin
(Prims.strcat "new_effect " i.FStar_Ident.idText)
end
| FStar_Parser_AST.NewEffect (FStar_Parser_AST.RedefineEffect (i, uu____736, uu____737)) -> begin
(Prims.strcat "new_effect " i.FStar_Ident.idText)
end
| FStar_Parser_AST.SubEffect (uu____742) -> begin
"sub_effect"
end
| FStar_Parser_AST.Pragma (uu____743) -> begin
"pragma"
end
| FStar_Parser_AST.Splice (t) -> begin
(

let uu____745 = (FStar_Parser_AST.term_to_string t)
in (Prims.strcat "splice " uu____745))
end
| FStar_Parser_AST.Fsdoc (comm, uu____747) -> begin
comm
end))


let decl_documented : FStar_Parser_AST.decl  ->  Prims.bool = (fun d -> (

let tycon_documented = (fun tt -> (

let tyconvars_documented = (fun tycon -> (match (tycon) with
| FStar_Parser_AST.TyconAbstract (uu____787) -> begin
false
end
| FStar_Parser_AST.TyconAbbrev (uu____798) -> begin
false
end
| FStar_Parser_AST.TyconRecord (uu____811, uu____812, uu____813, fields) -> begin
(FStar_List.existsb (fun uu____855 -> (match (uu____855) with
| (_id, _t, doco) -> begin
(FStar_Util.is_some doco)
end)) fields)
end
| FStar_Parser_AST.TyconVariant (uu____871, uu____872, uu____873, vars) -> begin
(FStar_List.existsb (fun uu____928 -> (match (uu____928) with
| (_id, _t, doco, _u) -> begin
(FStar_Util.is_some doco)
end)) vars)
end))
in (FStar_List.existsb (fun uu____962 -> (match (uu____962) with
| (tycon, doco) -> begin
((tyconvars_documented tycon) || (FStar_Util.is_some doco))
end)) tt)))
in (match (d.FStar_Parser_AST.doc) with
| FStar_Pervasives_Native.Some (uu____975) -> begin
true
end
| uu____976 -> begin
(match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Fsdoc (uu____979) -> begin
true
end
| FStar_Parser_AST.Tycon (uu____980, ty) -> begin
(tycon_documented ty)
end
| uu____998 -> begin
false
end)
end)))


let document_decl : (Prims.string  ->  Prims.unit)  ->  FStar_Parser_AST.decl  ->  Prims.unit = (fun w d -> (match ((decl_documented d)) with
| true -> begin
(

let uu____1010 = d
in (match (uu____1010) with
| {FStar_Parser_AST.d = decl; FStar_Parser_AST.drange = uu____1012; FStar_Parser_AST.doc = fsdoc; FStar_Parser_AST.quals = uu____1014; FStar_Parser_AST.attrs = uu____1015} -> begin
((

let uu____1019 = (

let uu____1020 = (string_of_decl' d.FStar_Parser_AST.d)
in (code_wrap uu____1020))
in (w uu____1019));
(match (fsdoc) with
| FStar_Pervasives_Native.Some (doc1, _kw) -> begin
(w (Prims.strcat "\n" doc1))
end
| uu____1046 -> begin
()
end);
(w "");
)
end))
end
| uu____1049 -> begin
()
end))


let document_toplevel : 'Auu____1053 . 'Auu____1053  ->  FStar_Parser_AST.decl  ->  (Prims.string FStar_Pervasives_Native.option * Prims.string FStar_Pervasives_Native.option) = (fun name topdecl -> (match (topdecl.FStar_Parser_AST.d) with
| FStar_Parser_AST.TopLevelModule (uu____1070) -> begin
(match (topdecl.FStar_Parser_AST.doc) with
| FStar_Pervasives_Native.Some (doc1, kw) -> begin
(

let uu____1103 = (FStar_List.tryFind (fun uu____1117 -> (match (uu____1117) with
| (k, v1) -> begin
(Prims.op_Equality k "summary")
end)) kw)
in (match (uu____1103) with
| FStar_Pervasives_Native.None -> begin
((FStar_Pervasives_Native.None), (FStar_Pervasives_Native.Some (doc1)))
end
| FStar_Pervasives_Native.Some (uu____1140, summary) -> begin
((FStar_Pervasives_Native.Some (summary)), (FStar_Pervasives_Native.Some (doc1)))
end))
end
| FStar_Pervasives_Native.None -> begin
((FStar_Pervasives_Native.None), (FStar_Pervasives_Native.None))
end)
end
| uu____1154 -> begin
(FStar_Errors.raise_err ((FStar_Errors.Fatal_NotTopLevelModule), ("Not Top-level Module")))
end))


let document_module : FStar_Parser_AST.modul  ->  FStar_Ident.lid = (fun m -> (

let uu____1166 = (match (m) with
| FStar_Parser_AST.Module (n1, d) -> begin
((n1), (d), ("module"))
end
| FStar_Parser_AST.Interface (n1, d, uu____1193) -> begin
((n1), (d), ("interface"))
end)
in (match (uu____1166) with
| (name, decls, _mt) -> begin
(

let uu____1207 = (one_toplevel decls)
in (match (uu____1207) with
| FStar_Pervasives_Native.Some (top_decl, other_decls) -> begin
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

let uu____1235 = (document_toplevel name top_decl)
in (match (uu____1235) with
| (summary, comment) -> begin
(

let summary1 = (match (summary) with
| FStar_Pervasives_Native.Some (s) -> begin
s
end
| FStar_Pervasives_Native.None -> begin
no_summary
end)
in (

let comment1 = (match (comment) with
| FStar_Pervasives_Native.Some (s) -> begin
s
end
| FStar_Pervasives_Native.None -> begin
no_comment
end)
in ((

let uu____1259 = (FStar_Util.format "# module %s" ((name.FStar_Ident.str)::[]))
in (w uu____1259));
(

let uu____1261 = (FStar_Util.format "%s\n" ((summary1)::[]))
in (w uu____1261));
(

let uu____1263 = (FStar_Util.format "%s\n" ((comment1)::[]))
in (w uu____1263));
(FStar_List.iter (document_decl w) other_decls);
(FStar_Util.close_file fd);
name;
)))
end)))))))
end
| FStar_Pervasives_Native.None -> begin
(

let uu____1272 = (

let uu____1277 = (FStar_Util.format1 "No singleton toplevel in module %s" name.FStar_Ident.str)
in ((FStar_Errors.Fatal_NonSingletonTopLevel), (uu____1277)))
in (FStar_Errors.raise_err uu____1272))
end))
end)))


let generate : Prims.string Prims.list  ->  Prims.unit = (fun files -> (

let modules = (FStar_List.map (fun fn -> (

let uu____1291 = (FStar_Parser_Driver.parse_file fn)
in (FStar_Pervasives_Native.fst uu____1291))) files)
in (

let mods = (FStar_List.map document_module modules)
in (

let on = (FStar_Options.prepend_output_dir "index.md")
in (

let fd = (FStar_Util.open_file_for_writing on)
in ((FStar_List.iter (fun m -> (

let uu____1317 = (FStar_Util.format "%s\n" ((m.FStar_Ident.str)::[]))
in (FStar_Util.append_to_file fd uu____1317))) mods);
(FStar_Util.close_file fd);
))))))




