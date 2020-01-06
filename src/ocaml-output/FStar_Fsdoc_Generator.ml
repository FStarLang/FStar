
open Prims
open FStar_Pervasives

let one_toplevel : FStar_Parser_AST.decl Prims.list  ->  (FStar_Parser_AST.decl * FStar_Parser_AST.decl Prims.list) FStar_Pervasives_Native.option = (fun decls -> (

let uu____17 = (FStar_List.partition (fun d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.TopLevelModule (uu____30) -> begin
true
end
| uu____32 -> begin
false
end)) decls)
in (match (uu____17) with
| (top, nontops) -> begin
(match (top) with
| (t)::[] -> begin
FStar_Pervasives_Native.Some (((t), (nontops)))
end
| uu____69 -> begin
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
| uu____112 -> begin
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
| uu____151 -> begin
false
end))


let __proj__Branch__item___0 : mforest  ->  mforest FStar_Util.smap = (fun projectee -> (match (projectee) with
| Branch (_0) -> begin
_0
end))


let htree : mforest FStar_Util.smap = (FStar_Util.smap_create (Prims.parse_int "50"))


let string_of_optiont : 'Auu____181 'Auu____182 . ('Auu____181  ->  'Auu____182)  ->  'Auu____182  ->  'Auu____181 FStar_Pervasives_Native.option  ->  'Auu____182 = (fun f y xo -> (match (xo) with
| FStar_Pervasives_Native.Some (x) -> begin
(f x)
end
| FStar_Pervasives_Native.None -> begin
y
end))


let string_of_fsdoco : (Prims.string * (Prims.string * Prims.string) Prims.list) FStar_Pervasives_Native.option  ->  Prims.string = (fun d -> (string_of_optiont (fun x -> (

let uu____275 = (

let uu____277 = (FStar_Parser_AST.string_of_fsdoc x)
in (Prims.op_Hat uu____277 "*)"))
in (Prims.op_Hat "(*" uu____275))) "" d))


let string_of_termo : FStar_Parser_AST.term FStar_Pervasives_Native.option  ->  Prims.string = (fun t -> (string_of_optiont FStar_Parser_AST.term_to_string "" t))


let code_wrap : Prims.string  ->  Prims.string = (fun s -> (Prims.op_Hat "```fsharp\n" (Prims.op_Hat s "\n```\n")))


let string_of_tycon : FStar_Parser_AST.tycon  ->  Prims.string = (fun tycon -> (match (tycon) with
| FStar_Parser_AST.TyconAbstract (uu____314) -> begin
"abstract"
end
| FStar_Parser_AST.TyconAbbrev (uu____326) -> begin
"abbrev"
end
| FStar_Parser_AST.TyconRecord (id1, _bb, _ko, fields) -> begin
(

let uu____372 = (

let uu____374 = (

let uu____376 = (

let uu____378 = (FStar_All.pipe_right fields (FStar_List.map (fun uu____436 -> (match (uu____436) with
| (id2, t, doco) -> begin
(

let uu____492 = (string_of_fsdoco doco)
in (

let uu____494 = (

let uu____496 = (

let uu____498 = (FStar_Parser_AST.term_to_string t)
in (Prims.op_Hat ":" uu____498))
in (Prims.op_Hat id2.FStar_Ident.idText uu____496))
in (Prims.op_Hat uu____492 uu____494)))
end))))
in (FStar_All.pipe_right uu____378 (FStar_String.concat "; ")))
in (Prims.op_Hat uu____376 " }"))
in (Prims.op_Hat " = { " uu____374))
in (Prims.op_Hat id1.FStar_Ident.idText uu____372))
end
| FStar_Parser_AST.TyconVariant (id1, _bb, _ko, vars) -> begin
(

let uu____550 = (

let uu____552 = (

let uu____554 = (FStar_All.pipe_right vars (FStar_List.map (fun uu____623 -> (match (uu____623) with
| (id2, trmo, doco, u) -> begin
(

let uu____691 = (string_of_fsdoco doco)
in (

let uu____693 = (

let uu____695 = (

let uu____697 = (string_of_optiont FStar_Parser_AST.term_to_string "" trmo)
in (Prims.op_Hat ":" uu____697))
in (Prims.op_Hat id2.FStar_Ident.idText uu____695))
in (Prims.op_Hat uu____691 uu____693)))
end))))
in (FStar_All.pipe_right uu____554 (FStar_String.concat " | ")))
in (Prims.op_Hat " = " uu____552))
in (Prims.op_Hat id1.FStar_Ident.idText uu____550))
end))


let string_of_decl' : FStar_Parser_AST.decl'  ->  Prims.string = (fun d -> (match (d) with
| FStar_Parser_AST.TopLevelModule (l) -> begin
(Prims.op_Hat "module " l.FStar_Ident.str)
end
| FStar_Parser_AST.Open (l) -> begin
(Prims.op_Hat "open " l.FStar_Ident.str)
end
| FStar_Parser_AST.Include (l) -> begin
(Prims.op_Hat "include " l.FStar_Ident.str)
end
| FStar_Parser_AST.Friend (l) -> begin
(Prims.op_Hat "friend " l.FStar_Ident.str)
end
| FStar_Parser_AST.ModuleAbbrev (i, l) -> begin
(Prims.op_Hat "module " (Prims.op_Hat i.FStar_Ident.idText (Prims.op_Hat " = " l.FStar_Ident.str)))
end
| FStar_Parser_AST.TopLevelLet (uu____728, pats) -> begin
(

let termty = (FStar_List.map (fun uu____766 -> (match (uu____766) with
| (p, t) -> begin
(

let uu____779 = (FStar_Parser_AST.pat_to_string p)
in (

let uu____781 = (FStar_Parser_AST.term_to_string t)
in ((uu____779), (uu____781))))
end)) pats)
in (

let termty' = (FStar_List.map (fun uu____799 -> (match (uu____799) with
| (p, t) -> begin
(Prims.op_Hat p (Prims.op_Hat ":" t))
end)) termty)
in (Prims.op_Hat "let " (FStar_String.concat ", " termty'))))
end
| FStar_Parser_AST.Main (uu____816) -> begin
"main ..."
end
| FStar_Parser_AST.Assume (i, t) -> begin
(

let uu____820 = (

let uu____822 = (

let uu____824 = (FStar_Parser_AST.term_to_string t)
in (Prims.op_Hat ":" uu____824))
in (Prims.op_Hat i.FStar_Ident.idText uu____822))
in (Prims.op_Hat "assume " uu____820))
end
| FStar_Parser_AST.Tycon (uu____828, tc, tys) -> begin
(

let s = (match (tc) with
| true -> begin
"class"
end
| uu____856 -> begin
"type"
end)
in (

let uu____859 = (

let uu____861 = (FStar_All.pipe_right tys (FStar_List.map (fun uu____914 -> (match (uu____914) with
| (t, d1) -> begin
(

let uu____967 = (string_of_tycon t)
in (

let uu____969 = (

let uu____971 = (string_of_fsdoco d1)
in (Prims.op_Hat " " uu____971))
in (Prims.op_Hat uu____967 uu____969)))
end))))
in (FStar_All.pipe_right uu____861 (FStar_String.concat " and ")))
in (Prims.op_Hat s uu____859)))
end
| FStar_Parser_AST.Val (i, t) -> begin
(

let uu____981 = (

let uu____983 = (

let uu____985 = (FStar_Parser_AST.term_to_string t)
in (Prims.op_Hat ":" uu____985))
in (Prims.op_Hat i.FStar_Ident.idText uu____983))
in (Prims.op_Hat "val " uu____981))
end
| FStar_Parser_AST.Exception (i, uu____990) -> begin
(Prims.op_Hat "exception " i.FStar_Ident.idText)
end
| FStar_Parser_AST.NewEffect (FStar_Parser_AST.DefineEffect (i, uu____997, uu____998, uu____999)) -> begin
(Prims.op_Hat "new_effect " i.FStar_Ident.idText)
end
| FStar_Parser_AST.NewEffect (FStar_Parser_AST.RedefineEffect (i, uu____1010, uu____1011)) -> begin
(Prims.op_Hat "new_effect " i.FStar_Ident.idText)
end
| FStar_Parser_AST.SubEffect (uu____1017) -> begin
"sub_effect"
end
| FStar_Parser_AST.Pragma (uu____1019) -> begin
"pragma"
end
| FStar_Parser_AST.Splice (ids, t) -> begin
(

let uu____1027 = (FStar_Parser_AST.term_to_string t)
in (Prims.op_Hat "splice " uu____1027))
end
| FStar_Parser_AST.Fsdoc (comm, uu____1031) -> begin
comm
end))


let decl_documented : FStar_Parser_AST.decl  ->  Prims.bool = (fun d -> (

let tycon_documented = (fun tt -> (

let tyconvars_documented = (fun tycon -> (match (tycon) with
| FStar_Parser_AST.TyconAbstract (uu____1088) -> begin
false
end
| FStar_Parser_AST.TyconAbbrev (uu____1100) -> begin
false
end
| FStar_Parser_AST.TyconRecord (uu____1114, uu____1115, uu____1116, fields) -> begin
(FStar_List.existsb (fun uu____1158 -> (match (uu____1158) with
| (_id, _t, doco) -> begin
(FStar_Util.is_some doco)
end)) fields)
end
| FStar_Parser_AST.TyconVariant (uu____1175, uu____1176, uu____1177, vars) -> begin
(FStar_List.existsb (fun uu____1235 -> (match (uu____1235) with
| (_id, _t, doco, _u) -> begin
(FStar_Util.is_some doco)
end)) vars)
end))
in (FStar_List.existsb (fun uu____1273 -> (match (uu____1273) with
| (tycon, doco) -> begin
((tyconvars_documented tycon) || (FStar_Util.is_some doco))
end)) tt)))
in (match (d.FStar_Parser_AST.doc) with
| FStar_Pervasives_Native.Some (uu____1288) -> begin
true
end
| uu____1290 -> begin
(match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Fsdoc (uu____1294) -> begin
true
end
| FStar_Parser_AST.Tycon (uu____1296, uu____1297, ty) -> begin
(tycon_documented ty)
end
| uu____1319 -> begin
false
end)
end)))


let document_decl : (Prims.string  ->  unit)  ->  FStar_Parser_AST.decl  ->  unit = (fun w d -> (match ((decl_documented d)) with
| true -> begin
(

let uu____1340 = d
in (match (uu____1340) with
| {FStar_Parser_AST.d = decl; FStar_Parser_AST.drange = uu____1342; FStar_Parser_AST.doc = fsdoc; FStar_Parser_AST.quals = uu____1344; FStar_Parser_AST.attrs = uu____1345} -> begin
((

let uu____1349 = (

let uu____1351 = (string_of_decl' d.FStar_Parser_AST.d)
in (code_wrap uu____1351))
in (w uu____1349));
(match (fsdoc) with
| FStar_Pervasives_Native.Some (doc1, _kw) -> begin
(w (Prims.op_Hat "\n" doc1))
end
| uu____1375 -> begin
()
end);
(w "");
)
end))
end
| uu____1379 -> begin
()
end))


let document_toplevel : 'Auu____1388 . 'Auu____1388  ->  FStar_Parser_AST.decl  ->  (Prims.string FStar_Pervasives_Native.option * Prims.string FStar_Pervasives_Native.option) = (fun name topdecl -> (match (topdecl.FStar_Parser_AST.d) with
| FStar_Parser_AST.TopLevelModule (uu____1409) -> begin
(match (topdecl.FStar_Parser_AST.doc) with
| FStar_Pervasives_Native.Some (doc1, kw) -> begin
(

let uu____1440 = (FStar_List.tryFind (fun uu____1458 -> (match (uu____1458) with
| (k, v1) -> begin
(Prims.op_Equality k "summary")
end)) kw)
in (match (uu____1440) with
| FStar_Pervasives_Native.None -> begin
((FStar_Pervasives_Native.None), (FStar_Pervasives_Native.Some (doc1)))
end
| FStar_Pervasives_Native.Some (uu____1498, summary) -> begin
((FStar_Pervasives_Native.Some (summary)), (FStar_Pervasives_Native.Some (doc1)))
end))
end
| FStar_Pervasives_Native.None -> begin
((FStar_Pervasives_Native.None), (FStar_Pervasives_Native.None))
end)
end
| uu____1526 -> begin
(FStar_Errors.raise_err ((FStar_Errors.Fatal_NotTopLevelModule), ("Not Top-level Module")))
end))


let document_module : FStar_Parser_AST.modul  ->  FStar_Ident.lident = (fun m -> (

let uu____1545 = (match (m) with
| FStar_Parser_AST.Module (n1, d) -> begin
((n1), (d), ("module"))
end
| FStar_Parser_AST.Interface (n1, d, uu____1576) -> begin
((n1), (d), ("interface"))
end)
in (match (uu____1545) with
| (name, decls, _mt) -> begin
(

let uu____1596 = (one_toplevel decls)
in (match (uu____1596) with
| FStar_Pervasives_Native.Some (top_decl, other_decls) -> begin
(

let on1 = (FStar_Options.prepend_output_dir (Prims.op_Hat name.FStar_Ident.str ".md"))
in (

let fd = (FStar_Util.open_file_for_writing on1)
in (

let w = (FStar_Util.append_to_file fd)
in (

let no_summary = "fsdoc: no-summary-found"
in (

let no_comment = "fsdoc: no-comment-found"
in (

let uu____1633 = (document_toplevel name top_decl)
in (match (uu____1633) with
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

let uu____1673 = (FStar_Util.format "# module %s" ((name.FStar_Ident.str)::[]))
in (w uu____1673));
(

let uu____1679 = (FStar_Util.format "%s\n" ((summary1)::[]))
in (w uu____1679));
(

let uu____1685 = (FStar_Util.format "%s\n" ((comment1)::[]))
in (w uu____1685));
(FStar_List.iter (document_decl w) other_decls);
(FStar_Util.close_file fd);
name;
)))
end)))))))
end
| FStar_Pervasives_Native.None -> begin
(

let uu____1698 = (

let uu____1704 = (FStar_Util.format1 "No singleton toplevel in module %s" name.FStar_Ident.str)
in ((FStar_Errors.Fatal_NonSingletonTopLevel), (uu____1704)))
in (FStar_Errors.raise_err uu____1698))
end))
end)))


let generate : Prims.string Prims.list  ->  unit = (fun files -> (

let modules = (FStar_List.map (fun fn -> (

let uu____1728 = (FStar_Parser_Driver.parse_file fn)
in (FStar_Pervasives_Native.fst uu____1728))) files)
in (

let mods = (FStar_List.map document_module modules)
in (

let on1 = (FStar_Options.prepend_output_dir "index.md")
in (

let fd = (FStar_Util.open_file_for_writing on1)
in ((FStar_List.iter (fun m -> (

let uu____1758 = (FStar_Util.format "%s\n" ((m.FStar_Ident.str)::[]))
in (FStar_Util.append_to_file fd uu____1758))) mods);
(FStar_Util.close_file fd);
))))))




