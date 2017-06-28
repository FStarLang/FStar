
open Prims
open FStar_Pervasives

let one_toplevel : FStar_Parser_AST.decl Prims.list  ->  (FStar_Parser_AST.decl * FStar_Parser_AST.decl Prims.list) FStar_Pervasives_Native.option = (fun decls -> (

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
FStar_Pervasives_Native.Some (((t), (nontops)))
end
| uu____37 -> begin
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
| uu____59 -> begin
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
| uu____78 -> begin
false
end))


let __proj__Branch__item___0 : mforest  ->  mforest FStar_Util.smap = (fun projectee -> (match (projectee) with
| Branch (_0) -> begin
_0
end))


let htree : mforest FStar_Util.smap = (FStar_Util.smap_create (Prims.parse_int "50"))


let string_of_optiont = (fun f y xo -> (match (xo) with
| FStar_Pervasives_Native.Some (x) -> begin
(f x)
end
| FStar_Pervasives_Native.None -> begin
y
end))


let string_of_fsdoco : (Prims.string * (Prims.string * Prims.string) Prims.list) FStar_Pervasives_Native.option  ->  Prims.string = (fun d -> (string_of_optiont (fun x -> (

let uu____143 = (

let uu____144 = (FStar_Parser_AST.string_of_fsdoc x)
in (Prims.strcat uu____144 "*)"))
in (Prims.strcat "(*" uu____143))) "" d))


let string_of_termo : FStar_Parser_AST.term FStar_Pervasives_Native.option  ->  Prims.string = (fun t -> (string_of_optiont FStar_Parser_AST.term_to_string "" t))


let code_wrap : Prims.string  ->  Prims.string = (fun s -> (Prims.strcat "```fsharp\n" (Prims.strcat s "\n```\n")))


let string_of_tycon : FStar_Parser_AST.tycon  ->  Prims.string = (fun tycon -> (match (tycon) with
| FStar_Parser_AST.TyconAbstract (uu____156) -> begin
"abstract"
end
| FStar_Parser_AST.TyconAbbrev (uu____162) -> begin
"abbrev"
end
| FStar_Parser_AST.TyconRecord (id, _bb, _ko, fields) -> begin
(

let uu____187 = (

let uu____188 = (

let uu____189 = (

let uu____190 = (FStar_All.pipe_right fields (FStar_List.map (fun uu____207 -> (match (uu____207) with
| (id1, t, doco) -> begin
(

let uu____232 = (string_of_fsdoco doco)
in (

let uu____233 = (

let uu____234 = (

let uu____235 = (FStar_Parser_AST.term_to_string t)
in (Prims.strcat ":" uu____235))
in (Prims.strcat id1.FStar_Ident.idText uu____234))
in (Prims.strcat uu____232 uu____233)))
end))))
in (FStar_All.pipe_right uu____190 (FStar_String.concat "; ")))
in (Prims.strcat uu____189 " }"))
in (Prims.strcat " = { " uu____188))
in (Prims.strcat id.FStar_Ident.idText uu____187))
end
| FStar_Parser_AST.TyconVariant (id, _bb, _ko, vars) -> begin
(

let uu____259 = (

let uu____260 = (

let uu____261 = (FStar_All.pipe_right vars (FStar_List.map (fun uu____282 -> (match (uu____282) with
| (id1, trmo, doco, u) -> begin
(

let uu____312 = (string_of_fsdoco doco)
in (

let uu____313 = (

let uu____314 = (

let uu____315 = (string_of_optiont FStar_Parser_AST.term_to_string "" trmo)
in (Prims.strcat ":" uu____315))
in (Prims.strcat id1.FStar_Ident.idText uu____314))
in (Prims.strcat uu____312 uu____313)))
end))))
in (FStar_All.pipe_right uu____261 (FStar_String.concat " | ")))
in (Prims.strcat " = " uu____260))
in (Prims.strcat id.FStar_Ident.idText uu____259))
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
| FStar_Parser_AST.TopLevelLet (uu____325, pats) -> begin
(

let termty = (FStar_List.map (fun uu____341 -> (match (uu____341) with
| (p, t) -> begin
(

let uu____348 = (FStar_Parser_AST.pat_to_string p)
in (

let uu____349 = (FStar_Parser_AST.term_to_string t)
in ((uu____348), (uu____349))))
end)) pats)
in (

let termty' = (FStar_List.map (fun uu____354 -> (match (uu____354) with
| (p, t) -> begin
(Prims.strcat p (Prims.strcat ":" t))
end)) termty)
in (Prims.strcat "let " (FStar_String.concat ", " termty'))))
end
| FStar_Parser_AST.Main (uu____359) -> begin
"main ..."
end
| FStar_Parser_AST.Assume (i, t) -> begin
(

let uu____362 = (

let uu____363 = (

let uu____364 = (FStar_Parser_AST.term_to_string t)
in (Prims.strcat ":" uu____364))
in (Prims.strcat i.FStar_Ident.idText uu____363))
in (Prims.strcat "assume " uu____362))
end
| FStar_Parser_AST.Tycon (uu____365, tys) -> begin
(

let uu____375 = (

let uu____376 = (FStar_All.pipe_right tys (FStar_List.map (fun uu____391 -> (match (uu____391) with
| (t, d1) -> begin
(

let uu____414 = (string_of_tycon t)
in (

let uu____415 = (

let uu____416 = (string_of_fsdoco d1)
in (Prims.strcat " " uu____416))
in (Prims.strcat uu____414 uu____415)))
end))))
in (FStar_All.pipe_right uu____376 (FStar_String.concat " and ")))
in (Prims.strcat "type " uu____375))
end
| FStar_Parser_AST.Val (i, t) -> begin
(

let uu____420 = (

let uu____421 = (

let uu____422 = (FStar_Parser_AST.term_to_string t)
in (Prims.strcat ":" uu____422))
in (Prims.strcat i.FStar_Ident.idText uu____421))
in (Prims.strcat "val " uu____420))
end
| FStar_Parser_AST.Exception (i, uu____424) -> begin
(Prims.strcat "exception " i.FStar_Ident.idText)
end
| FStar_Parser_AST.NewEffect (FStar_Parser_AST.DefineEffect (i, uu____428, uu____429, uu____430)) -> begin
(Prims.strcat "new_effect " i.FStar_Ident.idText)
end
| FStar_Parser_AST.NewEffect (FStar_Parser_AST.RedefineEffect (i, uu____436, uu____437)) -> begin
(Prims.strcat "new_effect " i.FStar_Ident.idText)
end
| FStar_Parser_AST.SubEffect (uu____440) -> begin
"sub_effect"
end
| FStar_Parser_AST.Pragma (uu____441) -> begin
"pragma"
end
| FStar_Parser_AST.Fsdoc (comm, uu____443) -> begin
comm
end))


let decl_documented : FStar_Parser_AST.decl  ->  Prims.bool = (fun d -> (

let tycon_documented = (fun tt -> (

let tyconvars_documented = (fun tycon -> (match (tycon) with
| FStar_Parser_AST.TyconAbstract (uu____469) -> begin
false
end
| FStar_Parser_AST.TyconAbbrev (uu____475) -> begin
false
end
| FStar_Parser_AST.TyconRecord (uu____482, uu____483, uu____484, fields) -> begin
(FStar_List.existsb (fun uu____504 -> (match (uu____504) with
| (_id, _t, doco) -> begin
(FStar_Util.is_some doco)
end)) fields)
end
| FStar_Parser_AST.TyconVariant (uu____514, uu____515, uu____516, vars) -> begin
(FStar_List.existsb (fun uu____542 -> (match (uu____542) with
| (_id, _t, doco, _u) -> begin
(FStar_Util.is_some doco)
end)) vars)
end))
in (FStar_List.existsb (fun uu____560 -> (match (uu____560) with
| (tycon, doco) -> begin
((tyconvars_documented tycon) || (FStar_Util.is_some doco))
end)) tt)))
in (match (d.FStar_Parser_AST.doc) with
| FStar_Pervasives_Native.Some (uu____568) -> begin
true
end
| uu____569 -> begin
(match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Fsdoc (uu____571) -> begin
true
end
| FStar_Parser_AST.Tycon (uu____572, ty) -> begin
(tycon_documented ty)
end
| uu____582 -> begin
false
end)
end)))


let document_decl : (Prims.string  ->  Prims.unit)  ->  FStar_Parser_AST.decl  ->  Prims.unit = (fun w d -> (match ((decl_documented d)) with
| true -> begin
(

let uu____594 = d
in (match (uu____594) with
| {FStar_Parser_AST.d = decl; FStar_Parser_AST.drange = uu____596; FStar_Parser_AST.doc = fsdoc; FStar_Parser_AST.quals = uu____598; FStar_Parser_AST.attrs = uu____599} -> begin
((

let uu____602 = (

let uu____603 = (string_of_decl' d.FStar_Parser_AST.d)
in (code_wrap uu____603))
in (w uu____602));
(match (fsdoc) with
| FStar_Pervasives_Native.Some (doc1, _kw) -> begin
(w (Prims.strcat "\n" doc1))
end
| uu____618 -> begin
()
end);
(w "");
)
end))
end
| uu____620 -> begin
()
end))


let document_toplevel = (fun name topdecl -> (match (topdecl.FStar_Parser_AST.d) with
| FStar_Parser_AST.TopLevelModule (uu____637) -> begin
(match (topdecl.FStar_Parser_AST.doc) with
| FStar_Pervasives_Native.Some (doc1, kw) -> begin
(

let uu____655 = (FStar_List.tryFind (fun uu____661 -> (match (uu____661) with
| (k, v1) -> begin
(k = "summary")
end)) kw)
in (match (uu____655) with
| FStar_Pervasives_Native.None -> begin
((FStar_Pervasives_Native.None), (FStar_Pervasives_Native.Some (doc1)))
end
| FStar_Pervasives_Native.Some (uu____674, summary) -> begin
((FStar_Pervasives_Native.Some (summary)), (FStar_Pervasives_Native.Some (doc1)))
end))
end
| FStar_Pervasives_Native.None -> begin
((FStar_Pervasives_Native.None), (FStar_Pervasives_Native.None))
end)
end
| uu____682 -> begin
(FStar_Pervasives.raise (FStar_Errors.Err ("Not a TopLevelModule")))
end))


let document_module : FStar_Parser_AST.modul  ->  FStar_Ident.lid = (fun m -> (

let uu____690 = (match (m) with
| FStar_Parser_AST.Module (n1, d) -> begin
((n1), (d), ("module"))
end
| FStar_Parser_AST.Interface (n1, d, uu____706) -> begin
((n1), (d), ("interface"))
end)
in (match (uu____690) with
| (name, decls, _mt) -> begin
(

let uu____715 = (one_toplevel decls)
in (match (uu____715) with
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

let uu____734 = (document_toplevel name top_decl)
in (match (uu____734) with
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

let uu____750 = (FStar_Util.format "# module %s" ((name.FStar_Ident.str)::[]))
in (w uu____750));
(

let uu____752 = (FStar_Util.format "%s\n" ((summary1)::[]))
in (w uu____752));
(

let uu____754 = (FStar_Util.format "%s\n" ((comment1)::[]))
in (w uu____754));
(FStar_List.iter (document_decl w) other_decls);
(FStar_Util.close_file fd);
name;
)))
end)))))))
end
| FStar_Pervasives_Native.None -> begin
(

let uu____760 = (

let uu____761 = (FStar_Util.format1 "No singleton toplevel in module %s" name.FStar_Ident.str)
in FStar_Errors.Err (uu____761))
in (FStar_Pervasives.raise uu____760))
end))
end)))


let generate : Prims.string Prims.list  ->  Prims.unit = (fun files -> (

let modules = (FStar_List.collect (fun fn -> (

let uu____770 = (FStar_Parser_Driver.parse_file fn)
in (FStar_Pervasives_Native.fst uu____770))) files)
in (

let mods = (FStar_List.map document_module modules)
in (

let on = (FStar_Options.prepend_output_dir "index.md")
in (

let fd = (FStar_Util.open_file_for_writing on)
in ((FStar_List.iter (fun m -> (

let uu____785 = (FStar_Util.format "%s\n" ((m.FStar_Ident.str)::[]))
in (FStar_Util.append_to_file fd uu____785))) mods);
(FStar_Util.close_file fd);
))))))




