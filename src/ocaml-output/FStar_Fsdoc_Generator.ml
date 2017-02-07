
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


let string_of_fsdoco : (Prims.string * (Prims.string * Prims.string) Prims.list) Prims.option  ->  Prims.string = (fun d -> (string_of_optiont (fun x -> (

let uu____141 = (

let uu____142 = (FStar_Parser_AST.string_of_fsdoc x)
in (Prims.strcat uu____142 "*)"))
in (Prims.strcat "(*" uu____141))) "" d))


let string_of_termo : FStar_Parser_AST.term Prims.option  ->  Prims.string = (fun t -> (string_of_optiont FStar_Parser_AST.term_to_string "" t))


let code_wrap : Prims.string  ->  Prims.string = (fun s -> (Prims.strcat "```fsharp\n" (Prims.strcat s "\n```\n")))


let string_of_tycon : FStar_Parser_AST.tycon  ->  Prims.string = (fun tycon -> (match (tycon) with
| FStar_Parser_AST.TyconAbstract (uu____154) -> begin
"abstract"
end
| FStar_Parser_AST.TyconAbbrev (uu____160) -> begin
"abbrev"
end
| FStar_Parser_AST.TyconRecord (id, _bb, _ko, fields) -> begin
(

let uu____185 = (

let uu____186 = (

let uu____187 = (

let uu____188 = (FStar_All.pipe_right fields (FStar_List.map (fun uu____205 -> (match (uu____205) with
| (id, t, doco) -> begin
(

let uu____230 = (string_of_fsdoco doco)
in (

let uu____231 = (

let uu____232 = (

let uu____233 = (FStar_Parser_AST.term_to_string t)
in (Prims.strcat ":" uu____233))
in (Prims.strcat id.FStar_Ident.idText uu____232))
in (Prims.strcat uu____230 uu____231)))
end))))
in (FStar_All.pipe_right uu____188 (FStar_String.concat "; ")))
in (Prims.strcat uu____187 " }"))
in (Prims.strcat " = { " uu____186))
in (Prims.strcat id.FStar_Ident.idText uu____185))
end
| FStar_Parser_AST.TyconVariant (id, _bb, _ko, vars) -> begin
(

let uu____257 = (

let uu____258 = (

let uu____259 = (FStar_All.pipe_right vars (FStar_List.map (fun uu____280 -> (match (uu____280) with
| (id, trmo, doco, u) -> begin
(

let uu____310 = (string_of_fsdoco doco)
in (

let uu____311 = (

let uu____312 = (

let uu____313 = (string_of_optiont FStar_Parser_AST.term_to_string "" trmo)
in (Prims.strcat ":" uu____313))
in (Prims.strcat id.FStar_Ident.idText uu____312))
in (Prims.strcat uu____310 uu____311)))
end))))
in (FStar_All.pipe_right uu____259 (FStar_String.concat " | ")))
in (Prims.strcat " = " uu____258))
in (Prims.strcat id.FStar_Ident.idText uu____257))
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
| FStar_Parser_AST.TopLevelLet (uu____323, pats) -> begin
(

let termty = (FStar_List.map (fun uu____339 -> (match (uu____339) with
| (p, t) -> begin
(

let uu____346 = (FStar_Parser_AST.pat_to_string p)
in (

let uu____347 = (FStar_Parser_AST.term_to_string t)
in ((uu____346), (uu____347))))
end)) pats)
in (

let termty' = (FStar_List.map (fun uu____352 -> (match (uu____352) with
| (p, t) -> begin
(Prims.strcat p (Prims.strcat ":" t))
end)) termty)
in (Prims.strcat "let " (FStar_String.concat ", " termty'))))
end
| FStar_Parser_AST.Main (uu____357) -> begin
"main ..."
end
| FStar_Parser_AST.Assume (i, t) -> begin
(

let uu____360 = (

let uu____361 = (

let uu____362 = (FStar_Parser_AST.term_to_string t)
in (Prims.strcat ":" uu____362))
in (Prims.strcat i.FStar_Ident.idText uu____361))
in (Prims.strcat "assume " uu____360))
end
| FStar_Parser_AST.Tycon (uu____363, tys) -> begin
(

let uu____373 = (

let uu____374 = (FStar_All.pipe_right tys (FStar_List.map (fun uu____389 -> (match (uu____389) with
| (t, d) -> begin
(

let uu____412 = (string_of_tycon t)
in (

let uu____413 = (

let uu____414 = (string_of_fsdoco d)
in (Prims.strcat " " uu____414))
in (Prims.strcat uu____412 uu____413)))
end))))
in (FStar_All.pipe_right uu____374 (FStar_String.concat " and ")))
in (Prims.strcat "type " uu____373))
end
| FStar_Parser_AST.Val (i, t) -> begin
(

let uu____418 = (

let uu____419 = (

let uu____420 = (FStar_Parser_AST.term_to_string t)
in (Prims.strcat ":" uu____420))
in (Prims.strcat i.FStar_Ident.idText uu____419))
in (Prims.strcat "val " uu____418))
end
| FStar_Parser_AST.Exception (i, uu____422) -> begin
(Prims.strcat "exception " i.FStar_Ident.idText)
end
| (FStar_Parser_AST.NewEffect (FStar_Parser_AST.DefineEffect (i, _, _, _, _))) | (FStar_Parser_AST.NewEffect (FStar_Parser_AST.RedefineEffect (i, _, _))) -> begin
(Prims.strcat "new_effect " i.FStar_Ident.idText)
end
| (FStar_Parser_AST.NewEffectForFree (FStar_Parser_AST.DefineEffect (i, _, _, _, _))) | (FStar_Parser_AST.NewEffectForFree (FStar_Parser_AST.RedefineEffect (i, _, _))) -> begin
(Prims.strcat "new_effect_for_free " i.FStar_Ident.idText)
end
| FStar_Parser_AST.SubEffect (uu____447) -> begin
"sub_effect"
end
| FStar_Parser_AST.Pragma (uu____448) -> begin
"pragma"
end
| FStar_Parser_AST.Fsdoc (comm, uu____450) -> begin
comm
end))


let decl_documented : FStar_Parser_AST.decl  ->  Prims.bool = (fun d -> (

let tycon_documented = (fun tt -> (

let tyconvars_documented = (fun tycon -> (match (tycon) with
| (FStar_Parser_AST.TyconAbstract (_)) | (FStar_Parser_AST.TyconAbbrev (_)) -> begin
false
end
| FStar_Parser_AST.TyconRecord (uu____478, uu____479, uu____480, fields) -> begin
(FStar_List.existsb (fun uu____500 -> (match (uu____500) with
| (_id, _t, doco) -> begin
(FStar_Util.is_some doco)
end)) fields)
end
| FStar_Parser_AST.TyconVariant (uu____510, uu____511, uu____512, vars) -> begin
(FStar_List.existsb (fun uu____538 -> (match (uu____538) with
| (_id, _t, doco, _u) -> begin
(FStar_Util.is_some doco)
end)) vars)
end))
in (FStar_List.existsb (fun uu____556 -> (match (uu____556) with
| (tycon, doco) -> begin
((tyconvars_documented tycon) || (FStar_Util.is_some doco))
end)) tt)))
in (match (d.FStar_Parser_AST.doc) with
| Some (uu____564) -> begin
true
end
| uu____565 -> begin
(match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Fsdoc (uu____567) -> begin
true
end
| FStar_Parser_AST.Tycon (uu____568, ty) -> begin
(tycon_documented ty)
end
| uu____578 -> begin
false
end)
end)))


let document_decl : (Prims.string  ->  Prims.unit)  ->  FStar_Parser_AST.decl  ->  Prims.unit = (fun w d -> (match ((decl_documented d)) with
| true -> begin
(

let uu____590 = d
in (match (uu____590) with
| {FStar_Parser_AST.d = decl; FStar_Parser_AST.drange = uu____592; FStar_Parser_AST.doc = fsdoc; FStar_Parser_AST.quals = uu____594; FStar_Parser_AST.attrs = uu____595} -> begin
((

let uu____598 = (

let uu____599 = (string_of_decl' d.FStar_Parser_AST.d)
in (code_wrap uu____599))
in (w uu____598));
(match (fsdoc) with
| Some (doc, _kw) -> begin
(w (Prims.strcat "\n" doc))
end
| uu____614 -> begin
()
end);
(w "");
)
end))
end
| uu____616 -> begin
()
end))


let document_toplevel = (fun name topdecl -> (match (topdecl.FStar_Parser_AST.d) with
| FStar_Parser_AST.TopLevelModule (uu____633) -> begin
(match (topdecl.FStar_Parser_AST.doc) with
| Some (doc, kw) -> begin
(

let uu____651 = (FStar_List.tryFind (fun uu____657 -> (match (uu____657) with
| (k, v) -> begin
(k = "summary")
end)) kw)
in (match (uu____651) with
| None -> begin
((None), (Some (doc)))
end
| Some (uu____670, summary) -> begin
((Some (summary)), (Some (doc)))
end))
end
| None -> begin
((None), (None))
end)
end
| uu____678 -> begin
(Prims.raise (FStar_Errors.Err ("Not a TopLevelModule")))
end))


let document_module : FStar_Parser_AST.modul  ->  FStar_Ident.lid = (fun m -> (

let uu____686 = (match (m) with
| FStar_Parser_AST.Module (n, d) -> begin
((n), (d), ("module"))
end
| FStar_Parser_AST.Interface (n, d, uu____702) -> begin
((n), (d), ("interface"))
end)
in (match (uu____686) with
| (name, decls, _mt) -> begin
(

let uu____711 = (one_toplevel decls)
in (match (uu____711) with
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

let uu____730 = (document_toplevel name top_decl)
in (match (uu____730) with
| (summary, comment) -> begin
(

let summary = (match (summary) with
| Some (s) -> begin
s
end
| None -> begin
no_summary
end)
in (

let comment = (match (comment) with
| Some (s) -> begin
s
end
| None -> begin
no_comment
end)
in ((

let uu____746 = (FStar_Util.format "# module %s" ((name.FStar_Ident.str)::[]))
in (w uu____746));
(

let uu____748 = (FStar_Util.format "%s\n" ((summary)::[]))
in (w uu____748));
(

let uu____750 = (FStar_Util.format "%s\n" ((comment)::[]))
in (w uu____750));
(FStar_List.iter (document_decl w) other_decls);
(FStar_Util.close_file fd);
name;
)))
end)))))))
end
| None -> begin
(

let uu____756 = (

let uu____757 = (FStar_Util.format1 "No singleton toplevel in module %s" name.FStar_Ident.str)
in FStar_Errors.Err (uu____757))
in (Prims.raise uu____756))
end))
end)))


let generate : Prims.string Prims.list  ->  Prims.unit = (fun files -> (

let modules = (FStar_List.collect (fun fn -> (

let uu____766 = (FStar_Parser_Driver.parse_file fn)
in (Prims.fst uu____766))) files)
in (

let mods = (FStar_List.map document_module modules)
in (

let on = (FStar_Options.prepend_output_dir "index.md")
in (

let fd = (FStar_Util.open_file_for_writing on)
in ((FStar_List.iter (fun m -> (

let uu____781 = (FStar_Util.format "%s\n" ((m.FStar_Ident.str)::[]))
in (FStar_Util.append_to_file fd uu____781))) mods);
(FStar_Util.close_file fd);
))))))




