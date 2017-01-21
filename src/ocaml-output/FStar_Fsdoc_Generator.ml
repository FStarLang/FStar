
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


let string_of_fsdoco : (Prims.string * (Prims.string * Prims.string) Prims.list) Prims.option  ->  Prims.string = (fun d -> (string_of_optiont (fun x -> (let _0_630 = (let _0_629 = (FStar_Parser_AST.string_of_fsdoc x)
in (Prims.strcat _0_629 "*)"))
in (Prims.strcat "(*" _0_630))) "" d))


let string_of_termo : FStar_Parser_AST.term Prims.option  ->  Prims.string = (fun t -> (string_of_optiont FStar_Parser_AST.term_to_string "" t))


let code_wrap : Prims.string  ->  Prims.string = (fun s -> (Prims.strcat "```fsharp\n" (Prims.strcat s "\n```\n")))


let string_of_tycon : FStar_Parser_AST.tycon  ->  Prims.string = (fun tycon -> (match (tycon) with
| FStar_Parser_AST.TyconAbstract (uu____152) -> begin
"abstract"
end
| FStar_Parser_AST.TyconAbbrev (uu____158) -> begin
"abbrev"
end
| FStar_Parser_AST.TyconRecord (id, _bb, _ko, fields) -> begin
(let _0_638 = (let _0_637 = (let _0_636 = (let _0_635 = (FStar_All.pipe_right fields (FStar_List.map (fun uu____199 -> (match (uu____199) with
| (id, t, doco) -> begin
(let _0_634 = (string_of_fsdoco doco)
in (let _0_633 = (let _0_632 = (let _0_631 = (FStar_Parser_AST.term_to_string t)
in (Prims.strcat ":" _0_631))
in (Prims.strcat id.FStar_Ident.idText _0_632))
in (Prims.strcat _0_634 _0_633)))
end))))
in (FStar_All.pipe_right _0_635 (FStar_String.concat "; ")))
in (Prims.strcat _0_636 " }"))
in (Prims.strcat " = { " _0_637))
in (Prims.strcat id.FStar_Ident.idText _0_638))
end
| FStar_Parser_AST.TyconVariant (id, _bb, _ko, vars) -> begin
(let _0_645 = (let _0_644 = (let _0_643 = (FStar_All.pipe_right vars (FStar_List.map (fun uu____266 -> (match (uu____266) with
| (id, trmo, doco, u) -> begin
(let _0_642 = (string_of_fsdoco doco)
in (let _0_641 = (let _0_640 = (let _0_639 = (string_of_optiont FStar_Parser_AST.term_to_string "" trmo)
in (Prims.strcat ":" _0_639))
in (Prims.strcat id.FStar_Ident.idText _0_640))
in (Prims.strcat _0_642 _0_641)))
end))))
in (FStar_All.pipe_right _0_643 (FStar_String.concat " | ")))
in (Prims.strcat " = " _0_644))
in (Prims.strcat id.FStar_Ident.idText _0_645))
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
| FStar_Parser_AST.KindAbbrev (i, uu____305, uu____306) -> begin
(Prims.strcat "kind " i.FStar_Ident.idText)
end
| FStar_Parser_AST.TopLevelLet (uu____309, pats) -> begin
(

let termty = (FStar_List.map (fun uu____325 -> (match (uu____325) with
| (p, t) -> begin
(let _0_647 = (FStar_Parser_AST.pat_to_string p)
in (let _0_646 = (FStar_Parser_AST.term_to_string t)
in ((_0_647), (_0_646))))
end)) pats)
in (

let termty' = (FStar_List.map (fun uu____336 -> (match (uu____336) with
| (p, t) -> begin
(Prims.strcat p (Prims.strcat ":" t))
end)) termty)
in (Prims.strcat "let " (FStar_String.concat ", " termty'))))
end
| FStar_Parser_AST.Main (uu____341) -> begin
"main ..."
end
| FStar_Parser_AST.Assume (i, t) -> begin
(let _0_650 = (let _0_649 = (let _0_648 = (FStar_Parser_AST.term_to_string t)
in (Prims.strcat ":" _0_648))
in (Prims.strcat i.FStar_Ident.idText _0_649))
in (Prims.strcat "assume " _0_650))
end
| FStar_Parser_AST.Tycon (uu____344, tys) -> begin
(let _0_655 = (let _0_654 = (FStar_All.pipe_right tys (FStar_List.map (fun uu____368 -> (match (uu____368) with
| (t, d) -> begin
(let _0_653 = (string_of_tycon t)
in (let _0_652 = (let _0_651 = (string_of_fsdoco d)
in (Prims.strcat " " _0_651))
in (Prims.strcat _0_653 _0_652)))
end))))
in (FStar_All.pipe_right _0_654 (FStar_String.concat " and ")))
in (Prims.strcat "type " _0_655))
end
| FStar_Parser_AST.Val (i, t) -> begin
(let _0_658 = (let _0_657 = (let _0_656 = (FStar_Parser_AST.term_to_string t)
in (Prims.strcat ":" _0_656))
in (Prims.strcat i.FStar_Ident.idText _0_657))
in (Prims.strcat "val " _0_658))
end
| FStar_Parser_AST.Exception (i, uu____394) -> begin
(Prims.strcat "exception " i.FStar_Ident.idText)
end
| (FStar_Parser_AST.NewEffect (FStar_Parser_AST.DefineEffect (i, _, _, _, _))) | (FStar_Parser_AST.NewEffect (FStar_Parser_AST.RedefineEffect (i, _, _))) -> begin
(Prims.strcat "new_effect " i.FStar_Ident.idText)
end
| (FStar_Parser_AST.NewEffectForFree (FStar_Parser_AST.DefineEffect (i, _, _, _, _))) | (FStar_Parser_AST.NewEffectForFree (FStar_Parser_AST.RedefineEffect (i, _, _))) -> begin
(Prims.strcat "new_effect_for_free " i.FStar_Ident.idText)
end
| FStar_Parser_AST.SubEffect (uu____419) -> begin
"sub_effect"
end
| FStar_Parser_AST.Pragma (uu____420) -> begin
"pragma"
end
| FStar_Parser_AST.Fsdoc (comm, uu____422) -> begin
comm
end))


let decl_documented : FStar_Parser_AST.decl  ->  Prims.bool = (fun d -> (

let tycon_documented = (fun tt -> (

let tyconvars_documented = (fun tycon -> (match (tycon) with
| (FStar_Parser_AST.TyconAbstract (_)) | (FStar_Parser_AST.TyconAbbrev (_)) -> begin
false
end
| FStar_Parser_AST.TyconRecord (uu____450, uu____451, uu____452, fields) -> begin
(FStar_List.existsb (fun uu____472 -> (match (uu____472) with
| (_id, _t, doco) -> begin
(FStar_Util.is_some doco)
end)) fields)
end
| FStar_Parser_AST.TyconVariant (uu____482, uu____483, uu____484, vars) -> begin
(FStar_List.existsb (fun uu____510 -> (match (uu____510) with
| (_id, _t, doco, _u) -> begin
(FStar_Util.is_some doco)
end)) vars)
end))
in (FStar_List.existsb (fun uu____528 -> (match (uu____528) with
| (tycon, doco) -> begin
((tyconvars_documented tycon) || (FStar_Util.is_some doco))
end)) tt)))
in (match (d.FStar_Parser_AST.doc) with
| Some (uu____536) -> begin
true
end
| uu____537 -> begin
(match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Fsdoc (uu____539) -> begin
true
end
| FStar_Parser_AST.Tycon (uu____540, ty) -> begin
(tycon_documented ty)
end
| uu____550 -> begin
false
end)
end)))


let document_decl : (Prims.string  ->  Prims.unit)  ->  FStar_Parser_AST.decl  ->  Prims.unit = (fun w d -> (match ((decl_documented d)) with
| true -> begin
(

let uu____562 = d
in (match (uu____562) with
| {FStar_Parser_AST.d = decl; FStar_Parser_AST.drange = uu____564; FStar_Parser_AST.doc = fsdoc; FStar_Parser_AST.quals = uu____566; FStar_Parser_AST.attrs = uu____567} -> begin
((w (code_wrap (string_of_decl' d.FStar_Parser_AST.d)));
(match (fsdoc) with
| Some (doc, _kw) -> begin
(w (Prims.strcat "\n" doc))
end
| uu____584 -> begin
()
end);
(w "");
)
end))
end
| uu____586 -> begin
()
end))


let document_toplevel = (fun name topdecl -> (match (topdecl.FStar_Parser_AST.d) with
| FStar_Parser_AST.TopLevelModule (uu____603) -> begin
(match (topdecl.FStar_Parser_AST.doc) with
| Some (doc, kw) -> begin
(

let uu____621 = (FStar_List.tryFind (fun uu____627 -> (match (uu____627) with
| (k, v) -> begin
(k = "summary")
end)) kw)
in (match (uu____621) with
| None -> begin
((None), (Some (doc)))
end
| Some (uu____640, summary) -> begin
((Some (summary)), (Some (doc)))
end))
end
| None -> begin
((None), (None))
end)
end
| uu____648 -> begin
(Prims.raise (FStar_Errors.Err ("Not a TopLevelModule")))
end))


let document_module : FStar_Parser_AST.modul  ->  FStar_Ident.lid = (fun m -> (

let uu____656 = (match (m) with
| FStar_Parser_AST.Module (n, d) -> begin
((n), (d), ("module"))
end
| FStar_Parser_AST.Interface (n, d, uu____672) -> begin
((n), (d), ("interface"))
end)
in (match (uu____656) with
| (name, decls, _mt) -> begin
(

let uu____681 = (one_toplevel decls)
in (match (uu____681) with
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

let uu____700 = (document_toplevel name top_decl)
in (match (uu____700) with
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
in ((w (FStar_Util.format "# module %s" ((name.FStar_Ident.str)::[])));
(w (FStar_Util.format "%s\n" ((summary)::[])));
(w (FStar_Util.format "%s\n" ((comment)::[])));
(FStar_List.iter (document_decl w) other_decls);
(FStar_Util.close_file fd);
name;
)))
end)))))))
end
| None -> begin
(Prims.raise (FStar_Errors.Err ((FStar_Util.format1 "No singleton toplevel in module %s" name.FStar_Ident.str))))
end))
end)))


let generate : Prims.string Prims.list  ->  Prims.unit = (fun files -> (

let modules = (FStar_List.collect (fun fn -> (Prims.fst (FStar_Parser_Driver.parse_file fn))) files)
in (

let mods = (FStar_List.map document_module modules)
in (

let on = (FStar_Options.prepend_output_dir "index.md")
in (

let fd = (FStar_Util.open_file_for_writing on)
in ((FStar_List.iter (fun m -> (let _0_659 = (FStar_Util.format "%s\n" ((m.FStar_Ident.str)::[]))
in (FStar_Util.append_to_file fd _0_659))) mods);
(FStar_Util.close_file fd);
))))))




