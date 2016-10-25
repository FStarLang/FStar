
open Prims

let one_toplevel : FStar_Parser_AST.decl Prims.list  ->  (FStar_Parser_AST.decl * FStar_Parser_AST.decl Prims.list) Prims.option = (fun decls -> (

let _82_10 = (FStar_List.partition (fun d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.TopLevelModule (_82_4) -> begin
true
end
| _82_7 -> begin
false
end)) decls)
in (match (_82_10) with
| (top, nontops) -> begin
(match (top) with
| (t)::[] -> begin
Some (((t), (nontops)))
end
| _82_15 -> begin
None
end)
end)))


type mforest =
| Leaf of (Prims.string * Prims.string)
| Branch of mforest FStar_Util.smap


let is_Leaf = (fun _discr_ -> (match (_discr_) with
| Leaf (_) -> begin
true
end
| _ -> begin
false
end))


let is_Branch = (fun _discr_ -> (match (_discr_) with
| Branch (_) -> begin
true
end
| _ -> begin
false
end))


let ___Leaf____0 = (fun projectee -> (match (projectee) with
| Leaf (_82_18) -> begin
_82_18
end))


let ___Branch____0 = (fun projectee -> (match (projectee) with
| Branch (_82_21) -> begin
_82_21
end))


let htree : mforest FStar_Util.smap = (FStar_Util.smap_create (Prims.parse_int "50"))


let string_of_optiont = (fun f y xo -> (match (xo) with
| Some (x) -> begin
(f x)
end
| None -> begin
y
end))


let string_of_fsdoco : (Prims.string * (Prims.string * Prims.string) Prims.list) Prims.option  ->  Prims.string = (fun d -> (string_of_optiont (fun x -> (let _176_42 = (let _176_41 = (FStar_Parser_AST.string_of_fsdoc x)
in (Prims.strcat _176_41 "*)"))
in (Prims.strcat "(*" _176_42))) "" d))


let string_of_termo : FStar_Parser_AST.term Prims.option  ->  Prims.string = (fun t -> (string_of_optiont FStar_Parser_AST.term_to_string "" t))


let code_wrap : Prims.string  ->  Prims.string = (fun s -> (Prims.strcat "```fsharp\n" (Prims.strcat s "\n```\n")))


let string_of_tycon : FStar_Parser_AST.tycon  ->  Prims.string = (fun tycon -> (match (tycon) with
| FStar_Parser_AST.TyconAbstract (_82_34) -> begin
"abstract"
end
| FStar_Parser_AST.TyconAbbrev (_82_37) -> begin
"abbrev"
end
| FStar_Parser_AST.TyconRecord (id, _bb, _ko, fields) -> begin
(let _176_57 = (let _176_56 = (let _176_55 = (let _176_54 = (FStar_All.pipe_right fields (FStar_List.map (fun _82_48 -> (match (_82_48) with
| (id, t, doco) -> begin
(let _176_53 = (string_of_fsdoco doco)
in (let _176_52 = (let _176_51 = (let _176_50 = (FStar_Parser_AST.term_to_string t)
in (Prims.strcat ":" _176_50))
in (Prims.strcat id.FStar_Ident.idText _176_51))
in (Prims.strcat _176_53 _176_52)))
end))))
in (FStar_All.pipe_right _176_54 (FStar_String.concat "; ")))
in (Prims.strcat _176_55 " }"))
in (Prims.strcat " = { " _176_56))
in (Prims.strcat id.FStar_Ident.idText _176_57))
end
| FStar_Parser_AST.TyconVariant (id, _bb, _ko, vars) -> begin
(let _176_65 = (let _176_64 = (let _176_63 = (FStar_All.pipe_right vars (FStar_List.map (fun _82_59 -> (match (_82_59) with
| (id, trmo, doco, u) -> begin
(let _176_62 = (string_of_fsdoco doco)
in (let _176_61 = (let _176_60 = (let _176_59 = (string_of_optiont FStar_Parser_AST.term_to_string "" trmo)
in (Prims.strcat ":" _176_59))
in (Prims.strcat id.FStar_Ident.idText _176_60))
in (Prims.strcat _176_62 _176_61)))
end))))
in (FStar_All.pipe_right _176_63 (FStar_String.concat " | ")))
in (Prims.strcat " = " _176_64))
in (Prims.strcat id.FStar_Ident.idText _176_65))
end))


let string_of_decl' : FStar_Parser_AST.decl'  ->  Prims.string = (fun d -> (match (d) with
| FStar_Parser_AST.TopLevelModule (l) -> begin
(Prims.strcat "module " l.FStar_Ident.str)
end
| FStar_Parser_AST.Open (l) -> begin
(Prims.strcat "open " l.FStar_Ident.str)
end
| FStar_Parser_AST.ModuleAbbrev (i, l) -> begin
(Prims.strcat "module " (Prims.strcat i.FStar_Ident.idText (Prims.strcat " = " l.FStar_Ident.str)))
end
| FStar_Parser_AST.KindAbbrev (i, _82_71, _82_73) -> begin
(Prims.strcat "kind " i.FStar_Ident.idText)
end
| FStar_Parser_AST.ToplevelLet (_82_77, _82_79, pats) -> begin
(

let termty = (FStar_List.map (fun _82_85 -> (match (_82_85) with
| (p, t) -> begin
(let _176_70 = (FStar_Parser_AST.pat_to_string p)
in (let _176_69 = (FStar_Parser_AST.term_to_string t)
in ((_176_70), (_176_69))))
end)) pats)
in (

let termty' = (FStar_List.map (fun _82_89 -> (match (_82_89) with
| (p, t) -> begin
(Prims.strcat p (Prims.strcat ":" t))
end)) termty)
in (Prims.strcat "let " (FStar_String.concat ", " termty'))))
end
| FStar_Parser_AST.Main (_82_92) -> begin
"main ..."
end
| FStar_Parser_AST.Assume (_82_95, i, t) -> begin
(let _176_74 = (let _176_73 = (let _176_72 = (FStar_Parser_AST.term_to_string t)
in (Prims.strcat ":" _176_72))
in (Prims.strcat i.FStar_Ident.idText _176_73))
in (Prims.strcat "assume " _176_74))
end
| FStar_Parser_AST.Tycon (_82_101, tys) -> begin
(let _176_80 = (let _176_79 = (FStar_All.pipe_right tys (FStar_List.map (fun _82_107 -> (match (_82_107) with
| (t, d) -> begin
(let _176_78 = (string_of_tycon t)
in (let _176_77 = (let _176_76 = (string_of_fsdoco d)
in (Prims.strcat " " _176_76))
in (Prims.strcat _176_78 _176_77)))
end))))
in (FStar_All.pipe_right _176_79 (FStar_String.concat " and ")))
in (Prims.strcat "type " _176_80))
end
| FStar_Parser_AST.Val (_82_109, i, t) -> begin
(let _176_83 = (let _176_82 = (let _176_81 = (FStar_Parser_AST.term_to_string t)
in (Prims.strcat ":" _176_81))
in (Prims.strcat i.FStar_Ident.idText _176_82))
in (Prims.strcat "val " _176_83))
end
| FStar_Parser_AST.Exception (i, _82_116) -> begin
(Prims.strcat "exception " i.FStar_Ident.idText)
end
| (FStar_Parser_AST.NewEffect (_, FStar_Parser_AST.DefineEffect (i, _, _, _, _))) | (FStar_Parser_AST.NewEffect (_, FStar_Parser_AST.RedefineEffect (i, _, _))) -> begin
(Prims.strcat "new_effect " i.FStar_Ident.idText)
end
| (FStar_Parser_AST.NewEffectForFree (_, FStar_Parser_AST.DefineEffect (i, _, _, _, _))) | (FStar_Parser_AST.NewEffectForFree (_, FStar_Parser_AST.RedefineEffect (i, _, _))) -> begin
(Prims.strcat "new_effect_for_free " i.FStar_Ident.idText)
end
| FStar_Parser_AST.SubEffect (_82_170) -> begin
"sub_effect"
end
| FStar_Parser_AST.Pragma (_82_173) -> begin
"pragma"
end
| FStar_Parser_AST.Fsdoc (comm, _82_177) -> begin
comm
end))


let decl_documented : FStar_Parser_AST.decl  ->  Prims.bool = (fun d -> (

let tycon_documented = (fun tt -> (

let tyconvars_documented = (fun tycon -> (match (tycon) with
| (FStar_Parser_AST.TyconAbstract (_)) | (FStar_Parser_AST.TyconAbbrev (_)) -> begin
false
end
| FStar_Parser_AST.TyconRecord (_82_192, _82_194, _82_196, fields) -> begin
(FStar_List.existsb (fun _82_203 -> (match (_82_203) with
| (_id, _t, doco) -> begin
(FStar_Util.is_some doco)
end)) fields)
end
| FStar_Parser_AST.TyconVariant (_82_205, _82_207, _82_209, vars) -> begin
(FStar_List.existsb (fun _82_217 -> (match (_82_217) with
| (_id, _t, doco, _u) -> begin
(FStar_Util.is_some doco)
end)) vars)
end))
in (FStar_List.existsb (fun _82_220 -> (match (_82_220) with
| (tycon, doco) -> begin
((tyconvars_documented tycon) || (FStar_Util.is_some doco))
end)) tt)))
in (match (d.FStar_Parser_AST.doc) with
| Some (_82_222) -> begin
true
end
| _82_225 -> begin
(match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Fsdoc (_82_227) -> begin
true
end
| FStar_Parser_AST.Tycon (_82_230, ty) -> begin
(tycon_documented ty)
end
| _82_235 -> begin
false
end)
end)))


let document_decl : (Prims.string  ->  Prims.unit)  ->  FStar_Parser_AST.decl  ->  Prims.unit = (fun w d -> if (decl_documented d) then begin
(

let _82_242 = d
in (match (_82_242) with
| {FStar_Parser_AST.d = decl; FStar_Parser_AST.drange = _82_240; FStar_Parser_AST.doc = fsdoc} -> begin
(

let _82_243 = (let _176_103 = (let _176_102 = (string_of_decl' d.FStar_Parser_AST.d)
in (code_wrap _176_102))
in (w _176_103))
in (

let _82_251 = (match (fsdoc) with
| Some (doc, _kw) -> begin
(w (Prims.strcat "\n" doc))
end
| _82_250 -> begin
()
end)
in (w "")))
end))
end else begin
()
end)


let document_toplevel = (fun name topdecl -> (match (topdecl.FStar_Parser_AST.d) with
| FStar_Parser_AST.TopLevelModule (_82_256) -> begin
(match (topdecl.FStar_Parser_AST.doc) with
| Some (doc, kw) -> begin
(match ((FStar_List.tryFind (fun _82_264 -> (match (_82_264) with
| (k, v) -> begin
(k = "summary")
end)) kw)) with
| None -> begin
((None), (Some (doc)))
end
| Some (_82_267, summary) -> begin
((Some (summary)), (Some (doc)))
end)
end
| None -> begin
((None), (None))
end)
end
| _82_273 -> begin
(Prims.raise (FStar_Syntax_Syntax.Err ("Not a TopLevelModule")))
end))


let document_module : FStar_Parser_AST.modul  ->  FStar_Ident.lid = (fun m -> (

let _82_288 = (match (m) with
| FStar_Parser_AST.Module (n, d) -> begin
((n), (d), ("module"))
end
| FStar_Parser_AST.Interface (n, d, _82_282) -> begin
((n), (d), ("interface"))
end)
in (match (_82_288) with
| (name, decls, _mt) -> begin
(match ((one_toplevel decls)) with
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

let _82_300 = (document_toplevel name top_decl)
in (match (_82_300) with
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
in (

let _82_309 = (let _176_110 = (FStar_Util.format "# module %s" ((name.FStar_Ident.str)::[]))
in (w _176_110))
in (

let _82_311 = (let _176_111 = (FStar_Util.format "%s\n" ((summary)::[]))
in (w _176_111))
in (

let _82_313 = (let _176_112 = (FStar_Util.format "%s\n" ((comment)::[]))
in (w _176_112))
in (

let _82_315 = (FStar_List.iter (document_decl w) other_decls)
in (

let _82_317 = (FStar_Util.close_file fd)
in name)))))))
end)))))))
end
| None -> begin
(let _176_114 = (let _176_113 = (FStar_Util.format1 "No singleton toplevel in module %s" name.FStar_Ident.str)
in FStar_Syntax_Syntax.Err (_176_113))
in (Prims.raise _176_114))
end)
end)))


let generate : Prims.string Prims.list  ->  Prims.unit = (fun files -> (

let modules = (FStar_List.collect (fun fn -> (FStar_Parser_Driver.parse_file fn)) files)
in (

let mods = (FStar_List.map document_module modules)
in (

let on = (FStar_Options.prepend_output_dir "index.md")
in (

let fd = (FStar_Util.open_file_for_writing on)
in (

let _82_327 = (FStar_List.iter (fun m -> (let _176_119 = (FStar_Util.format "%s\n" ((m.FStar_Ident.str)::[]))
in (FStar_Util.append_to_file fd _176_119))) mods)
in (FStar_Util.close_file fd)))))))




