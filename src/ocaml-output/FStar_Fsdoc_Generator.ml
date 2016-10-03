
open Prims

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
| Leaf (_82_3) -> begin
_82_3
end))


let ___Branch____0 = (fun projectee -> (match (projectee) with
| Branch (_82_6) -> begin
_82_6
end))


let htree : mforest FStar_Util.smap = (FStar_Util.smap_create (Prims.parse_int "50"))


let string_of_optiont = (fun f y xo -> (match (xo) with
| Some (x) -> begin
(f x)
end
| None -> begin
y
end))


let string_of_fsdoco : (Prims.string * (Prims.string * Prims.string) Prims.list) Prims.option  ->  Prims.string = (fun d -> (string_of_optiont (fun x -> (let _176_39 = (let _176_38 = (FStar_Parser_AST.string_of_fsdoc x)
in (Prims.strcat _176_38 "*)"))
in (Prims.strcat "(*" _176_39))) "" d))


let string_of_termo : FStar_Parser_AST.term Prims.option  ->  Prims.string = (fun t -> (string_of_optiont FStar_Parser_AST.term_to_string "" t))


let code_wrap : Prims.string  ->  Prims.string = (fun s -> (Prims.strcat "```\n" (Prims.strcat s "\n```\n")))


let string_of_tycon : FStar_Parser_AST.tycon  ->  Prims.string = (fun tycon -> (match (tycon) with
| FStar_Parser_AST.TyconAbstract (_82_19) -> begin
"abstract"
end
| FStar_Parser_AST.TyconAbbrev (_82_22) -> begin
"abbrev"
end
| FStar_Parser_AST.TyconRecord (id, _bb, _ko, fields) -> begin
(let _176_54 = (let _176_53 = (let _176_52 = (let _176_51 = (FStar_All.pipe_right fields (FStar_List.map (fun _82_33 -> (match (_82_33) with
| (id, t, doco) -> begin
(let _176_50 = (string_of_fsdoco doco)
in (let _176_49 = (let _176_48 = (let _176_47 = (FStar_Parser_AST.term_to_string t)
in (Prims.strcat ":" _176_47))
in (Prims.strcat id.FStar_Ident.idText _176_48))
in (Prims.strcat _176_50 _176_49)))
end))))
in (FStar_All.pipe_right _176_51 (FStar_String.concat "; ")))
in (Prims.strcat _176_52 " }"))
in (Prims.strcat " = { " _176_53))
in (Prims.strcat id.FStar_Ident.idText _176_54))
end
| FStar_Parser_AST.TyconVariant (id, _bb, _ko, vars) -> begin
(let _176_62 = (let _176_61 = (let _176_60 = (FStar_All.pipe_right vars (FStar_List.map (fun _82_44 -> (match (_82_44) with
| (id, trmo, doco, u) -> begin
(let _176_59 = (string_of_fsdoco doco)
in (let _176_58 = (let _176_57 = (let _176_56 = (string_of_optiont FStar_Parser_AST.term_to_string "" trmo)
in (Prims.strcat ":" _176_56))
in (Prims.strcat id.FStar_Ident.idText _176_57))
in (Prims.strcat _176_59 _176_58)))
end))))
in (FStar_All.pipe_right _176_60 (FStar_String.concat " | ")))
in (Prims.strcat " = " _176_61))
in (Prims.strcat id.FStar_Ident.idText _176_62))
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
| FStar_Parser_AST.KindAbbrev (i, _82_56, _82_58) -> begin
(Prims.strcat "kind " i.FStar_Ident.idText)
end
| FStar_Parser_AST.ToplevelLet (_82_62, _82_64, pats) -> begin
(let _176_69 = (let _176_68 = (let _176_67 = (let _176_66 = (FStar_Parser_AST.lids_of_let pats)
in (FStar_All.pipe_right _176_66 (FStar_List.map (fun l -> l.FStar_Ident.str))))
in (FStar_All.pipe_right _176_67 (FStar_String.concat ", ")))
in (Prims.strcat "let " _176_68))
in (code_wrap _176_69))
end
| FStar_Parser_AST.Main (_82_70) -> begin
"main ..."
end
| FStar_Parser_AST.Assume (_82_73, i, _82_76) -> begin
(Prims.strcat "assume " i.FStar_Ident.idText)
end
| FStar_Parser_AST.Tycon (_82_80, tys) -> begin
(let _176_76 = (let _176_75 = (let _176_74 = (FStar_All.pipe_right tys (FStar_List.map (fun _82_86 -> (match (_82_86) with
| (t, d) -> begin
(let _176_73 = (string_of_tycon t)
in (let _176_72 = (let _176_71 = (string_of_fsdoco d)
in (Prims.strcat " " _176_71))
in (Prims.strcat _176_73 _176_72)))
end))))
in (FStar_All.pipe_right _176_74 (FStar_String.concat " and ")))
in (Prims.strcat "type " _176_75))
in (code_wrap _176_76))
end
| FStar_Parser_AST.Val (_82_88, i, _82_91) -> begin
(Prims.strcat "val " i.FStar_Ident.idText)
end
| FStar_Parser_AST.Exception (i, _82_96) -> begin
(Prims.strcat "exception " i.FStar_Ident.idText)
end
| (FStar_Parser_AST.NewEffect (_, FStar_Parser_AST.DefineEffect (i, _, _, _, _))) | (FStar_Parser_AST.NewEffect (_, FStar_Parser_AST.RedefineEffect (i, _, _))) -> begin
(Prims.strcat "new_effect " i.FStar_Ident.idText)
end
| (FStar_Parser_AST.NewEffectForFree (_, FStar_Parser_AST.DefineEffect (i, _, _, _, _))) | (FStar_Parser_AST.NewEffectForFree (_, FStar_Parser_AST.RedefineEffect (i, _, _))) -> begin
(Prims.strcat "new_effect_for_free " i.FStar_Ident.idText)
end
| FStar_Parser_AST.SubEffect (_82_150) -> begin
"sub_effect"
end
| FStar_Parser_AST.Pragma (_82_153) -> begin
"pragma"
end
| FStar_Parser_AST.Fsdoc (com, _82_157) -> begin
com
end))


let decl_documented : FStar_Parser_AST.decl  ->  Prims.bool = (fun d -> (

let tycon_documented = (fun tt -> (

let tyconvars_documented = (fun tycon -> (match (tycon) with
| (FStar_Parser_AST.TyconAbstract (_)) | (FStar_Parser_AST.TyconAbbrev (_)) -> begin
false
end
| FStar_Parser_AST.TyconRecord (_82_172, _82_174, _82_176, fields) -> begin
(FStar_List.existsb (fun _82_183 -> (match (_82_183) with
| (_id, _t, doco) -> begin
(FStar_Util.is_some doco)
end)) fields)
end
| FStar_Parser_AST.TyconVariant (_82_185, _82_187, _82_189, vars) -> begin
(FStar_List.existsb (fun _82_197 -> (match (_82_197) with
| (_id, _t, doco, _u) -> begin
(FStar_Util.is_some doco)
end)) vars)
end))
in (FStar_List.existsb (fun _82_200 -> (match (_82_200) with
| (tycon, doco) -> begin
((tyconvars_documented tycon) || (FStar_Util.is_some doco))
end)) tt)))
in (match (d.FStar_Parser_AST.doc) with
| Some (_82_202) -> begin
true
end
| _82_205 -> begin
(match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Fsdoc (_82_207) -> begin
true
end
| FStar_Parser_AST.Tycon (_82_210, ty) -> begin
(tycon_documented ty)
end
| _82_215 -> begin
false
end)
end)))


let document_decl : (Prims.string  ->  Prims.unit)  ->  FStar_Parser_AST.decl  ->  Prims.unit = (fun w d -> if (decl_documented d) then begin
(

let _82_222 = d
in (match (_82_222) with
| {FStar_Parser_AST.d = decl; FStar_Parser_AST.drange = _82_220; FStar_Parser_AST.doc = fsdoc} -> begin
(

let _82_223 = (let _176_95 = (string_of_decl' d.FStar_Parser_AST.d)
in (w _176_95))
in (

let _82_231 = (match (fsdoc) with
| Some (doc, _kw) -> begin
(w (Prims.strcat "\n" doc))
end
| _82_230 -> begin
()
end)
in (w "")))
end))
end else begin
()
end)


let document_toplevel : FStar_Ident.lident  ->  FStar_Parser_AST.decl  ->  Prims.string = (fun name topdecl -> (

let no_doc_provided = (Prims.strcat "(* fsdoc: no doc for module " (Prims.strcat name.FStar_Ident.str " *)"))
in (match (topdecl.FStar_Parser_AST.d) with
| FStar_Parser_AST.TopLevelModule (_82_237) -> begin
(match (topdecl.FStar_Parser_AST.doc) with
| Some (doc, kw) -> begin
(match ((FStar_List.tryFind (fun _82_245 -> (match (_82_245) with
| (k, v) -> begin
(k = "summary")
end)) kw)) with
| None -> begin
doc
end
| Some (_82_248, summary) -> begin
(Prims.strcat "summary:" summary)
end)
end
| None -> begin
no_doc_provided
end)
end
| _82_254 -> begin
(Prims.raise (FStar_Syntax_Syntax.Err ("Not a TopLevelModule")))
end)))


let one_toplevel : FStar_Parser_AST.decl Prims.list  ->  (FStar_Parser_AST.decl * FStar_Parser_AST.decl Prims.list) Prims.option = (fun decls -> (

let _82_264 = (FStar_List.partition (fun d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.TopLevelModule (_82_258) -> begin
true
end
| _82_261 -> begin
false
end)) decls)
in (match (_82_264) with
| (top, nontops) -> begin
(match (top) with
| (t)::[] -> begin
Some (((t), (nontops)))
end
| _82_269 -> begin
None
end)
end)))


let document_module : FStar_Parser_AST.modul  ->  FStar_Ident.lid = (fun m -> (

let _82_284 = (match (m) with
| FStar_Parser_AST.Module (n, d) -> begin
((n), (d), ("module"))
end
| FStar_Parser_AST.Interface (n, d, _82_278) -> begin
((n), (d), ("interface"))
end)
in (match (_82_284) with
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

let com = (document_toplevel name top_decl)
in (

let _82_293 = (let _176_107 = (FStar_Util.format "# module %s" ((name.FStar_Ident.str)::[]))
in (w _176_107))
in (

let _82_295 = (w "```fstar")
in (

let _82_297 = (let _176_108 = (FStar_Util.format "%s" ((com)::[]))
in (w _176_108))
in (

let _82_299 = (w "```")
in (

let _82_308 = (match (top_decl.FStar_Parser_AST.doc) with
| Some (doc, _82_303) -> begin
(w doc)
end
| _82_307 -> begin
()
end)
in (

let _82_310 = (FStar_List.iter (document_decl w) other_decls)
in (

let _82_312 = (FStar_Util.close_file fd)
in name)))))))))))
end
| None -> begin
(let _176_110 = (let _176_109 = (FStar_Util.format1 "No singleton toplevel in module %s" name.FStar_Ident.str)
in FStar_Syntax_Syntax.Err (_176_109))
in (Prims.raise _176_110))
end)
end)))


let generate : Prims.string Prims.list  ->  Prims.unit = (fun files -> (

let modules = (FStar_List.collect (fun fn -> (FStar_Parser_Driver.parse_file fn)) files)
in (

let mod_names = (FStar_List.map document_module modules)
in (

let on = (FStar_Options.prepend_output_dir "index.md")
in (

let fd = (FStar_Util.open_file_for_writing on)
in (

let _82_322 = (FStar_List.iter (fun m -> (let _176_115 = (FStar_Util.format "%s" ((m.FStar_Ident.str)::[]))
in (FStar_Util.append_to_file fd _176_115))) mod_names)
in (FStar_Util.close_file fd)))))))




