
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
| Leaf (_82_4) -> begin
_82_4
end))


let ___Branch____0 = (fun projectee -> (match (projectee) with
| Branch (_82_7) -> begin
_82_7
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
| FStar_Parser_AST.TyconAbstract (_82_20) -> begin
"abstract"
end
| FStar_Parser_AST.TyconAbbrev (_82_23) -> begin
"abbrev"
end
| FStar_Parser_AST.TyconRecord (id, _bb, _ko, fields) -> begin
(let _176_54 = (let _176_53 = (let _176_52 = (let _176_51 = (FStar_All.pipe_right fields (FStar_List.map (fun _82_34 -> (match (_82_34) with
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
(let _176_62 = (let _176_61 = (let _176_60 = (FStar_All.pipe_right vars (FStar_List.map (fun _82_45 -> (match (_82_45) with
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
| FStar_Parser_AST.KindAbbrev (i, _82_57, _82_59) -> begin
(Prims.strcat "kind " i.FStar_Ident.idText)
end
| FStar_Parser_AST.ToplevelLet (_82_63, _82_65, pats) -> begin
(let _176_69 = (let _176_68 = (let _176_67 = (let _176_66 = (FStar_Parser_AST.lids_of_let pats)
in (FStar_All.pipe_right _176_66 (FStar_List.map (fun l -> l.FStar_Ident.str))))
in (FStar_All.pipe_right _176_67 (FStar_String.concat ", ")))
in (Prims.strcat "let " _176_68))
in (code_wrap _176_69))
end
| FStar_Parser_AST.Main (_82_71) -> begin
"main ..."
end
| FStar_Parser_AST.Assume (_82_74, i, _82_77) -> begin
(Prims.strcat "assume " i.FStar_Ident.idText)
end
| FStar_Parser_AST.Tycon (_82_81, tys) -> begin
(let _176_76 = (let _176_75 = (let _176_74 = (FStar_All.pipe_right tys (FStar_List.map (fun _82_87 -> (match (_82_87) with
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
| FStar_Parser_AST.Val (_82_89, i, _82_92) -> begin
(Prims.strcat "val " i.FStar_Ident.idText)
end
| FStar_Parser_AST.Exception (i, _82_97) -> begin
(Prims.strcat "exception " i.FStar_Ident.idText)
end
| (FStar_Parser_AST.NewEffect (_, FStar_Parser_AST.DefineEffect (i, _, _, _, _))) | (FStar_Parser_AST.NewEffect (_, FStar_Parser_AST.RedefineEffect (i, _, _))) -> begin
(Prims.strcat "new_effect " i.FStar_Ident.idText)
end
| (FStar_Parser_AST.NewEffectForFree (_, FStar_Parser_AST.DefineEffect (i, _, _, _, _))) | (FStar_Parser_AST.NewEffectForFree (_, FStar_Parser_AST.RedefineEffect (i, _, _))) -> begin
(Prims.strcat "new_effect_for_free " i.FStar_Ident.idText)
end
| FStar_Parser_AST.SubEffect (_82_151) -> begin
"sub_effect"
end
| FStar_Parser_AST.Pragma (_82_154) -> begin
"pragma"
end
| FStar_Parser_AST.Fsdoc (com, _82_158) -> begin
com
end))


let decl_documented : FStar_Parser_AST.decl  ->  Prims.bool = (fun d -> (

let tycon_documented = (fun tt -> (

let tyconvars_documented = (fun tycon -> (match (tycon) with
| (FStar_Parser_AST.TyconAbstract (_)) | (FStar_Parser_AST.TyconAbbrev (_)) -> begin
false
end
| FStar_Parser_AST.TyconRecord (_82_173, _82_175, _82_177, fields) -> begin
(FStar_List.existsb (fun _82_184 -> (match (_82_184) with
| (_id, _t, doco) -> begin
(FStar_Util.is_some doco)
end)) fields)
end
| FStar_Parser_AST.TyconVariant (_82_186, _82_188, _82_190, vars) -> begin
(FStar_List.existsb (fun _82_198 -> (match (_82_198) with
| (_id, _t, doco, _u) -> begin
(FStar_Util.is_some doco)
end)) vars)
end))
in (FStar_List.existsb (fun _82_201 -> (match (_82_201) with
| (tycon, doco) -> begin
((tyconvars_documented tycon) || (FStar_Util.is_some doco))
end)) tt)))
in (match (d.FStar_Parser_AST.doc) with
| Some (_82_203) -> begin
true
end
| _82_206 -> begin
(match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Fsdoc (_82_208) -> begin
true
end
| FStar_Parser_AST.Tycon (_82_211, ty) -> begin
(tycon_documented ty)
end
| _82_216 -> begin
false
end)
end)))


let document_decl : (Prims.string  ->  Prims.unit)  ->  FStar_Parser_AST.decl  ->  Prims.unit = (fun w d -> if (decl_documented d) then begin
(

let _82_223 = d
in (match (_82_223) with
| {FStar_Parser_AST.d = decl; FStar_Parser_AST.drange = _82_221; FStar_Parser_AST.doc = fsdoc} -> begin
(

let _82_224 = (let _176_95 = (string_of_decl' d.FStar_Parser_AST.d)
in (w _176_95))
in (

let _82_232 = (match (fsdoc) with
| Some (doc, _kw) -> begin
(w (Prims.strcat "\n" doc))
end
| _82_231 -> begin
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
| FStar_Parser_AST.TopLevelModule (_82_238) -> begin
(match (topdecl.FStar_Parser_AST.doc) with
| Some (doc, kw) -> begin
(match ((FStar_List.tryFind (fun _82_246 -> (match (_82_246) with
| (k, v) -> begin
(k = "summary")
end)) kw)) with
| None -> begin
doc
end
| Some (_82_249, summary) -> begin
(Prims.strcat "summary:" summary)
end)
end
| None -> begin
no_doc_provided
end)
end
| _82_255 -> begin
(Prims.raise (FStar_Syntax_Syntax.Err ("Not a TopLevelModule")))
end)))


let one_toplevel : FStar_Parser_AST.decl Prims.list  ->  (FStar_Parser_AST.decl * FStar_Parser_AST.decl Prims.list) Prims.option = (fun decls -> (

let _82_265 = (FStar_List.partition (fun d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.TopLevelModule (_82_259) -> begin
true
end
| _82_262 -> begin
false
end)) decls)
in (match (_82_265) with
| (top, nontops) -> begin
(match (top) with
| (t)::[] -> begin
Some (((t), (nontops)))
end
| _82_270 -> begin
None
end)
end)))


let document_module : FStar_Parser_AST.modul  ->  FStar_Ident.lid = (fun m -> (

let _82_272 = (let _176_107 = (let _176_106 = (FStar_Parser_AST.modul_to_string m)
in (_176_106)::[])
in (FStar_Util.print "doc_module: %s\n" _176_107))
in (

let _82_287 = (match (m) with
| FStar_Parser_AST.Module (n, d) -> begin
((n), (d), ("module"))
end
| FStar_Parser_AST.Interface (n, d, _82_281) -> begin
((n), (d), ("interface"))
end)
in (match (_82_287) with
| (name, decls, _mt) -> begin
(match ((one_toplevel decls)) with
| Some (top_decl, other_decls) -> begin
(

let on = (FStar_Options.prepend_output_dir (Prims.strcat name.FStar_Ident.str ".mk"))
in (

let fd = (FStar_Util.open_file_for_writing on)
in (

let w = (FStar_Util.append_to_file fd)
in (

let com = (document_toplevel name top_decl)
in (

let _82_296 = (let _176_109 = (FStar_Util.format "# module %s" ((name.FStar_Ident.str)::[]))
in (w _176_109))
in (

let _82_298 = (w "```fstar")
in (

let _82_300 = (let _176_110 = (FStar_Util.format "%s" ((com)::[]))
in (w _176_110))
in (

let _82_302 = (w "```")
in (

let _82_311 = (match (top_decl.FStar_Parser_AST.doc) with
| Some (doc, _82_306) -> begin
(w doc)
end
| _82_310 -> begin
()
end)
in (

let _82_313 = (FStar_List.iter (document_decl w) other_decls)
in (

let _82_315 = (FStar_Util.close_file fd)
in name)))))))))))
end
| None -> begin
(let _176_112 = (let _176_111 = (FStar_Util.format1 "No singleton toplevel in module %s" name.FStar_Ident.str)
in FStar_Syntax_Syntax.Err (_176_111))
in (Prims.raise _176_112))
end)
end))))


let generate : Prims.string Prims.list  ->  Prims.unit = (fun files -> (

let modules = (FStar_List.collect (fun fn -> (FStar_Parser_Driver.parse_file fn)) files)
in (

let mod_names = (FStar_List.map document_module modules)
in (

let on = (FStar_Options.prepend_output_dir "index.mk")
in (

let fd = (FStar_Util.open_file_for_writing on)
in (

let _82_325 = (FStar_List.iter (fun m -> (let _176_117 = (FStar_Util.format "%s" ((m.FStar_Ident.str)::[]))
in (FStar_Util.append_to_file fd _176_117))) mod_names)
in (FStar_Util.close_file fd)))))))


let as_frag : FStar_Parser_AST.decl  ->  FStar_Parser_AST.decl Prims.list  ->  (FStar_Parser_AST.modul Prims.list, FStar_Parser_AST.decl Prims.list) FStar_Util.either = (fun d ds -> (

let rec as_mlist = (fun out _82_336 ds -> (match (_82_336) with
| ((m, r, doc), cur) -> begin
(match (ds) with
| [] -> begin
(FStar_List.rev ((FStar_Parser_AST.Module (((m), (((FStar_Parser_AST.mk_decl (FStar_Parser_AST.TopLevelModule (m)) r doc))::(FStar_List.rev cur)))))::out))
end
| (d)::ds -> begin
(match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.TopLevelModule (m') -> begin
(as_mlist ((FStar_Parser_AST.Module (((m), (((FStar_Parser_AST.mk_decl (FStar_Parser_AST.TopLevelModule (m)) r doc))::(FStar_List.rev cur)))))::out) ((((m'), (d.FStar_Parser_AST.drange), (d.FStar_Parser_AST.doc))), ([])) ds)
end
| _82_345 -> begin
(as_mlist out ((((m), (r), (doc))), ((d)::cur)) ds)
end)
end)
end))
in (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.TopLevelModule (m) -> begin
(

let ms = (as_mlist [] ((((m), (d.FStar_Parser_AST.drange), (d.FStar_Parser_AST.doc))), ([])) ds)
in (

let _82_363 = ()
in FStar_Util.Inl (ms)))
end
| _82_366 -> begin
(

let ds = (d)::ds
in (

let _82_378 = (FStar_List.iter (fun _82_1 -> (match (_82_1) with
| {FStar_Parser_AST.d = FStar_Parser_AST.TopLevelModule (_82_373); FStar_Parser_AST.drange = r; FStar_Parser_AST.doc = _82_370} -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Unexpected module declaration"), (r)))))
end
| _82_377 -> begin
()
end)) ds)
in FStar_Util.Inr (ds)))
end)))




