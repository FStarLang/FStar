
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
| Leaf (_81_3) -> begin
_81_3
end))


let ___Branch____0 = (fun projectee -> (match (projectee) with
| Branch (_81_6) -> begin
_81_6
end))


let htree : mforest FStar_Util.smap = (FStar_Util.smap_create (Prims.parse_int "50"))


let string_of_optiont = (fun f y xo -> (match (xo) with
| Some (x) -> begin
(f x)
end
| None -> begin
y
end))


let string_of_fsdoco : (Prims.string * (Prims.string * Prims.string) Prims.list) Prims.option  ->  Prims.string = (fun d -> (string_of_optiont (fun x -> (let _174_39 = (let _174_38 = (FStar_Parser_AST.string_of_fsdoc x)
in (Prims.strcat _174_38 "*)"))
in (Prims.strcat "(*" _174_39))) "" d))


let string_of_termo : FStar_Parser_AST.term Prims.option  ->  Prims.string = (fun t -> (string_of_optiont FStar_Parser_AST.term_to_string "" t))


let string_of_tycon : FStar_Parser_AST.tycon  ->  Prims.string = (fun tycon -> (match (tycon) with
| FStar_Parser_AST.TyconAbstract (_81_18) -> begin
"abstract"
end
| FStar_Parser_AST.TyconAbbrev (_81_21) -> begin
"abbrev"
end
| FStar_Parser_AST.TyconRecord (id, _bb, _ko, fields) -> begin
(let _174_52 = (let _174_51 = (let _174_50 = (let _174_49 = (FStar_All.pipe_right fields (FStar_List.map (fun _81_32 -> (match (_81_32) with
| (id, t, doco) -> begin
(let _174_48 = (string_of_fsdoco doco)
in (let _174_47 = (let _174_46 = (let _174_45 = (FStar_Parser_AST.term_to_string t)
in (Prims.strcat ":" _174_45))
in (Prims.strcat id.FStar_Ident.idText _174_46))
in (Prims.strcat _174_48 _174_47)))
end))))
in (FStar_All.pipe_right _174_49 (FStar_String.concat "; ")))
in (Prims.strcat _174_50 " }"))
in (Prims.strcat " = { " _174_51))
in (Prims.strcat id.FStar_Ident.idText _174_52))
end
| FStar_Parser_AST.TyconVariant (id, _bb, _ko, vars) -> begin
(let _174_60 = (let _174_59 = (let _174_58 = (FStar_All.pipe_right vars (FStar_List.map (fun _81_43 -> (match (_81_43) with
| (id, trmo, doco, u) -> begin
(let _174_57 = (string_of_fsdoco doco)
in (let _174_56 = (let _174_55 = (let _174_54 = (string_of_optiont FStar_Parser_AST.term_to_string "" trmo)
in (Prims.strcat ":" _174_54))
in (Prims.strcat id.FStar_Ident.idText _174_55))
in (Prims.strcat _174_57 _174_56)))
end))))
in (FStar_All.pipe_right _174_58 (FStar_String.concat " | ")))
in (Prims.strcat " = | " _174_59))
in (Prims.strcat id.FStar_Ident.idText _174_60))
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
| FStar_Parser_AST.KindAbbrev (i, _81_55, _81_57) -> begin
(Prims.strcat "kind " i.FStar_Ident.idText)
end
| FStar_Parser_AST.ToplevelLet (_81_61, _81_63, pats) -> begin
(let _174_66 = (let _174_65 = (let _174_64 = (FStar_Parser_AST.lids_of_let pats)
in (FStar_All.pipe_right _174_64 (FStar_List.map (fun l -> l.FStar_Ident.str))))
in (FStar_All.pipe_right _174_65 (FStar_String.concat ", ")))
in (Prims.strcat "let " _174_66))
end
| FStar_Parser_AST.Main (_81_69) -> begin
"main ..."
end
| FStar_Parser_AST.Assume (_81_72, i, _81_75) -> begin
(Prims.strcat "assume " i.FStar_Ident.idText)
end
| FStar_Parser_AST.Tycon (_81_79, tys) -> begin
(let _174_71 = (let _174_70 = (FStar_All.pipe_right tys (FStar_List.map (fun _81_85 -> (match (_81_85) with
| (t, d) -> begin
(let _174_69 = (string_of_tycon t)
in (let _174_68 = (string_of_fsdoco d)
in (Prims.strcat _174_69 _174_68)))
end))))
in (FStar_All.pipe_right _174_70 (FStar_String.concat ", ")))
in (Prims.strcat "type " _174_71))
end
| FStar_Parser_AST.Val (_81_87, i, _81_90) -> begin
(Prims.strcat "val " i.FStar_Ident.idText)
end
| FStar_Parser_AST.Exception (i, _81_95) -> begin
(Prims.strcat "exception " i.FStar_Ident.idText)
end
| (FStar_Parser_AST.NewEffect (_, FStar_Parser_AST.DefineEffect (i, _, _, _, _))) | (FStar_Parser_AST.NewEffect (_, FStar_Parser_AST.RedefineEffect (i, _, _))) -> begin
(Prims.strcat "new_effect " i.FStar_Ident.idText)
end
| (FStar_Parser_AST.NewEffectForFree (_, FStar_Parser_AST.DefineEffect (i, _, _, _, _))) | (FStar_Parser_AST.NewEffectForFree (_, FStar_Parser_AST.RedefineEffect (i, _, _))) -> begin
(Prims.strcat "new_effect_for_free " i.FStar_Ident.idText)
end
| FStar_Parser_AST.SubEffect (_81_149) -> begin
"sub_effect"
end
| FStar_Parser_AST.Pragma (_81_152) -> begin
"pragma"
end
| FStar_Parser_AST.Fsdoc (fsd) -> begin
(Prims.strcat "(*" (Prims.strcat (Prims.fst fsd) "*)"))
end))


let decl_documented : FStar_Parser_AST.decl  ->  Prims.bool = (fun d -> (

let tycon_documented = (fun tt -> (

let tyconvars_documented = (fun tycon -> (match (tycon) with
| (FStar_Parser_AST.TyconAbstract (_)) | (FStar_Parser_AST.TyconAbbrev (_)) -> begin
false
end
| FStar_Parser_AST.TyconRecord (_81_168, _81_170, _81_172, fields) -> begin
(FStar_List.existsb (fun _81_179 -> (match (_81_179) with
| (_id, _t, doco) -> begin
(FStar_Util.is_some doco)
end)) fields)
end
| FStar_Parser_AST.TyconVariant (_81_181, _81_183, _81_185, vars) -> begin
(FStar_List.existsb (fun _81_193 -> (match (_81_193) with
| (_id, _t, doco, _u) -> begin
(FStar_Util.is_some doco)
end)) vars)
end))
in (FStar_List.existsb (fun _81_196 -> (match (_81_196) with
| (tycon, doco) -> begin
((tyconvars_documented tycon) || (FStar_Util.is_some doco))
end)) tt)))
in (match (d.FStar_Parser_AST.doc) with
| Some (_81_198) -> begin
true
end
| _81_201 -> begin
(match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Fsdoc (_81_203) -> begin
true
end
| FStar_Parser_AST.Tycon (_81_206, ty) -> begin
(tycon_documented ty)
end
| _81_211 -> begin
false
end)
end)))


let document_decl : (Prims.string  ->  Prims.unit)  ->  FStar_Parser_AST.decl  ->  Prims.unit = (fun w d -> if (decl_documented d) then begin
(

let _81_218 = d
in (match (_81_218) with
| {FStar_Parser_AST.d = decl; FStar_Parser_AST.drange = _81_216; FStar_Parser_AST.doc = fsdoc} -> begin
(

let _81_225 = (match (fsdoc) with
| Some (doc, _kw) -> begin
(w doc)
end
| _81_224 -> begin
()
end)
in (

let _81_227 = (w "```fstar")
in (

let _81_229 = (let _174_90 = (string_of_decl' d.FStar_Parser_AST.d)
in (w _174_90))
in (w "```\n"))))
end))
end else begin
()
end)


let document_toplevel : FStar_Ident.lident  ->  FStar_Parser_AST.decl Prims.list  ->  ((FStar_Ident.lid * FStar_Parser_AST.fsdoc Prims.option) Prims.option * FStar_Ident.lid * Prims.string) = (fun name decls -> (

let no_doc_provided = (Prims.strcat "(* no fsdoc provided for module " (Prims.strcat name.FStar_Ident.str " *)"))
in (

let f = (fun d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.TopLevelModule (k) -> begin
Some (((k), (d.FStar_Parser_AST.doc)))
end
| _81_239 -> begin
None
end))
in (

let mdoc = (FStar_List.tryPick f decls)
in (

let _81_263 = (match (mdoc) with
| Some (n, com) -> begin
(

let com = (match (com) with
| Some (doc, kw) -> begin
(match ((FStar_List.tryFind (fun _81_251 -> (match (_81_251) with
| (k, v) -> begin
(k = "summary")
end)) kw)) with
| None -> begin
doc
end
| Some (_81_254, summary) -> begin
(Prims.strcat "summary:" summary)
end)
end
| None -> begin
no_doc_provided
end)
in ((n), (com)))
end
| None -> begin
((name), (no_doc_provided))
end)
in (match (_81_263) with
| (name, com) -> begin
((mdoc), (name), (com))
end))))))


let exists_toplevel : FStar_Parser_AST.decl Prims.list  ->  Prims.unit = (fun decls -> (

let r = (FStar_List.existsb (fun d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.TopLevelModule (_81_267) -> begin
true
end
| _81_270 -> begin
false
end)) decls)
in (FStar_Util.print1 "+ exists_toplevel: %b\n" (Prims.string_of_bool r))))


let document_module : FStar_Parser_AST.modul  ->  FStar_Ident.lid = (fun m -> (

let _81_286 = (match (m) with
| FStar_Parser_AST.Module (n, d) -> begin
((n), (d), ("module"))
end
| FStar_Parser_AST.Interface (n, d, _81_280) -> begin
((n), (d), ("interface"))
end)
in (match (_81_286) with
| (name, decls, _mt) -> begin
(

let _81_287 = (exists_toplevel decls)
in (

let _81_292 = (document_toplevel name decls)
in (match (_81_292) with
| (mdoc, name, com) -> begin
(

let on = (FStar_Options.prepend_output_dir (Prims.strcat name.FStar_Ident.str ".mk"))
in (

let fd = (FStar_Util.open_file_for_writing on)
in (

let w = (FStar_Util.append_to_file fd)
in (

let _81_296 = (let _174_104 = (FStar_Util.format "# module %s" ((name.FStar_Ident.str)::[]))
in (w _174_104))
in (

let _81_298 = (w "```fstar")
in (

let _81_300 = (let _174_105 = (FStar_Util.format "%s" ((com)::[]))
in (w _174_105))
in (

let _81_302 = (w "```")
in (

let _81_315 = (match (mdoc) with
| Some (_81_305, Some (doc, _81_308)) -> begin
(w doc)
end
| _81_314 -> begin
()
end)
in (

let _81_317 = (FStar_List.iter (document_decl w) decls)
in (

let _81_319 = (FStar_Util.close_file fd)
in name))))))))))
end)))
end)))


let generate : Prims.string Prims.list  ->  Prims.unit = (fun files -> (

let modules = (FStar_List.collect (fun fn -> (FStar_Parser_Driver.parse_file fn)) files)
in (

let mod_names = (FStar_List.map document_module modules)
in (

let on = (FStar_Options.prepend_output_dir "index.mk")
in (

let fd = (FStar_Util.open_file_for_writing on)
in (

let _81_328 = (FStar_List.iter (fun m -> (let _174_110 = (FStar_Util.format "%s" ((m.FStar_Ident.str)::[]))
in (FStar_Util.append_to_file fd _174_110))) mod_names)
in (FStar_Util.close_file fd)))))))




