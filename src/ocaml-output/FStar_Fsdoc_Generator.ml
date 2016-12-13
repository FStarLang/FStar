
open Prims

let one_toplevel : FStar_Parser_AST.decl Prims.list  ->  (FStar_Parser_AST.decl * FStar_Parser_AST.decl Prims.list) Prims.option = (fun decls -> (

let _84_10 = (FStar_List.partition (fun d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.TopLevelModule (_84_4) -> begin
true
end
| _84_7 -> begin
false
end)) decls)
in (match (_84_10) with
| (top, nontops) -> begin
(match (top) with
| (t)::[] -> begin
Some (((t), (nontops)))
end
| _84_15 -> begin
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
| Leaf (_84_18) -> begin
_84_18
end))


let ___Branch____0 = (fun projectee -> (match (projectee) with
| Branch (_84_21) -> begin
_84_21
end))


let htree : mforest FStar_Util.smap = (FStar_Util.smap_create (Prims.parse_int "50"))


let string_of_optiont = (fun f y xo -> (match (xo) with
| Some (x) -> begin
(f x)
end
| None -> begin
y
end))


let string_of_fsdoco : (Prims.string * (Prims.string * Prims.string) Prims.list) Prims.option  ->  Prims.string = (fun d -> (string_of_optiont (fun x -> (let _181_42 = (let _181_41 = (FStar_Parser_AST.string_of_fsdoc x)
in (Prims.strcat _181_41 "*)"))
in (Prims.strcat "(*" _181_42))) "" d))


let string_of_termo : FStar_Parser_AST.term Prims.option  ->  Prims.string = (fun t -> (string_of_optiont FStar_Parser_AST.term_to_string "" t))


let code_wrap : Prims.string  ->  Prims.string = (fun s -> (Prims.strcat "```fsharp\n" (Prims.strcat s "\n```\n")))


let string_of_tycon : FStar_Parser_AST.tycon  ->  Prims.string = (fun tycon -> (match (tycon) with
| FStar_Parser_AST.TyconAbstract (_84_34) -> begin
"abstract"
end
| FStar_Parser_AST.TyconAbbrev (_84_37) -> begin
"abbrev"
end
| FStar_Parser_AST.TyconRecord (id, _bb, _ko, fields) -> begin
(let _181_57 = (let _181_56 = (let _181_55 = (let _181_54 = (FStar_All.pipe_right fields (FStar_List.map (fun _84_48 -> (match (_84_48) with
| (id, t, doco) -> begin
(let _181_53 = (string_of_fsdoco doco)
in (let _181_52 = (let _181_51 = (let _181_50 = (FStar_Parser_AST.term_to_string t)
in (Prims.strcat ":" _181_50))
in (Prims.strcat id.FStar_Ident.idText _181_51))
in (Prims.strcat _181_53 _181_52)))
end))))
in (FStar_All.pipe_right _181_54 (FStar_String.concat "; ")))
in (Prims.strcat _181_55 " }"))
in (Prims.strcat " = { " _181_56))
in (Prims.strcat id.FStar_Ident.idText _181_57))
end
| FStar_Parser_AST.TyconVariant (id, _bb, _ko, vars) -> begin
(let _181_65 = (let _181_64 = (let _181_63 = (FStar_All.pipe_right vars (FStar_List.map (fun _84_59 -> (match (_84_59) with
| (id, trmo, doco, u) -> begin
(let _181_62 = (string_of_fsdoco doco)
in (let _181_61 = (let _181_60 = (let _181_59 = (string_of_optiont FStar_Parser_AST.term_to_string "" trmo)
in (Prims.strcat ":" _181_59))
in (Prims.strcat id.FStar_Ident.idText _181_60))
in (Prims.strcat _181_62 _181_61)))
end))))
in (FStar_All.pipe_right _181_63 (FStar_String.concat " | ")))
in (Prims.strcat " = " _181_64))
in (Prims.strcat id.FStar_Ident.idText _181_65))
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
| FStar_Parser_AST.KindAbbrev (i, _84_71, _84_73) -> begin
(Prims.strcat "kind " i.FStar_Ident.idText)
end
| FStar_Parser_AST.TopLevelLet (_84_77, _84_79, pats) -> begin
(

let termty = (FStar_List.map (fun _84_85 -> (match (_84_85) with
| (p, t) -> begin
(let _181_70 = (FStar_Parser_AST.pat_to_string p)
in (let _181_69 = (FStar_Parser_AST.term_to_string t)
in ((_181_70), (_181_69))))
end)) pats)
in (

let termty' = (FStar_List.map (fun _84_89 -> (match (_84_89) with
| (p, t) -> begin
(Prims.strcat p (Prims.strcat ":" t))
end)) termty)
in (Prims.strcat "let " (FStar_String.concat ", " termty'))))
end
| FStar_Parser_AST.Main (_84_92) -> begin
"main ..."
end
| FStar_Parser_AST.Assume (_84_95, i, t) -> begin
(let _181_74 = (let _181_73 = (let _181_72 = (FStar_Parser_AST.term_to_string t)
in (Prims.strcat ":" _181_72))
in (Prims.strcat i.FStar_Ident.idText _181_73))
in (Prims.strcat "assume " _181_74))
end
| FStar_Parser_AST.Tycon (_84_101, tys) -> begin
(let _181_80 = (let _181_79 = (FStar_All.pipe_right tys (FStar_List.map (fun _84_107 -> (match (_84_107) with
| (t, d) -> begin
(let _181_78 = (string_of_tycon t)
in (let _181_77 = (let _181_76 = (string_of_fsdoco d)
in (Prims.strcat " " _181_76))
in (Prims.strcat _181_78 _181_77)))
end))))
in (FStar_All.pipe_right _181_79 (FStar_String.concat " and ")))
in (Prims.strcat "type " _181_80))
end
| FStar_Parser_AST.Val (_84_109, i, t) -> begin
(let _181_83 = (let _181_82 = (let _181_81 = (FStar_Parser_AST.term_to_string t)
in (Prims.strcat ":" _181_81))
in (Prims.strcat i.FStar_Ident.idText _181_82))
in (Prims.strcat "val " _181_83))
end
| FStar_Parser_AST.Exception (i, _84_116) -> begin
(Prims.strcat "exception " i.FStar_Ident.idText)
end
| (FStar_Parser_AST.NewEffect (_, FStar_Parser_AST.DefineEffect (i, _, _, _, _))) | (FStar_Parser_AST.NewEffect (_, FStar_Parser_AST.RedefineEffect (i, _, _))) -> begin
(Prims.strcat "new_effect " i.FStar_Ident.idText)
end
| (FStar_Parser_AST.NewEffectForFree (_, FStar_Parser_AST.DefineEffect (i, _, _, _, _))) | (FStar_Parser_AST.NewEffectForFree (_, FStar_Parser_AST.RedefineEffect (i, _, _))) -> begin
(Prims.strcat "new_effect_for_free " i.FStar_Ident.idText)
end
| FStar_Parser_AST.SubEffect (_84_170) -> begin
"sub_effect"
end
| FStar_Parser_AST.Pragma (_84_173) -> begin
"pragma"
end
| FStar_Parser_AST.Fsdoc (comm, _84_177) -> begin
comm
end))


let decl_documented : FStar_Parser_AST.decl  ->  Prims.bool = (fun d -> (

let tycon_documented = (fun tt -> (

let tyconvars_documented = (fun tycon -> (match (tycon) with
| (FStar_Parser_AST.TyconAbstract (_)) | (FStar_Parser_AST.TyconAbbrev (_)) -> begin
false
end
| FStar_Parser_AST.TyconRecord (_84_192, _84_194, _84_196, fields) -> begin
(FStar_List.existsb (fun _84_203 -> (match (_84_203) with
| (_id, _t, doco) -> begin
(FStar_Util.is_some doco)
end)) fields)
end
| FStar_Parser_AST.TyconVariant (_84_205, _84_207, _84_209, vars) -> begin
(FStar_List.existsb (fun _84_217 -> (match (_84_217) with
| (_id, _t, doco, _u) -> begin
(FStar_Util.is_some doco)
end)) vars)
end))
in (FStar_List.existsb (fun _84_220 -> (match (_84_220) with
| (tycon, doco) -> begin
((tyconvars_documented tycon) || (FStar_Util.is_some doco))
end)) tt)))
in (match (d.FStar_Parser_AST.doc) with
| Some (_84_222) -> begin
true
end
| _84_225 -> begin
(match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Fsdoc (_84_227) -> begin
true
end
| FStar_Parser_AST.Tycon (_84_230, ty) -> begin
(tycon_documented ty)
end
| _84_235 -> begin
false
end)
end)))


let document_decl : (Prims.string  ->  Prims.unit)  ->  FStar_Parser_AST.decl  ->  Prims.unit = (fun w d -> if (decl_documented d) then begin
(

let _84_242 = d
in (match (_84_242) with
| {FStar_Parser_AST.d = decl; FStar_Parser_AST.drange = _84_240; FStar_Parser_AST.doc = fsdoc} -> begin
(

let _84_243 = (let _181_103 = (let _181_102 = (string_of_decl' d.FStar_Parser_AST.d)
in (code_wrap _181_102))
in (w _181_103))
in (

let _84_251 = (match (fsdoc) with
| Some (doc, _kw) -> begin
(w (Prims.strcat "\n" doc))
end
| _84_250 -> begin
()
end)
in (w "")))
end))
end else begin
()
end)


let document_toplevel = (fun name topdecl -> (match (topdecl.FStar_Parser_AST.d) with
| FStar_Parser_AST.TopLevelModule (_84_256) -> begin
(match (topdecl.FStar_Parser_AST.doc) with
| Some (doc, kw) -> begin
(match ((FStar_List.tryFind (fun _84_264 -> (match (_84_264) with
| (k, v) -> begin
(k = "summary")
end)) kw)) with
| None -> begin
((None), (Some (doc)))
end
| Some (_84_267, summary) -> begin
((Some (summary)), (Some (doc)))
end)
end
| None -> begin
((None), (None))
end)
end
| _84_273 -> begin
(Prims.raise (FStar_Syntax_Syntax.Err ("Not a TopLevelModule")))
end))


let document_module : FStar_Parser_AST.modul  ->  FStar_Ident.lid = (fun m -> (

let _84_288 = (match (m) with
| FStar_Parser_AST.Module (n, d) -> begin
((n), (d), ("module"))
end
| FStar_Parser_AST.Interface (n, d, _84_282) -> begin
((n), (d), ("interface"))
end)
in (match (_84_288) with
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

let _84_300 = (document_toplevel name top_decl)
in (match (_84_300) with
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

let _84_309 = (let _181_110 = (FStar_Util.format "# module %s" ((name.FStar_Ident.str)::[]))
in (w _181_110))
in (

let _84_311 = (let _181_111 = (FStar_Util.format "%s\n" ((summary)::[]))
in (w _181_111))
in (

let _84_313 = (let _181_112 = (FStar_Util.format "%s\n" ((comment)::[]))
in (w _181_112))
in (

let _84_315 = (FStar_List.iter (document_decl w) other_decls)
in (

let _84_317 = (FStar_Util.close_file fd)
in name)))))))
end)))))))
end
| None -> begin
(let _181_114 = (let _181_113 = (FStar_Util.format1 "No singleton toplevel in module %s" name.FStar_Ident.str)
in FStar_Syntax_Syntax.Err (_181_113))
in (Prims.raise _181_114))
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

let _84_327 = (FStar_List.iter (fun m -> (let _181_119 = (FStar_Util.format "%s\n" ((m.FStar_Ident.str)::[]))
in (FStar_Util.append_to_file fd _181_119))) mods)
in (FStar_Util.close_file fd)))))))




