
open Prims

let one_toplevel : FStar_Parser_AST.decl Prims.list  ->  (FStar_Parser_AST.decl * FStar_Parser_AST.decl Prims.list) Prims.option = (fun decls -> (

let _87_10 = (FStar_List.partition (fun d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.TopLevelModule (_87_4) -> begin
true
end
| _87_7 -> begin
false
end)) decls)
in (match (_87_10) with
| (top, nontops) -> begin
(match (top) with
| (t)::[] -> begin
Some (((t), (nontops)))
end
| _87_15 -> begin
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
| Leaf (_87_18) -> begin
_87_18
end))


let ___Branch____0 = (fun projectee -> (match (projectee) with
| Branch (_87_21) -> begin
_87_21
end))


let htree : mforest FStar_Util.smap = (FStar_Util.smap_create (Prims.parse_int "50"))


let string_of_optiont = (fun f y xo -> (match (xo) with
| Some (x) -> begin
(f x)
end
| None -> begin
y
end))


let string_of_fsdoco : (Prims.string * (Prims.string * Prims.string) Prims.list) Prims.option  ->  Prims.string = (fun d -> (string_of_optiont (fun x -> (let _187_42 = (let _187_41 = (FStar_Parser_AST.string_of_fsdoc x)
in (Prims.strcat _187_41 "*)"))
in (Prims.strcat "(*" _187_42))) "" d))


let string_of_termo : FStar_Parser_AST.term Prims.option  ->  Prims.string = (fun t -> (string_of_optiont FStar_Parser_AST.term_to_string "" t))


let code_wrap : Prims.string  ->  Prims.string = (fun s -> (Prims.strcat "```fsharp\n" (Prims.strcat s "\n```\n")))


let string_of_tycon : FStar_Parser_AST.tycon  ->  Prims.string = (fun tycon -> (match (tycon) with
| FStar_Parser_AST.TyconAbstract (_87_34) -> begin
"abstract"
end
| FStar_Parser_AST.TyconAbbrev (_87_37) -> begin
"abbrev"
end
| FStar_Parser_AST.TyconRecord (id, _bb, _ko, fields) -> begin
(let _187_57 = (let _187_56 = (let _187_55 = (let _187_54 = (FStar_All.pipe_right fields (FStar_List.map (fun _87_48 -> (match (_87_48) with
| (id, t, doco) -> begin
(let _187_53 = (string_of_fsdoco doco)
in (let _187_52 = (let _187_51 = (let _187_50 = (FStar_Parser_AST.term_to_string t)
in (Prims.strcat ":" _187_50))
in (Prims.strcat id.FStar_Ident.idText _187_51))
in (Prims.strcat _187_53 _187_52)))
end))))
in (FStar_All.pipe_right _187_54 (FStar_String.concat "; ")))
in (Prims.strcat _187_55 " }"))
in (Prims.strcat " = { " _187_56))
in (Prims.strcat id.FStar_Ident.idText _187_57))
end
| FStar_Parser_AST.TyconVariant (id, _bb, _ko, vars) -> begin
(let _187_65 = (let _187_64 = (let _187_63 = (FStar_All.pipe_right vars (FStar_List.map (fun _87_59 -> (match (_87_59) with
| (id, trmo, doco, u) -> begin
(let _187_62 = (string_of_fsdoco doco)
in (let _187_61 = (let _187_60 = (let _187_59 = (string_of_optiont FStar_Parser_AST.term_to_string "" trmo)
in (Prims.strcat ":" _187_59))
in (Prims.strcat id.FStar_Ident.idText _187_60))
in (Prims.strcat _187_62 _187_61)))
end))))
in (FStar_All.pipe_right _187_63 (FStar_String.concat " | ")))
in (Prims.strcat " = " _187_64))
in (Prims.strcat id.FStar_Ident.idText _187_65))
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
| FStar_Parser_AST.KindAbbrev (i, _87_71, _87_73) -> begin
(Prims.strcat "kind " i.FStar_Ident.idText)
end
| FStar_Parser_AST.TopLevelLet (_87_77, pats) -> begin
(

let termty = (FStar_List.map (fun _87_83 -> (match (_87_83) with
| (p, t) -> begin
(let _187_70 = (FStar_Parser_AST.pat_to_string p)
in (let _187_69 = (FStar_Parser_AST.term_to_string t)
in ((_187_70), (_187_69))))
end)) pats)
in (

let termty' = (FStar_List.map (fun _87_87 -> (match (_87_87) with
| (p, t) -> begin
(Prims.strcat p (Prims.strcat ":" t))
end)) termty)
in (Prims.strcat "let " (FStar_String.concat ", " termty'))))
end
| FStar_Parser_AST.Main (_87_90) -> begin
"main ..."
end
| FStar_Parser_AST.Assume (i, t) -> begin
(let _187_74 = (let _187_73 = (let _187_72 = (FStar_Parser_AST.term_to_string t)
in (Prims.strcat ":" _187_72))
in (Prims.strcat i.FStar_Ident.idText _187_73))
in (Prims.strcat "assume " _187_74))
end
| FStar_Parser_AST.Tycon (_87_97, tys) -> begin
(let _187_80 = (let _187_79 = (FStar_All.pipe_right tys (FStar_List.map (fun _87_103 -> (match (_87_103) with
| (t, d) -> begin
(let _187_78 = (string_of_tycon t)
in (let _187_77 = (let _187_76 = (string_of_fsdoco d)
in (Prims.strcat " " _187_76))
in (Prims.strcat _187_78 _187_77)))
end))))
in (FStar_All.pipe_right _187_79 (FStar_String.concat " and ")))
in (Prims.strcat "type " _187_80))
end
| FStar_Parser_AST.Val (i, t) -> begin
(let _187_83 = (let _187_82 = (let _187_81 = (FStar_Parser_AST.term_to_string t)
in (Prims.strcat ":" _187_81))
in (Prims.strcat i.FStar_Ident.idText _187_82))
in (Prims.strcat "val " _187_83))
end
| FStar_Parser_AST.Exception (i, _87_110) -> begin
(Prims.strcat "exception " i.FStar_Ident.idText)
end
| (FStar_Parser_AST.NewEffect (FStar_Parser_AST.DefineEffect (i, _, _, _, _))) | (FStar_Parser_AST.NewEffect (FStar_Parser_AST.RedefineEffect (i, _, _))) -> begin
(Prims.strcat "new_effect " i.FStar_Ident.idText)
end
| (FStar_Parser_AST.NewEffectForFree (FStar_Parser_AST.DefineEffect (i, _, _, _, _))) | (FStar_Parser_AST.NewEffectForFree (FStar_Parser_AST.RedefineEffect (i, _, _))) -> begin
(Prims.strcat "new_effect_for_free " i.FStar_Ident.idText)
end
| FStar_Parser_AST.SubEffect (_87_152) -> begin
"sub_effect"
end
| FStar_Parser_AST.Pragma (_87_155) -> begin
"pragma"
end
| FStar_Parser_AST.Fsdoc (comm, _87_159) -> begin
comm
end))


let decl_documented : FStar_Parser_AST.decl  ->  Prims.bool = (fun d -> (

let tycon_documented = (fun tt -> (

let tyconvars_documented = (fun tycon -> (match (tycon) with
| (FStar_Parser_AST.TyconAbstract (_)) | (FStar_Parser_AST.TyconAbbrev (_)) -> begin
false
end
| FStar_Parser_AST.TyconRecord (_87_174, _87_176, _87_178, fields) -> begin
(FStar_List.existsb (fun _87_185 -> (match (_87_185) with
| (_id, _t, doco) -> begin
(FStar_Util.is_some doco)
end)) fields)
end
| FStar_Parser_AST.TyconVariant (_87_187, _87_189, _87_191, vars) -> begin
(FStar_List.existsb (fun _87_199 -> (match (_87_199) with
| (_id, _t, doco, _u) -> begin
(FStar_Util.is_some doco)
end)) vars)
end))
in (FStar_List.existsb (fun _87_202 -> (match (_87_202) with
| (tycon, doco) -> begin
((tyconvars_documented tycon) || (FStar_Util.is_some doco))
end)) tt)))
in (match (d.FStar_Parser_AST.doc) with
| Some (_87_204) -> begin
true
end
| _87_207 -> begin
(match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Fsdoc (_87_209) -> begin
true
end
| FStar_Parser_AST.Tycon (_87_212, ty) -> begin
(tycon_documented ty)
end
| _87_217 -> begin
false
end)
end)))


let document_decl : (Prims.string  ->  Prims.unit)  ->  FStar_Parser_AST.decl  ->  Prims.unit = (fun w d -> if (decl_documented d) then begin
(

let _87_228 = d
in (match (_87_228) with
| {FStar_Parser_AST.d = decl; FStar_Parser_AST.drange = _87_226; FStar_Parser_AST.doc = fsdoc; FStar_Parser_AST.quals = _87_223; FStar_Parser_AST.attrs = _87_221} -> begin
(

let _87_229 = (let _187_103 = (let _187_102 = (string_of_decl' d.FStar_Parser_AST.d)
in (code_wrap _187_102))
in (w _187_103))
in (

let _87_237 = (match (fsdoc) with
| Some (doc, _kw) -> begin
(w (Prims.strcat "\n" doc))
end
| _87_236 -> begin
()
end)
in (w "")))
end))
end else begin
()
end)


let document_toplevel = (fun name topdecl -> (match (topdecl.FStar_Parser_AST.d) with
| FStar_Parser_AST.TopLevelModule (_87_242) -> begin
(match (topdecl.FStar_Parser_AST.doc) with
| Some (doc, kw) -> begin
(match ((FStar_List.tryFind (fun _87_250 -> (match (_87_250) with
| (k, v) -> begin
(k = "summary")
end)) kw)) with
| None -> begin
((None), (Some (doc)))
end
| Some (_87_253, summary) -> begin
((Some (summary)), (Some (doc)))
end)
end
| None -> begin
((None), (None))
end)
end
| _87_259 -> begin
(Prims.raise (FStar_Syntax_Syntax.Err ("Not a TopLevelModule")))
end))


let document_module : FStar_Parser_AST.modul  ->  FStar_Ident.lid = (fun m -> (

let _87_274 = (match (m) with
| FStar_Parser_AST.Module (n, d) -> begin
((n), (d), ("module"))
end
| FStar_Parser_AST.Interface (n, d, _87_268) -> begin
((n), (d), ("interface"))
end)
in (match (_87_274) with
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

let _87_286 = (document_toplevel name top_decl)
in (match (_87_286) with
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

let _87_295 = (let _187_110 = (FStar_Util.format "# module %s" ((name.FStar_Ident.str)::[]))
in (w _187_110))
in (

let _87_297 = (let _187_111 = (FStar_Util.format "%s\n" ((summary)::[]))
in (w _187_111))
in (

let _87_299 = (let _187_112 = (FStar_Util.format "%s\n" ((comment)::[]))
in (w _187_112))
in (

let _87_301 = (FStar_List.iter (document_decl w) other_decls)
in (

let _87_303 = (FStar_Util.close_file fd)
in name)))))))
end)))))))
end
| None -> begin
(let _187_114 = (let _187_113 = (FStar_Util.format1 "No singleton toplevel in module %s" name.FStar_Ident.str)
in FStar_Syntax_Syntax.Err (_187_113))
in (Prims.raise _187_114))
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

let _87_313 = (FStar_List.iter (fun m -> (let _187_119 = (FStar_Util.format "%s\n" ((m.FStar_Ident.str)::[]))
in (FStar_Util.append_to_file fd _187_119))) mods)
in (FStar_Util.close_file fd)))))))




