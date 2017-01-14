
open Prims

let fail_exp : FStar_Ident.lident  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.exp = (fun lid t -> (let _187_16 = (let _187_15 = (FStar_Absyn_Util.fvar None FStar_Absyn_Const.failwith_lid FStar_Absyn_Syntax.dummyRange)
in (let _187_14 = (let _187_13 = (FStar_Absyn_Syntax.targ t)
in (let _187_12 = (let _187_11 = (let _187_10 = (let _187_9 = (let _187_8 = (let _187_7 = (let _187_6 = (let _187_5 = (FStar_Absyn_Print.sli lid)
in (Prims.strcat "Not yet implemented:" _187_5))
in (FStar_Bytes.string_as_unicode_bytes _187_6))
in ((_187_7), (FStar_Absyn_Syntax.dummyRange)))
in FStar_Const.Const_string (_187_8))
in (FStar_Absyn_Syntax.mk_Exp_constant _187_9 None FStar_Absyn_Syntax.dummyRange))
in (FStar_All.pipe_left FStar_Absyn_Syntax.varg _187_10))
in (_187_11)::[])
in (_187_13)::_187_12))
in ((_187_15), (_187_14))))
in (FStar_Absyn_Syntax.mk_Exp_app _187_16 None FStar_Absyn_Syntax.dummyRange)))


let mangle_projector_lid : FStar_Ident.lident  ->  FStar_Ident.lident = (fun x -> (

let projecteeName = x.FStar_Ident.ident
in (

let _86_7 = (FStar_Util.prefix x.FStar_Ident.ns)
in (match (_86_7) with
| (prefix, constrName) -> begin
(

let mangledName = (FStar_Absyn_Syntax.id_of_text (Prims.strcat "___" (Prims.strcat constrName.FStar_Ident.idText (Prims.strcat "___" projecteeName.FStar_Ident.idText))))
in (FStar_Ident.lid_of_ids (FStar_List.append prefix ((mangledName)::[]))))
end))))


let rec extract_sig : FStar_StratifiedExtraction_ML_Env.env  ->  FStar_Absyn_Syntax.sigelt  ->  (FStar_StratifiedExtraction_ML_Env.env * FStar_Extraction_ML_Syntax.mlmodule1 Prims.list) = (fun g se -> (

let _86_12 = (FStar_StratifiedExtraction_ML_Env.debug g (fun u -> (let _187_25 = (let _187_24 = (FStar_Absyn_Print.sigelt_to_string se)
in (FStar_Util.format1 "now extracting :  %s \n" _187_24))
in (FStar_Util.print_string _187_25))))
in (match (se) with
| (FStar_Absyn_Syntax.Sig_datacon (_)) | (FStar_Absyn_Syntax.Sig_bundle (_)) | (FStar_Absyn_Syntax.Sig_tycon (_)) | (FStar_Absyn_Syntax.Sig_typ_abbrev (_)) -> begin
(

let _86_28 = (FStar_StratifiedExtraction_ML_ExtractTyp.extractSigElt g se)
in (match (_86_28) with
| (c, tds) -> begin
((c), (tds))
end))
end
| FStar_Absyn_Syntax.Sig_let (lbs, r, _86_32, quals) -> begin
(

let elet = (FStar_Absyn_Syntax.mk_Exp_let ((lbs), (FStar_Absyn_Const.exp_false_bool)) None r)
in (

let _86_42 = (FStar_StratifiedExtraction_ML_ExtractExp.synth_exp g elet)
in (match (_86_42) with
| (ml_let, _86_39, _86_41) -> begin
(match (ml_let.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Let ((flavor, _86_45, bindings), _86_49) -> begin
(

let _86_81 = (FStar_List.fold_left2 (fun _86_54 ml_lb _86_62 -> (match (((_86_54), (_86_62))) with
| ((env, ml_lbs), {FStar_Absyn_Syntax.lbname = lbname; FStar_Absyn_Syntax.lbtyp = t; FStar_Absyn_Syntax.lbeff = _86_59; FStar_Absyn_Syntax.lbdef = _86_57}) -> begin
(

let _86_78 = if (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___561 -> (match (uu___561) with
| FStar_Absyn_Syntax.Projector (_86_65) -> begin
true
end
| _86_68 -> begin
false
end)))) then begin
(

let mname = (let _187_31 = (let _187_30 = (FStar_Util.right lbname)
in (mangle_projector_lid _187_30))
in (FStar_All.pipe_right _187_31 FStar_Extraction_ML_Syntax.mlpath_of_lident))
in (

let env = (let _187_34 = (let _187_32 = (FStar_Util.right lbname)
in (FStar_All.pipe_left FStar_Absyn_Util.fv _187_32))
in (let _187_33 = (FStar_Util.must ml_lb.FStar_Extraction_ML_Syntax.mllb_tysc)
in (FStar_StratifiedExtraction_ML_Env.extend_fv' env _187_34 mname _187_33 ml_lb.FStar_Extraction_ML_Syntax.mllb_add_unit false)))
in (

let ml_lb = (

let _86_71 = ml_lb
in {FStar_Extraction_ML_Syntax.mllb_name = _86_71.FStar_Extraction_ML_Syntax.mllb_name; FStar_Extraction_ML_Syntax.mllb_tysc = _86_71.FStar_Extraction_ML_Syntax.mllb_tysc; FStar_Extraction_ML_Syntax.mllb_add_unit = _86_71.FStar_Extraction_ML_Syntax.mllb_add_unit; FStar_Extraction_ML_Syntax.mllb_def = _86_71.FStar_Extraction_ML_Syntax.mllb_def; FStar_Extraction_ML_Syntax.print_typ = false})
in ((env), ((

let _86_74 = ml_lb
in {FStar_Extraction_ML_Syntax.mllb_name = (((Prims.snd mname)), ((Prims.parse_int "0"))); FStar_Extraction_ML_Syntax.mllb_tysc = _86_74.FStar_Extraction_ML_Syntax.mllb_tysc; FStar_Extraction_ML_Syntax.mllb_add_unit = _86_74.FStar_Extraction_ML_Syntax.mllb_add_unit; FStar_Extraction_ML_Syntax.mllb_def = _86_74.FStar_Extraction_ML_Syntax.mllb_def; FStar_Extraction_ML_Syntax.print_typ = _86_74.FStar_Extraction_ML_Syntax.print_typ}))))))
end else begin
(let _187_37 = (let _187_36 = (let _187_35 = (FStar_Util.must ml_lb.FStar_Extraction_ML_Syntax.mllb_tysc)
in (FStar_StratifiedExtraction_ML_Env.extend_lb env lbname t _187_35 ml_lb.FStar_Extraction_ML_Syntax.mllb_add_unit false))
in (FStar_All.pipe_left Prims.fst _187_36))
in ((_187_37), (ml_lb)))
end
in (match (_86_78) with
| (g, ml_lb) -> begin
((g), ((ml_lb)::ml_lbs))
end))
end)) ((g), ([])) bindings (Prims.snd lbs))
in (match (_86_81) with
| (g, ml_lbs') -> begin
(let _187_40 = (let _187_39 = (let _187_38 = (FStar_StratifiedExtraction_ML_Util.mlloc_of_range r)
in FStar_Extraction_ML_Syntax.MLM_Loc (_187_38))
in (_187_39)::(FStar_Extraction_ML_Syntax.MLM_Let (((flavor), ([]), ((FStar_List.rev ml_lbs')))))::[])
in ((g), (_187_40)))
end))
end
| _86_83 -> begin
(failwith "impossible")
end)
end)))
end
| FStar_Absyn_Syntax.Sig_val_decl (lid, t, quals, r) -> begin
if (FStar_All.pipe_right quals (FStar_List.contains FStar_Absyn_Syntax.Assumption)) then begin
(

let impl = (match ((FStar_Absyn_Util.function_formals t)) with
| Some (bs, c) -> begin
(let _187_42 = (let _187_41 = (fail_exp lid (FStar_Absyn_Util.comp_result c))
in ((bs), (_187_41)))
in (FStar_Absyn_Syntax.mk_Exp_abs _187_42 None FStar_Absyn_Syntax.dummyRange))
end
| _86_95 -> begin
(fail_exp lid t)
end)
in (

let se = FStar_Absyn_Syntax.Sig_let (((((false), (({FStar_Absyn_Syntax.lbname = FStar_Util.Inr (lid); FStar_Absyn_Syntax.lbtyp = t; FStar_Absyn_Syntax.lbeff = FStar_Absyn_Const.effect_ML_lid; FStar_Absyn_Syntax.lbdef = impl})::[]))), (r), ([]), (quals)))
in (

let _86_100 = (extract_sig g se)
in (match (_86_100) with
| (g, mlm) -> begin
(

let is_record = (FStar_Util.for_some (fun uu___562 -> (match (uu___562) with
| FStar_Absyn_Syntax.RecordType (_86_103) -> begin
true
end
| _86_106 -> begin
false
end)) quals)
in (match ((FStar_Util.find_map quals (fun uu___563 -> (match (uu___563) with
| FStar_Absyn_Syntax.Discriminator (l) -> begin
Some (l)
end
| _86_112 -> begin
None
end)))) with
| Some (l) when (not (is_record)) -> begin
(let _187_49 = (let _187_48 = (let _187_45 = (FStar_StratifiedExtraction_ML_Util.mlloc_of_range r)
in FStar_Extraction_ML_Syntax.MLM_Loc (_187_45))
in (let _187_47 = (let _187_46 = (FStar_StratifiedExtraction_ML_ExtractExp.ind_discriminator_body g lid l)
in (_187_46)::[])
in (_187_48)::_187_47))
in ((g), (_187_49)))
end
| _86_116 -> begin
(match ((FStar_Util.find_map quals (fun uu___564 -> (match (uu___564) with
| FStar_Absyn_Syntax.Projector (l, _86_120) -> begin
Some (l)
end
| _86_124 -> begin
None
end)))) with
| Some (_86_126) -> begin
((g), ([]))
end
| _86_129 -> begin
((g), (mlm))
end)
end))
end))))
end else begin
((g), ([]))
end
end
| FStar_Absyn_Syntax.Sig_main (e, r) -> begin
(

let _86_139 = (FStar_StratifiedExtraction_ML_ExtractExp.synth_exp g e)
in (match (_86_139) with
| (ml_main, _86_136, _86_138) -> begin
(let _187_53 = (let _187_52 = (let _187_51 = (FStar_StratifiedExtraction_ML_Util.mlloc_of_range r)
in FStar_Extraction_ML_Syntax.MLM_Loc (_187_51))
in (_187_52)::(FStar_Extraction_ML_Syntax.MLM_Top (ml_main))::[])
in ((g), (_187_53)))
end))
end
| (FStar_Absyn_Syntax.Sig_kind_abbrev (_)) | (FStar_Absyn_Syntax.Sig_assume (_)) | (FStar_Absyn_Syntax.Sig_new_effect (_)) | (FStar_Absyn_Syntax.Sig_sub_effect (_)) | (FStar_Absyn_Syntax.Sig_effect_abbrev (_)) | (FStar_Absyn_Syntax.Sig_pragma (_)) -> begin
((g), ([]))
end)))


let extract_iface : FStar_StratifiedExtraction_ML_Env.env  ->  FStar_Absyn_Syntax.modul  ->  FStar_StratifiedExtraction_ML_Env.env = (fun g m -> (let _187_58 = (FStar_Util.fold_map extract_sig g m.FStar_Absyn_Syntax.declarations)
in (FStar_All.pipe_right _187_58 Prims.fst)))


let rec extract : FStar_StratifiedExtraction_ML_Env.env  ->  FStar_Absyn_Syntax.modul  ->  (FStar_StratifiedExtraction_ML_Env.env * FStar_Extraction_ML_Syntax.mllib Prims.list) = (fun g m -> (

let _86_162 = (FStar_Absyn_Util.reset_gensym ())
in (

let name = (FStar_Extraction_ML_Syntax.mlpath_of_lident m.FStar_Absyn_Syntax.name)
in (

let g = (

let _86_165 = g
in {FStar_StratifiedExtraction_ML_Env.tcenv = _86_165.FStar_StratifiedExtraction_ML_Env.tcenv; FStar_StratifiedExtraction_ML_Env.gamma = _86_165.FStar_StratifiedExtraction_ML_Env.gamma; FStar_StratifiedExtraction_ML_Env.tydefs = _86_165.FStar_StratifiedExtraction_ML_Env.tydefs; FStar_StratifiedExtraction_ML_Env.currentModule = name})
in if (((m.FStar_Absyn_Syntax.name.FStar_Ident.str = "Prims") || m.FStar_Absyn_Syntax.is_interface) || (FStar_Options.no_extract m.FStar_Absyn_Syntax.name.FStar_Ident.str)) then begin
(

let g = (extract_iface g m)
in ((g), ([])))
end else begin
(

let _86_171 = (FStar_Util.fold_map extract_sig g m.FStar_Absyn_Syntax.declarations)
in (match (_86_171) with
| (g, sigs) -> begin
(

let mlm = (FStar_List.flatten sigs)
in ((g), ((FStar_Extraction_ML_Syntax.MLLib ((((name), (Some ((([]), (mlm)))), (FStar_Extraction_ML_Syntax.MLLib ([]))))::[]))::[])))
end))
end))))




