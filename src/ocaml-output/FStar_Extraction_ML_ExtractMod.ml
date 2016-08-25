
open Prims

let fail_exp : FStar_Ident.lident  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.exp = (fun lid t -> (let _170_16 = (let _170_15 = (FStar_Absyn_Util.fvar None FStar_Absyn_Const.failwith_lid FStar_Absyn_Syntax.dummyRange)
in (let _170_14 = (let _170_13 = (FStar_Absyn_Syntax.targ t)
in (let _170_12 = (let _170_11 = (let _170_10 = (let _170_9 = (let _170_8 = (let _170_7 = (let _170_6 = (let _170_5 = (FStar_Absyn_Print.sli lid)
in (Prims.strcat "Not yet implemented:" _170_5))
in (FStar_Bytes.string_as_unicode_bytes _170_6))
in ((_170_7), (FStar_Absyn_Syntax.dummyRange)))
in FStar_Const.Const_string (_170_8))
in (FStar_Absyn_Syntax.mk_Exp_constant _170_9 None FStar_Absyn_Syntax.dummyRange))
in (FStar_All.pipe_left FStar_Absyn_Syntax.varg _170_10))
in (_170_11)::[])
in (_170_13)::_170_12))
in ((_170_15), (_170_14))))
in (FStar_Absyn_Syntax.mk_Exp_app _170_16 None FStar_Absyn_Syntax.dummyRange)))


let mangle_projector_lid : FStar_Ident.lident  ->  FStar_Ident.lident = (fun x -> (

let projecteeName = x.FStar_Ident.ident
in (

let _77_11 = (FStar_Util.prefix x.FStar_Ident.ns)
in (match (_77_11) with
| (prefix, constrName) -> begin
(

let mangledName = (FStar_Absyn_Syntax.id_of_text (Prims.strcat "___" (Prims.strcat constrName.FStar_Ident.idText (Prims.strcat "___" projecteeName.FStar_Ident.idText))))
in (FStar_Ident.lid_of_ids (FStar_List.append prefix ((mangledName)::[]))))
end))))


let rec extract_sig : FStar_Extraction_ML_Env.env  ->  FStar_Absyn_Syntax.sigelt  ->  (FStar_Extraction_ML_Env.env * FStar_Extraction_ML_Syntax.mlmodule1 Prims.list) = (fun g se -> (

let _77_16 = (FStar_Extraction_ML_Env.debug g (fun u -> (let _170_25 = (let _170_24 = (FStar_Absyn_Print.sigelt_to_string se)
in (FStar_Util.format1 "now extracting :  %s \n" _170_24))
in (FStar_Util.print_string _170_25))))
in (match (se) with
| (FStar_Absyn_Syntax.Sig_datacon (_)) | (FStar_Absyn_Syntax.Sig_bundle (_)) | (FStar_Absyn_Syntax.Sig_tycon (_)) | (FStar_Absyn_Syntax.Sig_typ_abbrev (_)) -> begin
(

let _77_32 = (FStar_Extraction_ML_ExtractTyp.extractSigElt g se)
in (match (_77_32) with
| (c, tds) -> begin
((c), (tds))
end))
end
| FStar_Absyn_Syntax.Sig_let (lbs, r, _77_36, quals) -> begin
(

let elet = (FStar_Absyn_Syntax.mk_Exp_let ((lbs), (FStar_Absyn_Const.exp_false_bool)) None r)
in (

let _77_46 = (FStar_Extraction_ML_ExtractExp.synth_exp g elet)
in (match (_77_46) with
| (ml_let, _77_43, _77_45) -> begin
(match (ml_let.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Let (ml_lbs, _77_49) -> begin
(

let _77_81 = (FStar_List.fold_left2 (fun _77_54 ml_lb _77_62 -> (match (((_77_54), (_77_62))) with
| ((env, ml_lbs), {FStar_Absyn_Syntax.lbname = lbname; FStar_Absyn_Syntax.lbtyp = t; FStar_Absyn_Syntax.lbeff = _77_59; FStar_Absyn_Syntax.lbdef = _77_57}) -> begin
(

let _77_78 = if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _77_1 -> (match (_77_1) with
| FStar_Absyn_Syntax.Projector (_77_65) -> begin
true
end
| _77_68 -> begin
false
end)))) then begin
(

let mname = (let _170_31 = (let _170_30 = (FStar_Util.right lbname)
in (mangle_projector_lid _170_30))
in (FStar_All.pipe_right _170_31 FStar_Extraction_ML_Syntax.mlpath_of_lident))
in (

let env = (let _170_34 = (let _170_32 = (FStar_Util.right lbname)
in (FStar_All.pipe_left FStar_Absyn_Util.fv _170_32))
in (let _170_33 = (FStar_Util.must ml_lb.FStar_Extraction_ML_Syntax.mllb_tysc)
in (FStar_Extraction_ML_Env.extend_fv' env _170_34 mname _170_33 ml_lb.FStar_Extraction_ML_Syntax.mllb_add_unit false)))
in (

let ml_lb = (

let _77_71 = ml_lb
in {FStar_Extraction_ML_Syntax.mllb_name = _77_71.FStar_Extraction_ML_Syntax.mllb_name; FStar_Extraction_ML_Syntax.mllb_tysc = _77_71.FStar_Extraction_ML_Syntax.mllb_tysc; FStar_Extraction_ML_Syntax.mllb_add_unit = _77_71.FStar_Extraction_ML_Syntax.mllb_add_unit; FStar_Extraction_ML_Syntax.mllb_def = _77_71.FStar_Extraction_ML_Syntax.mllb_def; FStar_Extraction_ML_Syntax.print_typ = false})
in ((env), ((

let _77_74 = ml_lb
in {FStar_Extraction_ML_Syntax.mllb_name = (((Prims.snd mname)), (0)); FStar_Extraction_ML_Syntax.mllb_tysc = _77_74.FStar_Extraction_ML_Syntax.mllb_tysc; FStar_Extraction_ML_Syntax.mllb_add_unit = _77_74.FStar_Extraction_ML_Syntax.mllb_add_unit; FStar_Extraction_ML_Syntax.mllb_def = _77_74.FStar_Extraction_ML_Syntax.mllb_def; FStar_Extraction_ML_Syntax.print_typ = _77_74.FStar_Extraction_ML_Syntax.print_typ}))))))
end else begin
(let _170_37 = (let _170_36 = (let _170_35 = (FStar_Util.must ml_lb.FStar_Extraction_ML_Syntax.mllb_tysc)
in (FStar_Extraction_ML_Env.extend_lb env lbname t _170_35 ml_lb.FStar_Extraction_ML_Syntax.mllb_add_unit false))
in (FStar_All.pipe_left Prims.fst _170_36))
in ((_170_37), (ml_lb)))
end
in (match (_77_78) with
| (g, ml_lb) -> begin
((g), ((ml_lb)::ml_lbs))
end))
end)) ((g), ([])) (Prims.snd ml_lbs) (Prims.snd lbs))
in (match (_77_81) with
| (g, ml_lbs') -> begin
(let _170_40 = (let _170_39 = (let _170_38 = (FStar_Extraction_ML_Util.mlloc_of_range r)
in FStar_Extraction_ML_Syntax.MLM_Loc (_170_38))
in (_170_39)::(FStar_Extraction_ML_Syntax.MLM_Let ((((Prims.fst ml_lbs)), ((FStar_List.rev ml_lbs')))))::[])
in ((g), (_170_40)))
end))
end
| _77_83 -> begin
(FStar_All.failwith "impossible")
end)
end)))
end
| FStar_Absyn_Syntax.Sig_val_decl (lid, t, quals, r) -> begin
if (FStar_All.pipe_right quals (FStar_List.contains FStar_Absyn_Syntax.Assumption)) then begin
(

let impl = (match ((FStar_Absyn_Util.function_formals t)) with
| Some (bs, c) -> begin
(let _170_42 = (let _170_41 = (fail_exp lid (FStar_Absyn_Util.comp_result c))
in ((bs), (_170_41)))
in (FStar_Absyn_Syntax.mk_Exp_abs _170_42 None FStar_Absyn_Syntax.dummyRange))
end
| _77_95 -> begin
(fail_exp lid t)
end)
in (

let se = FStar_Absyn_Syntax.Sig_let (((((false), (({FStar_Absyn_Syntax.lbname = FStar_Util.Inr (lid); FStar_Absyn_Syntax.lbtyp = t; FStar_Absyn_Syntax.lbeff = FStar_Absyn_Const.effect_ML_lid; FStar_Absyn_Syntax.lbdef = impl})::[]))), (r), ([]), (quals)))
in (

let _77_100 = (extract_sig g se)
in (match (_77_100) with
| (g, mlm) -> begin
(

let is_record = (FStar_Util.for_some (fun _77_2 -> (match (_77_2) with
| FStar_Absyn_Syntax.RecordType (_77_103) -> begin
true
end
| _77_106 -> begin
false
end)) quals)
in (match ((FStar_Util.find_map quals (fun _77_3 -> (match (_77_3) with
| FStar_Absyn_Syntax.Discriminator (l) -> begin
Some (l)
end
| _77_112 -> begin
None
end)))) with
| Some (l) when (not (is_record)) -> begin
(let _170_49 = (let _170_48 = (let _170_45 = (FStar_Extraction_ML_Util.mlloc_of_range r)
in FStar_Extraction_ML_Syntax.MLM_Loc (_170_45))
in (let _170_47 = (let _170_46 = (FStar_Extraction_ML_ExtractExp.ind_discriminator_body g lid l)
in (_170_46)::[])
in (_170_48)::_170_47))
in ((g), (_170_49)))
end
| _77_116 -> begin
(match ((FStar_Util.find_map quals (fun _77_4 -> (match (_77_4) with
| FStar_Absyn_Syntax.Projector (l, _77_120) -> begin
Some (l)
end
| _77_124 -> begin
None
end)))) with
| Some (_77_126) -> begin
((g), ([]))
end
| _77_129 -> begin
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

let _77_139 = (FStar_Extraction_ML_ExtractExp.synth_exp g e)
in (match (_77_139) with
| (ml_main, _77_136, _77_138) -> begin
(let _170_53 = (let _170_52 = (let _170_51 = (FStar_Extraction_ML_Util.mlloc_of_range r)
in FStar_Extraction_ML_Syntax.MLM_Loc (_170_51))
in (_170_52)::(FStar_Extraction_ML_Syntax.MLM_Top (ml_main))::[])
in ((g), (_170_53)))
end))
end
| (FStar_Absyn_Syntax.Sig_kind_abbrev (_)) | (FStar_Absyn_Syntax.Sig_assume (_)) | (FStar_Absyn_Syntax.Sig_new_effect (_)) | (FStar_Absyn_Syntax.Sig_sub_effect (_)) | (FStar_Absyn_Syntax.Sig_effect_abbrev (_)) | (FStar_Absyn_Syntax.Sig_pragma (_)) -> begin
((g), ([]))
end)))


let extract_iface : FStar_Extraction_ML_Env.env  ->  FStar_Absyn_Syntax.modul  ->  FStar_Extraction_ML_Env.env = (fun g m -> (let _170_58 = (FStar_Util.fold_map extract_sig g m.FStar_Absyn_Syntax.declarations)
in (FStar_All.pipe_right _170_58 Prims.fst)))


let rec extract : FStar_Extraction_ML_Env.env  ->  FStar_Absyn_Syntax.modul  ->  (FStar_Extraction_ML_Env.env * FStar_Extraction_ML_Syntax.mllib Prims.list) = (fun g m -> (

let _77_162 = (FStar_Absyn_Util.reset_gensym ())
in (

let name = (FStar_Extraction_ML_Syntax.mlpath_of_lident m.FStar_Absyn_Syntax.name)
in (

let g = (

let _77_165 = g
in {FStar_Extraction_ML_Env.tcenv = _77_165.FStar_Extraction_ML_Env.tcenv; FStar_Extraction_ML_Env.gamma = _77_165.FStar_Extraction_ML_Env.gamma; FStar_Extraction_ML_Env.tydefs = _77_165.FStar_Extraction_ML_Env.tydefs; FStar_Extraction_ML_Env.currentModule = name})
in if (((m.FStar_Absyn_Syntax.name.FStar_Ident.str = "Prims") || m.FStar_Absyn_Syntax.is_interface) || (FStar_Options.no_extract m.FStar_Absyn_Syntax.name.FStar_Ident.str)) then begin
(

let g = (extract_iface g m)
in ((g), ([])))
end else begin
(

let _77_171 = (FStar_Util.fold_map extract_sig g m.FStar_Absyn_Syntax.declarations)
in (match (_77_171) with
| (g, sigs) -> begin
(

let mlm = (FStar_List.flatten sigs)
in ((g), ((FStar_Extraction_ML_Syntax.MLLib ((((name), (Some ((([]), (mlm)))), (FStar_Extraction_ML_Syntax.MLLib ([]))))::[]))::[])))
end))
end))))




