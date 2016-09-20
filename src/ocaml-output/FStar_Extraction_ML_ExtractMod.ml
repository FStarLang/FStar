
open Prims

let fail_exp : FStar_Ident.lident  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.exp = (fun lid t -> (let _172_16 = (let _172_15 = (FStar_Absyn_Util.fvar None FStar_Absyn_Const.failwith_lid FStar_Absyn_Syntax.dummyRange)
in (let _172_14 = (let _172_13 = (FStar_Absyn_Syntax.targ t)
in (let _172_12 = (let _172_11 = (let _172_10 = (let _172_9 = (let _172_8 = (let _172_7 = (let _172_6 = (let _172_5 = (FStar_Absyn_Print.sli lid)
in (Prims.strcat "Not yet implemented:" _172_5))
in (FStar_Bytes.string_as_unicode_bytes _172_6))
in ((_172_7), (FStar_Absyn_Syntax.dummyRange)))
in FStar_Const.Const_string (_172_8))
in (FStar_Absyn_Syntax.mk_Exp_constant _172_9 None FStar_Absyn_Syntax.dummyRange))
in (FStar_All.pipe_left FStar_Absyn_Syntax.varg _172_10))
in (_172_11)::[])
in (_172_13)::_172_12))
in ((_172_15), (_172_14))))
in (FStar_Absyn_Syntax.mk_Exp_app _172_16 None FStar_Absyn_Syntax.dummyRange)))


let mangle_projector_lid : FStar_Ident.lident  ->  FStar_Ident.lident = (fun x -> (

let projecteeName = x.FStar_Ident.ident
in (

let _78_11 = (FStar_Util.prefix x.FStar_Ident.ns)
in (match (_78_11) with
| (prefix, constrName) -> begin
(

let mangledName = (FStar_Absyn_Syntax.id_of_text (Prims.strcat "___" (Prims.strcat constrName.FStar_Ident.idText (Prims.strcat "___" projecteeName.FStar_Ident.idText))))
in (FStar_Ident.lid_of_ids (FStar_List.append prefix ((mangledName)::[]))))
end))))


let rec extract_sig : FStar_Extraction_ML_Env.env  ->  FStar_Absyn_Syntax.sigelt  ->  (FStar_Extraction_ML_Env.env * FStar_Extraction_ML_Syntax.mlmodule1 Prims.list) = (fun g se -> (

let _78_16 = (FStar_Extraction_ML_Env.debug g (fun u -> (let _172_25 = (let _172_24 = (FStar_Absyn_Print.sigelt_to_string se)
in (FStar_Util.format1 "now extracting :  %s \n" _172_24))
in (FStar_Util.print_string _172_25))))
in (match (se) with
| (FStar_Absyn_Syntax.Sig_datacon (_)) | (FStar_Absyn_Syntax.Sig_bundle (_)) | (FStar_Absyn_Syntax.Sig_tycon (_)) | (FStar_Absyn_Syntax.Sig_typ_abbrev (_)) -> begin
(

let _78_32 = (FStar_Extraction_ML_ExtractTyp.extractSigElt g se)
in (match (_78_32) with
| (c, tds) -> begin
((c), (tds))
end))
end
| FStar_Absyn_Syntax.Sig_let (lbs, r, _78_36, quals) -> begin
(

let elet = (FStar_Absyn_Syntax.mk_Exp_let ((lbs), (FStar_Absyn_Const.exp_false_bool)) None r)
in (

let _78_46 = (FStar_Extraction_ML_ExtractExp.synth_exp g elet)
in (match (_78_46) with
| (ml_let, _78_43, _78_45) -> begin
(match (ml_let.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Let (ml_lbs, _78_49) -> begin
(

let _78_81 = (FStar_List.fold_left2 (fun _78_54 ml_lb _78_62 -> (match (((_78_54), (_78_62))) with
| ((env, ml_lbs), {FStar_Absyn_Syntax.lbname = lbname; FStar_Absyn_Syntax.lbtyp = t; FStar_Absyn_Syntax.lbeff = _78_59; FStar_Absyn_Syntax.lbdef = _78_57}) -> begin
(

let _78_78 = if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _78_1 -> (match (_78_1) with
| FStar_Absyn_Syntax.Projector (_78_65) -> begin
true
end
| _78_68 -> begin
false
end)))) then begin
(

let mname = (let _172_31 = (let _172_30 = (FStar_Util.right lbname)
in (mangle_projector_lid _172_30))
in (FStar_All.pipe_right _172_31 FStar_Extraction_ML_Syntax.mlpath_of_lident))
in (

let env = (let _172_34 = (let _172_32 = (FStar_Util.right lbname)
in (FStar_All.pipe_left FStar_Absyn_Util.fv _172_32))
in (let _172_33 = (FStar_Util.must ml_lb.FStar_Extraction_ML_Syntax.mllb_tysc)
in (FStar_Extraction_ML_Env.extend_fv' env _172_34 mname _172_33 ml_lb.FStar_Extraction_ML_Syntax.mllb_add_unit false)))
in (

let ml_lb = (

let _78_71 = ml_lb
in {FStar_Extraction_ML_Syntax.mllb_name = _78_71.FStar_Extraction_ML_Syntax.mllb_name; FStar_Extraction_ML_Syntax.mllb_tysc = _78_71.FStar_Extraction_ML_Syntax.mllb_tysc; FStar_Extraction_ML_Syntax.mllb_add_unit = _78_71.FStar_Extraction_ML_Syntax.mllb_add_unit; FStar_Extraction_ML_Syntax.mllb_def = _78_71.FStar_Extraction_ML_Syntax.mllb_def; FStar_Extraction_ML_Syntax.print_typ = false})
in ((env), ((

let _78_74 = ml_lb
in {FStar_Extraction_ML_Syntax.mllb_name = (((Prims.snd mname)), ((Prims.parse_int "0"))); FStar_Extraction_ML_Syntax.mllb_tysc = _78_74.FStar_Extraction_ML_Syntax.mllb_tysc; FStar_Extraction_ML_Syntax.mllb_add_unit = _78_74.FStar_Extraction_ML_Syntax.mllb_add_unit; FStar_Extraction_ML_Syntax.mllb_def = _78_74.FStar_Extraction_ML_Syntax.mllb_def; FStar_Extraction_ML_Syntax.print_typ = _78_74.FStar_Extraction_ML_Syntax.print_typ}))))))
end else begin
(let _172_37 = (let _172_36 = (let _172_35 = (FStar_Util.must ml_lb.FStar_Extraction_ML_Syntax.mllb_tysc)
in (FStar_Extraction_ML_Env.extend_lb env lbname t _172_35 ml_lb.FStar_Extraction_ML_Syntax.mllb_add_unit false))
in (FStar_All.pipe_left Prims.fst _172_36))
in ((_172_37), (ml_lb)))
end
in (match (_78_78) with
| (g, ml_lb) -> begin
((g), ((ml_lb)::ml_lbs))
end))
end)) ((g), ([])) (Prims.snd ml_lbs) (Prims.snd lbs))
in (match (_78_81) with
| (g, ml_lbs') -> begin
(let _172_40 = (let _172_39 = (let _172_38 = (FStar_Extraction_ML_Util.mlloc_of_range r)
in FStar_Extraction_ML_Syntax.MLM_Loc (_172_38))
in (_172_39)::(FStar_Extraction_ML_Syntax.MLM_Let ((((Prims.fst ml_lbs)), ((FStar_List.rev ml_lbs')))))::[])
in ((g), (_172_40)))
end))
end
| _78_83 -> begin
(FStar_All.failwith "impossible")
end)
end)))
end
| FStar_Absyn_Syntax.Sig_val_decl (lid, t, quals, r) -> begin
if (FStar_All.pipe_right quals (FStar_List.contains FStar_Absyn_Syntax.Assumption)) then begin
(

let impl = (match ((FStar_Absyn_Util.function_formals t)) with
| Some (bs, c) -> begin
(let _172_42 = (let _172_41 = (fail_exp lid (FStar_Absyn_Util.comp_result c))
in ((bs), (_172_41)))
in (FStar_Absyn_Syntax.mk_Exp_abs _172_42 None FStar_Absyn_Syntax.dummyRange))
end
| _78_95 -> begin
(fail_exp lid t)
end)
in (

let se = FStar_Absyn_Syntax.Sig_let (((((false), (({FStar_Absyn_Syntax.lbname = FStar_Util.Inr (lid); FStar_Absyn_Syntax.lbtyp = t; FStar_Absyn_Syntax.lbeff = FStar_Absyn_Const.effect_ML_lid; FStar_Absyn_Syntax.lbdef = impl})::[]))), (r), ([]), (quals)))
in (

let _78_100 = (extract_sig g se)
in (match (_78_100) with
| (g, mlm) -> begin
(

let is_record = (FStar_Util.for_some (fun _78_2 -> (match (_78_2) with
| FStar_Absyn_Syntax.RecordType (_78_103) -> begin
true
end
| _78_106 -> begin
false
end)) quals)
in (match ((FStar_Util.find_map quals (fun _78_3 -> (match (_78_3) with
| FStar_Absyn_Syntax.Discriminator (l) -> begin
Some (l)
end
| _78_112 -> begin
None
end)))) with
| Some (l) when (not (is_record)) -> begin
(let _172_49 = (let _172_48 = (let _172_45 = (FStar_Extraction_ML_Util.mlloc_of_range r)
in FStar_Extraction_ML_Syntax.MLM_Loc (_172_45))
in (let _172_47 = (let _172_46 = (FStar_Extraction_ML_ExtractExp.ind_discriminator_body g lid l)
in (_172_46)::[])
in (_172_48)::_172_47))
in ((g), (_172_49)))
end
| _78_116 -> begin
(match ((FStar_Util.find_map quals (fun _78_4 -> (match (_78_4) with
| FStar_Absyn_Syntax.Projector (l, _78_120) -> begin
Some (l)
end
| _78_124 -> begin
None
end)))) with
| Some (_78_126) -> begin
((g), ([]))
end
| _78_129 -> begin
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

let _78_139 = (FStar_Extraction_ML_ExtractExp.synth_exp g e)
in (match (_78_139) with
| (ml_main, _78_136, _78_138) -> begin
(let _172_53 = (let _172_52 = (let _172_51 = (FStar_Extraction_ML_Util.mlloc_of_range r)
in FStar_Extraction_ML_Syntax.MLM_Loc (_172_51))
in (_172_52)::(FStar_Extraction_ML_Syntax.MLM_Top (ml_main))::[])
in ((g), (_172_53)))
end))
end
| (FStar_Absyn_Syntax.Sig_kind_abbrev (_)) | (FStar_Absyn_Syntax.Sig_assume (_)) | (FStar_Absyn_Syntax.Sig_new_effect (_)) | (FStar_Absyn_Syntax.Sig_sub_effect (_)) | (FStar_Absyn_Syntax.Sig_effect_abbrev (_)) | (FStar_Absyn_Syntax.Sig_pragma (_)) -> begin
((g), ([]))
end)))


let extract_iface : FStar_Extraction_ML_Env.env  ->  FStar_Absyn_Syntax.modul  ->  FStar_Extraction_ML_Env.env = (fun g m -> (let _172_58 = (FStar_Util.fold_map extract_sig g m.FStar_Absyn_Syntax.declarations)
in (FStar_All.pipe_right _172_58 Prims.fst)))


let rec extract : FStar_Extraction_ML_Env.env  ->  FStar_Absyn_Syntax.modul  ->  (FStar_Extraction_ML_Env.env * FStar_Extraction_ML_Syntax.mllib Prims.list) = (fun g m -> (

let _78_162 = (FStar_Absyn_Util.reset_gensym ())
in (

let name = (FStar_Extraction_ML_Syntax.mlpath_of_lident m.FStar_Absyn_Syntax.name)
in (

let g = (

let _78_165 = g
in {FStar_Extraction_ML_Env.tcenv = _78_165.FStar_Extraction_ML_Env.tcenv; FStar_Extraction_ML_Env.gamma = _78_165.FStar_Extraction_ML_Env.gamma; FStar_Extraction_ML_Env.tydefs = _78_165.FStar_Extraction_ML_Env.tydefs; FStar_Extraction_ML_Env.currentModule = name})
in if (((m.FStar_Absyn_Syntax.name.FStar_Ident.str = "Prims") || m.FStar_Absyn_Syntax.is_interface) || (FStar_Options.no_extract m.FStar_Absyn_Syntax.name.FStar_Ident.str)) then begin
(

let g = (extract_iface g m)
in ((g), ([])))
end else begin
(

let _78_171 = (FStar_Util.fold_map extract_sig g m.FStar_Absyn_Syntax.declarations)
in (match (_78_171) with
| (g, sigs) -> begin
(

let mlm = (FStar_List.flatten sigs)
in ((g), ((FStar_Extraction_ML_Syntax.MLLib ((((name), (Some ((([]), (mlm)))), (FStar_Extraction_ML_Syntax.MLLib ([]))))::[]))::[])))
end))
end))))




