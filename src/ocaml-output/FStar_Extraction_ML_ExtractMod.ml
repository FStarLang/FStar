
open Prims

let fail_exp : FStar_Ident.lident  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.exp = (fun lid t -> (let _178_16 = (let _178_15 = (FStar_Absyn_Util.fvar None FStar_Absyn_Const.failwith_lid FStar_Absyn_Syntax.dummyRange)
in (let _178_14 = (let _178_13 = (FStar_Absyn_Syntax.targ t)
in (let _178_12 = (let _178_11 = (let _178_10 = (let _178_9 = (let _178_8 = (let _178_7 = (let _178_6 = (let _178_5 = (FStar_Absyn_Print.sli lid)
in (Prims.strcat "Not yet implemented:" _178_5))
in (FStar_Bytes.string_as_unicode_bytes _178_6))
in ((_178_7), (FStar_Absyn_Syntax.dummyRange)))
in FStar_Const.Const_string (_178_8))
in (FStar_Absyn_Syntax.mk_Exp_constant _178_9 None FStar_Absyn_Syntax.dummyRange))
in (FStar_All.pipe_left FStar_Absyn_Syntax.varg _178_10))
in (_178_11)::[])
in (_178_13)::_178_12))
in ((_178_15), (_178_14))))
in (FStar_Absyn_Syntax.mk_Exp_app _178_16 None FStar_Absyn_Syntax.dummyRange)))


let mangle_projector_lid : FStar_Ident.lident  ->  FStar_Ident.lident = (fun x -> (

let projecteeName = x.FStar_Ident.ident
in (

let _80_11 = (FStar_Util.prefix x.FStar_Ident.ns)
in (match (_80_11) with
| (prefix, constrName) -> begin
(

let mangledName = (FStar_Absyn_Syntax.id_of_text (Prims.strcat "___" (Prims.strcat constrName.FStar_Ident.idText (Prims.strcat "___" projecteeName.FStar_Ident.idText))))
in (FStar_Ident.lid_of_ids (FStar_List.append prefix ((mangledName)::[]))))
end))))


let rec extract_sig : FStar_Extraction_ML_Env.env  ->  FStar_Absyn_Syntax.sigelt  ->  (FStar_Extraction_ML_Env.env * FStar_Extraction_ML_Syntax.mlmodule1 Prims.list) = (fun g se -> (

let _80_16 = (FStar_Extraction_ML_Env.debug g (fun u -> (let _178_25 = (let _178_24 = (FStar_Absyn_Print.sigelt_to_string se)
in (FStar_Util.format1 "now extracting :  %s \n" _178_24))
in (FStar_Util.print_string _178_25))))
in (match (se) with
| (FStar_Absyn_Syntax.Sig_datacon (_)) | (FStar_Absyn_Syntax.Sig_bundle (_)) | (FStar_Absyn_Syntax.Sig_tycon (_)) | (FStar_Absyn_Syntax.Sig_typ_abbrev (_)) -> begin
(

let _80_32 = (FStar_Extraction_ML_ExtractTyp.extractSigElt g se)
in (match (_80_32) with
| (c, tds) -> begin
((c), (tds))
end))
end
| FStar_Absyn_Syntax.Sig_let (lbs, r, _80_36, quals) -> begin
(

let elet = (FStar_Absyn_Syntax.mk_Exp_let ((lbs), (FStar_Absyn_Const.exp_false_bool)) None r)
in (

let _80_46 = (FStar_Extraction_ML_ExtractExp.synth_exp g elet)
in (match (_80_46) with
| (ml_let, _80_43, _80_45) -> begin
(match (ml_let.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Let ((flavor, _80_49, bindings), _80_53) -> begin
(

let _80_85 = (FStar_List.fold_left2 (fun _80_58 ml_lb _80_66 -> (match (((_80_58), (_80_66))) with
| ((env, ml_lbs), {FStar_Absyn_Syntax.lbname = lbname; FStar_Absyn_Syntax.lbtyp = t; FStar_Absyn_Syntax.lbeff = _80_63; FStar_Absyn_Syntax.lbdef = _80_61}) -> begin
(

let _80_82 = if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _80_1 -> (match (_80_1) with
| FStar_Absyn_Syntax.Projector (_80_69) -> begin
true
end
| _80_72 -> begin
false
end)))) then begin
(

let mname = (let _178_31 = (let _178_30 = (FStar_Util.right lbname)
in (mangle_projector_lid _178_30))
in (FStar_All.pipe_right _178_31 FStar_Extraction_ML_Syntax.mlpath_of_lident))
in (

let env = (let _178_34 = (let _178_32 = (FStar_Util.right lbname)
in (FStar_All.pipe_left FStar_Absyn_Util.fv _178_32))
in (let _178_33 = (FStar_Util.must ml_lb.FStar_Extraction_ML_Syntax.mllb_tysc)
in (FStar_Extraction_ML_Env.extend_fv' env _178_34 mname _178_33 ml_lb.FStar_Extraction_ML_Syntax.mllb_add_unit false)))
in (

let ml_lb = (

let _80_75 = ml_lb
in {FStar_Extraction_ML_Syntax.mllb_name = _80_75.FStar_Extraction_ML_Syntax.mllb_name; FStar_Extraction_ML_Syntax.mllb_tysc = _80_75.FStar_Extraction_ML_Syntax.mllb_tysc; FStar_Extraction_ML_Syntax.mllb_add_unit = _80_75.FStar_Extraction_ML_Syntax.mllb_add_unit; FStar_Extraction_ML_Syntax.mllb_def = _80_75.FStar_Extraction_ML_Syntax.mllb_def; FStar_Extraction_ML_Syntax.print_typ = false})
in ((env), ((

let _80_78 = ml_lb
in {FStar_Extraction_ML_Syntax.mllb_name = (((Prims.snd mname)), ((Prims.parse_int "0"))); FStar_Extraction_ML_Syntax.mllb_tysc = _80_78.FStar_Extraction_ML_Syntax.mllb_tysc; FStar_Extraction_ML_Syntax.mllb_add_unit = _80_78.FStar_Extraction_ML_Syntax.mllb_add_unit; FStar_Extraction_ML_Syntax.mllb_def = _80_78.FStar_Extraction_ML_Syntax.mllb_def; FStar_Extraction_ML_Syntax.print_typ = _80_78.FStar_Extraction_ML_Syntax.print_typ}))))))
end else begin
(let _178_37 = (let _178_36 = (let _178_35 = (FStar_Util.must ml_lb.FStar_Extraction_ML_Syntax.mllb_tysc)
in (FStar_Extraction_ML_Env.extend_lb env lbname t _178_35 ml_lb.FStar_Extraction_ML_Syntax.mllb_add_unit false))
in (FStar_All.pipe_left Prims.fst _178_36))
in ((_178_37), (ml_lb)))
end
in (match (_80_82) with
| (g, ml_lb) -> begin
((g), ((ml_lb)::ml_lbs))
end))
end)) ((g), ([])) bindings (Prims.snd lbs))
in (match (_80_85) with
| (g, ml_lbs') -> begin
(let _178_40 = (let _178_39 = (let _178_38 = (FStar_Extraction_ML_Util.mlloc_of_range r)
in FStar_Extraction_ML_Syntax.MLM_Loc (_178_38))
in (_178_39)::(FStar_Extraction_ML_Syntax.MLM_Let (((flavor), ([]), ((FStar_List.rev ml_lbs')))))::[])
in ((g), (_178_40)))
end))
end
| _80_87 -> begin
(failwith "impossible")
end)
end)))
end
| FStar_Absyn_Syntax.Sig_val_decl (lid, t, quals, r) -> begin
if (FStar_All.pipe_right quals (FStar_List.contains FStar_Absyn_Syntax.Assumption)) then begin
(

let impl = (match ((FStar_Absyn_Util.function_formals t)) with
| Some (bs, c) -> begin
(let _178_42 = (let _178_41 = (fail_exp lid (FStar_Absyn_Util.comp_result c))
in ((bs), (_178_41)))
in (FStar_Absyn_Syntax.mk_Exp_abs _178_42 None FStar_Absyn_Syntax.dummyRange))
end
| _80_99 -> begin
(fail_exp lid t)
end)
in (

let se = FStar_Absyn_Syntax.Sig_let (((((false), (({FStar_Absyn_Syntax.lbname = FStar_Util.Inr (lid); FStar_Absyn_Syntax.lbtyp = t; FStar_Absyn_Syntax.lbeff = FStar_Absyn_Const.effect_ML_lid; FStar_Absyn_Syntax.lbdef = impl})::[]))), (r), ([]), (quals)))
in (

let _80_104 = (extract_sig g se)
in (match (_80_104) with
| (g, mlm) -> begin
(

let is_record = (FStar_Util.for_some (fun _80_2 -> (match (_80_2) with
| FStar_Absyn_Syntax.RecordType (_80_107) -> begin
true
end
| _80_110 -> begin
false
end)) quals)
in (match ((FStar_Util.find_map quals (fun _80_3 -> (match (_80_3) with
| FStar_Absyn_Syntax.Discriminator (l) -> begin
Some (l)
end
| _80_116 -> begin
None
end)))) with
| Some (l) when (not (is_record)) -> begin
(let _178_49 = (let _178_48 = (let _178_45 = (FStar_Extraction_ML_Util.mlloc_of_range r)
in FStar_Extraction_ML_Syntax.MLM_Loc (_178_45))
in (let _178_47 = (let _178_46 = (FStar_Extraction_ML_ExtractExp.ind_discriminator_body g lid l)
in (_178_46)::[])
in (_178_48)::_178_47))
in ((g), (_178_49)))
end
| _80_120 -> begin
(match ((FStar_Util.find_map quals (fun _80_4 -> (match (_80_4) with
| FStar_Absyn_Syntax.Projector (l, _80_124) -> begin
Some (l)
end
| _80_128 -> begin
None
end)))) with
| Some (_80_130) -> begin
((g), ([]))
end
| _80_133 -> begin
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

let _80_143 = (FStar_Extraction_ML_ExtractExp.synth_exp g e)
in (match (_80_143) with
| (ml_main, _80_140, _80_142) -> begin
(let _178_53 = (let _178_52 = (let _178_51 = (FStar_Extraction_ML_Util.mlloc_of_range r)
in FStar_Extraction_ML_Syntax.MLM_Loc (_178_51))
in (_178_52)::(FStar_Extraction_ML_Syntax.MLM_Top (ml_main))::[])
in ((g), (_178_53)))
end))
end
| (FStar_Absyn_Syntax.Sig_kind_abbrev (_)) | (FStar_Absyn_Syntax.Sig_assume (_)) | (FStar_Absyn_Syntax.Sig_new_effect (_)) | (FStar_Absyn_Syntax.Sig_sub_effect (_)) | (FStar_Absyn_Syntax.Sig_effect_abbrev (_)) | (FStar_Absyn_Syntax.Sig_pragma (_)) -> begin
((g), ([]))
end)))


let extract_iface : FStar_Extraction_ML_Env.env  ->  FStar_Absyn_Syntax.modul  ->  FStar_Extraction_ML_Env.env = (fun g m -> (let _178_58 = (FStar_Util.fold_map extract_sig g m.FStar_Absyn_Syntax.declarations)
in (FStar_All.pipe_right _178_58 Prims.fst)))


let rec extract : FStar_Extraction_ML_Env.env  ->  FStar_Absyn_Syntax.modul  ->  (FStar_Extraction_ML_Env.env * FStar_Extraction_ML_Syntax.mllib Prims.list) = (fun g m -> (

let _80_166 = (FStar_Absyn_Util.reset_gensym ())
in (

let name = (FStar_Extraction_ML_Syntax.mlpath_of_lident m.FStar_Absyn_Syntax.name)
in (

let g = (

let _80_169 = g
in {FStar_Extraction_ML_Env.tcenv = _80_169.FStar_Extraction_ML_Env.tcenv; FStar_Extraction_ML_Env.gamma = _80_169.FStar_Extraction_ML_Env.gamma; FStar_Extraction_ML_Env.tydefs = _80_169.FStar_Extraction_ML_Env.tydefs; FStar_Extraction_ML_Env.currentModule = name})
in if (((m.FStar_Absyn_Syntax.name.FStar_Ident.str = "Prims") || m.FStar_Absyn_Syntax.is_interface) || (FStar_Options.no_extract m.FStar_Absyn_Syntax.name.FStar_Ident.str)) then begin
(

let g = (extract_iface g m)
in ((g), ([])))
end else begin
(

let _80_175 = (FStar_Util.fold_map extract_sig g m.FStar_Absyn_Syntax.declarations)
in (match (_80_175) with
| (g, sigs) -> begin
(

let mlm = (FStar_List.flatten sigs)
in ((g), ((FStar_Extraction_ML_Syntax.MLLib ((((name), (Some ((([]), (mlm)))), (FStar_Extraction_ML_Syntax.MLLib ([]))))::[]))::[])))
end))
end))))




