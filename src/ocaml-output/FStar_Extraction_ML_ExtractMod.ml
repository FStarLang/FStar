
open Prims

let fail_exp : FStar_Ident.lident  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.exp = (fun lid t -> (let _180_16 = (let _180_15 = (FStar_Absyn_Util.fvar None FStar_Absyn_Const.failwith_lid FStar_Absyn_Syntax.dummyRange)
in (let _180_14 = (let _180_13 = (FStar_Absyn_Syntax.targ t)
in (let _180_12 = (let _180_11 = (let _180_10 = (let _180_9 = (let _180_8 = (let _180_7 = (let _180_6 = (let _180_5 = (FStar_Absyn_Print.sli lid)
in (Prims.strcat "Not yet implemented:" _180_5))
in (FStar_Bytes.string_as_unicode_bytes _180_6))
in ((_180_7), (FStar_Absyn_Syntax.dummyRange)))
in FStar_Const.Const_string (_180_8))
in (FStar_Absyn_Syntax.mk_Exp_constant _180_9 None FStar_Absyn_Syntax.dummyRange))
in (FStar_All.pipe_left FStar_Absyn_Syntax.varg _180_10))
in (_180_11)::[])
in (_180_13)::_180_12))
in ((_180_15), (_180_14))))
in (FStar_Absyn_Syntax.mk_Exp_app _180_16 None FStar_Absyn_Syntax.dummyRange)))


let mangle_projector_lid : FStar_Ident.lident  ->  FStar_Ident.lident = (fun x -> (

let projecteeName = x.FStar_Ident.ident
in (

let _81_11 = (FStar_Util.prefix x.FStar_Ident.ns)
in (match (_81_11) with
| (prefix, constrName) -> begin
(

let mangledName = (FStar_Absyn_Syntax.id_of_text (Prims.strcat "___" (Prims.strcat constrName.FStar_Ident.idText (Prims.strcat "___" projecteeName.FStar_Ident.idText))))
in (FStar_Ident.lid_of_ids (FStar_List.append prefix ((mangledName)::[]))))
end))))


let rec extract_sig : FStar_Extraction_ML_Env.env  ->  FStar_Absyn_Syntax.sigelt  ->  (FStar_Extraction_ML_Env.env * FStar_Extraction_ML_Syntax.mlmodule1 Prims.list) = (fun g se -> (

let _81_16 = (FStar_Extraction_ML_Env.debug g (fun u -> (let _180_25 = (let _180_24 = (FStar_Absyn_Print.sigelt_to_string se)
in (FStar_Util.format1 "now extracting :  %s \n" _180_24))
in (FStar_Util.print_string _180_25))))
in (match (se) with
| (FStar_Absyn_Syntax.Sig_datacon (_)) | (FStar_Absyn_Syntax.Sig_bundle (_)) | (FStar_Absyn_Syntax.Sig_tycon (_)) | (FStar_Absyn_Syntax.Sig_typ_abbrev (_)) -> begin
(

let _81_32 = (FStar_Extraction_ML_ExtractTyp.extractSigElt g se)
in (match (_81_32) with
| (c, tds) -> begin
((c), (tds))
end))
end
| FStar_Absyn_Syntax.Sig_let (lbs, r, _81_36, quals) -> begin
(

let elet = (FStar_Absyn_Syntax.mk_Exp_let ((lbs), (FStar_Absyn_Const.exp_false_bool)) None r)
in (

let _81_46 = (FStar_Extraction_ML_ExtractExp.synth_exp g elet)
in (match (_81_46) with
| (ml_let, _81_43, _81_45) -> begin
(match (ml_let.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Let ((flavor, _81_49, bindings), _81_53) -> begin
(

let _81_85 = (FStar_List.fold_left2 (fun _81_58 ml_lb _81_66 -> (match (((_81_58), (_81_66))) with
| ((env, ml_lbs), {FStar_Absyn_Syntax.lbname = lbname; FStar_Absyn_Syntax.lbtyp = t; FStar_Absyn_Syntax.lbeff = _81_63; FStar_Absyn_Syntax.lbdef = _81_61}) -> begin
(

let _81_82 = if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _81_1 -> (match (_81_1) with
| FStar_Absyn_Syntax.Projector (_81_69) -> begin
true
end
| _81_72 -> begin
false
end)))) then begin
(

let mname = (let _180_31 = (let _180_30 = (FStar_Util.right lbname)
in (mangle_projector_lid _180_30))
in (FStar_All.pipe_right _180_31 FStar_Extraction_ML_Syntax.mlpath_of_lident))
in (

let env = (let _180_34 = (let _180_32 = (FStar_Util.right lbname)
in (FStar_All.pipe_left FStar_Absyn_Util.fv _180_32))
in (let _180_33 = (FStar_Util.must ml_lb.FStar_Extraction_ML_Syntax.mllb_tysc)
in (FStar_Extraction_ML_Env.extend_fv' env _180_34 mname _180_33 ml_lb.FStar_Extraction_ML_Syntax.mllb_add_unit false)))
in (

let ml_lb = (

let _81_75 = ml_lb
in {FStar_Extraction_ML_Syntax.mllb_name = _81_75.FStar_Extraction_ML_Syntax.mllb_name; FStar_Extraction_ML_Syntax.mllb_tysc = _81_75.FStar_Extraction_ML_Syntax.mllb_tysc; FStar_Extraction_ML_Syntax.mllb_add_unit = _81_75.FStar_Extraction_ML_Syntax.mllb_add_unit; FStar_Extraction_ML_Syntax.mllb_def = _81_75.FStar_Extraction_ML_Syntax.mllb_def; FStar_Extraction_ML_Syntax.print_typ = false})
in ((env), ((

let _81_78 = ml_lb
in {FStar_Extraction_ML_Syntax.mllb_name = (((Prims.snd mname)), ((Prims.parse_int "0"))); FStar_Extraction_ML_Syntax.mllb_tysc = _81_78.FStar_Extraction_ML_Syntax.mllb_tysc; FStar_Extraction_ML_Syntax.mllb_add_unit = _81_78.FStar_Extraction_ML_Syntax.mllb_add_unit; FStar_Extraction_ML_Syntax.mllb_def = _81_78.FStar_Extraction_ML_Syntax.mllb_def; FStar_Extraction_ML_Syntax.print_typ = _81_78.FStar_Extraction_ML_Syntax.print_typ}))))))
end else begin
(let _180_37 = (let _180_36 = (let _180_35 = (FStar_Util.must ml_lb.FStar_Extraction_ML_Syntax.mllb_tysc)
in (FStar_Extraction_ML_Env.extend_lb env lbname t _180_35 ml_lb.FStar_Extraction_ML_Syntax.mllb_add_unit false))
in (FStar_All.pipe_left Prims.fst _180_36))
in ((_180_37), (ml_lb)))
end
in (match (_81_82) with
| (g, ml_lb) -> begin
((g), ((ml_lb)::ml_lbs))
end))
end)) ((g), ([])) bindings (Prims.snd lbs))
in (match (_81_85) with
| (g, ml_lbs') -> begin
(let _180_40 = (let _180_39 = (let _180_38 = (FStar_Extraction_ML_Util.mlloc_of_range r)
in FStar_Extraction_ML_Syntax.MLM_Loc (_180_38))
in (_180_39)::(FStar_Extraction_ML_Syntax.MLM_Let (((flavor), ([]), ((FStar_List.rev ml_lbs')))))::[])
in ((g), (_180_40)))
end))
end
| _81_87 -> begin
(failwith "impossible")
end)
end)))
end
| FStar_Absyn_Syntax.Sig_val_decl (lid, t, quals, r) -> begin
if (FStar_All.pipe_right quals (FStar_List.contains FStar_Absyn_Syntax.Assumption)) then begin
(

let impl = (match ((FStar_Absyn_Util.function_formals t)) with
| Some (bs, c) -> begin
(let _180_42 = (let _180_41 = (fail_exp lid (FStar_Absyn_Util.comp_result c))
in ((bs), (_180_41)))
in (FStar_Absyn_Syntax.mk_Exp_abs _180_42 None FStar_Absyn_Syntax.dummyRange))
end
| _81_99 -> begin
(fail_exp lid t)
end)
in (

let se = FStar_Absyn_Syntax.Sig_let (((((false), (({FStar_Absyn_Syntax.lbname = FStar_Util.Inr (lid); FStar_Absyn_Syntax.lbtyp = t; FStar_Absyn_Syntax.lbeff = FStar_Absyn_Const.effect_ML_lid; FStar_Absyn_Syntax.lbdef = impl})::[]))), (r), ([]), (quals)))
in (

let _81_104 = (extract_sig g se)
in (match (_81_104) with
| (g, mlm) -> begin
(

let is_record = (FStar_Util.for_some (fun _81_2 -> (match (_81_2) with
| FStar_Absyn_Syntax.RecordType (_81_107) -> begin
true
end
| _81_110 -> begin
false
end)) quals)
in (match ((FStar_Util.find_map quals (fun _81_3 -> (match (_81_3) with
| FStar_Absyn_Syntax.Discriminator (l) -> begin
Some (l)
end
| _81_116 -> begin
None
end)))) with
| Some (l) when (not (is_record)) -> begin
(let _180_49 = (let _180_48 = (let _180_45 = (FStar_Extraction_ML_Util.mlloc_of_range r)
in FStar_Extraction_ML_Syntax.MLM_Loc (_180_45))
in (let _180_47 = (let _180_46 = (FStar_Extraction_ML_ExtractExp.ind_discriminator_body g lid l)
in (_180_46)::[])
in (_180_48)::_180_47))
in ((g), (_180_49)))
end
| _81_120 -> begin
(match ((FStar_Util.find_map quals (fun _81_4 -> (match (_81_4) with
| FStar_Absyn_Syntax.Projector (l, _81_124) -> begin
Some (l)
end
| _81_128 -> begin
None
end)))) with
| Some (_81_130) -> begin
((g), ([]))
end
| _81_133 -> begin
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

let _81_143 = (FStar_Extraction_ML_ExtractExp.synth_exp g e)
in (match (_81_143) with
| (ml_main, _81_140, _81_142) -> begin
(let _180_53 = (let _180_52 = (let _180_51 = (FStar_Extraction_ML_Util.mlloc_of_range r)
in FStar_Extraction_ML_Syntax.MLM_Loc (_180_51))
in (_180_52)::(FStar_Extraction_ML_Syntax.MLM_Top (ml_main))::[])
in ((g), (_180_53)))
end))
end
| (FStar_Absyn_Syntax.Sig_kind_abbrev (_)) | (FStar_Absyn_Syntax.Sig_assume (_)) | (FStar_Absyn_Syntax.Sig_new_effect (_)) | (FStar_Absyn_Syntax.Sig_sub_effect (_)) | (FStar_Absyn_Syntax.Sig_effect_abbrev (_)) | (FStar_Absyn_Syntax.Sig_pragma (_)) -> begin
((g), ([]))
end)))


let extract_iface : FStar_Extraction_ML_Env.env  ->  FStar_Absyn_Syntax.modul  ->  FStar_Extraction_ML_Env.env = (fun g m -> (let _180_58 = (FStar_Util.fold_map extract_sig g m.FStar_Absyn_Syntax.declarations)
in (FStar_All.pipe_right _180_58 Prims.fst)))


let rec extract : FStar_Extraction_ML_Env.env  ->  FStar_Absyn_Syntax.modul  ->  (FStar_Extraction_ML_Env.env * FStar_Extraction_ML_Syntax.mllib Prims.list) = (fun g m -> (

let _81_166 = (FStar_Absyn_Util.reset_gensym ())
in (

let name = (FStar_Extraction_ML_Syntax.mlpath_of_lident m.FStar_Absyn_Syntax.name)
in (

let g = (

let _81_169 = g
in {FStar_Extraction_ML_Env.tcenv = _81_169.FStar_Extraction_ML_Env.tcenv; FStar_Extraction_ML_Env.gamma = _81_169.FStar_Extraction_ML_Env.gamma; FStar_Extraction_ML_Env.tydefs = _81_169.FStar_Extraction_ML_Env.tydefs; FStar_Extraction_ML_Env.currentModule = name})
in if (((m.FStar_Absyn_Syntax.name.FStar_Ident.str = "Prims") || m.FStar_Absyn_Syntax.is_interface) || (FStar_Options.no_extract m.FStar_Absyn_Syntax.name.FStar_Ident.str)) then begin
(

let g = (extract_iface g m)
in ((g), ([])))
end else begin
(

let _81_175 = (FStar_Util.fold_map extract_sig g m.FStar_Absyn_Syntax.declarations)
in (match (_81_175) with
| (g, sigs) -> begin
(

let mlm = (FStar_List.flatten sigs)
in ((g), ((FStar_Extraction_ML_Syntax.MLLib ((((name), (Some ((([]), (mlm)))), (FStar_Extraction_ML_Syntax.MLLib ([]))))::[]))::[])))
end))
end))))




