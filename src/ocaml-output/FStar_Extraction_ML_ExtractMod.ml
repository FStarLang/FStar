
open Prims
# 29 "FStar.Extraction.ML.ExtractMod.fst"
let fail_exp : FStar_Ident.lident  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.exp = (fun lid t -> (let _143_16 = (let _143_15 = (FStar_Absyn_Util.fvar None FStar_Absyn_Const.failwith_lid FStar_Absyn_Syntax.dummyRange)
in (let _143_14 = (let _143_13 = (FStar_Absyn_Syntax.targ t)
in (let _143_12 = (let _143_11 = (let _143_10 = (let _143_9 = (let _143_8 = (let _143_7 = (let _143_6 = (let _143_5 = (FStar_Absyn_Print.sli lid)
in (Prims.strcat "Not yet implemented:" _143_5))
in (FStar_Bytes.string_as_unicode_bytes _143_6))
in (_143_7, FStar_Absyn_Syntax.dummyRange))
in FStar_Const.Const_string (_143_8))
in (FStar_Absyn_Syntax.mk_Exp_constant _143_9 None FStar_Absyn_Syntax.dummyRange))
in (FStar_All.pipe_left FStar_Absyn_Syntax.varg _143_10))
in (_143_11)::[])
in (_143_13)::_143_12))
in (_143_15, _143_14)))
in (FStar_Absyn_Syntax.mk_Exp_app _143_16 None FStar_Absyn_Syntax.dummyRange)))

# 33 "FStar.Extraction.ML.ExtractMod.fst"
let mangle_projector_lid : FStar_Ident.lident  ->  FStar_Ident.lident = (fun x -> (
# 34 "FStar.Extraction.ML.ExtractMod.fst"
let projecteeName = x.FStar_Ident.ident
in (
# 35 "FStar.Extraction.ML.ExtractMod.fst"
let _64_11 = (FStar_Util.prefix x.FStar_Ident.ns)
in (match (_64_11) with
| (prefix, constrName) -> begin
(
# 36 "FStar.Extraction.ML.ExtractMod.fst"
let mangledName = (FStar_Absyn_Syntax.id_of_text (Prims.strcat (Prims.strcat (Prims.strcat "___" constrName.FStar_Ident.idText) "___") projecteeName.FStar_Ident.idText))
in (FStar_Ident.lid_of_ids (FStar_List.append prefix ((mangledName)::[]))))
end))))

# 39 "FStar.Extraction.ML.ExtractMod.fst"
let rec extract_sig : FStar_Extraction_ML_Env.env  ->  FStar_Absyn_Syntax.sigelt  ->  (FStar_Extraction_ML_Env.env * FStar_Extraction_ML_Syntax.mlmodule1 Prims.list) = (fun g se -> (
# 40 "FStar.Extraction.ML.ExtractMod.fst"
let _64_16 = (FStar_Extraction_ML_Env.debug g (fun u -> (let _143_25 = (let _143_24 = (FStar_Absyn_Print.sigelt_to_string se)
in (FStar_Util.format1 "now extracting :  %s \n" _143_24))
in (FStar_Util.print_string _143_25))))
in (match (se) with
| (FStar_Absyn_Syntax.Sig_datacon (_)) | (FStar_Absyn_Syntax.Sig_bundle (_)) | (FStar_Absyn_Syntax.Sig_tycon (_)) | (FStar_Absyn_Syntax.Sig_typ_abbrev (_)) -> begin
(
# 46 "FStar.Extraction.ML.ExtractMod.fst"
let _64_32 = (FStar_Extraction_ML_ExtractTyp.extractSigElt g se)
in (match (_64_32) with
| (c, tds) -> begin
(c, tds)
end))
end
| FStar_Absyn_Syntax.Sig_let (lbs, r, _64_36, quals) -> begin
(
# 50 "FStar.Extraction.ML.ExtractMod.fst"
let elet = (FStar_Absyn_Syntax.mk_Exp_let (lbs, FStar_Absyn_Const.exp_false_bool) None r)
in (
# 51 "FStar.Extraction.ML.ExtractMod.fst"
let _64_46 = (FStar_Extraction_ML_ExtractExp.synth_exp g elet)
in (match (_64_46) with
| (ml_let, _64_43, _64_45) -> begin
(match (ml_let.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Let (ml_lbs, _64_49) -> begin
(
# 54 "FStar.Extraction.ML.ExtractMod.fst"
let _64_78 = (FStar_List.fold_left2 (fun _64_54 ml_lb _64_62 -> (match ((_64_54, _64_62)) with
| ((env, ml_lbs), {FStar_Absyn_Syntax.lbname = lbname; FStar_Absyn_Syntax.lbtyp = t; FStar_Absyn_Syntax.lbeff = _64_59; FStar_Absyn_Syntax.lbdef = _64_57}) -> begin
(
# 56 "FStar.Extraction.ML.ExtractMod.fst"
let _64_75 = if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _64_1 -> (match (_64_1) with
| FStar_Absyn_Syntax.Projector (_64_65) -> begin
true
end
| _64_68 -> begin
false
end)))) then begin
(
# 58 "FStar.Extraction.ML.ExtractMod.fst"
let mname = (let _143_31 = (let _143_30 = (FStar_Util.right lbname)
in (mangle_projector_lid _143_30))
in (FStar_All.pipe_right _143_31 FStar_Extraction_ML_Syntax.mlpath_of_lident))
in (
# 59 "FStar.Extraction.ML.ExtractMod.fst"
let env = (let _143_34 = (let _143_32 = (FStar_Util.right lbname)
in (FStar_All.pipe_left FStar_Absyn_Util.fv _143_32))
in (let _143_33 = (FStar_Util.must ml_lb.FStar_Extraction_ML_Syntax.mllb_tysc)
in (FStar_Extraction_ML_Env.extend_fv' env _143_34 mname _143_33 ml_lb.FStar_Extraction_ML_Syntax.mllb_add_unit false)))
in (env, (
# 60 "FStar.Extraction.ML.ExtractMod.fst"
let _64_71 = ml_lb
in {FStar_Extraction_ML_Syntax.mllb_name = ((Prims.snd mname), 0); FStar_Extraction_ML_Syntax.mllb_tysc = _64_71.FStar_Extraction_ML_Syntax.mllb_tysc; FStar_Extraction_ML_Syntax.mllb_add_unit = _64_71.FStar_Extraction_ML_Syntax.mllb_add_unit; FStar_Extraction_ML_Syntax.mllb_def = _64_71.FStar_Extraction_ML_Syntax.mllb_def}))))
end else begin
(let _143_37 = (let _143_36 = (let _143_35 = (FStar_Util.must ml_lb.FStar_Extraction_ML_Syntax.mllb_tysc)
in (FStar_Extraction_ML_Env.extend_lb env lbname t _143_35 ml_lb.FStar_Extraction_ML_Syntax.mllb_add_unit false))
in (FStar_All.pipe_left Prims.fst _143_36))
in (_143_37, ml_lb))
end
in (match (_64_75) with
| (g, ml_lb) -> begin
(g, (ml_lb)::ml_lbs)
end))
end)) (g, []) (Prims.snd ml_lbs) (Prims.snd lbs))
in (match (_64_78) with
| (g, ml_lbs') -> begin
(let _143_40 = (let _143_39 = (let _143_38 = (FStar_Extraction_ML_ExtractTyp.mlloc_of_range r)
in FStar_Extraction_ML_Syntax.MLM_Loc (_143_38))
in (_143_39)::(FStar_Extraction_ML_Syntax.MLM_Let (((Prims.fst ml_lbs), (FStar_List.rev ml_lbs'))))::[])
in (g, _143_40))
end))
end
| _64_80 -> begin
(FStar_All.failwith "impossible")
end)
end)))
end
| FStar_Absyn_Syntax.Sig_val_decl (lid, t, quals, r) -> begin
if (FStar_All.pipe_right quals (FStar_List.contains FStar_Absyn_Syntax.Assumption)) then begin
(
# 73 "FStar.Extraction.ML.ExtractMod.fst"
let impl = (match ((FStar_Absyn_Util.function_formals t)) with
| Some (bs, c) -> begin
(let _143_42 = (let _143_41 = (fail_exp lid (FStar_Absyn_Util.comp_result c))
in (bs, _143_41))
in (FStar_Absyn_Syntax.mk_Exp_abs _143_42 None FStar_Absyn_Syntax.dummyRange))
end
| _64_92 -> begin
(fail_exp lid t)
end)
in (
# 76 "FStar.Extraction.ML.ExtractMod.fst"
let se = FStar_Absyn_Syntax.Sig_let (((false, ({FStar_Absyn_Syntax.lbname = FStar_Util.Inr (lid); FStar_Absyn_Syntax.lbtyp = t; FStar_Absyn_Syntax.lbeff = FStar_Absyn_Const.effect_ML_lid; FStar_Absyn_Syntax.lbdef = impl})::[]), r, [], quals))
in (
# 77 "FStar.Extraction.ML.ExtractMod.fst"
let _64_97 = (extract_sig g se)
in (match (_64_97) with
| (g, mlm) -> begin
(
# 78 "FStar.Extraction.ML.ExtractMod.fst"
let is_record = (FStar_Util.for_some (fun _64_2 -> (match (_64_2) with
| FStar_Absyn_Syntax.RecordType (_64_100) -> begin
true
end
| _64_103 -> begin
false
end)) quals)
in (match ((FStar_Util.find_map quals (fun _64_3 -> (match (_64_3) with
| FStar_Absyn_Syntax.Discriminator (l) -> begin
Some (l)
end
| _64_109 -> begin
None
end)))) with
| Some (l) when (not (is_record)) -> begin
(let _143_49 = (let _143_48 = (let _143_45 = (FStar_Extraction_ML_ExtractTyp.mlloc_of_range r)
in FStar_Extraction_ML_Syntax.MLM_Loc (_143_45))
in (let _143_47 = (let _143_46 = (FStar_Extraction_ML_ExtractExp.ind_discriminator_body g lid l)
in (_143_46)::[])
in (_143_48)::_143_47))
in (g, _143_49))
end
| _64_113 -> begin
(match ((FStar_Util.find_map quals (fun _64_4 -> (match (_64_4) with
| FStar_Absyn_Syntax.Projector (l, _64_117) -> begin
Some (l)
end
| _64_121 -> begin
None
end)))) with
| Some (_64_123) -> begin
(g, [])
end
| _64_126 -> begin
(g, mlm)
end)
end))
end))))
end else begin
(g, [])
end
end
| FStar_Absyn_Syntax.Sig_main (e, r) -> begin
(
# 89 "FStar.Extraction.ML.ExtractMod.fst"
let _64_136 = (FStar_Extraction_ML_ExtractExp.synth_exp g e)
in (match (_64_136) with
| (ml_main, _64_133, _64_135) -> begin
(let _143_53 = (let _143_52 = (let _143_51 = (FStar_Extraction_ML_ExtractTyp.mlloc_of_range r)
in FStar_Extraction_ML_Syntax.MLM_Loc (_143_51))
in (_143_52)::(FStar_Extraction_ML_Syntax.MLM_Top (ml_main))::[])
in (g, _143_53))
end))
end
| (FStar_Absyn_Syntax.Sig_kind_abbrev (_)) | (FStar_Absyn_Syntax.Sig_assume (_)) | (FStar_Absyn_Syntax.Sig_new_effect (_)) | (FStar_Absyn_Syntax.Sig_sub_effect (_)) | (FStar_Absyn_Syntax.Sig_effect_abbrev (_)) | (FStar_Absyn_Syntax.Sig_pragma (_)) -> begin
(g, [])
end)))

# 102 "FStar.Extraction.ML.ExtractMod.fst"
let extract_iface : FStar_Extraction_ML_Env.env  ->  FStar_Absyn_Syntax.modul  ->  FStar_Extraction_ML_Env.env = (fun g m -> (let _143_58 = (FStar_Util.fold_map extract_sig g m.FStar_Absyn_Syntax.declarations)
in (FStar_All.pipe_right _143_58 Prims.fst)))

# 104 "FStar.Extraction.ML.ExtractMod.fst"
let rec extract : FStar_Extraction_ML_Env.env  ->  FStar_Absyn_Syntax.modul  ->  (FStar_Extraction_ML_Env.env * FStar_Extraction_ML_Syntax.mllib Prims.list) = (fun g m -> (
# 105 "FStar.Extraction.ML.ExtractMod.fst"
let _64_159 = (FStar_Absyn_Util.reset_gensym ())
in (
# 106 "FStar.Extraction.ML.ExtractMod.fst"
let name = (FStar_Extraction_ML_Syntax.mlpath_of_lident m.FStar_Absyn_Syntax.name)
in (
# 107 "FStar.Extraction.ML.ExtractMod.fst"
let g = (
# 107 "FStar.Extraction.ML.ExtractMod.fst"
let _64_162 = g
in {FStar_Extraction_ML_Env.tcenv = _64_162.FStar_Extraction_ML_Env.tcenv; FStar_Extraction_ML_Env.gamma = _64_162.FStar_Extraction_ML_Env.gamma; FStar_Extraction_ML_Env.tydefs = _64_162.FStar_Extraction_ML_Env.tydefs; FStar_Extraction_ML_Env.currentModule = name})
in if (((m.FStar_Absyn_Syntax.name.FStar_Ident.str = "Prims") || m.FStar_Absyn_Syntax.is_interface) || (let _143_63 = (FStar_ST.read FStar_Options.no_extract)
in (FStar_List.contains m.FStar_Absyn_Syntax.name.FStar_Ident.str _143_63))) then begin
(
# 111 "FStar.Extraction.ML.ExtractMod.fst"
let g = (extract_iface g m)
in (g, []))
end else begin
(
# 113 "FStar.Extraction.ML.ExtractMod.fst"
let _64_168 = (FStar_Util.fold_map extract_sig g m.FStar_Absyn_Syntax.declarations)
in (match (_64_168) with
| (g, sigs) -> begin
(
# 114 "FStar.Extraction.ML.ExtractMod.fst"
let mlm = (FStar_List.flatten sigs)
in (let _143_68 = (let _143_67 = (let _143_66 = (let _143_65 = (let _143_64 = (FStar_Extraction_ML_Util.flatten_mlpath name)
in (_143_64, Some (([], mlm)), FStar_Extraction_ML_Syntax.MLLib ([])))
in (_143_65)::[])
in FStar_Extraction_ML_Syntax.MLLib (_143_66))
in (_143_67)::[])
in (g, _143_68)))
end))
end))))




