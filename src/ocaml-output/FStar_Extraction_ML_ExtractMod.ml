
open Prims
# 29 "FStar.Extraction.ML.ExtractMod.fst"
let fail_exp : FStar_Ident.lident  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.exp = (fun lid t -> (let _155_16 = (let _155_15 = (FStar_Absyn_Util.fvar None FStar_Absyn_Const.failwith_lid FStar_Absyn_Syntax.dummyRange)
in (let _155_14 = (let _155_13 = (FStar_Absyn_Syntax.targ t)
in (let _155_12 = (let _155_11 = (let _155_10 = (let _155_9 = (let _155_8 = (let _155_7 = (let _155_6 = (let _155_5 = (FStar_Absyn_Print.sli lid)
in (Prims.strcat "Not yet implemented:" _155_5))
in (FStar_Bytes.string_as_unicode_bytes _155_6))
in (_155_7, FStar_Absyn_Syntax.dummyRange))
in FStar_Const.Const_string (_155_8))
in (FStar_Absyn_Syntax.mk_Exp_constant _155_9 None FStar_Absyn_Syntax.dummyRange))
in (FStar_All.pipe_left FStar_Absyn_Syntax.varg _155_10))
in (_155_11)::[])
in (_155_13)::_155_12))
in (_155_15, _155_14)))
in (FStar_Absyn_Syntax.mk_Exp_app _155_16 None FStar_Absyn_Syntax.dummyRange)))

# 33 "FStar.Extraction.ML.ExtractMod.fst"
let mangle_projector_lid : FStar_Ident.lident  ->  FStar_Ident.lident = (fun x -> (
# 34 "FStar.Extraction.ML.ExtractMod.fst"
let projecteeName = x.FStar_Ident.ident
in (
# 35 "FStar.Extraction.ML.ExtractMod.fst"
let _71_11 = (FStar_Util.prefix x.FStar_Ident.ns)
in (match (_71_11) with
| (prefix, constrName) -> begin
(
# 36 "FStar.Extraction.ML.ExtractMod.fst"
let mangledName = (FStar_Absyn_Syntax.id_of_text (Prims.strcat (Prims.strcat (Prims.strcat "___" constrName.FStar_Ident.idText) "___") projecteeName.FStar_Ident.idText))
in (FStar_Ident.lid_of_ids (FStar_List.append prefix ((mangledName)::[]))))
end))))

# 39 "FStar.Extraction.ML.ExtractMod.fst"
let rec extract_sig : FStar_Extraction_ML_Env.env  ->  FStar_Absyn_Syntax.sigelt  ->  (FStar_Extraction_ML_Env.env * FStar_Extraction_ML_Syntax.mlmodule1 Prims.list) = (fun g se -> (
# 40 "FStar.Extraction.ML.ExtractMod.fst"
let _71_16 = (FStar_Extraction_ML_Env.debug g (fun u -> (let _155_25 = (let _155_24 = (FStar_Absyn_Print.sigelt_to_string se)
in (FStar_Util.format1 "now extracting :  %s \n" _155_24))
in (FStar_Util.print_string _155_25))))
in (match (se) with
| (FStar_Absyn_Syntax.Sig_datacon (_)) | (FStar_Absyn_Syntax.Sig_bundle (_)) | (FStar_Absyn_Syntax.Sig_tycon (_)) | (FStar_Absyn_Syntax.Sig_typ_abbrev (_)) -> begin
(
# 46 "FStar.Extraction.ML.ExtractMod.fst"
let _71_32 = (FStar_Extraction_ML_ExtractTyp.extractSigElt g se)
in (match (_71_32) with
| (c, tds) -> begin
(c, tds)
end))
end
| FStar_Absyn_Syntax.Sig_let (lbs, r, _71_36, quals) -> begin
(
# 50 "FStar.Extraction.ML.ExtractMod.fst"
let elet = (FStar_Absyn_Syntax.mk_Exp_let (lbs, FStar_Absyn_Const.exp_false_bool) None r)
in (
# 51 "FStar.Extraction.ML.ExtractMod.fst"
let _71_46 = (FStar_Extraction_ML_ExtractExp.synth_exp g elet)
in (match (_71_46) with
| (ml_let, _71_43, _71_45) -> begin
(match (ml_let.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Let (ml_lbs, _71_49) -> begin
(
# 54 "FStar.Extraction.ML.ExtractMod.fst"
let _71_81 = (FStar_List.fold_left2 (fun _71_54 ml_lb _71_62 -> (match ((_71_54, _71_62)) with
| ((env, ml_lbs), {FStar_Absyn_Syntax.lbname = lbname; FStar_Absyn_Syntax.lbtyp = t; FStar_Absyn_Syntax.lbeff = _71_59; FStar_Absyn_Syntax.lbdef = _71_57}) -> begin
(
# 56 "FStar.Extraction.ML.ExtractMod.fst"
let _71_78 = if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _71_1 -> (match (_71_1) with
| FStar_Absyn_Syntax.Projector (_71_65) -> begin
true
end
| _71_68 -> begin
false
end)))) then begin
(
# 58 "FStar.Extraction.ML.ExtractMod.fst"
let mname = (let _155_31 = (let _155_30 = (FStar_Util.right lbname)
in (mangle_projector_lid _155_30))
in (FStar_All.pipe_right _155_31 FStar_Extraction_ML_Syntax.mlpath_of_lident))
in (
# 59 "FStar.Extraction.ML.ExtractMod.fst"
let env = (let _155_34 = (let _155_32 = (FStar_Util.right lbname)
in (FStar_All.pipe_left FStar_Absyn_Util.fv _155_32))
in (let _155_33 = (FStar_Util.must ml_lb.FStar_Extraction_ML_Syntax.mllb_tysc)
in (FStar_Extraction_ML_Env.extend_fv' env _155_34 mname _155_33 ml_lb.FStar_Extraction_ML_Syntax.mllb_add_unit false)))
in (
# 60 "FStar.Extraction.ML.ExtractMod.fst"
let ml_lb = (
# 60 "FStar.Extraction.ML.ExtractMod.fst"
let _71_71 = ml_lb
in {FStar_Extraction_ML_Syntax.mllb_name = _71_71.FStar_Extraction_ML_Syntax.mllb_name; FStar_Extraction_ML_Syntax.mllb_tysc = _71_71.FStar_Extraction_ML_Syntax.mllb_tysc; FStar_Extraction_ML_Syntax.mllb_add_unit = _71_71.FStar_Extraction_ML_Syntax.mllb_add_unit; FStar_Extraction_ML_Syntax.mllb_def = _71_71.FStar_Extraction_ML_Syntax.mllb_def; FStar_Extraction_ML_Syntax.print_typ = false})
in (env, (
# 61 "FStar.Extraction.ML.ExtractMod.fst"
let _71_74 = ml_lb
in {FStar_Extraction_ML_Syntax.mllb_name = ((Prims.snd mname), 0); FStar_Extraction_ML_Syntax.mllb_tysc = _71_74.FStar_Extraction_ML_Syntax.mllb_tysc; FStar_Extraction_ML_Syntax.mllb_add_unit = _71_74.FStar_Extraction_ML_Syntax.mllb_add_unit; FStar_Extraction_ML_Syntax.mllb_def = _71_74.FStar_Extraction_ML_Syntax.mllb_def; FStar_Extraction_ML_Syntax.print_typ = _71_74.FStar_Extraction_ML_Syntax.print_typ})))))
end else begin
(let _155_37 = (let _155_36 = (let _155_35 = (FStar_Util.must ml_lb.FStar_Extraction_ML_Syntax.mllb_tysc)
in (FStar_Extraction_ML_Env.extend_lb env lbname t _155_35 ml_lb.FStar_Extraction_ML_Syntax.mllb_add_unit false))
in (FStar_All.pipe_left Prims.fst _155_36))
in (_155_37, ml_lb))
end
in (match (_71_78) with
| (g, ml_lb) -> begin
(g, (ml_lb)::ml_lbs)
end))
end)) (g, []) (Prims.snd ml_lbs) (Prims.snd lbs))
in (match (_71_81) with
| (g, ml_lbs') -> begin
(let _155_40 = (let _155_39 = (let _155_38 = (FStar_Extraction_ML_Util.mlloc_of_range r)
in FStar_Extraction_ML_Syntax.MLM_Loc (_155_38))
in (_155_39)::(FStar_Extraction_ML_Syntax.MLM_Let (((Prims.fst ml_lbs), (FStar_List.rev ml_lbs'))))::[])
in (g, _155_40))
end))
end
| _71_83 -> begin
(FStar_All.failwith "impossible")
end)
end)))
end
| FStar_Absyn_Syntax.Sig_val_decl (lid, t, quals, r) -> begin
if (FStar_All.pipe_right quals (FStar_List.contains FStar_Absyn_Syntax.Assumption)) then begin
(
# 74 "FStar.Extraction.ML.ExtractMod.fst"
let impl = (match ((FStar_Absyn_Util.function_formals t)) with
| Some (bs, c) -> begin
(let _155_42 = (let _155_41 = (fail_exp lid (FStar_Absyn_Util.comp_result c))
in (bs, _155_41))
in (FStar_Absyn_Syntax.mk_Exp_abs _155_42 None FStar_Absyn_Syntax.dummyRange))
end
| _71_95 -> begin
(fail_exp lid t)
end)
in (
# 77 "FStar.Extraction.ML.ExtractMod.fst"
let se = FStar_Absyn_Syntax.Sig_let (((false, ({FStar_Absyn_Syntax.lbname = FStar_Util.Inr (lid); FStar_Absyn_Syntax.lbtyp = t; FStar_Absyn_Syntax.lbeff = FStar_Absyn_Const.effect_ML_lid; FStar_Absyn_Syntax.lbdef = impl})::[]), r, [], quals))
in (
# 78 "FStar.Extraction.ML.ExtractMod.fst"
let _71_100 = (extract_sig g se)
in (match (_71_100) with
| (g, mlm) -> begin
(
# 79 "FStar.Extraction.ML.ExtractMod.fst"
let is_record = (FStar_Util.for_some (fun _71_2 -> (match (_71_2) with
| FStar_Absyn_Syntax.RecordType (_71_103) -> begin
true
end
| _71_106 -> begin
false
end)) quals)
in (match ((FStar_Util.find_map quals (fun _71_3 -> (match (_71_3) with
| FStar_Absyn_Syntax.Discriminator (l) -> begin
Some (l)
end
| _71_112 -> begin
None
end)))) with
| Some (l) when (not (is_record)) -> begin
(let _155_49 = (let _155_48 = (let _155_45 = (FStar_Extraction_ML_Util.mlloc_of_range r)
in FStar_Extraction_ML_Syntax.MLM_Loc (_155_45))
in (let _155_47 = (let _155_46 = (FStar_Extraction_ML_ExtractExp.ind_discriminator_body g lid l)
in (_155_46)::[])
in (_155_48)::_155_47))
in (g, _155_49))
end
| _71_116 -> begin
(match ((FStar_Util.find_map quals (fun _71_4 -> (match (_71_4) with
| FStar_Absyn_Syntax.Projector (l, _71_120) -> begin
Some (l)
end
| _71_124 -> begin
None
end)))) with
| Some (_71_126) -> begin
(g, [])
end
| _71_129 -> begin
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
# 90 "FStar.Extraction.ML.ExtractMod.fst"
let _71_139 = (FStar_Extraction_ML_ExtractExp.synth_exp g e)
in (match (_71_139) with
| (ml_main, _71_136, _71_138) -> begin
(let _155_53 = (let _155_52 = (let _155_51 = (FStar_Extraction_ML_Util.mlloc_of_range r)
in FStar_Extraction_ML_Syntax.MLM_Loc (_155_51))
in (_155_52)::(FStar_Extraction_ML_Syntax.MLM_Top (ml_main))::[])
in (g, _155_53))
end))
end
| (FStar_Absyn_Syntax.Sig_kind_abbrev (_)) | (FStar_Absyn_Syntax.Sig_assume (_)) | (FStar_Absyn_Syntax.Sig_new_effect (_)) | (FStar_Absyn_Syntax.Sig_sub_effect (_)) | (FStar_Absyn_Syntax.Sig_effect_abbrev (_)) | (FStar_Absyn_Syntax.Sig_pragma (_)) -> begin
(g, [])
end)))

# 103 "FStar.Extraction.ML.ExtractMod.fst"
let extract_iface : FStar_Extraction_ML_Env.env  ->  FStar_Absyn_Syntax.modul  ->  FStar_Extraction_ML_Env.env = (fun g m -> (let _155_58 = (FStar_Util.fold_map extract_sig g m.FStar_Absyn_Syntax.declarations)
in (FStar_All.pipe_right _155_58 Prims.fst)))

# 105 "FStar.Extraction.ML.ExtractMod.fst"
let rec extract : FStar_Extraction_ML_Env.env  ->  FStar_Absyn_Syntax.modul  ->  (FStar_Extraction_ML_Env.env * FStar_Extraction_ML_Syntax.mllib Prims.list) = (fun g m -> (
# 106 "FStar.Extraction.ML.ExtractMod.fst"
let _71_162 = (FStar_Absyn_Util.reset_gensym ())
in (
# 107 "FStar.Extraction.ML.ExtractMod.fst"
let name = (FStar_Extraction_ML_Syntax.mlpath_of_lident m.FStar_Absyn_Syntax.name)
in (
# 108 "FStar.Extraction.ML.ExtractMod.fst"
let g = (
# 108 "FStar.Extraction.ML.ExtractMod.fst"
let _71_165 = g
in {FStar_Extraction_ML_Env.tcenv = _71_165.FStar_Extraction_ML_Env.tcenv; FStar_Extraction_ML_Env.gamma = _71_165.FStar_Extraction_ML_Env.gamma; FStar_Extraction_ML_Env.tydefs = _71_165.FStar_Extraction_ML_Env.tydefs; FStar_Extraction_ML_Env.currentModule = name})
in if (((m.FStar_Absyn_Syntax.name.FStar_Ident.str = "Prims") || m.FStar_Absyn_Syntax.is_interface) || (let _155_63 = (FStar_ST.read FStar_Options.no_extract)
in (FStar_List.contains m.FStar_Absyn_Syntax.name.FStar_Ident.str _155_63))) then begin
(
# 112 "FStar.Extraction.ML.ExtractMod.fst"
let g = (extract_iface g m)
in (g, []))
end else begin
(
# 114 "FStar.Extraction.ML.ExtractMod.fst"
let _71_171 = (FStar_Util.fold_map extract_sig g m.FStar_Absyn_Syntax.declarations)
in (match (_71_171) with
| (g, sigs) -> begin
(
# 115 "FStar.Extraction.ML.ExtractMod.fst"
let mlm = (FStar_List.flatten sigs)
in (let _155_68 = (let _155_67 = (let _155_66 = (let _155_65 = (let _155_64 = (FStar_Extraction_ML_Util.flatten_mlpath name)
in (_155_64, Some (([], mlm)), FStar_Extraction_ML_Syntax.MLLib ([])))
in (_155_65)::[])
in FStar_Extraction_ML_Syntax.MLLib (_155_66))
in (_155_67)::[])
in (g, _155_68)))
end))
end))))




