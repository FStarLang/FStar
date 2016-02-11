
open Prims
# 29 "extractmod.fs"

let fail_exp : FStar_Ident.lident  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.exp = (fun lid t -> (let _182_15 = (let _182_14 = (FStar_Absyn_Util.fvar None FStar_Absyn_Const.failwith_lid FStar_Absyn_Syntax.dummyRange)
in (let _182_13 = (let _182_12 = (let _182_11 = (let _182_10 = (let _182_9 = (let _182_8 = (let _182_7 = (let _182_6 = (let _182_5 = (FStar_Absyn_Print.sli lid)
in (Prims.strcat "Not yet implemented:" _182_5))
in (FStar_Bytes.string_as_unicode_bytes _182_6))
in (_182_7, FStar_Absyn_Syntax.dummyRange))
in FStar_Const.Const_string (_182_8))
in (FStar_Absyn_Syntax.mk_Exp_constant _182_9 None FStar_Absyn_Syntax.dummyRange))
in (FStar_All.pipe_left FStar_Absyn_Syntax.varg _182_10))
in (_182_11)::[])
in ((FStar_Absyn_Syntax.targ t))::_182_12)
in (_182_14, _182_13)))
in (FStar_Absyn_Syntax.mk_Exp_app _182_15 None FStar_Absyn_Syntax.dummyRange)))

# 33 "extractmod.fs"

let mangle_projector_lid : FStar_Ident.lident  ->  FStar_Ident.lident = (fun x -> (let projecteeName = x.FStar_Ident.ident
in (let _80_11 = (FStar_Util.prefix x.FStar_Ident.ns)
in (match (_80_11) with
| (prefix, constrName) -> begin
(let mangledName = (FStar_Absyn_Syntax.id_of_text (Prims.strcat (Prims.strcat (Prims.strcat "___" constrName.FStar_Ident.idText) "___") projecteeName.FStar_Ident.idText))
in (FStar_Ident.lid_of_ids (FStar_List.append prefix ((mangledName)::[]))))
end))))

# 39 "extractmod.fs"

let rec extract_sig : FStar_Extraction_ML_Env.env  ->  FStar_Absyn_Syntax.sigelt  ->  (FStar_Extraction_ML_Env.env * FStar_Extraction_ML_Syntax.mlmodule1 Prims.list) = (fun g se -> (let _80_16 = (FStar_Extraction_ML_Env.debug g (fun u -> (let _182_24 = (let _182_23 = (FStar_Absyn_Print.sigelt_to_string se)
in (FStar_Util.format1 "now extracting :  %s \n" _182_23))
in (FStar_Util.print_string _182_24))))
in (match (se) with
| (FStar_Absyn_Syntax.Sig_datacon (_)) | (FStar_Absyn_Syntax.Sig_bundle (_)) | (FStar_Absyn_Syntax.Sig_tycon (_)) | (FStar_Absyn_Syntax.Sig_typ_abbrev (_)) -> begin
(let _80_32 = (FStar_Extraction_ML_ExtractTyp.extractSigElt g se)
in (match (_80_32) with
| (c, tds) -> begin
(c, tds)
end))
end
| FStar_Absyn_Syntax.Sig_let (lbs, r, _80_36, quals) -> begin
(let elet = (FStar_Absyn_Syntax.mk_Exp_let (lbs, FStar_Absyn_Const.exp_false_bool) None r)
in (let _80_46 = (FStar_Extraction_ML_ExtractExp.synth_exp g elet)
in (match (_80_46) with
| (ml_let, _80_43, _80_45) -> begin
(match (ml_let.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Let (ml_lbs, _80_49) -> begin
(let _80_78 = (FStar_List.fold_left2 (fun _80_54 ml_lb _80_62 -> (match ((_80_54, _80_62)) with
| ((env, ml_lbs), {FStar_Absyn_Syntax.lbname = lbname; FStar_Absyn_Syntax.lbtyp = t; FStar_Absyn_Syntax.lbeff = _80_59; FStar_Absyn_Syntax.lbdef = _80_57}) -> begin
(let _80_75 = if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _80_1 -> (match (_80_1) with
| FStar_Absyn_Syntax.Projector (_80_65) -> begin
true
end
| _80_68 -> begin
false
end)))) then begin
(let mname = (let _182_30 = (let _182_29 = (FStar_Util.right lbname)
in (mangle_projector_lid _182_29))
in (FStar_All.pipe_right _182_30 FStar_Extraction_ML_Syntax.mlpath_of_lident))
in (let env = (let _182_32 = (let _182_31 = (FStar_Util.right lbname)
in (FStar_All.pipe_left FStar_Absyn_Util.fv _182_31))
in (FStar_Extraction_ML_Env.extend_fv' env _182_32 mname ml_lb.FStar_Extraction_ML_Syntax.mllb_tysc ml_lb.FStar_Extraction_ML_Syntax.mllb_add_unit false))
in (env, (let _80_71 = ml_lb
in {FStar_Extraction_ML_Syntax.mllb_name = ((Prims.snd mname), 0); FStar_Extraction_ML_Syntax.mllb_tysc = _80_71.FStar_Extraction_ML_Syntax.mllb_tysc; FStar_Extraction_ML_Syntax.mllb_add_unit = _80_71.FStar_Extraction_ML_Syntax.mllb_add_unit; FStar_Extraction_ML_Syntax.mllb_def = _80_71.FStar_Extraction_ML_Syntax.mllb_def}))))
end else begin
(let _182_34 = (let _182_33 = (FStar_Extraction_ML_Env.extend_lb env lbname t ml_lb.FStar_Extraction_ML_Syntax.mllb_tysc ml_lb.FStar_Extraction_ML_Syntax.mllb_add_unit false)
in (FStar_All.pipe_left Prims.fst _182_33))
in (_182_34, ml_lb))
end
in (match (_80_75) with
| (g, ml_lb) -> begin
(g, (ml_lb)::ml_lbs)
end))
end)) (g, []) (Prims.snd ml_lbs) (Prims.snd lbs))
in (match (_80_78) with
| (g, ml_lbs') -> begin
(let _182_36 = (let _182_35 = (FStar_Extraction_ML_ExtractTyp.mlloc_of_range r)
in (_182_35)::(FStar_Extraction_ML_Syntax.MLM_Let (((Prims.fst ml_lbs), (FStar_List.rev ml_lbs'))))::[])
in (g, _182_36))
end))
end
| _80_80 -> begin
(FStar_All.failwith "impossible")
end)
end)))
end
| FStar_Absyn_Syntax.Sig_val_decl (lid, t, quals, r) -> begin
if (FStar_All.pipe_right quals (FStar_List.contains FStar_Absyn_Syntax.Assumption)) then begin
(let impl = (match ((FStar_Absyn_Util.function_formals t)) with
| Some (bs, c) -> begin
(let _182_38 = (let _182_37 = (fail_exp lid (FStar_Absyn_Util.comp_result c))
in (bs, _182_37))
in (FStar_Absyn_Syntax.mk_Exp_abs _182_38 None FStar_Absyn_Syntax.dummyRange))
end
| _80_92 -> begin
(fail_exp lid t)
end)
in (let se = FStar_Absyn_Syntax.Sig_let (((false, ({FStar_Absyn_Syntax.lbname = FStar_Util.Inr (lid); FStar_Absyn_Syntax.lbtyp = t; FStar_Absyn_Syntax.lbeff = FStar_Absyn_Const.effect_ML_lid; FStar_Absyn_Syntax.lbdef = impl})::[]), r, [], quals))
in (let _80_97 = (extract_sig g se)
in (match (_80_97) with
| (g, mlm) -> begin
(let is_record = (FStar_Util.for_some (fun _80_2 -> (match (_80_2) with
| FStar_Absyn_Syntax.RecordType (_80_100) -> begin
true
end
| _80_103 -> begin
false
end)) quals)
in (match ((FStar_Util.find_map quals (fun _80_3 -> (match (_80_3) with
| FStar_Absyn_Syntax.Discriminator (l) -> begin
Some (l)
end
| _80_109 -> begin
None
end)))) with
| Some (l) when (not (is_record)) -> begin
(let _182_44 = (let _182_43 = (FStar_Extraction_ML_ExtractTyp.mlloc_of_range r)
in (let _182_42 = (let _182_41 = (FStar_Extraction_ML_ExtractExp.ind_discriminator_body g lid l)
in (_182_41)::[])
in (_182_43)::_182_42))
in (g, _182_44))
end
| _80_113 -> begin
(match ((FStar_Util.find_map quals (fun _80_4 -> (match (_80_4) with
| FStar_Absyn_Syntax.Projector (l, _80_117) -> begin
Some (l)
end
| _80_121 -> begin
None
end)))) with
| Some (_80_123) -> begin
(g, [])
end
| _80_126 -> begin
(g, mlm)
end)
end))
end))))
end else begin
(g, [])
end
end
| FStar_Absyn_Syntax.Sig_main (e, r) -> begin
(let _80_136 = (FStar_Extraction_ML_ExtractExp.synth_exp g e)
in (match (_80_136) with
| (ml_main, _80_133, _80_135) -> begin
(let _182_47 = (let _182_46 = (FStar_Extraction_ML_ExtractTyp.mlloc_of_range r)
in (_182_46)::(FStar_Extraction_ML_Syntax.MLM_Top (ml_main))::[])
in (g, _182_47))
end))
end
| (FStar_Absyn_Syntax.Sig_kind_abbrev (_)) | (FStar_Absyn_Syntax.Sig_assume (_)) | (FStar_Absyn_Syntax.Sig_new_effect (_)) | (FStar_Absyn_Syntax.Sig_sub_effect (_)) | (FStar_Absyn_Syntax.Sig_effect_abbrev (_)) | (FStar_Absyn_Syntax.Sig_pragma (_)) -> begin
(g, [])
end)))

# 102 "extractmod.fs"

let extract_iface : FStar_Extraction_ML_Env.env  ->  FStar_Absyn_Syntax.modul  ->  FStar_Extraction_ML_Env.env = (fun g m -> (let _182_52 = (FStar_Util.fold_map extract_sig g m.FStar_Absyn_Syntax.declarations)
in (FStar_All.pipe_right _182_52 Prims.fst)))

# 104 "extractmod.fs"

let rec extract : FStar_Extraction_ML_Env.env  ->  FStar_Absyn_Syntax.modul  ->  (FStar_Extraction_ML_Env.env * FStar_Extraction_ML_Syntax.mllib Prims.list) = (fun g m -> (let _80_159 = (FStar_Absyn_Util.reset_gensym ())
in (let name = (FStar_Extraction_ML_Syntax.mlpath_of_lident m.FStar_Absyn_Syntax.name)
in (let g = (let _80_162 = g
in {FStar_Extraction_ML_Env.tcenv = _80_162.FStar_Extraction_ML_Env.tcenv; FStar_Extraction_ML_Env.gamma = _80_162.FStar_Extraction_ML_Env.gamma; FStar_Extraction_ML_Env.tydefs = _80_162.FStar_Extraction_ML_Env.tydefs; FStar_Extraction_ML_Env.currentModule = name})
in if (((m.FStar_Absyn_Syntax.name.FStar_Ident.str = "Prims") || m.FStar_Absyn_Syntax.is_interface) || (let _182_57 = (FStar_ST.read FStar_Options.admit_fsi)
in (FStar_List.contains m.FStar_Absyn_Syntax.name.FStar_Ident.str _182_57))) then begin
(let g = (extract_iface g m)
in (g, []))
end else begin
(let _80_168 = (FStar_Util.fold_map extract_sig g m.FStar_Absyn_Syntax.declarations)
in (match (_80_168) with
| (g, sigs) -> begin
(let mlm = (FStar_List.flatten sigs)
in (let _182_62 = (let _182_61 = (let _182_60 = (let _182_59 = (let _182_58 = (FStar_Extraction_ML_Util.flatten_mlpath name)
in (_182_58, Some (([], mlm)), FStar_Extraction_ML_Syntax.MLLib ([])))
in (_182_59)::[])
in FStar_Extraction_ML_Syntax.MLLib (_182_60))
in (_182_61)::[])
in (g, _182_62)))
end))
end))))




