
exception NYI of (Prims.string)

let is_NYI = (fun _discr_ -> (match (_discr_) with
| NYI (_) -> begin
true
end
| _ -> begin
false
end))

let ___NYI____0 = (fun projectee -> (match (projectee) with
| NYI (_64_2) -> begin
_64_2
end))

let prims_ffi_names = ("op_Addition")::("op_Subtraction")::("op_Multiply")::("op_Division")::("op_Equality")::("op_disEquality")::("op_AmpAmp")::("op_BarBar")::("op_LessThanOrEqual")::("op_GreaterThanOrEqual")::("op_LessThan")::("op_GreaterThan")::("op_Modulus")::[]

let wys_ffi_names = ("mem")::("singleton")::("subset")::("union")::("size")::("choose")::("remove")::("read")::("main")::("wprint")::[]

let extract_const = (fun c -> (match (c) with
| FStar_Absyn_Syntax.Const_unit -> begin
"()"
end
| FStar_Absyn_Syntax.Const_bool (b) -> begin
(match (b) with
| true -> begin
"true"
end
| false -> begin
"false"
end)
end
| FStar_Absyn_Syntax.Const_int32 (n) -> begin
(FStar_Util.string_of_int32 n)
end
| FStar_Absyn_Syntax.Const_int (x) -> begin
x
end
| _64_12 -> begin
(Prims.raise (NYI ("Constant not expected")))
end))

let extract_binder = (fun b -> (match (b) with
| (FStar_Util.Inl (_64_15), _64_18) -> begin
""
end
| (FStar_Util.Inr (bvar), _64_23) -> begin
bvar.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.ppname.FStar_Absyn_Syntax.idText
end))

let rec extract_exp = (fun e -> (match ((let _130_21 = (FStar_Absyn_Util.compress_exp e)
in _130_21.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Exp_bvar (bvar) -> begin
bvar.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.ppname.FStar_Absyn_Syntax.idText
end
| FStar_Absyn_Syntax.Exp_fvar (fvar, _64_30) -> begin
fvar.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.ident.FStar_Absyn_Syntax.idText
end
| FStar_Absyn_Syntax.Exp_constant (c) -> begin
(extract_const c)
end
| FStar_Absyn_Syntax.Exp_abs (bs, e) -> begin
(let bs_str = (FStar_List.fold_left (fun s b -> (Prims.strcat (Prims.strcat (Prims.strcat s "fun ") (extract_binder b)) ". ")) "" bs)
in (let _130_24 = (extract_exp e)
in (Prims.strcat bs_str _130_24)))
end
| FStar_Absyn_Syntax.Exp_app (e, args) -> begin
(let args = (FStar_List.filter (fun a -> (match (a) with
| (FStar_Util.Inl (_64_48), _64_51) -> begin
false
end
| (FStar_Util.Inr (_64_54), _64_57) -> begin
true
end)) args)
in (let _64_62 = (extract_prims_ffi e args)
in (match (_64_62) with
| (b, s) -> begin
(match (b) with
| true -> begin
s
end
| false -> begin
(let _64_65 = (extract_wys_ffi e args)
in (match (_64_65) with
| (b, s) -> begin
(match (b) with
| true -> begin
s
end
| false -> begin
(let s = (extract_exp e)
in (let _64_69 = (extract_wysteria_specific_ast s args)
in (match (_64_69) with
| (b, s') -> begin
(match (b) with
| true -> begin
s'
end
| false -> begin
(match ((s = "_assert")) with
| true -> begin
"()"
end
| false -> begin
(FStar_List.fold_left (fun s a -> (let _130_29 = (let _130_28 = (extract_arg a)
in (Prims.strcat (Prims.strcat (Prims.strcat "(apply " s) " ") _130_28))
in (Prims.strcat _130_29 ")"))) s args)
end)
end)
end)))
end)
end))
end)
end)))
end
| FStar_Absyn_Syntax.Exp_match (e, pats) -> begin
(let s = (extract_exp e)
in (let _130_31 = (let _130_30 = (extract_pats pats)
in (Prims.strcat (Prims.strcat (Prims.strcat "match " s) " with\n") _130_30))
in (Prims.strcat _130_31 "\nend")))
end
| FStar_Absyn_Syntax.Exp_ascribed (e, _64_79, _64_81) -> begin
(extract_exp e)
end
| FStar_Absyn_Syntax.Exp_let (lbs, e) -> begin
(match ((Prims.fst lbs)) with
| true -> begin
(Prims.raise (NYI ("Recursive let not expected (only top level)")))
end
| false -> begin
(let lb = (FStar_List.hd (Prims.snd lbs))
in (let _130_38 = (let _130_36 = (let _130_35 = (let _130_33 = (let _130_32 = (FStar_Absyn_Print.lbname_to_string lb.FStar_Absyn_Syntax.lbname)
in (Prims.strcat "let " _130_32))
in (Prims.strcat _130_33 " = "))
in (let _130_34 = (extract_exp lb.FStar_Absyn_Syntax.lbdef)
in (Prims.strcat _130_35 _130_34)))
in (Prims.strcat _130_36 " in\n"))
in (let _130_37 = (extract_exp e)
in (Prims.strcat _130_38 _130_37))))
end)
end
| (FStar_Absyn_Syntax.Exp_uvar (_)) | (_) -> begin
(let _64_94 = (let _130_40 = (let _130_39 = (FStar_Absyn_Print.tag_of_exp e)
in (Prims.strcat "Expression not expected " _130_39))
in (FStar_Util.print_string _130_40))
in (Prims.raise (NYI (""))))
end))
and extract_prims_ffi = (fun e args_l -> (match ((let _130_43 = (FStar_Absyn_Util.compress_exp e)
in _130_43.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Exp_fvar (fvar, _64_100) -> begin
(let fn_name = fvar.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.ident.FStar_Absyn_Syntax.idText
in (let mlid = (FStar_Absyn_Syntax.lid_of_ids fvar.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.ns)
in (match (((((FStar_List.length mlid.FStar_Absyn_Syntax.ns) = 0) && (mlid.FStar_Absyn_Syntax.ident.FStar_Absyn_Syntax.idText = "Prims")) && (FStar_Util.for_some (fun s -> (s = fn_name)) prims_ffi_names))) with
| true -> begin
(let args_s = (FStar_List.fold_left (fun s a -> (let _130_48 = (let _130_47 = (extract_arg a)
in (Prims.strcat s _130_47))
in (Prims.strcat _130_48 "; "))) "" args_l)
in (true, (Prims.strcat (Prims.strcat (Prims.strcat (Prims.strcat "ffi " fn_name) " [ ") args_s) " ]")))
end
| false -> begin
(false, "")
end)))
end
| _64_110 -> begin
(false, "")
end))
and extract_wys_ffi = (fun e args_l -> (match ((let _130_51 = (FStar_Absyn_Util.compress_exp e)
in _130_51.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Exp_fvar (fvar, _64_115) -> begin
(let fn_name = fvar.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.ident.FStar_Absyn_Syntax.idText
in (match ((FStar_Util.for_some (fun s -> (s = fn_name)) wys_ffi_names)) with
| true -> begin
(match ((fn_name = "main")) with
| true -> begin
(let f = (let _130_53 = (FStar_List.tl args_l)
in (FStar_List.hd _130_53))
in (let _64_134 = (match (f) with
| (FStar_Util.Inl (_64_122), _64_125) -> begin
(false, "")
end
| (FStar_Util.Inr (f), _64_130) -> begin
(let _130_59 = (let _130_58 = (let _130_57 = (let _130_56 = (let _130_55 = (let _130_54 = (FStar_Absyn_Syntax.mk_Exp_constant FStar_Absyn_Syntax.Const_unit None FStar_Absyn_Syntax.dummyRange)
in (FStar_Absyn_Syntax.varg _130_54))
in (_130_55)::[])
in (f, _130_56))
in (FStar_Absyn_Syntax.mk_Exp_app _130_57 None FStar_Absyn_Syntax.dummyRange))
in (extract_exp _130_58))
in (true, _130_59))
end)
in (match (_64_134) with
| (b, s) -> begin
(b, s)
end)))
end
| false -> begin
(let args_s = (FStar_List.fold_left (fun s a -> (let _130_63 = (let _130_62 = (extract_arg a)
in (Prims.strcat s _130_62))
in (Prims.strcat _130_63 "; "))) "" args_l)
in (true, (Prims.strcat (Prims.strcat (Prims.strcat (Prims.strcat "ffi " fn_name) " [ ") args_s) " ]")))
end)
end
| false -> begin
(false, "")
end))
end
| _64_139 -> begin
(false, "")
end))
and extract_wysteria_specific_ast = (fun s args -> (let _64_155 = (match (s) with
| ("unbox_p") | ("unbox_s") | ("mkwire_p") | ("projwire_p") | ("projwire_s") -> begin
(let _130_66 = (FStar_List.tl args)
in (true, _130_66))
end
| "concat_wire" -> begin
(let _130_68 = (let _130_67 = (FStar_List.tl args)
in (FStar_List.tl _130_67))
in (true, _130_68))
end
| ("as_par") | ("as_sec") | ("mkwire_s") -> begin
(true, args)
end
| _64_152 -> begin
(false, args)
end)
in (match (_64_155) with
| (b, args) -> begin
(match (b) with
| true -> begin
(let _130_72 = (FStar_List.fold_left (fun s a -> (let _130_71 = (extract_arg a)
in (Prims.strcat (Prims.strcat s " ") _130_71))) s args)
in (b, _130_72))
end
| false -> begin
(b, "")
end)
end)))
and extract_arg = (fun a -> (match (a) with
| (FStar_Util.Inl (_64_160), _64_163) -> begin
(Prims.raise (NYI ("Type arguments should already have been filtered")))
end
| (FStar_Util.Inr (e), _64_168) -> begin
(let _130_75 = (let _130_74 = (extract_exp e)
in (Prims.strcat "( " _130_74))
in (Prims.strcat _130_75 " )"))
end))
and extract_pats = (fun pats -> (FStar_List.fold_left (fun s _64_175 -> (match (_64_175) with
| (p, w, e) -> begin
(let s' = (let _130_82 = (let _130_80 = (let _130_79 = (extract_pat p)
in (Prims.strcat "| " _130_79))
in (Prims.strcat _130_80 " -> "))
in (let _130_81 = (extract_exp e)
in (Prims.strcat _130_82 _130_81)))
in (Prims.strcat (Prims.strcat s "\n") s'))
end)) "" pats))
and extract_pat = (fun p -> (match (p.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_constant (c) -> begin
(extract_const c)
end
| _64_181 -> begin
(Prims.raise (NYI ("Pattern not expected")))
end))

let filter_ascriptions = (fun e -> (match ((let _130_86 = (FStar_Absyn_Util.compress_exp e)
in _130_86.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Exp_ascribed (e, _64_185, _64_187) -> begin
e
end
| _64_191 -> begin
e
end))

let extract_sigelt = (fun s -> (match (s) with
| FStar_Absyn_Syntax.Sig_let (lbs, _64_195, _64_197, _64_199) -> begin
(match ((Prims.fst lbs)) with
| true -> begin
(match (((FStar_List.length (Prims.snd lbs)) <> 1)) with
| true -> begin
(Prims.raise (NYI ("Mutually recursive lets not expected")))
end
| false -> begin
(let lb = (FStar_List.hd (Prims.snd lbs))
in (let lbname = (FStar_Absyn_Print.lbname_to_string lb.FStar_Absyn_Syntax.lbname)
in (let lb_body = (filter_ascriptions lb.FStar_Absyn_Syntax.lbdef)
in (match ((let _130_89 = (FStar_Absyn_Util.compress_exp lb_body)
in _130_89.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Exp_abs (bs, e) -> begin
(let bs = (FStar_List.filter (fun a -> (match (a) with
| (FStar_Util.Inl (_64_211), _64_214) -> begin
false
end
| (FStar_Util.Inr (_64_217), _64_220) -> begin
true
end)) bs)
in (let bname = (fun b -> (match (b) with
| (FStar_Util.Inl (_64_226), _64_229) -> begin
""
end
| (FStar_Util.Inr (bvar), _64_234) -> begin
bvar.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.ppname.FStar_Absyn_Syntax.idText
end))
in (let first_b = (FStar_List.hd bs)
in (let s = (Prims.strcat (Prims.strcat (Prims.strcat (Prims.strcat (Prims.strcat (Prims.strcat "let " lbname) " = fix ") lbname) ". ") (bname first_b)) ". ")
in (let bs_str = (let _130_95 = (FStar_List.tl bs)
in (FStar_List.fold_left (fun s b -> (Prims.strcat (Prims.strcat (Prims.strcat s "fun ") (extract_binder b)) ". ")) "" _130_95))
in (let _130_97 = (let _130_96 = (extract_exp e)
in (Prims.strcat (Prims.strcat s bs_str) _130_96))
in (Prims.strcat _130_97 " in")))))))
end
| _64_242 -> begin
(Prims.raise (NYI ("Expected an abs with recursive let")))
end))))
end)
end
| false -> begin
(let lb = (FStar_List.hd (Prims.snd lbs))
in (let _130_102 = (let _130_101 = (let _130_99 = (let _130_98 = (FStar_Absyn_Print.lbname_to_string lb.FStar_Absyn_Syntax.lbname)
in (Prims.strcat "let " _130_98))
in (Prims.strcat _130_99 " = "))
in (let _130_100 = (extract_exp lb.FStar_Absyn_Syntax.lbdef)
in (Prims.strcat _130_101 _130_100)))
in (Prims.strcat _130_102 " in")))
end)
end
| FStar_Absyn_Syntax.Sig_main (e, _64_246) -> begin
(extract_exp e)
end
| _64_250 -> begin
""
end))

let extract = (fun fh m -> (let name = m.FStar_Absyn_Syntax.name.FStar_Absyn_Syntax.str
in (let _64_254 = (FStar_Util.print_string (Prims.strcat (Prims.strcat "Extracting module: " name) "\n"))
in (match (((name = "WLib") || (name = "SMC"))) with
| true -> begin
(let s = (FStar_List.fold_left (fun s sigelt -> (let _130_109 = (extract_sigelt sigelt)
in (Prims.strcat (Prims.strcat s "\n") _130_109))) "" m.FStar_Absyn_Syntax.declarations)
in (let _64_259 = (FStar_Util.append_to_file fh s)
in (FStar_Util.append_to_file fh "\n")))
end
| false -> begin
()
end))))




