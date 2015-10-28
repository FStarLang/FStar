
open Prims
type comp =
| Do
| Skip
| NA

let is_Do = (fun _discr_ -> (match (_discr_) with
| Do -> begin
true
end
| _ -> begin
false
end))

let is_Skip = (fun _discr_ -> (match (_discr_) with
| Skip -> begin
true
end
| _ -> begin
false
end))

let is_NA = (fun _discr_ -> (match (_discr_) with
| NA -> begin
true
end
| _ -> begin
false
end))

let is_empty = (fun s -> ((FStar_OrdSet.size ((fun s -> Prins.p_cmp) s) s) = 0))

let e_of_t_exp = (fun _20_5 -> (match (_20_5) with
| AST.T_exp (e) -> begin
e
end))

let concat_traces = (fun t1 t2 -> ())

let rec vals_traces_h_append_lemma = (fun tr1 tr2 -> ())

let vals_traces_h_append_lemma_forall = (Obj.magic (fun _ -> (FStar_All.failwith "Not yet implemented:vals_traces_h_append_lemma_forall")))

let vals_traces_concat_lemma = (fun tr1 tr2 -> ())

let pre_easpar = (fun c -> (((AST.is_T_exp (AST.t_of_conf c)) && (AST.is_E_aspar (e_of_t_exp (AST.t_of_conf c)))) && (AST.is_par c)))

let step_aspar_e1 = (fun _20_43 -> (match (_20_43) with
| AST.Conf (l, m, s, en, AST.T_exp (AST.E_aspar (e1, e2)), tr) -> begin
AST.Conf (l, m, (AST.Frame (m, en, AST.F_aspar_ps (e2), ()))::s, en, AST.T_exp (e1), ())
end))

let step_aspar_e2 = (fun _20_63 -> (match (_20_63) with
| AST.Conf (l, _20_61, AST.Frame (m, en, AST.F_aspar_ps (e), tr)::s, _20_51, AST.T_val (_20_5455, AST.V_eprins (ps)), tr') -> begin
AST.Conf (l, m, (AST.Frame (m, en, AST.F_aspar_e (ps), ()))::s, en, AST.T_exp (e), ())
end))

let step_aspar_red = (fun _20_82 -> (match (_20_82) with
| AST.Conf (l, _20_80, AST.Frame (m, en, AST.F_aspar_e (ps), tr)::s, _20_70, AST.T_val (_20_7583, v), tr') -> begin
AST.Conf (l, m, s, en, AST.T_red (AST.R_aspar (((fun _20_82 l _20_80 m en ps tr s _20_70 _20_7583 v tr' -> _20_7583) _20_82 l _20_80 m en ps () s _20_70 _20_7583 v ()), ps, v)), ())
end))

let pre_aspar = (fun c -> (match (c) with
| AST.Conf (l, AST.Mode (AST.Par, ps1), _20_93, _20_91, AST.T_red (AST.R_aspar (_20_8627, ps2, v)), _20_85) -> begin
if (AST.is_clos ((fun c l ps1 _20_93 _20_91 _20_8627 ps2 v _20_85 -> _20_8627) c l ps1 _20_93 _20_91 _20_8627 ps2 v ()) v) then begin
if (AST.src l) then begin
if (FStar_OrdSet.subset ((fun c l ps1 _20_93 _20_91 _20_8627 ps2 v _20_85 -> Prins.p_cmp) c l ps1 _20_93 _20_91 _20_8627 ps2 v ()) ps2 ps1) then begin
Do
end else begin
NA
end
end else begin
if (FStar_OrdSet.subset ((fun c l ps1 _20_93 _20_91 _20_8627 ps2 v _20_85 -> Prins.p_cmp) c l ps1 _20_93 _20_91 _20_8627 ps2 v ()) ps1 ps2) then begin
Do
end else begin
Skip
end
end
end else begin
NA
end
end
| _20_100 -> begin
NA
end))

let step_aspar = (fun c -> (match (c) with
| AST.Conf (l, m, s, en', AST.T_red (AST.R_aspar (_20_10180, ps, v)), tr) -> begin
(let _20_117 = (AST.get_en_b ((fun c l m s en' _20_10180 ps v tr -> _20_10180) c l m s en' _20_10180 ps v ()) v)
in (match (_20_117) with
| (en, x, e) -> begin
(let m' = if (AST.src l) then begin
AST.Mode (AST.Par, ps)
end else begin
m
end
in (let s' = (AST.Frame (m, en', AST.F_aspar_ret (ps), ()))::s
in (let _20_122 = if (AST.src l) then begin
((AST.update_env ((fun c l m s en' _20_10180 ps v tr _20_117 en x e m' s' -> AST.Meta ((FStar_OrdSet.empty Prins.p_cmp), AST.Can_b, (FStar_OrdSet.empty Prins.p_cmp), AST.Can_w)) c l m s en' _20_10180 ps v () _20_117 en x e m' s') en x AST.V_unit), AST.T_exp (e))
end else begin
if ((pre_aspar c) = Do) then begin
((AST.update_env ((fun c l m s en' _20_10180 ps v tr _20_117 en x e m' s' -> AST.Meta ((FStar_OrdSet.empty Prins.p_cmp), AST.Can_b, (FStar_OrdSet.empty Prins.p_cmp), AST.Can_w)) c l m s en' _20_10180 ps v () _20_117 en x e m' s') en x AST.V_unit), AST.T_exp (e))
end else begin
(AST.empty_env, AST.T_val (((fun c l m s en' _20_10180 ps v tr _20_117 en x e m' s' -> AST.Meta ((FStar_OrdSet.empty Prins.p_cmp), AST.Can_b, (FStar_OrdSet.empty Prins.p_cmp), AST.Can_w)) c l m s en' _20_10180 ps v () _20_117 en x e m' s'), AST.V_emp))
end
end
in (match (_20_122) with
| (en', t') -> begin
AST.Conf (l, m', s', en', t', ())
end))))
end))
end))

let pre_aspar_ret = (fun c -> (match (c) with
| AST.Conf (_20_147, _20_145, AST.Frame (_20_141, _20_139, AST.F_aspar_ret (ps), _20_135)::_20_133, _20_131, AST.T_val (meta, _20_127), _20_125) -> begin
if (AST.is_meta_boxable ps meta) then begin
Do
end else begin
NA
end
end
| _20_150 -> begin
NA
end))

let scope_trace = (fun ps t -> (AST.Tr_scope (ps, t))::[])

let step_aspar_ret = (fun c -> (match (c) with
| AST.Conf (l, _20_170, AST.Frame (m, en, AST.F_aspar_ret (ps), tr)::s, _20_160, AST.T_val (_20_25112, v), tr') -> begin
(let tr = ()
in AST.Conf (l, m, s, en, AST.T_val (((fun c l _20_170 m en ps tr s _20_160 _20_25112 v tr' tr -> AST.Meta (ps, AST.Can_b, (AST.___Meta___wps ((fun c l _20_170 m en ps tr s _20_160 _20_25112 v tr' tr -> _20_25112) c l _20_170 m en ps () s _20_160 _20_25112 v () ())), AST.Cannot_w)) c l _20_170 m en ps () s _20_160 _20_25112 v () ()), AST.V_box (((fun c l _20_170 m en ps tr s _20_160 _20_25112 v tr' tr -> _20_25112) c l _20_170 m en ps () s _20_160 _20_25112 v () ()), ps, v)), ()))
end))

let pre_ebox = (fun c -> ((AST.is_T_exp (AST.t_of_conf c)) && (AST.is_E_box (e_of_t_exp (AST.t_of_conf c)))))

let step_box_e1 = (fun _20_186 -> (match (_20_186) with
| AST.Conf (l, m, s, en, AST.T_exp (AST.E_box (e1, e2)), tr) -> begin
AST.Conf (l, m, (AST.Frame (m, en, AST.F_box_ps (e2), ()))::s, en, AST.T_exp (e1), ())
end))

let step_box_e2 = (fun _20_206 -> (match (_20_206) with
| AST.Conf (l, _20_204, AST.Frame (m, en, AST.F_box_ps (e), tr)::s, _20_194, AST.T_val (_20_29421, AST.V_eprins (ps)), tr') -> begin
AST.Conf (l, m, (AST.Frame (m, en, AST.F_box_e (ps), ()))::s, en, AST.T_exp (e), ())
end))

let step_box_red = (fun _20_225 -> (match (_20_225) with
| AST.Conf (l, _20_223, AST.Frame (m, en, AST.F_box_e (ps), tr)::s, _20_213, AST.T_val (_20_31549, v), tr') -> begin
AST.Conf (l, m, s, en, AST.T_red (AST.R_box (((fun _20_225 l _20_223 m en ps tr s _20_213 _20_31549 v tr' -> _20_31549) _20_225 l _20_223 m en ps () s _20_213 _20_31549 v ()), ps, v)), ())
end))

let pre_box = (fun c -> (match (c) with
| AST.Conf (l, AST.Mode (_20_241, ps), _20_238, _20_236, AST.T_red (AST.R_box (meta, ps', v)), _20_229) -> begin
if (AST.is_meta_boxable ps' meta) then begin
if (AST.src l) then begin
if (FStar_OrdSet.subset ((fun c l _20_241 ps _20_238 _20_236 meta ps' v _20_229 -> Prins.p_cmp) c l _20_241 ps _20_238 _20_236 meta ps' v ()) ps' ps) then begin
Do
end else begin
NA
end
end else begin
Do
end
end else begin
NA
end
end
| _20_246 -> begin
NA
end))

let step_box = (fun _20_258 -> (match (_20_258) with
| AST.Conf (l, m, s, en, AST.T_red (AST.R_box (_20_33851, ps', v)), tr) -> begin
(let _20_261 = m
in (match (_20_261) with
| AST.Mode (as_m, ps) -> begin
if ((AST.src l) || (as_m = AST.Sec)) then begin
AST.Conf (l, m, s, en, AST.T_val (((fun _20_258 l m s en _20_33851 ps' v tr _20_261 as_m ps -> AST.Meta (ps', AST.Can_b, (AST.___Meta___wps ((fun _20_258 l m s en _20_33851 ps' v tr _20_261 as_m ps -> _20_33851) _20_258 l m s en _20_33851 ps' v () _20_261 as_m ps)), AST.Cannot_w)) _20_258 l m s en _20_33851 ps' v () _20_261 as_m ps), AST.V_box (((fun _20_258 l m s en _20_33851 ps' v tr _20_261 as_m ps -> _20_33851) _20_258 l m s en _20_33851 ps' v () _20_261 as_m ps), ps', v)), ())
end else begin
if (FStar_OrdSet.subset ((fun _20_258 l m s en _20_33851 ps' v tr _20_261 as_m ps -> Prins.p_cmp) _20_258 l m s en _20_33851 ps' v () _20_261 as_m ps) ps ps') then begin
AST.Conf (l, m, s, en, AST.T_val (((fun _20_258 l m s en _20_33851 ps' v tr _20_261 as_m ps -> AST.Meta (ps', AST.Can_b, (AST.___Meta___wps ((fun _20_258 l m s en _20_33851 ps' v tr _20_261 as_m ps -> _20_33851) _20_258 l m s en _20_33851 ps' v () _20_261 as_m ps)), AST.Cannot_w)) _20_258 l m s en _20_33851 ps' v () _20_261 as_m ps), AST.V_box (((fun _20_258 l m s en _20_33851 ps' v tr _20_261 as_m ps -> _20_33851) _20_258 l m s en _20_33851 ps' v () _20_261 as_m ps), ps', v)), ())
end else begin
AST.Conf (l, m, s, en, AST.T_val (((fun _20_258 l m s en _20_33851 ps' v tr _20_261 as_m ps -> AST.Meta (ps', AST.Can_b, (AST.___Meta___wps ((fun _20_258 l m s en _20_33851 ps' v tr _20_261 as_m ps -> AST.Meta ((FStar_OrdSet.empty Prins.p_cmp), AST.Can_b, (FStar_OrdSet.empty Prins.p_cmp), AST.Can_w)) _20_258 l m s en _20_33851 ps' v () _20_261 as_m ps)), AST.Cannot_w)) _20_258 l m s en _20_33851 ps' v () _20_261 as_m ps), AST.V_box (((fun _20_258 l m s en _20_33851 ps' v tr _20_261 as_m ps -> AST.Meta ((FStar_OrdSet.empty Prins.p_cmp), AST.Can_b, (FStar_OrdSet.empty Prins.p_cmp), AST.Can_w)) _20_258 l m s en _20_33851 ps' v () _20_261 as_m ps), ps', AST.V_emp)), ())
end
end
end))
end))

let pre_eapp = (fun c -> ((AST.is_T_exp (AST.t_of_conf c)) && (AST.is_E_app (e_of_t_exp (AST.t_of_conf c)))))

let step_app_e1 = (fun _20_274 -> (match (_20_274) with
| AST.Conf (l, m, s, en, AST.T_exp (AST.E_app (e1, e2)), tr) -> begin
AST.Conf (l, m, (AST.Frame (m, en, AST.F_app_e1 (e2), ()))::s, en, AST.T_exp (e1), ())
end))

let step_app_e2 = (fun _20_293 -> (match (_20_293) with
| AST.Conf (l, _20_291, AST.Frame (m, en, AST.F_app_e1 (e2), tr)::s, _20_281, AST.T_val (_20_37919, v), tr') -> begin
AST.Conf (l, m, (AST.Frame (m, en, AST.F_app_e2 (((fun _20_293 l _20_291 m en e2 tr s _20_281 _20_37919 v tr' -> _20_37919) _20_293 l _20_291 m en e2 () s _20_281 _20_37919 v ()), v), ()))::s, en, AST.T_exp (e2), ())
end))

let step_app_red = (fun _20_312 -> (match (_20_312) with
| AST.Conf (l, _20_310, AST.Frame (m, en, AST.F_app_e2 (_20_39813, v1), tr)::s, _20_300, AST.T_val (_20_39815, v2), tr') -> begin
AST.Conf (l, m, s, en, AST.T_red (AST.R_app (((fun _20_312 l _20_310 m en _20_39813 v1 tr s _20_300 _20_39815 v2 tr' -> _20_39813) _20_312 l _20_310 m en _20_39813 v1 () s _20_300 _20_39815 v2 ()), ((fun _20_312 l _20_310 m en _20_39813 v1 tr s _20_300 _20_39815 v2 tr' -> _20_39815) _20_312 l _20_310 m en _20_39813 v1 () s _20_300 _20_39815 v2 ()), v1, v2)), ())
end))

let pre_app = (fun c -> (match (c) with
| AST.Conf (_20_329, _20_327, _20_325, _20_323, AST.T_red (AST.R_app (_20_40768, _20_40769, v, _20_318)), _20_316) -> begin
(AST.is_clos ((fun c _20_329 _20_327 _20_325 _20_323 _20_40768 _20_40769 v _20_318 _20_316 -> _20_40768) c _20_329 _20_327 _20_325 _20_323 _20_40768 _20_40769 v _20_318 ()) v)
end
| _20_332 -> begin
false
end))

let step_app = (fun c -> (match (c) with
| AST.Conf (l, m, s, _20_342, AST.T_red (AST.R_app (_20_41176, _20_41177, f, v)), tr) -> begin
(let _20_350 = (AST.get_en_b ((fun c l m s _20_342 _20_41176 _20_41177 f v tr -> _20_41176) c l m s _20_342 _20_41176 _20_41177 f v ()) f)
in (match (_20_350) with
| (en, x, e) -> begin
AST.Conf (l, m, s, (AST.update_env ((fun c l m s _20_342 _20_41176 _20_41177 f v tr _20_350 en x e -> _20_41177) c l m s _20_342 _20_41176 _20_41177 f v () _20_350 en x e) en x v), AST.T_exp (e), ())
end))
end))

let pre_eabs = (fun c -> ((AST.is_T_exp (AST.t_of_conf c)) && (AST.is_E_abs (e_of_t_exp (AST.t_of_conf c)))))

let step_abs = (fun _20_363 -> (match (_20_363) with
| AST.Conf (l, m, s, en, AST.T_exp (AST.E_abs (x, e)), tr) -> begin
AST.Conf (l, m, s, en, AST.T_val (((fun _20_363 l m s en x e tr -> AST.Meta ((FStar_OrdSet.empty Prins.p_cmp), AST.Cannot_b, (FStar_OrdSet.empty Prins.p_cmp), AST.Cannot_w)) _20_363 l m s en x e ()), AST.V_clos (en, x, e)), ())
end))

let pre_efix = (fun c -> ((AST.is_T_exp (AST.t_of_conf c)) && (AST.is_E_fix (e_of_t_exp (AST.t_of_conf c)))))

let step_fix = (fun _20_377 -> (match (_20_377) with
| AST.Conf (l, m, s, en, AST.T_exp (AST.E_fix (f, x, e)), tr) -> begin
AST.Conf (l, m, s, en, AST.T_val (((fun _20_377 l m s en f x e tr -> AST.Meta ((FStar_OrdSet.empty Prins.p_cmp), AST.Cannot_b, (FStar_OrdSet.empty Prins.p_cmp), AST.Cannot_w)) _20_377 l m s en f x e ()), AST.V_fix_clos (en, f, x, e)), ())
end))

let pre_eempabs = (fun c -> ((AST.is_T_exp (AST.t_of_conf c)) && (AST.is_E_empabs (e_of_t_exp (AST.t_of_conf c)))))

let step_empabs = (fun _20_390 -> (match (_20_390) with
| AST.Conf (l, m, s, en, AST.T_exp (AST.E_empabs (x, e)), tr) -> begin
AST.Conf (l, m, s, en, AST.T_val (((fun _20_390 l m s en x e tr -> AST.Meta ((FStar_OrdSet.empty Prins.p_cmp), AST.Can_b, (FStar_OrdSet.empty Prins.p_cmp), AST.Can_w)) _20_390 l m s en x e ()), AST.V_emp_clos (x, e)), ())
end))

let pre_elet = (fun c -> ((AST.is_T_exp (AST.t_of_conf c)) && (AST.is_E_let (e_of_t_exp (AST.t_of_conf c)))))

let step_let_e1 = (fun _20_404 -> (match (_20_404) with
| AST.Conf (l, m, s, en, AST.T_exp (AST.E_let (x, e1, e2)), tr) -> begin
AST.Conf (l, m, (AST.Frame (m, en, AST.F_let (x, e2), ()))::s, en, AST.T_exp (e1), ())
end))

let step_let_red = (fun _20_424 -> (match (_20_424) with
| AST.Conf (l, _20_422, AST.Frame (m, en, AST.F_let (x, e2), tr)::s, _20_411, AST.T_val (_20_46121, v), tr') -> begin
AST.Conf (l, m, s, en, AST.T_red (AST.R_let (((fun _20_424 l _20_422 m en x e2 tr s _20_411 _20_46121 v tr' -> _20_46121) _20_424 l _20_422 m en x e2 () s _20_411 _20_46121 v ()), x, v, e2)), ())
end))

let pre_let = (fun c -> (match (c) with
| AST.Conf (_20_444, _20_442, _20_440, _20_438, AST.T_red (AST.R_let (_20_47075, _20_434, _20_432, _20_430)), _20_428) -> begin
true
end
| _20_447 -> begin
false
end))

let step_let = (fun c -> (match (c) with
| AST.Conf (l, m, s, en, AST.T_red (AST.R_let (_20_47470, x, v1, e2)), tr) -> begin
AST.Conf (l, m, s, (AST.update_env ((fun c l m s en _20_47470 x v1 e2 tr -> _20_47470) c l m s en _20_47470 x v1 e2 ()) en x v1), AST.T_exp (e2), ())
end))

let x_of_e_var = (fun _20_465 -> (match (_20_465) with
| AST.E_var (x) -> begin
x
end))

let is_Some = (fun x -> (match (x) with
| Some (_20_469) -> begin
true
end
| _20_472 -> begin
false
end))

let en_of_conf = (fun _20_484 -> (match (_20_484) with
| AST.Conf (_20_483, _20_481, _20_479, en, _20_476, _20_474) -> begin
en
end))

let pre_evar = (fun c -> (((AST.is_T_exp (AST.t_of_conf c)) && (AST.is_E_var (e_of_t_exp (AST.t_of_conf c)))) && (is_Some (en_of_conf c (x_of_e_var (e_of_t_exp (AST.t_of_conf c)))))))

let step_var = (fun _20_496 -> (match (_20_496) with
| AST.Conf (l, m, s, en, AST.T_exp (AST.E_var (x)), tr) -> begin
(let _20_501 = (en x)
in (match (_20_501) with
| Some (AST.D_v (_20_499, v)) -> begin
AST.Conf (l, m, s, en, AST.T_val (((fun _20_496 l m s en x tr _20_501 _20_499 v -> _20_499) _20_496 l m s en x () _20_501 _20_499 v), v), ())
end))
end))

let pre_econst = (fun c -> ((AST.is_T_exp (AST.t_of_conf c)) && (AST.is_E_const (e_of_t_exp (AST.t_of_conf c)))))

let slice_const = (fun p x -> x)

let compose_const = (fun x _20_509 -> x)

let slice_const_sps = (fun ps x -> x)

let step_const = (fun _20_525 -> (match (_20_525) with
| AST.Conf (l, m, s, en, AST.T_exp (AST.E_const (c)), tr) -> begin
(let meta = AST.Meta ((FStar_OrdSet.empty ((fun _20_525 l m s en c tr -> Prins.p_cmp) _20_525 l m s en c ())), AST.Can_b, (FStar_OrdSet.empty ((fun _20_525 l m s en c tr -> Prins.p_cmp) _20_525 l m s en c ())), AST.Can_w)
in (let v = (match (c) with
| AST.C_prin (p) -> begin
AST.V_prin (p)
end
| AST.C_eprins (eps) -> begin
AST.V_eprins (eps)
end
| AST.C_unit (_20_532) -> begin
AST.V_unit
end
| AST.C_bool (b) -> begin
AST.V_bool (b)
end
| AST.C_opaque (_, v) -> begin
AST.V_opaque ((), v, meta, slice_const, compose_const, slice_const_sps)
end)
in AST.Conf (l, m, s, en, AST.T_val (((fun _20_525 l m s en c tr meta v -> ((fun _20_525 l m s en c tr meta -> AST.Meta ((FStar_OrdSet.empty Prins.p_cmp), AST.Can_b, (FStar_OrdSet.empty Prins.p_cmp), AST.Can_w)) _20_525 l m s en c () meta)) _20_525 l m s en c () meta v), v), ())))
end))

let pre_eunbox = (fun c -> ((AST.is_T_exp (AST.t_of_conf c)) && (AST.is_E_unbox (e_of_t_exp (AST.t_of_conf c)))))

let step_unbox_e = (fun _20_551 -> (match (_20_551) with
| AST.Conf (l, m, s, en, AST.T_exp (AST.E_unbox (e)), tr) -> begin
AST.Conf (l, m, (AST.Frame (m, en, AST.F_unbox, ()))::s, en, AST.T_exp (e), ())
end))

let step_unbox_red = (fun _20_569 -> (match (_20_569) with
| AST.Conf (l, _20_567, AST.Frame (m, en, AST.F_unbox, tr)::s, _20_558, AST.T_val (_20_53858, v), tr') -> begin
AST.Conf (l, m, s, en, AST.T_red (AST.R_unbox (((fun _20_569 l _20_567 m en tr s _20_558 _20_53858 v tr' -> _20_53858) _20_569 l _20_567 m en () s _20_558 _20_53858 v ()), v)), ())
end))

let pre_unbox = (fun c -> (match (c) with
| AST.Conf (_20_587, AST.Mode (as_m, ps1), _20_582, _20_580, AST.T_red (AST.R_unbox (_20_54760, AST.V_box (_20_54759, ps2, _20_574))), _20_572) -> begin
if (as_m = AST.Par) then begin
if (FStar_OrdSet.subset ((fun c _20_587 as_m ps1 _20_582 _20_580 _20_54760 _20_54759 ps2 _20_574 _20_572 -> Prins.p_cmp) c _20_587 as_m ps1 _20_582 _20_580 _20_54760 _20_54759 ps2 _20_574 ()) ps1 ps2) then begin
Do
end else begin
NA
end
end else begin
if (not ((is_empty (FStar_OrdSet.intersect ((fun c _20_587 as_m ps1 _20_582 _20_580 _20_54760 _20_54759 ps2 _20_574 _20_572 -> Prins.p_cmp) c _20_587 as_m ps1 _20_582 _20_580 _20_54760 _20_54759 ps2 _20_574 ()) ps1 ps2)))) then begin
Do
end else begin
NA
end
end
end
| _20_590 -> begin
NA
end))

let step_unbox = (fun c -> (match (c) with
| AST.Conf (l, m, s, en, AST.T_red (AST.R_unbox (_20_56678, AST.V_box (_20_56677, _20_597, v))), tr) -> begin
AST.Conf (l, m, s, en, AST.T_val (((fun c l m s en _20_56678 _20_56677 _20_597 v tr -> _20_56677) c l m s en _20_56678 _20_56677 _20_597 v ()), v), ())
end))

let pre_emkwire = (fun c -> ((AST.is_T_exp (AST.t_of_conf c)) && (AST.is_E_mkwire (e_of_t_exp (AST.t_of_conf c)))))

let step_mkwire_e1 = (fun _20_618 -> (match (_20_618) with
| AST.Conf (l, m, s, en, AST.T_exp (AST.E_mkwire (e1, e2)), tr) -> begin
AST.Conf (l, m, (AST.Frame (m, en, AST.F_mkwire_ps (e2), ()))::s, en, AST.T_exp (e1), ())
end))

let step_mkwire_e2 = (fun _20_638 -> (match (_20_638) with
| AST.Conf (l, _20_636, AST.Frame (m, en, AST.F_mkwire_ps (e), tr)::s, _20_626, AST.T_val (_20_58963, AST.V_eprins (ps)), tr') -> begin
AST.Conf (l, m, (AST.Frame (m, en, AST.F_mkwire_e (ps), ()))::s, en, AST.T_exp (e), ())
end))

let step_mkwire_red = (fun _20_657 -> (match (_20_657) with
| AST.Conf (l, _20_655, AST.Frame (m, en, AST.F_mkwire_e (ps), tr)::s, _20_645, AST.T_val (_20_61091, v), tr') -> begin
AST.Conf (l, m, s, en, AST.T_red (AST.R_mkwire (((fun _20_657 l _20_655 m en ps tr s _20_645 _20_61091 v tr' -> _20_61091) _20_657 l _20_655 m en ps () s _20_645 _20_61091 v ()), ps, v)), ())
end))

let pre_mkwire = (fun c -> (match (c) with
| AST.Conf (l, AST.Mode (AST.Par, ps), _20_672, _20_670, AST.T_red (AST.R_mkwire (_20_62135, ps', AST.V_box (mv, ps'', _20_662))), _20_660) -> begin
if (AST.is_meta_wireable mv) then begin
if (AST.src l) then begin
if ((FStar_OrdSet.subset ((fun c l ps _20_672 _20_670 _20_62135 ps' mv ps'' _20_662 _20_660 -> Prins.p_cmp) c l ps _20_672 _20_670 _20_62135 ps' mv ps'' _20_662 ()) ps' ps) && (FStar_OrdSet.subset ((fun c l ps _20_672 _20_670 _20_62135 ps' mv ps'' _20_662 _20_660 -> Prins.p_cmp) c l ps _20_672 _20_670 _20_62135 ps' mv ps'' _20_662 ()) ps' ps'')) then begin
Do
end else begin
NA
end
end else begin
Do
end
end else begin
NA
end
end
| AST.Conf (l, AST.Mode (AST.Sec, ps), _20_689, _20_687, AST.T_red (AST.R_mkwire (mv, ps', _20_681)), _20_679) -> begin
if (AST.is_meta_wireable mv) then begin
if (FStar_OrdSet.subset ((fun c l ps _20_689 _20_687 mv ps' _20_681 _20_679 -> Prins.p_cmp) c l ps _20_689 _20_687 mv ps' _20_681 ()) ps' ps) then begin
Do
end else begin
NA
end
end else begin
NA
end
end
| _20_696 -> begin
NA
end))

let mconst_on = (fun eps v -> (FStar_OrdMap.const_on ((fun eps v -> Prins.p_cmp) eps v) eps v))

let step_mkwire = (fun c -> (match (c) with
| AST.Conf (l, AST.Mode (AST.Par, ps), s, en, AST.T_red (AST.R_mkwire (_20_64871, ps', AST.V_box (_20_64870, _20_709, v))), tr) -> begin
(let _20_723 = if (AST.src l) then begin
(ps', (mconst_on ps' v))
end else begin
if (FStar_OrdSet.subset ((fun c l ps s en _20_64871 ps' _20_64870 _20_709 v tr -> Prins.p_cmp) c l ps s en _20_64871 ps' _20_64870 _20_709 v ()) ps ps') then begin
(ps, (mconst_on ps v))
end else begin
((FStar_OrdSet.empty ((fun c l ps s en _20_64871 ps' _20_64870 _20_709 v tr -> Prins.p_cmp) c l ps s en _20_64871 ps' _20_64870 _20_709 v ())), (FStar_OrdMap.empty ((fun c l ps s en _20_64871 ps' _20_64870 _20_709 v tr -> Prins.p_cmp) c l ps s en _20_64871 ps' _20_64870 _20_709 v ())))
end
end
in (match (_20_723) with
| (eps, w) -> begin
AST.Conf (l, AST.Mode (AST.Par, ps), s, en, AST.T_val (((fun c l ps s en _20_64871 ps' _20_64870 _20_709 v tr _20_723 eps w -> AST.Meta ((FStar_OrdSet.empty Prins.p_cmp), AST.Can_b, eps, AST.Cannot_w)) c l ps s en _20_64871 ps' _20_64870 _20_709 v () _20_723 eps w), AST.V_wire (eps, w)), ())
end))
end
| AST.Conf (l, AST.Mode (AST.Sec, ps), s, en, AST.T_red (AST.R_mkwire (_20_65932, ps', v)), tr) -> begin
AST.Conf (l, AST.Mode (AST.Sec, ps), s, en, AST.T_val (((fun c l ps s en _20_65932 ps' v tr -> AST.Meta ((FStar_OrdSet.empty Prins.p_cmp), AST.Can_b, ps', AST.Cannot_w)) c l ps s en _20_65932 ps' v ()), AST.V_wire (ps', (mconst_on ps' v))), ())
end))

let pre_eprojwire = (fun c -> ((AST.is_T_exp (AST.t_of_conf c)) && (AST.is_E_projwire (e_of_t_exp (AST.t_of_conf c)))))

let step_projwire_e1 = (fun _20_748 -> (match (_20_748) with
| AST.Conf (l, m, s, en, AST.T_exp (AST.E_projwire (e1, e2)), tr) -> begin
AST.Conf (l, m, (AST.Frame (m, en, AST.F_projwire_p (e2), ()))::s, en, AST.T_exp (e1), ())
end))

let step_projwire_e2 = (fun _20_768 -> (match (_20_768) with
| AST.Conf (l, _20_766, AST.Frame (m, en, AST.F_projwire_p (e), tr)::s, _20_756, AST.T_val (_20_78208, AST.V_prin (p)), tr') -> begin
AST.Conf (l, m, (AST.Frame (m, en, AST.F_projwire_e (p), ()))::s, en, AST.T_exp (e), ())
end))

let step_projwire_red = (fun _20_787 -> (match (_20_787) with
| AST.Conf (l, _20_785, AST.Frame (m, en, AST.F_projwire_e (p), tr)::s, _20_775, AST.T_val (_20_80202, v), tr') -> begin
AST.Conf (l, m, s, en, AST.T_red (AST.R_projwire (((fun _20_787 l _20_785 m en p tr s _20_775 _20_80202 v tr' -> _20_80202) _20_787 l _20_785 m en p () s _20_775 _20_80202 v ()), p, v)), ())
end))

let pre_projwire = (fun c -> (match (c) with
| AST.Conf (_20_806, AST.Mode (as_m, ps), _20_801, _20_799, AST.T_red (AST.R_projwire (_20_81129, p, AST.V_wire (eps, _20_792))), _20_790) -> begin
if (as_m = AST.Par) then begin
if ((ps = (FStar_OrdSet.singleton ((fun c _20_806 as_m ps _20_801 _20_799 _20_81129 p eps _20_792 _20_790 -> Prins.p_cmp) c _20_806 as_m ps _20_801 _20_799 _20_81129 p eps _20_792 ()) p)) && (FStar_OrdSet.mem ((fun c _20_806 as_m ps _20_801 _20_799 _20_81129 p eps _20_792 _20_790 -> Prins.p_cmp) c _20_806 as_m ps _20_801 _20_799 _20_81129 p eps _20_792 ()) p eps)) then begin
Do
end else begin
NA
end
end else begin
if ((FStar_OrdSet.mem ((fun c _20_806 as_m ps _20_801 _20_799 _20_81129 p eps _20_792 _20_790 -> Prins.p_cmp) c _20_806 as_m ps _20_801 _20_799 _20_81129 p eps _20_792 ()) p ps) && (FStar_OrdSet.mem ((fun c _20_806 as_m ps _20_801 _20_799 _20_81129 p eps _20_792 _20_790 -> Prins.p_cmp) c _20_806 as_m ps _20_801 _20_799 _20_81129 p eps _20_792 ()) p eps)) then begin
Do
end else begin
NA
end
end
end
| _20_809 -> begin
NA
end))

let v_of_some = (fun _20_814 -> (match (_20_814) with
| Some (x) -> begin
x
end))

let step_projwire = (fun c -> (match (c) with
| AST.Conf (l, m, s, en, AST.T_red (AST.R_projwire (_20_83712, p, AST.V_wire (_20_821, w))), tr) -> begin
AST.Conf (l, m, s, en, AST.T_val (((fun c l m s en _20_83712 p _20_821 w tr -> AST.Meta ((FStar_OrdSet.empty Prins.p_cmp), AST.Can_b, (FStar_OrdSet.empty Prins.p_cmp), AST.Can_w)) c l m s en _20_83712 p _20_821 w ()), (v_of_some (FStar_OrdMap.select ((fun c l m s en _20_83712 p _20_821 w tr -> Prins.p_cmp) c l m s en _20_83712 p _20_821 w ()) p w))), ())
end))

let pre_econcatwire = (fun c -> ((AST.is_T_exp (AST.t_of_conf c)) && (AST.is_E_concatwire (e_of_t_exp (AST.t_of_conf c)))))

let step_concatwire_e1 = (fun _20_843 -> (match (_20_843) with
| AST.Conf (l, m, s, en, AST.T_exp (AST.E_concatwire (e1, e2)), tr) -> begin
AST.Conf (l, m, (AST.Frame (m, en, AST.F_concatwire_e1 (e2), ()))::s, en, AST.T_exp (e1), ())
end))

let step_concatwire_e2 = (fun _20_862 -> (match (_20_862) with
| AST.Conf (l, _20_860, AST.Frame (m, en, AST.F_concatwire_e1 (e), tr)::s, _20_850, AST.T_val (_20_87200, v), tr') -> begin
AST.Conf (l, m, (AST.Frame (m, en, AST.F_concatwire_e2 (((fun _20_862 l _20_860 m en e tr s _20_850 _20_87200 v tr' -> _20_87200) _20_862 l _20_860 m en e () s _20_850 _20_87200 v ()), v), ()))::s, en, AST.T_exp (e), ())
end))

let step_concatwire_red = (fun _20_881 -> (match (_20_881) with
| AST.Conf (l, _20_879, AST.Frame (m, en, AST.F_concatwire_e2 (_20_89094, v1), tr)::s, _20_869, AST.T_val (_20_89096, v2), tr') -> begin
AST.Conf (l, m, s, en, AST.T_red (AST.R_concatwire (((fun _20_881 l _20_879 m en _20_89094 v1 tr s _20_869 _20_89096 v2 tr' -> _20_89094) _20_881 l _20_879 m en _20_89094 v1 () s _20_869 _20_89096 v2 ()), ((fun _20_881 l _20_879 m en _20_89094 v1 tr s _20_869 _20_89096 v2 tr' -> _20_89096) _20_881 l _20_879 m en _20_89094 v1 () s _20_869 _20_89096 v2 ()), v1, v2)), ())
end))

let pre_concatwire = (fun c -> (match (c) with
| AST.Conf (_20_901, _20_899, _20_897, _20_895, AST.T_red (AST.R_concatwire (_20_90049, _20_90050, AST.V_wire (eps1, _20_889), AST.V_wire (eps2, _20_885))), tr) -> begin
if (is_empty (FStar_OrdSet.intersect ((fun c _20_901 _20_899 _20_897 _20_895 _20_90049 _20_90050 eps1 _20_889 eps2 _20_885 tr -> Prins.p_cmp) c _20_901 _20_899 _20_897 _20_895 _20_90049 _20_90050 eps1 _20_889 eps2 _20_885 ()) eps1 eps2)) then begin
Do
end else begin
NA
end
end
| _20_904 -> begin
NA
end))

let empty_intersection_lemma = (fun eps1 eps2 p -> ())

let empty_intersection_lemma_forall = (fun eps1 eps2 -> ())

let rec compose_wires = (fun eps1 eps2 w1 w2 eps -> (let _20_935 = ()
in (let _20_937 = ()
in if (eps = (FStar_OrdSet.empty ((fun eps1 eps2 w1 w2 eps -> Prins.p_cmp) eps1 eps2 w1 w2 eps))) then begin
w2
end else begin
(let _20_940 = (FStar_OrdSet.choose ((fun eps1 eps2 w1 w2 eps -> Prins.p_cmp) eps1 eps2 w1 w2 eps) eps)
in (match (_20_940) with
| Some (p) -> begin
(let w = (compose_wires eps1 eps2 w1 w2 (FStar_OrdSet.remove ((fun eps1 eps2 w1 w2 eps _20_940 p -> Prins.p_cmp) eps1 eps2 w1 w2 eps _20_940 p) p eps))
in (FStar_OrdMap.update ((fun eps1 eps2 w1 w2 eps _20_940 p w -> Prins.p_cmp) eps1 eps2 w1 w2 eps _20_940 p w) p (v_of_some (FStar_OrdMap.select ((fun eps1 eps2 w1 w2 eps _20_940 p w -> Prins.p_cmp) eps1 eps2 w1 w2 eps _20_940 p w) p w1)) w))
end))
end)))

let step_concatwire = (fun c -> (match (c) with
| AST.Conf (l, m, s, en, AST.T_red (AST.R_concatwire (_20_99681, _20_99682, AST.V_wire (eps1, w1), AST.V_wire (eps2, w2))), tr) -> begin
AST.Conf (l, m, s, en, AST.T_val (((fun c l m s en _20_99681 _20_99682 eps1 w1 eps2 w2 tr -> AST.Meta ((FStar_OrdSet.empty Prins.p_cmp), AST.Can_b, (FStar_OrdSet.union ((fun c l m s en _20_99681 _20_99682 eps1 w1 eps2 w2 tr -> Prins.p_cmp) c l m s en _20_99681 _20_99682 eps1 w1 eps2 w2 ()) eps1 eps2), AST.Cannot_w)) c l m s en _20_99681 _20_99682 eps1 w1 eps2 w2 ()), AST.V_wire ((FStar_OrdSet.union ((fun c l m s en _20_99681 _20_99682 eps1 w1 eps2 w2 tr -> Prins.p_cmp) c l m s en _20_99681 _20_99682 eps1 w1 eps2 w2 ()) eps1 eps2), (compose_wires eps1 eps2 w1 w2 eps1))), ())
end))

let pre_effi = (fun c -> ((AST.is_T_exp (AST.t_of_conf c)) && (AST.is_E_ffi (e_of_t_exp (AST.t_of_conf c)))))

let step_ffi_e = (fun _20_977 -> (match (_20_977) with
| AST.Conf (l, m, s, en, AST.T_exp (AST.E_ffi (_, _, n, _20_967, fn, es, inj)), tr) -> begin
(match (es) with
| [] -> begin
AST.Conf (l, m, s, en, AST.T_red (AST.R_ffi ((), (), n, fn, [], inj)), ())
end
| e::tl -> begin
AST.Conf (l, m, (AST.Frame (m, en, AST.F_ffi ((), (), n, fn, tl, [], inj), ()))::s, en, AST.T_exp (e), ())
end)
end))

let step_ffi_l = (fun _20_1007 -> (match (_20_1007) with
| AST.Conf (l, _20_1005, AST.Frame (m, en, AST.F_ffi (_, _, n, fn, es, vs, inj), tr)::s, _20_989, AST.T_val (meta, v), tr') -> begin
(match (es) with
| [] -> begin
AST.Conf (l, m, s, en, AST.T_red (AST.R_ffi ((), (), n, fn, (AST.D_v (meta, v))::vs, inj)), ())
end
| e::tl -> begin
AST.Conf (l, m, (AST.Frame (m, en, AST.F_ffi ((), (), n, fn, tl, (AST.D_v (meta, v))::vs, inj), ()))::s, en, AST.T_exp (e), ())
end)
end))

let pre_ffi = (fun c -> (match (c) with
| AST.Conf (_20_1033, _20_1031, _20_1029, _20_1027, AST.T_red (AST.R_ffi (_, _, _20_1021, _20_1019, vs, _20_1016)), _20_1014) -> begin
Do
end
| _20_1036 -> begin
NA
end))

let step_ffi = (fun _20_1052 -> (match (_20_1052) with
| AST.Conf (l, m, s, en, AST.T_red (AST.R_ffi (_, _, n, fn, vs, inj)), tr) -> begin
(let _20_1056 = (Ffibridge.exec_ffi n fn vs inj)
in (match (_20_1056) with
| AST.D_v (_20_1055, v) -> begin
AST.Conf (l, m, s, en, AST.T_val (((fun _20_1052 l m s en a b n fn vs inj tr _20_1056 _20_1055 v -> _20_1055) _20_1052 l m s en () () n fn vs inj () _20_1056 _20_1055 v), v), ())
end))
end))

let pre_econd = (fun c -> ((AST.is_T_exp (AST.t_of_conf c)) && (AST.is_E_cond (e_of_t_exp (AST.t_of_conf c)))))

let step_cond_e = (fun _20_1070 -> (match (_20_1070) with
| AST.Conf (l, m, s, en, AST.T_exp (AST.E_cond (e, e1, e2)), tr) -> begin
AST.Conf (l, m, (AST.Frame (m, en, AST.F_cond (e1, e2), ()))::s, en, AST.T_exp (e), ())
end))

let step_cond_red = (fun _20_1090 -> (match (_20_1090) with
| AST.Conf (l, _20_1088, AST.Frame (m, en, AST.F_cond (e1, e2), tr)::s, _20_1077, AST.T_val (_20_113435, v), tr') -> begin
AST.Conf (l, m, s, en, AST.T_red (AST.R_cond (((fun _20_1090 l _20_1088 m en e1 e2 tr s _20_1077 _20_113435 v tr' -> _20_113435) _20_1090 l _20_1088 m en e1 e2 () s _20_1077 _20_113435 v ()), v, e1, e2)), ())
end))

let pre_cond = (fun c -> (match (c) with
| AST.Conf (_20_1111, _20_1109, _20_1107, _20_1105, AST.T_red (AST.R_cond (_20_114389, AST.V_bool (_20_1100), _20_1098, _20_1096)), _20_1094) -> begin
true
end
| _20_1114 -> begin
false
end))

let step_cond = (fun c -> (match (c) with
| AST.Conf (l, m, s, en, AST.T_red (AST.R_cond (_20_114968, AST.V_bool (b), e1, e2)), tr) -> begin
(let e = if b then begin
e1
end else begin
e2
end
in AST.Conf (l, m, s, en, AST.T_exp (e), ()))
end))

let pre_eassec = (fun c -> ((AST.is_T_exp (AST.t_of_conf c)) && (AST.is_E_assec (e_of_t_exp (AST.t_of_conf c)))))

let step_assec_e1 = (fun _20_1143 -> (match (_20_1143) with
| AST.Conf (l, m, s, en, AST.T_exp (AST.E_assec (e1, e2)), tr) -> begin
AST.Conf (l, m, (AST.Frame (m, en, AST.F_assec_ps (e2), ()))::s, en, AST.T_exp (e1), ())
end))

let step_assec_e2 = (fun _20_1163 -> (match (_20_1163) with
| AST.Conf (l, _20_1161, AST.Frame (m, en, AST.F_assec_ps (e), tr)::s, _20_1151, AST.T_val (_20_117589, AST.V_eprins (ps)), tr') -> begin
AST.Conf (l, m, (AST.Frame (m, en, AST.F_assec_e (ps), ()))::s, en, AST.T_exp (e), ())
end))

let step_assec_red = (fun _20_1182 -> (match (_20_1182) with
| AST.Conf (l, _20_1180, AST.Frame (m, en, AST.F_assec_e (ps), tr)::s, _20_1170, AST.T_val (_20_119717, v), tr') -> begin
AST.Conf (l, m, s, en, AST.T_red (AST.R_assec (((fun _20_1182 l _20_1180 m en ps tr s _20_1170 _20_119717 v tr' -> _20_119717) _20_1182 l _20_1180 m en ps () s _20_1170 _20_119717 v ()), ps, v)), ())
end))

let pre_assec = (fun c -> (match (c) with
| AST.Conf (l, AST.Mode (as_m, ps1), _20_1193, _20_1191, AST.T_red (AST.R_assec (_20_120761, ps2, v)), _20_1185) -> begin
if (AST.is_clos ((fun c l as_m ps1 _20_1193 _20_1191 _20_120761 ps2 v _20_1185 -> _20_120761) c l as_m ps1 _20_1193 _20_1191 _20_120761 ps2 v ()) v) then begin
if ((l = AST.Source) || (as_m = AST.Sec)) then begin
if (ps1 = ps2) then begin
Do
end else begin
NA
end
end else begin
NA
end
end else begin
NA
end
end
| _20_1200 -> begin
NA
end))

let step_assec = (fun c -> (match (c) with
| AST.Conf (l, m, s, en', AST.T_red (AST.R_assec (_20_122198, ps, v)), tr) -> begin
(let _20_1217 = (AST.get_en_b ((fun c l m s en' _20_122198 ps v tr -> _20_122198) c l m s en' _20_122198 ps v ()) v)
in (match (_20_1217) with
| (en, x, e) -> begin
AST.Conf (l, AST.Mode (AST.Sec, ps), (AST.Frame (m, en', AST.F_assec_ret, ()))::s, (AST.update_env ((fun c l m s en' _20_122198 ps v tr _20_1217 en x e -> AST.Meta ((FStar_OrdSet.empty Prins.p_cmp), AST.Can_b, (FStar_OrdSet.empty Prins.p_cmp), AST.Can_w)) c l m s en' _20_122198 ps v () _20_1217 en x e) en x AST.V_unit), AST.T_exp (e), ())
end))
end))

let step_assec_ret = (fun _20_1234 -> (match (_20_1234) with
| AST.Conf (l, _20_1232, AST.Frame (m, en, AST.F_assec_ret, tr)::s, _20_1223, t, tr') -> begin
(let tr' = ()
in AST.Conf (l, m, s, en, t, ()))
end))

type ('dummyV2, 'dummyV1) sstep =
| C_aspar_ps of AST.config * AST.config
| C_aspar_e of AST.config * AST.config
| C_aspar_red of AST.config * AST.config
| C_aspar_beta of AST.config * AST.config
| C_aspar_ret of AST.config * AST.config
| C_box_ps of AST.config * AST.config
| C_box_e of AST.config * AST.config
| C_box_red of AST.config * AST.config
| C_box_beta of AST.config * AST.config
| C_unbox of AST.config * AST.config
| C_unbox_red of AST.config * AST.config
| C_unbox_beta of AST.config * AST.config
| C_mkwire_e1 of AST.config * AST.config
| C_mkwire_e2 of AST.config * AST.config
| C_mkwire_red of AST.config * AST.config
| C_mkwire_beta of AST.config * AST.config
| C_projwire_p of AST.config * AST.config
| C_projwire_e of AST.config * AST.config
| C_projwire_red of AST.config * AST.config
| C_projwire_beta of AST.config * AST.config
| C_concatwire_e1 of AST.config * AST.config
| C_concatwire_e2 of AST.config * AST.config
| C_concatwire_red of AST.config * AST.config
| C_concatwire_beta of AST.config * AST.config
| C_const of AST.config * AST.config
| C_var of AST.config * AST.config
| C_let_e1 of AST.config * AST.config
| C_let_red of AST.config * AST.config
| C_let_beta of AST.config * AST.config
| C_abs of AST.config * AST.config
| C_fix of AST.config * AST.config
| C_empabs of AST.config * AST.config
| C_app_e1 of AST.config * AST.config
| C_app_e2 of AST.config * AST.config
| C_app_red of AST.config * AST.config
| C_app_beta of AST.config * AST.config
| C_ffi_e of AST.config * AST.config
| C_ffi_l of AST.config * AST.config
| C_ffi_beta of AST.config * AST.config
| C_cond_e of AST.config * AST.config
| C_cond_red of AST.config * AST.config
| C_cond_beta of AST.config * AST.config
| C_assec_ps of AST.config * AST.config
| C_assec_e of AST.config * AST.config
| C_assec_red of AST.config * AST.config
| C_assec_beta of AST.config * AST.config
| C_assec_ret of AST.config * AST.config

let is_C_aspar_ps = (fun _discr_ -> (match (_discr_) with
| C_aspar_ps (_) -> begin
true
end
| _ -> begin
false
end))

let is_C_aspar_e = (fun _discr_ -> (match (_discr_) with
| C_aspar_e (_) -> begin
true
end
| _ -> begin
false
end))

let is_C_aspar_red = (fun _discr_ -> (match (_discr_) with
| C_aspar_red (_) -> begin
true
end
| _ -> begin
false
end))

let is_C_aspar_beta = (fun _discr_ -> (match (_discr_) with
| C_aspar_beta (_) -> begin
true
end
| _ -> begin
false
end))

let is_C_aspar_ret = (fun _discr_ -> (match (_discr_) with
| C_aspar_ret (_) -> begin
true
end
| _ -> begin
false
end))

let is_C_box_ps = (fun _discr_ -> (match (_discr_) with
| C_box_ps (_) -> begin
true
end
| _ -> begin
false
end))

let is_C_box_e = (fun _discr_ -> (match (_discr_) with
| C_box_e (_) -> begin
true
end
| _ -> begin
false
end))

let is_C_box_red = (fun _discr_ -> (match (_discr_) with
| C_box_red (_) -> begin
true
end
| _ -> begin
false
end))

let is_C_box_beta = (fun _discr_ -> (match (_discr_) with
| C_box_beta (_) -> begin
true
end
| _ -> begin
false
end))

let is_C_unbox = (fun _discr_ -> (match (_discr_) with
| C_unbox (_) -> begin
true
end
| _ -> begin
false
end))

let is_C_unbox_red = (fun _discr_ -> (match (_discr_) with
| C_unbox_red (_) -> begin
true
end
| _ -> begin
false
end))

let is_C_unbox_beta = (fun _discr_ -> (match (_discr_) with
| C_unbox_beta (_) -> begin
true
end
| _ -> begin
false
end))

let is_C_mkwire_e1 = (fun _discr_ -> (match (_discr_) with
| C_mkwire_e1 (_) -> begin
true
end
| _ -> begin
false
end))

let is_C_mkwire_e2 = (fun _discr_ -> (match (_discr_) with
| C_mkwire_e2 (_) -> begin
true
end
| _ -> begin
false
end))

let is_C_mkwire_red = (fun _discr_ -> (match (_discr_) with
| C_mkwire_red (_) -> begin
true
end
| _ -> begin
false
end))

let is_C_mkwire_beta = (fun _discr_ -> (match (_discr_) with
| C_mkwire_beta (_) -> begin
true
end
| _ -> begin
false
end))

let is_C_projwire_p = (fun _discr_ -> (match (_discr_) with
| C_projwire_p (_) -> begin
true
end
| _ -> begin
false
end))

let is_C_projwire_e = (fun _discr_ -> (match (_discr_) with
| C_projwire_e (_) -> begin
true
end
| _ -> begin
false
end))

let is_C_projwire_red = (fun _discr_ -> (match (_discr_) with
| C_projwire_red (_) -> begin
true
end
| _ -> begin
false
end))

let is_C_projwire_beta = (fun _discr_ -> (match (_discr_) with
| C_projwire_beta (_) -> begin
true
end
| _ -> begin
false
end))

let is_C_concatwire_e1 = (fun _discr_ -> (match (_discr_) with
| C_concatwire_e1 (_) -> begin
true
end
| _ -> begin
false
end))

let is_C_concatwire_e2 = (fun _discr_ -> (match (_discr_) with
| C_concatwire_e2 (_) -> begin
true
end
| _ -> begin
false
end))

let is_C_concatwire_red = (fun _discr_ -> (match (_discr_) with
| C_concatwire_red (_) -> begin
true
end
| _ -> begin
false
end))

let is_C_concatwire_beta = (fun _discr_ -> (match (_discr_) with
| C_concatwire_beta (_) -> begin
true
end
| _ -> begin
false
end))

let is_C_const = (fun _discr_ -> (match (_discr_) with
| C_const (_) -> begin
true
end
| _ -> begin
false
end))

let is_C_var = (fun _discr_ -> (match (_discr_) with
| C_var (_) -> begin
true
end
| _ -> begin
false
end))

let is_C_let_e1 = (fun _discr_ -> (match (_discr_) with
| C_let_e1 (_) -> begin
true
end
| _ -> begin
false
end))

let is_C_let_red = (fun _discr_ -> (match (_discr_) with
| C_let_red (_) -> begin
true
end
| _ -> begin
false
end))

let is_C_let_beta = (fun _discr_ -> (match (_discr_) with
| C_let_beta (_) -> begin
true
end
| _ -> begin
false
end))

let is_C_abs = (fun _discr_ -> (match (_discr_) with
| C_abs (_) -> begin
true
end
| _ -> begin
false
end))

let is_C_fix = (fun _discr_ -> (match (_discr_) with
| C_fix (_) -> begin
true
end
| _ -> begin
false
end))

let is_C_empabs = (fun _discr_ -> (match (_discr_) with
| C_empabs (_) -> begin
true
end
| _ -> begin
false
end))

let is_C_app_e1 = (fun _discr_ -> (match (_discr_) with
| C_app_e1 (_) -> begin
true
end
| _ -> begin
false
end))

let is_C_app_e2 = (fun _discr_ -> (match (_discr_) with
| C_app_e2 (_) -> begin
true
end
| _ -> begin
false
end))

let is_C_app_red = (fun _discr_ -> (match (_discr_) with
| C_app_red (_) -> begin
true
end
| _ -> begin
false
end))

let is_C_app_beta = (fun _discr_ -> (match (_discr_) with
| C_app_beta (_) -> begin
true
end
| _ -> begin
false
end))

let is_C_ffi_e = (fun _discr_ -> (match (_discr_) with
| C_ffi_e (_) -> begin
true
end
| _ -> begin
false
end))

let is_C_ffi_l = (fun _discr_ -> (match (_discr_) with
| C_ffi_l (_) -> begin
true
end
| _ -> begin
false
end))

let is_C_ffi_beta = (fun _discr_ -> (match (_discr_) with
| C_ffi_beta (_) -> begin
true
end
| _ -> begin
false
end))

let is_C_cond_e = (fun _discr_ -> (match (_discr_) with
| C_cond_e (_) -> begin
true
end
| _ -> begin
false
end))

let is_C_cond_red = (fun _discr_ -> (match (_discr_) with
| C_cond_red (_) -> begin
true
end
| _ -> begin
false
end))

let is_C_cond_beta = (fun _discr_ -> (match (_discr_) with
| C_cond_beta (_) -> begin
true
end
| _ -> begin
false
end))

let is_C_assec_ps = (fun _discr_ -> (match (_discr_) with
| C_assec_ps (_) -> begin
true
end
| _ -> begin
false
end))

let is_C_assec_e = (fun _discr_ -> (match (_discr_) with
| C_assec_e (_) -> begin
true
end
| _ -> begin
false
end))

let is_C_assec_red = (fun _discr_ -> (match (_discr_) with
| C_assec_red (_) -> begin
true
end
| _ -> begin
false
end))

let is_C_assec_beta = (fun _discr_ -> (match (_discr_) with
| C_assec_beta (_) -> begin
true
end
| _ -> begin
false
end))

let is_C_assec_ret = (fun _discr_ -> (match (_discr_) with
| C_assec_ret (_) -> begin
true
end
| _ -> begin
false
end))

let ___C_aspar_ps___c = (fun _0 _1 projectee -> (match (projectee) with
| C_aspar_ps (_20_1426, _20_1427) -> begin
_20_1426
end))

let ___C_aspar_ps___c' = (fun _0 _1 projectee -> (match (projectee) with
| C_aspar_ps (_20_1429, _20_1428) -> begin
_20_1428
end))

let ___C_aspar_e___c = (fun _0 _1 projectee -> (match (projectee) with
| C_aspar_e (_20_1432, _20_1433) -> begin
_20_1432
end))

let ___C_aspar_e___c' = (fun _0 _1 projectee -> (match (projectee) with
| C_aspar_e (_20_1435, _20_1434) -> begin
_20_1434
end))

let ___C_aspar_red___c = (fun _0 _1 projectee -> (match (projectee) with
| C_aspar_red (_20_1438, _20_1439) -> begin
_20_1438
end))

let ___C_aspar_red___c' = (fun _0 _1 projectee -> (match (projectee) with
| C_aspar_red (_20_1441, _20_1440) -> begin
_20_1440
end))

let ___C_aspar_beta___c = (fun _0 _1 projectee -> (match (projectee) with
| C_aspar_beta (_20_1444, _20_1445) -> begin
_20_1444
end))

let ___C_aspar_beta___c' = (fun _0 _1 projectee -> (match (projectee) with
| C_aspar_beta (_20_1447, _20_1446) -> begin
_20_1446
end))

let ___C_aspar_ret___c = (fun _0 _1 projectee -> (match (projectee) with
| C_aspar_ret (_20_1450, _20_1451) -> begin
_20_1450
end))

let ___C_aspar_ret___c' = (fun _0 _1 projectee -> (match (projectee) with
| C_aspar_ret (_20_1453, _20_1452) -> begin
_20_1452
end))

let ___C_box_ps___c = (fun _0 _1 projectee -> (match (projectee) with
| C_box_ps (_20_1456, _20_1457) -> begin
_20_1456
end))

let ___C_box_ps___c' = (fun _0 _1 projectee -> (match (projectee) with
| C_box_ps (_20_1459, _20_1458) -> begin
_20_1458
end))

let ___C_box_e___c = (fun _0 _1 projectee -> (match (projectee) with
| C_box_e (_20_1462, _20_1463) -> begin
_20_1462
end))

let ___C_box_e___c' = (fun _0 _1 projectee -> (match (projectee) with
| C_box_e (_20_1465, _20_1464) -> begin
_20_1464
end))

let ___C_box_red___c = (fun _0 _1 projectee -> (match (projectee) with
| C_box_red (_20_1468, _20_1469) -> begin
_20_1468
end))

let ___C_box_red___c' = (fun _0 _1 projectee -> (match (projectee) with
| C_box_red (_20_1471, _20_1470) -> begin
_20_1470
end))

let ___C_box_beta___c = (fun _0 _1 projectee -> (match (projectee) with
| C_box_beta (_20_1474, _20_1475) -> begin
_20_1474
end))

let ___C_box_beta___c' = (fun _0 _1 projectee -> (match (projectee) with
| C_box_beta (_20_1477, _20_1476) -> begin
_20_1476
end))

let ___C_unbox___c = (fun _0 _1 projectee -> (match (projectee) with
| C_unbox (_20_1480, _20_1481) -> begin
_20_1480
end))

let ___C_unbox___c' = (fun _0 _1 projectee -> (match (projectee) with
| C_unbox (_20_1483, _20_1482) -> begin
_20_1482
end))

let ___C_unbox_red___c = (fun _0 _1 projectee -> (match (projectee) with
| C_unbox_red (_20_1486, _20_1487) -> begin
_20_1486
end))

let ___C_unbox_red___c' = (fun _0 _1 projectee -> (match (projectee) with
| C_unbox_red (_20_1489, _20_1488) -> begin
_20_1488
end))

let ___C_unbox_beta___c = (fun _0 _1 projectee -> (match (projectee) with
| C_unbox_beta (_20_1492, _20_1493) -> begin
_20_1492
end))

let ___C_unbox_beta___c' = (fun _0 _1 projectee -> (match (projectee) with
| C_unbox_beta (_20_1495, _20_1494) -> begin
_20_1494
end))

let ___C_mkwire_e1___c = (fun _0 _1 projectee -> (match (projectee) with
| C_mkwire_e1 (_20_1498, _20_1499) -> begin
_20_1498
end))

let ___C_mkwire_e1___c' = (fun _0 _1 projectee -> (match (projectee) with
| C_mkwire_e1 (_20_1501, _20_1500) -> begin
_20_1500
end))

let ___C_mkwire_e2___c = (fun _0 _1 projectee -> (match (projectee) with
| C_mkwire_e2 (_20_1504, _20_1505) -> begin
_20_1504
end))

let ___C_mkwire_e2___c' = (fun _0 _1 projectee -> (match (projectee) with
| C_mkwire_e2 (_20_1507, _20_1506) -> begin
_20_1506
end))

let ___C_mkwire_red___c = (fun _0 _1 projectee -> (match (projectee) with
| C_mkwire_red (_20_1510, _20_1511) -> begin
_20_1510
end))

let ___C_mkwire_red___c' = (fun _0 _1 projectee -> (match (projectee) with
| C_mkwire_red (_20_1513, _20_1512) -> begin
_20_1512
end))

let ___C_mkwire_beta___c = (fun _0 _1 projectee -> (match (projectee) with
| C_mkwire_beta (_20_1516, _20_1517) -> begin
_20_1516
end))

let ___C_mkwire_beta___c' = (fun _0 _1 projectee -> (match (projectee) with
| C_mkwire_beta (_20_1519, _20_1518) -> begin
_20_1518
end))

let ___C_projwire_p___c = (fun _0 _1 projectee -> (match (projectee) with
| C_projwire_p (_20_1522, _20_1523) -> begin
_20_1522
end))

let ___C_projwire_p___c' = (fun _0 _1 projectee -> (match (projectee) with
| C_projwire_p (_20_1525, _20_1524) -> begin
_20_1524
end))

let ___C_projwire_e___c = (fun _0 _1 projectee -> (match (projectee) with
| C_projwire_e (_20_1528, _20_1529) -> begin
_20_1528
end))

let ___C_projwire_e___c' = (fun _0 _1 projectee -> (match (projectee) with
| C_projwire_e (_20_1531, _20_1530) -> begin
_20_1530
end))

let ___C_projwire_red___c = (fun _0 _1 projectee -> (match (projectee) with
| C_projwire_red (_20_1534, _20_1535) -> begin
_20_1534
end))

let ___C_projwire_red___c' = (fun _0 _1 projectee -> (match (projectee) with
| C_projwire_red (_20_1537, _20_1536) -> begin
_20_1536
end))

let ___C_projwire_beta___c = (fun _0 _1 projectee -> (match (projectee) with
| C_projwire_beta (_20_1540, _20_1541) -> begin
_20_1540
end))

let ___C_projwire_beta___c' = (fun _0 _1 projectee -> (match (projectee) with
| C_projwire_beta (_20_1543, _20_1542) -> begin
_20_1542
end))

let ___C_concatwire_e1___c = (fun _0 _1 projectee -> (match (projectee) with
| C_concatwire_e1 (_20_1546, _20_1547) -> begin
_20_1546
end))

let ___C_concatwire_e1___c' = (fun _0 _1 projectee -> (match (projectee) with
| C_concatwire_e1 (_20_1549, _20_1548) -> begin
_20_1548
end))

let ___C_concatwire_e2___c = (fun _0 _1 projectee -> (match (projectee) with
| C_concatwire_e2 (_20_1552, _20_1553) -> begin
_20_1552
end))

let ___C_concatwire_e2___c' = (fun _0 _1 projectee -> (match (projectee) with
| C_concatwire_e2 (_20_1555, _20_1554) -> begin
_20_1554
end))

let ___C_concatwire_red___c = (fun _0 _1 projectee -> (match (projectee) with
| C_concatwire_red (_20_1558, _20_1559) -> begin
_20_1558
end))

let ___C_concatwire_red___c' = (fun _0 _1 projectee -> (match (projectee) with
| C_concatwire_red (_20_1561, _20_1560) -> begin
_20_1560
end))

let ___C_concatwire_beta___c = (fun _0 _1 projectee -> (match (projectee) with
| C_concatwire_beta (_20_1564, _20_1565) -> begin
_20_1564
end))

let ___C_concatwire_beta___c' = (fun _0 _1 projectee -> (match (projectee) with
| C_concatwire_beta (_20_1567, _20_1566) -> begin
_20_1566
end))

let ___C_const___c = (fun _0 _1 projectee -> (match (projectee) with
| C_const (_20_1570, _20_1571) -> begin
_20_1570
end))

let ___C_const___c' = (fun _0 _1 projectee -> (match (projectee) with
| C_const (_20_1573, _20_1572) -> begin
_20_1572
end))

let ___C_var___c = (fun _0 _1 projectee -> (match (projectee) with
| C_var (_20_1576, _20_1577) -> begin
_20_1576
end))

let ___C_var___c' = (fun _0 _1 projectee -> (match (projectee) with
| C_var (_20_1579, _20_1578) -> begin
_20_1578
end))

let ___C_let_e1___c = (fun _0 _1 projectee -> (match (projectee) with
| C_let_e1 (_20_1582, _20_1583) -> begin
_20_1582
end))

let ___C_let_e1___c' = (fun _0 _1 projectee -> (match (projectee) with
| C_let_e1 (_20_1585, _20_1584) -> begin
_20_1584
end))

let ___C_let_red___c = (fun _0 _1 projectee -> (match (projectee) with
| C_let_red (_20_1588, _20_1589) -> begin
_20_1588
end))

let ___C_let_red___c' = (fun _0 _1 projectee -> (match (projectee) with
| C_let_red (_20_1591, _20_1590) -> begin
_20_1590
end))

let ___C_let_beta___c = (fun _0 _1 projectee -> (match (projectee) with
| C_let_beta (_20_1594, _20_1595) -> begin
_20_1594
end))

let ___C_let_beta___c' = (fun _0 _1 projectee -> (match (projectee) with
| C_let_beta (_20_1597, _20_1596) -> begin
_20_1596
end))

let ___C_abs___c = (fun _0 _1 projectee -> (match (projectee) with
| C_abs (_20_1600, _20_1601) -> begin
_20_1600
end))

let ___C_abs___c' = (fun _0 _1 projectee -> (match (projectee) with
| C_abs (_20_1603, _20_1602) -> begin
_20_1602
end))

let ___C_fix___c = (fun _0 _1 projectee -> (match (projectee) with
| C_fix (_20_1606, _20_1607) -> begin
_20_1606
end))

let ___C_fix___c' = (fun _0 _1 projectee -> (match (projectee) with
| C_fix (_20_1609, _20_1608) -> begin
_20_1608
end))

let ___C_empabs___c = (fun _0 _1 projectee -> (match (projectee) with
| C_empabs (_20_1612, _20_1613) -> begin
_20_1612
end))

let ___C_empabs___c' = (fun _0 _1 projectee -> (match (projectee) with
| C_empabs (_20_1615, _20_1614) -> begin
_20_1614
end))

let ___C_app_e1___c = (fun _0 _1 projectee -> (match (projectee) with
| C_app_e1 (_20_1618, _20_1619) -> begin
_20_1618
end))

let ___C_app_e1___c' = (fun _0 _1 projectee -> (match (projectee) with
| C_app_e1 (_20_1621, _20_1620) -> begin
_20_1620
end))

let ___C_app_e2___c = (fun _0 _1 projectee -> (match (projectee) with
| C_app_e2 (_20_1624, _20_1625) -> begin
_20_1624
end))

let ___C_app_e2___c' = (fun _0 _1 projectee -> (match (projectee) with
| C_app_e2 (_20_1627, _20_1626) -> begin
_20_1626
end))

let ___C_app_red___c = (fun _0 _1 projectee -> (match (projectee) with
| C_app_red (_20_1630, _20_1631) -> begin
_20_1630
end))

let ___C_app_red___c' = (fun _0 _1 projectee -> (match (projectee) with
| C_app_red (_20_1633, _20_1632) -> begin
_20_1632
end))

let ___C_app_beta___c = (fun _0 _1 projectee -> (match (projectee) with
| C_app_beta (_20_1636, _20_1637) -> begin
_20_1636
end))

let ___C_app_beta___c' = (fun _0 _1 projectee -> (match (projectee) with
| C_app_beta (_20_1639, _20_1638) -> begin
_20_1638
end))

let ___C_ffi_e___c = (fun _0 _1 projectee -> (match (projectee) with
| C_ffi_e (_20_1642, _20_1643) -> begin
_20_1642
end))

let ___C_ffi_e___c' = (fun _0 _1 projectee -> (match (projectee) with
| C_ffi_e (_20_1645, _20_1644) -> begin
_20_1644
end))

let ___C_ffi_l___c = (fun _0 _1 projectee -> (match (projectee) with
| C_ffi_l (_20_1648, _20_1649) -> begin
_20_1648
end))

let ___C_ffi_l___c' = (fun _0 _1 projectee -> (match (projectee) with
| C_ffi_l (_20_1651, _20_1650) -> begin
_20_1650
end))

let ___C_ffi_beta___c = (fun _0 _1 projectee -> (match (projectee) with
| C_ffi_beta (_20_1654, _20_1655) -> begin
_20_1654
end))

let ___C_ffi_beta___c' = (fun _0 _1 projectee -> (match (projectee) with
| C_ffi_beta (_20_1657, _20_1656) -> begin
_20_1656
end))

let ___C_cond_e___c = (fun _0 _1 projectee -> (match (projectee) with
| C_cond_e (_20_1660, _20_1661) -> begin
_20_1660
end))

let ___C_cond_e___c' = (fun _0 _1 projectee -> (match (projectee) with
| C_cond_e (_20_1663, _20_1662) -> begin
_20_1662
end))

let ___C_cond_red___c = (fun _0 _1 projectee -> (match (projectee) with
| C_cond_red (_20_1666, _20_1667) -> begin
_20_1666
end))

let ___C_cond_red___c' = (fun _0 _1 projectee -> (match (projectee) with
| C_cond_red (_20_1669, _20_1668) -> begin
_20_1668
end))

let ___C_cond_beta___c = (fun _0 _1 projectee -> (match (projectee) with
| C_cond_beta (_20_1672, _20_1673) -> begin
_20_1672
end))

let ___C_cond_beta___c' = (fun _0 _1 projectee -> (match (projectee) with
| C_cond_beta (_20_1675, _20_1674) -> begin
_20_1674
end))

let ___C_assec_ps___c = (fun _0 _1 projectee -> (match (projectee) with
| C_assec_ps (_20_1678, _20_1679) -> begin
_20_1678
end))

let ___C_assec_ps___c' = (fun _0 _1 projectee -> (match (projectee) with
| C_assec_ps (_20_1681, _20_1680) -> begin
_20_1680
end))

let ___C_assec_e___c = (fun _0 _1 projectee -> (match (projectee) with
| C_assec_e (_20_1684, _20_1685) -> begin
_20_1684
end))

let ___C_assec_e___c' = (fun _0 _1 projectee -> (match (projectee) with
| C_assec_e (_20_1687, _20_1686) -> begin
_20_1686
end))

let ___C_assec_red___c = (fun _0 _1 projectee -> (match (projectee) with
| C_assec_red (_20_1690, _20_1691) -> begin
_20_1690
end))

let ___C_assec_red___c' = (fun _0 _1 projectee -> (match (projectee) with
| C_assec_red (_20_1693, _20_1692) -> begin
_20_1692
end))

let ___C_assec_beta___c = (fun _0 _1 projectee -> (match (projectee) with
| C_assec_beta (_20_1696, _20_1697) -> begin
_20_1696
end))

let ___C_assec_beta___c' = (fun _0 _1 projectee -> (match (projectee) with
| C_assec_beta (_20_1699, _20_1698) -> begin
_20_1698
end))

let ___C_assec_ret___c = (fun _0 _1 projectee -> (match (projectee) with
| C_assec_ret (_20_1702, _20_1703) -> begin
_20_1702
end))

let ___C_assec_ret___c' = (fun _0 _1 projectee -> (match (projectee) with
| C_assec_ret (_20_1705, _20_1704) -> begin
_20_1704
end))

let slice_wire = (fun eps p w -> if (FStar_OrdSet.mem ((fun eps p w -> Prins.p_cmp) eps p w) p eps) then begin
(FStar_OrdMap.update ((fun eps p w -> ((fun eps p w -> Prins.p_cmp) eps p w)) eps p w) p (Prims.___Some___v (FStar_OrdMap.select ((fun eps p w -> Prins.p_cmp) eps p w) p w)) (FStar_OrdMap.empty ((fun eps p w -> ((fun eps p w -> Prins.p_cmp) eps p w)) eps p w)))
end else begin
(FStar_OrdMap.empty ((fun eps p w -> Prins.p_cmp) eps p w))
end)

let rec slice_v = (fun meta p v -> (let def = AST.D_v (meta, v)
in (let emp = AST.D_v (AST.Meta ((FStar_OrdSet.empty ((fun meta p v def -> Prins.p_cmp) meta p v def)), AST.Can_b, (FStar_OrdSet.empty ((fun meta p v def -> Prins.p_cmp) meta p v def)), AST.Can_w), AST.V_emp)
in (match (v) with
| AST.V_prin (_20_1725) -> begin
def
end
| AST.V_eprins (_20_1728) -> begin
def
end
| AST.V_unit -> begin
def
end
| AST.V_bool (_20_1732) -> begin
def
end
| AST.V_opaque (_, v', m', s, c, sps) -> begin
(let _20_1745 = m'
in (match (_20_1745) with
| AST.Meta (bps, cb, wps, cw) -> begin
(let v'' = (s p v')
in (let m'' = AST.Meta (bps, cb, (FStar_OrdSet.intersect ((fun meta p v def emp a v' m' s c sps _20_1745 bps cb wps cw v'' -> Prins.p_cmp) meta p v def emp () v' m' s c sps _20_1745 bps cb wps cw v'') wps (FStar_OrdSet.singleton ((fun meta p v def emp a v' m' s c sps _20_1745 bps cb wps cw v'' -> ((fun meta p v def emp a v' m' s c sps _20_1745 bps cb wps cw v'' -> Prins.p_cmp) meta p v def emp () v' m' s c sps _20_1745 bps cb wps cw v'')) meta p v def emp () v' m' s c sps _20_1745 bps cb wps cw v'') p)), cw)
in (let _20_1748 = ()
in AST.D_v (m'', AST.V_opaque ((), v'', m'', s, c, sps)))))
end))
end
| AST.V_box (_20_173232, ps, v) -> begin
(let _20_1755 = if (FStar_OrdSet.mem ((fun meta p v def emp _20_173232 ps v -> Prins.p_cmp) meta p v def emp _20_173232 ps v) p ps) then begin
(slice_v ((fun meta p v def emp _20_173232 ps v -> _20_173232) meta p v def emp _20_173232 ps v) p v)
end else begin
emp
end
in (match (_20_1755) with
| AST.D_v (meta', v') -> begin
AST.D_v (AST.Meta (ps, AST.Can_b, (AST.___Meta___wps meta'), AST.Cannot_w), AST.V_box (((fun meta p v def emp _20_173232 ps v _20_1755 meta' v' -> meta') meta p v def emp _20_173232 ps v _20_1755 meta' v'), ps, v'))
end))
end
| AST.V_wire (eps, w) -> begin
AST.D_v (AST.Meta ((FStar_OrdSet.empty ((fun meta p v def emp eps w -> Prins.p_cmp) meta p v def emp eps w)), AST.Can_b, (FStar_OrdSet.intersect ((fun meta p v def emp eps w -> Prins.p_cmp) meta p v def emp eps w) eps (FStar_OrdSet.singleton ((fun meta p v def emp eps w -> ((fun meta p v def emp eps w -> Prins.p_cmp) meta p v def emp eps w)) meta p v def emp eps w) p)), AST.Cannot_w), AST.V_wire ((FStar_OrdSet.intersect ((fun meta p v def emp eps w -> Prins.p_cmp) meta p v def emp eps w) eps (FStar_OrdSet.singleton ((fun meta p v def emp eps w -> ((fun meta p v def emp eps w -> Prins.p_cmp) meta p v def emp eps w)) meta p v def emp eps w) p)), (slice_wire eps p w)))
end
| AST.V_clos (en, x, e) -> begin
AST.D_v (meta, AST.V_clos ((slice_en p en), x, e))
end
| AST.V_fix_clos (en, f, x, e) -> begin
AST.D_v (meta, AST.V_fix_clos ((slice_en p en), f, x, e))
end
| AST.V_emp_clos (_20_1771, _20_1769) -> begin
def
end
| AST.V_emp -> begin
emp
end))))
and slice_en = (fun p en -> (let _20_1776 = ()
in (fun x -> (let _20_1779 = ()
in if ((en x) = None) then begin
None
end else begin
Some ((slice_v ((fun p en _20_1776 x -> (AST.___D_v___meta (Prims.___Some___v (en x)))) p en () x) p (AST.___D_v___v (Prims.___Some___v (en x)))))
end))))

let is_v_emp = (fun meta v -> (match (v) with
| AST.V_emp -> begin
true
end
| _20_1787 -> begin
false
end))

let is_v_prin = (fun meta v -> (match (v) with
| AST.V_prin (_20_1793) -> begin
true
end
| _20_1796 -> begin
false
end))

let is_v_eprins = (fun meta v -> (match (v) with
| AST.V_eprins (_20_1802) -> begin
true
end
| _20_1805 -> begin
false
end))

let is_v_unit = (fun meta v -> (match (v) with
| AST.V_unit -> begin
true
end
| _20_1812 -> begin
false
end))

let is_v_bool = (fun meta v -> (match (v) with
| AST.V_bool (_20_1818) -> begin
true
end
| _20_1821 -> begin
false
end))

let is_v_opaque = (fun meta v -> (match (v) with
| AST.V_opaque (_, _20_1835, _20_1833, _20_1831, _20_1829, _20_1827) -> begin
true
end
| _20_1839 -> begin
false
end))

let is_v_box = (fun meta v -> (match (v) with
| AST.V_box (_20_182993, _20_1847, _20_1845) -> begin
true
end
| _20_1850 -> begin
false
end))

let is_v_wire = (fun meta v -> (match (v) with
| AST.V_wire (_20_1858, _20_1856) -> begin
true
end
| _20_1861 -> begin
false
end))

let is_v_clos = (fun meta v -> (match (v) with
| AST.V_clos (_20_1871, _20_1869, _20_1867) -> begin
true
end
| _20_1874 -> begin
false
end))

let is_v_fix_clos = (fun meta v -> (match (v) with
| AST.V_fix_clos (_20_1886, _20_1884, _20_1882, _20_1880) -> begin
true
end
| _20_1889 -> begin
false
end))

let is_v_emp_clos = (fun meta v -> (match (v) with
| AST.V_emp_clos (_20_1897, _20_1895) -> begin
true
end
| _20_1900 -> begin
false
end))

let rec compose_vals = (fun m1 m2 v1 v2 -> if (is_v_emp ((fun m1 m2 v1 v2 -> m1) m1 m2 v1 v2) v1) then begin
AST.D_v (m2, v2)
end else begin
if (is_v_emp ((fun m1 m2 v1 v2 -> m2) m1 m2 v1 v2) v2) then begin
AST.D_v (m1, v1)
end else begin
(let emp = AST.D_v (AST.Meta ((FStar_OrdSet.empty ((fun m1 m2 v1 v2 -> Prins.p_cmp) m1 m2 v1 v2)), AST.Can_b, (FStar_OrdSet.empty ((fun m1 m2 v1 v2 -> Prins.p_cmp) m1 m2 v1 v2)), AST.Can_w), AST.V_emp)
in (match (v1) with
| (AST.V_prin (_)) | (AST.V_eprins (_)) | (AST.V_unit) | (AST.V_bool (_)) -> begin
AST.D_v (m1, v1)
end
| AST.V_opaque (_, _20_1931, _20_1929, _20_1927, _20_1925, _20_1923) -> begin
if (is_v_opaque ((fun m1 m2 v1 v2 emp a _20_1931 _20_1929 _20_1927 _20_1925 _20_1923 -> m2) m1 m2 v1 v2 emp () _20_1931 _20_1929 _20_1927 _20_1925 _20_1923) v2) then begin
(Ffibridge.compose_v_opaques ((fun m1 m2 v1 v2 emp a _20_1931 _20_1929 _20_1927 _20_1925 _20_1923 -> m1) m1 m2 v1 v2 emp () _20_1931 _20_1929 _20_1927 _20_1925 _20_1923) ((fun m1 m2 v1 v2 emp a _20_1931 _20_1929 _20_1927 _20_1925 _20_1923 -> m2) m1 m2 v1 v2 emp () _20_1931 _20_1929 _20_1927 _20_1925 _20_1923) v1 v2)
end else begin
emp
end
end
| AST.V_box (_20_184022, ps1, v1) -> begin
if (is_v_box ((fun m1 m2 v1 v2 emp _20_184022 ps1 v1 -> m2) m1 m2 v1 v2 emp _20_184022 ps1 v1) v2) then begin
(let _20_1939 = v2
in (match (_20_1939) with
| AST.V_box (_20_184043, ps2, v2) -> begin
if (ps1 = ps2) then begin
(let _20_1942 = (compose_vals ((fun m1 m2 v1 v2 emp _20_184022 ps1 v1 _20_1939 _20_184043 ps2 v2 -> _20_184022) m1 m2 v1 v2 emp _20_184022 ps1 v1 _20_1939 _20_184043 ps2 v2) ((fun m1 m2 v1 v2 emp _20_184022 ps1 v1 _20_1939 _20_184043 ps2 v2 -> _20_184043) m1 m2 v1 v2 emp _20_184022 ps1 v1 _20_1939 _20_184043 ps2 v2) v1 v2)
in (match (_20_1942) with
| AST.D_v (meta, v) -> begin
AST.D_v (AST.Meta (ps1, AST.Can_b, (AST.___Meta___wps meta), AST.Cannot_w), AST.V_box (((fun m1 m2 v1 v2 emp _20_184022 ps1 v1 _20_1939 _20_184043 ps2 v2 _20_1942 meta v -> meta) m1 m2 v1 v2 emp _20_184022 ps1 v1 _20_1939 _20_184043 ps2 v2 _20_1942 meta v), ps1, v))
end))
end else begin
emp
end
end))
end else begin
emp
end
end
| AST.V_wire (eps1, w1) -> begin
if (is_v_wire ((fun m1 m2 v1 v2 emp eps1 w1 -> m2) m1 m2 v1 v2 emp eps1 w1) v2) then begin
(let _20_1948 = v2
in (match (_20_1948) with
| AST.V_wire (eps2, w2) -> begin
if (is_empty (FStar_OrdSet.intersect ((fun m1 m2 v1 v2 emp eps1 w1 _20_1948 eps2 w2 -> Prins.p_cmp) m1 m2 v1 v2 emp eps1 w1 _20_1948 eps2 w2) eps1 eps2)) then begin
AST.D_v (AST.Meta ((FStar_OrdSet.empty ((fun m1 m2 v1 v2 emp eps1 w1 _20_1948 eps2 w2 -> Prins.p_cmp) m1 m2 v1 v2 emp eps1 w1 _20_1948 eps2 w2)), AST.Can_b, (FStar_OrdSet.union ((fun m1 m2 v1 v2 emp eps1 w1 _20_1948 eps2 w2 -> Prins.p_cmp) m1 m2 v1 v2 emp eps1 w1 _20_1948 eps2 w2) eps1 eps2), AST.Cannot_w), AST.V_wire ((FStar_OrdSet.union ((fun m1 m2 v1 v2 emp eps1 w1 _20_1948 eps2 w2 -> Prins.p_cmp) m1 m2 v1 v2 emp eps1 w1 _20_1948 eps2 w2) eps1 eps2), (compose_wires eps1 eps2 w1 w2 eps1)))
end else begin
emp
end
end))
end else begin
emp
end
end
| AST.V_clos (en1, x1, e1) -> begin
if (is_v_clos ((fun m1 m2 v1 v2 emp en1 x1 e1 -> m2) m1 m2 v1 v2 emp en1 x1 e1) v2) then begin
(let _20_1958 = v2
in (match (_20_1958) with
| AST.V_clos (en2, _20_1956, _20_1954) -> begin
AST.D_v (m1, AST.V_clos ((compose_envs en1 en2), x1, e1))
end))
end else begin
emp
end
end
| AST.V_fix_clos (en1, f1, x1, e1) -> begin
if (is_v_fix_clos ((fun m1 m2 v1 v2 emp en1 f1 x1 e1 -> m2) m1 m2 v1 v2 emp en1 f1 x1 e1) v2) then begin
(let _20_1971 = v2
in (match (_20_1971) with
| AST.V_fix_clos (en2, _20_1969, _20_1967, _20_1965) -> begin
AST.D_v (m1, AST.V_fix_clos ((compose_envs en1 en2), f1, x1, e1))
end))
end else begin
emp
end
end
| AST.V_emp_clos (x1, e1) -> begin
if (is_v_emp_clos ((fun m1 m2 v1 v2 emp x1 e1 -> m2) m1 m2 v1 v2 emp x1 e1) v2) then begin
AST.D_v (m1, AST.V_emp_clos (x1, e1))
end else begin
emp
end
end))
end
end)
and compose_envs = (fun en1 en2 -> (let _20_1977 = ()
in (fun x -> (let _20_1980 = ()
in (let r1 = (en1 x)
in (let r2 = (en2 x)
in (match (r1) with
| None -> begin
r2
end
| Some (AST.D_v (m1, v1)) -> begin
(match (r2) with
| None -> begin
r1
end
| Some (AST.D_v (m2, v2)) -> begin
Some ((compose_vals ((fun en1 en2 _20_1977 x r1 r2 m1 v1 m2 v2 -> m1) en1 en2 () x r1 r2 m1 v1 m2 v2) ((fun en1 en2 _20_1977 x r1 r2 m1 v1 m2 v2 -> m2) en1 en2 () x r1 r2 m1 v1 m2 v2) v1 v2))
end)
end)))))))

type ' ps value_map =
(Prins.prin, AST.dvalue, Prims.unit) FStar_OrdMap.ordmap

type ' ps env_map =
(Prins.prin, AST.env, Prims.unit) FStar_OrdMap.ordmap

let rec compose_vals_m = (fun ps m -> (let _20_2007 = (FStar_OrdSet.choose ((fun ps m -> Prins.p_cmp) ps m) ps)
in (match (_20_2007) with
| Some (p) -> begin
(let _20_2011 = (FStar_OrdMap.select ((fun ps m _20_2007 p -> Prins.p_cmp) ps m _20_2007 p) p m)
in (match (_20_2011) with
| Some (AST.D_v (meta, v)) -> begin
(let ps_rest = (FStar_OrdSet.remove ((fun ps m _20_2007 p _20_2011 meta v -> Prins.p_cmp) ps m _20_2007 p _20_2011 meta v) p ps)
in if (is_empty ps_rest) then begin
AST.D_v (meta, v)
end else begin
(let _20_2016 = (compose_vals_m ps_rest m)
in (match (_20_2016) with
| AST.D_v (_20_2015, v') -> begin
(compose_vals ((fun ps m _20_2007 p _20_2011 meta v ps_rest _20_2016 _20_2015 v' -> meta) ps m _20_2007 p _20_2011 meta v ps_rest _20_2016 _20_2015 v') ((fun ps m _20_2007 p _20_2011 meta v ps_rest _20_2016 _20_2015 v' -> _20_2015) ps m _20_2007 p _20_2011 meta v ps_rest _20_2016 _20_2015 v') v v')
end))
end)
end))
end)))

let rec compose_envs_m = (fun ps m -> (let _20_2022 = (FStar_OrdSet.choose ((fun ps m -> Prins.p_cmp) ps m) ps)
in (match (_20_2022) with
| Some (p) -> begin
(let _20_2024 = (FStar_OrdMap.select ((fun ps m _20_2022 p -> Prins.p_cmp) ps m _20_2022 p) p m)
in (match (_20_2024) with
| Some (en) -> begin
(let ps_rest = (FStar_OrdSet.remove ((fun ps m _20_2022 p _20_2024 en -> Prins.p_cmp) ps m _20_2022 p _20_2024 en) p ps)
in if (is_empty ps_rest) then begin
en
end else begin
(let en' = (compose_envs_m ps_rest m)
in (compose_envs en en'))
end)
end))
end)))

let rec slice_wire_sps = (fun eps ps w -> (let _20_2036 = (FStar_OrdSet.choose ((fun eps ps w -> Prins.p_cmp) eps ps w) ps)
in (match (_20_2036) with
| Some (p) -> begin
(let ps_rest = (FStar_OrdSet.remove ((fun eps ps w _20_2036 p -> Prins.p_cmp) eps ps w _20_2036 p) p ps)
in if (is_empty ps_rest) then begin
if (FStar_OrdSet.mem ((fun eps ps w _20_2036 p ps_rest -> Prins.p_cmp) eps ps w _20_2036 p ps_rest) p eps) then begin
(FStar_OrdMap.update ((fun eps ps w _20_2036 p ps_rest -> ((fun eps ps w _20_2036 p ps_rest -> Prins.p_cmp) eps ps w _20_2036 p ps_rest)) eps ps w _20_2036 p ps_rest) p (Prims.___Some___v (FStar_OrdMap.select ((fun eps ps w _20_2036 p ps_rest -> Prins.p_cmp) eps ps w _20_2036 p ps_rest) p w)) (FStar_OrdMap.empty ((fun eps ps w _20_2036 p ps_rest -> ((fun eps ps w _20_2036 p ps_rest -> Prins.p_cmp) eps ps w _20_2036 p ps_rest)) eps ps w _20_2036 p ps_rest)))
end else begin
(FStar_OrdMap.empty ((fun eps ps w _20_2036 p ps_rest -> Prins.p_cmp) eps ps w _20_2036 p ps_rest))
end
end else begin
(let w' = (slice_wire_sps eps ps_rest w)
in if (FStar_OrdSet.mem ((fun eps ps w _20_2036 p ps_rest w' -> Prins.p_cmp) eps ps w _20_2036 p ps_rest w') p eps) then begin
(FStar_OrdMap.update ((fun eps ps w _20_2036 p ps_rest w' -> Prins.p_cmp) eps ps w _20_2036 p ps_rest w') p (Prims.___Some___v (FStar_OrdMap.select ((fun eps ps w _20_2036 p ps_rest w' -> Prins.p_cmp) eps ps w _20_2036 p ps_rest w') p w)) w')
end else begin
w'
end)
end)
end)))

let rec slice_v_sps = (fun meta ps v -> (let def = AST.D_v (meta, v)
in (let emp = AST.D_v (AST.Meta ((FStar_OrdSet.empty ((fun meta ps v def -> Prins.p_cmp) meta ps v def)), AST.Can_b, (FStar_OrdSet.empty ((fun meta ps v def -> Prins.p_cmp) meta ps v def)), AST.Can_w), AST.V_emp)
in (match (v) with
| AST.V_prin (_20_2049) -> begin
def
end
| AST.V_eprins (_20_2052) -> begin
def
end
| AST.V_unit -> begin
def
end
| AST.V_bool (_20_2056) -> begin
def
end
| AST.V_opaque (_, v', m', s, c, sps) -> begin
(let _20_2069 = m'
in (match (_20_2069) with
| AST.Meta (bps, cb, wps, cw) -> begin
(let v'' = (sps ps v')
in (let m'' = AST.Meta (bps, cb, (FStar_OrdSet.intersect ((fun meta ps v def emp a v' m' s c sps _20_2069 bps cb wps cw v'' -> Prins.p_cmp) meta ps v def emp () v' m' s c sps _20_2069 bps cb wps cw v'') wps ps), cw)
in (let _20_2072 = ()
in AST.D_v (m'', AST.V_opaque ((), v'', m'', s, c, sps)))))
end))
end
| AST.V_box (_20_204799, ps', v) -> begin
(let _20_2079 = if (is_empty (FStar_OrdSet.intersect ((fun meta ps v def emp _20_204799 ps' v -> Prins.p_cmp) meta ps v def emp _20_204799 ps' v) ps ps')) then begin
emp
end else begin
(slice_v_sps ((fun meta ps v def emp _20_204799 ps' v -> _20_204799) meta ps v def emp _20_204799 ps' v) ps v)
end
in (match (_20_2079) with
| AST.D_v (meta', v') -> begin
AST.D_v (AST.Meta (ps', AST.Can_b, (AST.___Meta___wps meta'), AST.Cannot_w), AST.V_box (((fun meta ps v def emp _20_204799 ps' v _20_2079 meta' v' -> meta') meta ps v def emp _20_204799 ps' v _20_2079 meta' v'), ps', v'))
end))
end
| AST.V_wire (eps, m) -> begin
AST.D_v (AST.Meta ((FStar_OrdSet.empty ((fun meta ps v def emp eps m -> Prins.p_cmp) meta ps v def emp eps m)), AST.Can_b, (FStar_OrdSet.intersect ((fun meta ps v def emp eps m -> Prins.p_cmp) meta ps v def emp eps m) eps ps), AST.Cannot_w), AST.V_wire ((FStar_OrdSet.intersect ((fun meta ps v def emp eps m -> Prins.p_cmp) meta ps v def emp eps m) eps ps), (slice_wire_sps eps ps m)))
end
| AST.V_clos (en, x, e) -> begin
AST.D_v (meta, AST.V_clos ((slice_en_sps ps en), x, e))
end
| AST.V_fix_clos (en, f, x, e) -> begin
AST.D_v (meta, AST.V_fix_clos ((slice_en_sps ps en), f, x, e))
end
| AST.V_emp_clos (_20_2095, _20_2093) -> begin
def
end
| AST.V_emp -> begin
emp
end))))
and slice_en_sps = (fun ps en -> (let _20_2100 = ()
in (fun x -> (let _20_2103 = ()
in if ((en x) = None) then begin
None
end else begin
Some ((slice_v_sps ((fun ps en _20_2100 x -> (AST.___D_v___meta (Prims.___Some___v (en x)))) ps en () x) ps (AST.___D_v___v (Prims.___Some___v (en x)))))
end))))

let slice_v_ffi = (fun p dv -> (let _20_2109 = dv
in (match (_20_2109) with
| AST.D_v (meta, v) -> begin
(slice_v meta p v)
end)))

let compose_vals_ffi = (fun dv1 dv2 -> (let _20_2114 = dv1
in (match (_20_2114) with
| AST.D_v (meta1, v1) -> begin
(let _20_2117 = dv2
in (match (_20_2117) with
| AST.D_v (meta2, v2) -> begin
(compose_vals meta1 meta2 v1 v2)
end))
end)))

let slice_v_sps_ffi = (fun ps dv -> (let _20_2122 = dv
in (match (_20_2122) with
| AST.D_v (meta, v) -> begin
(slice_v_sps meta ps v)
end)))




