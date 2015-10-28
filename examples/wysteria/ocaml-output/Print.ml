
open Prims
let prin_to_string = (fun _22_1 -> (match (_22_1) with
| Prins.Alice -> begin
"alice"
end
| Prins.Bob -> begin
"bob"
end
| Prins.Charlie -> begin
"charlie"
end
| Prins.Dave -> begin
"dave"
end
| Prins.Evelyn -> begin
"evelyn"
end
| Prins.Fred -> begin
"fred"
end))

let rec prins_to_string_helper = (fun eps s -> if (eps = (FStar_OrdSet.empty ((fun eps s -> Prins.p_cmp) eps s))) then begin
s
end else begin
(let _22_20 = (FStar_OrdSet.choose ((fun eps s -> Prins.p_cmp) eps s) eps)
in (match (_22_20) with
| Some (p) -> begin
(let eps' = (FStar_OrdSet.remove ((fun eps s _22_20 p -> Prins.p_cmp) eps s _22_20 p) p eps)
in (let s' = (FStar_String.strcat (FStar_String.strcat s (prin_to_string p)) ";")
in (prins_to_string_helper eps' s')))
end))
end)

let prins_to_string = (fun eps -> (FStar_String.strcat (FStar_String.strcat "{" (prins_to_string_helper eps "")) "}"))

let tagged_unary_to_string = (fun tag e -> (FStar_String.strcat (FStar_String.strcat (FStar_String.strcat tag " (") e) ")"))

let tagged_binary_to_string = (fun tag e1 e2 -> (FStar_String.strcat (FStar_String.strcat (FStar_String.strcat (FStar_String.strcat (FStar_String.strcat tag " (") e1) ") (") e2) ")"))

let tagged_ternary_to_string = (fun tag e1 e2 e3 -> (FStar_String.strcat (FStar_String.strcat (FStar_String.strcat (FStar_String.strcat (FStar_String.strcat (FStar_String.strcat (FStar_String.strcat tag " (") e1) ") (") e2) ") (") e3) ")"))

let const_to_string = (fun _22_2 -> (match (_22_2) with
| AST.C_prin (p) -> begin
(tagged_unary_to_string "C_prin" (prin_to_string p))
end
| AST.C_eprins (eps) -> begin
(tagged_unary_to_string "C_eprins" (prins_to_string eps))
end
| AST.C_unit (_22_39) -> begin
"C_unit"
end
| AST.C_bool (b) -> begin
(tagged_unary_to_string "C_bool" (Prims.string_of_bool b))
end
| AST.C_opaque (_, _22_44) -> begin
"C_opaque"
end))

let rec exp_to_string = (fun _22_3 -> (match (_22_3) with
| AST.E_aspar (ps, e) -> begin
(tagged_binary_to_string "E_aspar" (exp_to_string ps) (exp_to_string e))
end
| AST.E_assec (ps, e) -> begin
(tagged_binary_to_string "E_assec" (exp_to_string ps) (exp_to_string e))
end
| AST.E_box (ps, e) -> begin
(tagged_binary_to_string "E_box" (exp_to_string ps) (exp_to_string e))
end
| AST.E_unbox (e) -> begin
(tagged_unary_to_string "E_unbox" (exp_to_string e))
end
| AST.E_mkwire (e1, e2) -> begin
(tagged_binary_to_string "E_mkwire" (exp_to_string e1) (exp_to_string e2))
end
| AST.E_projwire (e1, e2) -> begin
(tagged_binary_to_string "E_projwire" (exp_to_string e1) (exp_to_string e2))
end
| AST.E_concatwire (e1, e2) -> begin
(tagged_binary_to_string "E_concatwire" (exp_to_string e1) (exp_to_string e2))
end
| AST.E_const (c) -> begin
(tagged_unary_to_string "E_const" (const_to_string c))
end
| AST.E_var (x) -> begin
(tagged_unary_to_string "E_var" x)
end
| AST.E_let (x, e1, e2) -> begin
(tagged_ternary_to_string "E_let" x (exp_to_string e1) (exp_to_string e2))
end
| AST.E_abs (x, e) -> begin
(tagged_binary_to_string "E_abs" x (exp_to_string e))
end
| AST.E_fix (f, x, e) -> begin
(tagged_ternary_to_string "E_fix" f x (exp_to_string e))
end
| AST.E_empabs (x, e) -> begin
(tagged_binary_to_string "E_empabs" x (exp_to_string e))
end
| AST.E_app (e1, e2) -> begin
(tagged_binary_to_string "E_app" (exp_to_string e1) (exp_to_string e2))
end
| AST.E_ffi (_, _, n, fname, _22_96, l, _22_93) -> begin
(tagged_ternary_to_string "E_ffi" (Prims.string_of_int n) fname (exp_list_to_string l))
end
| AST.E_cond (e, e1, e2) -> begin
(tagged_ternary_to_string "E_cond" (exp_to_string e) (exp_to_string e1) (exp_to_string e2))
end))
and exp_list_to_string_helper = (fun l s -> (match (l) with
| [] -> begin
s
end
| hd::tl -> begin
(let s' = (FStar_String.strcat (FStar_String.strcat s (exp_to_string hd)) "; ")
in (exp_list_to_string_helper tl s'))
end))
and exp_list_to_string = (fun l -> (let s = (exp_list_to_string_helper l "")
in (FStar_String.strcat (FStar_String.strcat "[" s) "]")))

let v_meta_to_string = (fun m -> (let _22_120 = m
in (match (_22_120) with
| AST.Meta (bps, cb, wps, cw) -> begin
(let scb = if (cb = AST.Can_b) then begin
"Can_b"
end else begin
"Cannot_b"
end
in (let scw = if (cw = AST.Can_w) then begin
"Can_w"
end else begin
"Cannot_w"
end
in (FStar_String.strcat (FStar_String.strcat (FStar_String.strcat (FStar_String.strcat (FStar_String.strcat (FStar_String.strcat (FStar_String.strcat "Meta " scb) " ") (prins_to_string bps)) " ") scw) " ") (prins_to_string wps))))
end)))

let rec value_to_string = (fun meta v -> (let s = (match (v) with
| AST.V_prin (p) -> begin
(tagged_unary_to_string "V_prin" (prin_to_string p))
end
| AST.V_eprins (eps) -> begin
(tagged_unary_to_string "V_eprins" (prins_to_string eps))
end
| AST.V_unit -> begin
"V_unit"
end
| AST.V_bool (b) -> begin
(tagged_unary_to_string "V_bool" (Prims.string_of_bool b))
end
| AST.V_opaque (_, _22_149, _22_147, _22_145, _22_143, _22_141) -> begin
"V_opaque"
end
| AST.V_box (_22_8343, ps, v') -> begin
(tagged_binary_to_string "V_box" (prins_to_string ps) (value_to_string ((fun meta v _22_8343 ps v' -> _22_8343) meta v _22_8343 ps v') v'))
end
| AST.V_wire (eps, m) -> begin
(tagged_unary_to_string "V_wire" (v_wire_to_string eps m))
end
| AST.V_clos (_22_162, x, _22_159) -> begin
(tagged_unary_to_string "V_clos" x)
end
| AST.V_fix_clos (_22_168, f, x, e) -> begin
(tagged_binary_to_string "V_fix_clos" f x)
end
| AST.V_emp_clos (x, _22_171) -> begin
(tagged_unary_to_string "V_emp_clos" x)
end
| AST.V_emp -> begin
"V_emp"
end)
in (FStar_String.strcat (FStar_String.strcat (FStar_String.strcat s " (") (v_meta_to_string meta)) ")")))
and v_wire_to_string_helper = (fun eps eps' m s -> if (eps' = (FStar_OrdSet.empty ((fun eps eps' m s -> Prins.p_cmp) eps eps' m s))) then begin
s
end else begin
(let _22_181 = (FStar_OrdSet.choose ((fun eps eps' m s -> Prins.p_cmp) eps eps' m s) eps')
in (match (_22_181) with
| Some (p) -> begin
(let eps'' = (FStar_OrdSet.remove ((fun eps eps' m s _22_181 p -> Prins.p_cmp) eps eps' m s _22_181 p) p eps')
in (let _22_184 = (FStar_OrdMap.select ((fun eps eps' m s _22_181 p eps'' -> Prins.p_cmp) eps eps' m s _22_181 p eps'') p m)
in (match (_22_184) with
| Some (v) -> begin
(let _22_185 = ()
in (let s' = (FStar_String.strcat (FStar_String.strcat (FStar_String.strcat (FStar_String.strcat s (prin_to_string p)) ":") (value_to_string ((fun eps eps' m s _22_181 p eps'' _22_184 v _22_185 -> AST.Meta ((FStar_OrdSet.empty Prins.p_cmp), AST.Can_b, (FStar_OrdSet.empty Prins.p_cmp), AST.Can_w)) eps eps' m s _22_181 p eps'' _22_184 v ()) v)) "; ")
in (v_wire_to_string_helper eps eps'' m s')))
end)))
end))
end)
and v_wire_to_string = (fun eps m -> (v_wire_to_string_helper eps eps m ""))

let redex_to_string = (fun _22_4 -> (match (_22_4) with
| AST.R_aspar (_22_13212, _22_194, _22_192) -> begin
"R_aspar"
end
| AST.R_assec (_22_13244, _22_199, _22_197) -> begin
"R_assec"
end
| AST.R_box (_22_13276, _22_204, _22_202) -> begin
"R_box"
end
| AST.R_unbox (_22_13308, _22_207) -> begin
"R_unbox"
end
| AST.R_mkwire (_22_13333, _22_212, _22_210) -> begin
"R_mkwire"
end
| AST.R_projwire (_22_13365, _22_217, _22_215) -> begin
"R_projwire"
end
| AST.R_concatwire (_22_13394, _22_13395, _22_222, _22_220) -> begin
"R_concatwire"
end
| AST.R_let (_22_13428, _22_229, _22_227, _22_225) -> begin
"R_let"
end
| AST.R_app (_22_13461, _22_13462, _22_234, _22_232) -> begin
"R_app"
end
| AST.R_ffi (_, _, _22_243, _22_241, _22_239, _22_237) -> begin
"R_ffi"
end
| AST.R_cond (_22_13532, _22_252, _22_250, _22_248) -> begin
"R_cond"
end))

let as_mode_to_string = (fun _22_5 -> (match (_22_5) with
| AST.Par -> begin
"par"
end
| AST.Sec -> begin
"sec"
end))

let mode_to_string = (fun _22_259 -> (match (_22_259) with
| AST.Mode (as_m, ps) -> begin
(FStar_String.strcat (FStar_String.strcat (FStar_String.strcat (as_mode_to_string as_m) "(") (prins_to_string ps)) ")")
end))

let frame'_to_string = (fun _22_6 -> (match (_22_6) with
| AST.F_aspar_ps (_22_262) -> begin
"F_aspar_ps"
end
| AST.F_aspar_e (_22_265) -> begin
"F_aspar_e"
end
| AST.F_aspar_ret (_22_268) -> begin
"F_aspar_ret"
end
| AST.F_assec_ps (_22_271) -> begin
"F_assec_ps"
end
| AST.F_assec_e (_22_274) -> begin
"F_assec_e"
end
| AST.F_assec_ret -> begin
"F_assec_ret"
end
| AST.F_box_ps (_22_278) -> begin
"F_box_ps"
end
| AST.F_box_e (_22_281) -> begin
"F_box_e"
end
| AST.F_unbox -> begin
"F_unbox"
end
| AST.F_mkwire_ps (_22_285) -> begin
"F_mkwire_ps"
end
| AST.F_mkwire_e (_22_288) -> begin
"F_mkwire_w"
end
| AST.F_projwire_p (_22_291) -> begin
"F_projwire_p"
end
| AST.F_projwire_e (_22_294) -> begin
"F_projwire_e"
end
| AST.F_concatwire_e1 (_22_297) -> begin
"F_concatwire_e1"
end
| AST.F_concatwire_e2 (_22_14471, _22_300) -> begin
"F_concatwire_e2"
end
| AST.F_let (_22_305, _22_303) -> begin
"F_let"
end
| AST.F_app_e1 (_22_308) -> begin
"F_app_e1"
end
| AST.F_app_e2 (_22_14540, _22_311) -> begin
"F_app_e2"
end
| AST.F_ffi (_, _, _22_322, _22_320, _22_318, _22_316, _22_314) -> begin
"F_ffi"
end
| AST.F_cond (_22_329, _22_327) -> begin
"F_cond"
end))

let frame_to_string = (fun _22_337 -> (match (_22_337) with
| AST.Frame (m, _22_335, f, _22_332) -> begin
(FStar_String.strcat (FStar_String.strcat (FStar_String.strcat (FStar_String.strcat "Frame (" (mode_to_string m)) ") (") (frame'_to_string f)) ")")
end))

let stack_to_string = (fun _22_7 -> (match (_22_7) with
| [] -> begin
"[]"
end
| f::_22_341 -> begin
(frame_to_string f)
end))

let term_to_string = (fun _22_8 -> (match (_22_8) with
| AST.T_exp (e) -> begin
(tagged_unary_to_string "T_exp" (exp_to_string e))
end
| AST.T_red (r) -> begin
(tagged_unary_to_string "T_red" (redex_to_string r))
end
| AST.T_val (_22_15416, v) -> begin
(tagged_unary_to_string "T_val" (value_to_string ((fun _22_8 _22_15416 v -> _22_15416) _22_8 _22_15416 v) v))
end
| AST.T_sec_wait -> begin
"T_sec_wait"
end))

let config_to_string = (fun _22_360 -> (match (_22_360) with
| AST.Conf (_22_359, m, s, en, t, _22_353) -> begin
(FStar_String.strcat (FStar_String.strcat (FStar_String.strcat (FStar_String.strcat (FStar_String.strcat (FStar_String.strcat "Conf (" (mode_to_string m)) ") (") (stack_to_string s)) ") (") (term_to_string t)) ")")
end))




