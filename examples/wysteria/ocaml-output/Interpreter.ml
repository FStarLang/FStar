
open Prims
let step = (fun c -> if (Semantics.pre_easpar c) then begin
Some ((Semantics.step_aspar_e1 c))
end else begin
if ((AST.is_value_ps c) && (AST.is_sframe c AST.is_F_aspar_ps)) then begin
Some ((Semantics.step_aspar_e2 c))
end else begin
if ((AST.is_value c) && (AST.is_sframe c AST.is_F_aspar_e)) then begin
Some ((Semantics.step_aspar_red c))
end else begin
if (not (((Semantics.pre_aspar c) = Semantics.NA))) then begin
Some ((Semantics.step_aspar c))
end else begin
if ((Semantics.pre_aspar_ret c) = Semantics.Do) then begin
Some ((Semantics.step_aspar_ret c))
end else begin
if (Semantics.pre_ebox c) then begin
Some ((Semantics.step_box_e1 c))
end else begin
if ((AST.is_value_ps c) && (AST.is_sframe c AST.is_F_box_ps)) then begin
Some ((Semantics.step_box_e2 c))
end else begin
if ((AST.is_value c) && (AST.is_sframe c AST.is_F_box_e)) then begin
Some ((Semantics.step_box_red c))
end else begin
if ((Semantics.pre_box c) = Semantics.Do) then begin
Some ((Semantics.step_box c))
end else begin
if (Semantics.pre_eunbox c) then begin
Some ((Semantics.step_unbox_e c))
end else begin
if ((AST.is_value c) && (AST.is_sframe c AST.is_F_unbox)) then begin
Some ((Semantics.step_unbox_red c))
end else begin
if ((Semantics.pre_unbox c) = Semantics.Do) then begin
Some ((Semantics.step_unbox c))
end else begin
if (Semantics.pre_emkwire c) then begin
Some ((Semantics.step_mkwire_e1 c))
end else begin
if ((AST.is_value_ps c) && (AST.is_sframe c AST.is_F_mkwire_ps)) then begin
Some ((Semantics.step_mkwire_e2 c))
end else begin
if ((AST.is_value c) && (AST.is_sframe c AST.is_F_mkwire_e)) then begin
Some ((Semantics.step_mkwire_red c))
end else begin
if ((Semantics.pre_mkwire c) = Semantics.Do) then begin
Some ((Semantics.step_mkwire c))
end else begin
if (Semantics.pre_eprojwire c) then begin
Some ((Semantics.step_projwire_e1 c))
end else begin
if ((AST.is_value_p c) && (AST.is_sframe c AST.is_F_projwire_p)) then begin
Some ((Semantics.step_projwire_e2 c))
end else begin
if ((AST.is_value c) && (AST.is_sframe c AST.is_F_projwire_e)) then begin
Some ((Semantics.step_projwire_red c))
end else begin
if ((Semantics.pre_projwire c) = Semantics.Do) then begin
Some ((Semantics.step_projwire c))
end else begin
if (Semantics.pre_econcatwire c) then begin
Some ((Semantics.step_concatwire_e1 c))
end else begin
if ((AST.is_value c) && (AST.is_sframe c AST.is_F_concatwire_e1)) then begin
Some ((Semantics.step_concatwire_e2 c))
end else begin
if ((AST.is_value c) && (AST.is_sframe c AST.is_F_concatwire_e2)) then begin
Some ((Semantics.step_concatwire_red c))
end else begin
if ((Semantics.pre_concatwire c) = Semantics.Do) then begin
Some ((Semantics.step_concatwire c))
end else begin
if (Semantics.pre_econst c) then begin
Some ((Semantics.step_const c))
end else begin
if (Semantics.pre_evar c) then begin
Some ((Semantics.step_var c))
end else begin
if (Semantics.pre_elet c) then begin
Some ((Semantics.step_let_e1 c))
end else begin
if ((AST.is_value c) && (AST.is_sframe c AST.is_F_let)) then begin
Some ((Semantics.step_let_red c))
end else begin
if (Semantics.pre_let c) then begin
Some ((Semantics.step_let c))
end else begin
if (Semantics.pre_eabs c) then begin
Some ((Semantics.step_abs c))
end else begin
if (Semantics.pre_efix c) then begin
Some ((Semantics.step_fix c))
end else begin
if (Semantics.pre_eempabs c) then begin
Some ((Semantics.step_empabs c))
end else begin
if (Semantics.pre_eapp c) then begin
Some ((Semantics.step_app_e1 c))
end else begin
if ((AST.is_value c) && (AST.is_sframe c AST.is_F_app_e1)) then begin
Some ((Semantics.step_app_e2 c))
end else begin
if ((AST.is_value c) && (AST.is_sframe c AST.is_F_app_e2)) then begin
Some ((Semantics.step_app_red c))
end else begin
if (Semantics.pre_app c) then begin
Some ((Semantics.step_app c))
end else begin
if (Semantics.pre_effi c) then begin
Some ((Semantics.step_ffi_e c))
end else begin
if ((AST.is_value c) && (AST.is_sframe c AST.is_F_ffi)) then begin
Some ((Semantics.step_ffi_l c))
end else begin
if ((Semantics.pre_ffi c) = Semantics.Do) then begin
Some ((Semantics.step_ffi c))
end else begin
if (Semantics.pre_econd c) then begin
Some ((Semantics.step_cond_e c))
end else begin
if ((AST.is_value c) && (AST.is_sframe c AST.is_F_cond)) then begin
Some ((Semantics.step_cond_red c))
end else begin
if (Semantics.pre_cond c) then begin
Some ((Semantics.step_cond c))
end else begin
if (Semantics.pre_eassec c) then begin
Some ((Semantics.step_assec_e1 c))
end else begin
if ((AST.is_value_ps c) && (AST.is_sframe c AST.is_F_assec_ps)) then begin
Some ((Semantics.step_assec_e2 c))
end else begin
if ((AST.is_value c) && (AST.is_sframe c AST.is_F_assec_e)) then begin
Some ((Semantics.step_assec_red c))
end else begin
if (not (((Semantics.pre_assec c) = Semantics.NA))) then begin
Some ((Semantics.step_assec c))
end else begin
if ((AST.is_value c) && (AST.is_sframe c AST.is_F_assec_ret)) then begin
Some ((Semantics.step_assec_ret c))
end else begin
None
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end)

let step_correctness = (fun c -> (let c' = (Semantics.v_of_some (step c))
in if (Semantics.pre_easpar c) then begin
Semantics.C_aspar_ps (c, c')
end else begin
if ((AST.is_value_ps c) && (AST.is_sframe c AST.is_F_aspar_ps)) then begin
Semantics.C_aspar_e (c, c')
end else begin
if ((AST.is_value c) && (AST.is_sframe c AST.is_F_aspar_e)) then begin
Semantics.C_aspar_red (c, c')
end else begin
if (not (((Semantics.pre_aspar c) = Semantics.NA))) then begin
Semantics.C_aspar_beta (c, c')
end else begin
if ((Semantics.pre_aspar_ret c) = Semantics.Do) then begin
Semantics.C_aspar_ret (c, c')
end else begin
if (Semantics.pre_ebox c) then begin
Semantics.C_box_ps (c, c')
end else begin
if ((AST.is_value_ps c) && (AST.is_sframe c AST.is_F_box_ps)) then begin
Semantics.C_box_e (c, c')
end else begin
if ((AST.is_value c) && (AST.is_sframe c AST.is_F_box_e)) then begin
Semantics.C_box_red (c, c')
end else begin
if ((Semantics.pre_box c) = Semantics.Do) then begin
Semantics.C_box_beta (c, c')
end else begin
if (Semantics.pre_eunbox c) then begin
Semantics.C_unbox (c, c')
end else begin
if ((AST.is_value c) && (AST.is_sframe c AST.is_F_unbox)) then begin
Semantics.C_unbox_red (c, c')
end else begin
if ((Semantics.pre_unbox c) = Semantics.Do) then begin
Semantics.C_unbox_beta (c, c')
end else begin
if (Semantics.pre_emkwire c) then begin
Semantics.C_mkwire_e1 (c, c')
end else begin
if ((AST.is_value_ps c) && (AST.is_sframe c AST.is_F_mkwire_ps)) then begin
Semantics.C_mkwire_e2 (c, c')
end else begin
if ((AST.is_value c) && (AST.is_sframe c AST.is_F_mkwire_e)) then begin
Semantics.C_mkwire_red (c, c')
end else begin
if ((Semantics.pre_mkwire c) = Semantics.Do) then begin
Semantics.C_mkwire_beta (c, c')
end else begin
if (Semantics.pre_eprojwire c) then begin
Semantics.C_projwire_p (c, c')
end else begin
if ((AST.is_value_p c) && (AST.is_sframe c AST.is_F_projwire_p)) then begin
Semantics.C_projwire_e (c, c')
end else begin
if ((AST.is_value c) && (AST.is_sframe c AST.is_F_projwire_e)) then begin
Semantics.C_projwire_red (c, c')
end else begin
if ((Semantics.pre_projwire c) = Semantics.Do) then begin
Semantics.C_projwire_beta (c, c')
end else begin
if (Semantics.pre_econcatwire c) then begin
Semantics.C_concatwire_e1 (c, c')
end else begin
if ((AST.is_value c) && (AST.is_sframe c AST.is_F_concatwire_e1)) then begin
Semantics.C_concatwire_e2 (c, c')
end else begin
if ((AST.is_value c) && (AST.is_sframe c AST.is_F_concatwire_e2)) then begin
Semantics.C_concatwire_red (c, c')
end else begin
if ((Semantics.pre_concatwire c) = Semantics.Do) then begin
Semantics.C_concatwire_beta (c, c')
end else begin
if (Semantics.pre_econst c) then begin
Semantics.C_const (c, c')
end else begin
if (Semantics.pre_evar c) then begin
Semantics.C_var (c, c')
end else begin
if (Semantics.pre_elet c) then begin
Semantics.C_let_e1 (c, c')
end else begin
if ((AST.is_value c) && (AST.is_sframe c AST.is_F_let)) then begin
Semantics.C_let_red (c, c')
end else begin
if (Semantics.pre_let c) then begin
Semantics.C_let_beta (c, c')
end else begin
if (Semantics.pre_eabs c) then begin
Semantics.C_abs (c, c')
end else begin
if (Semantics.pre_efix c) then begin
Semantics.C_fix (c, c')
end else begin
if (Semantics.pre_eempabs c) then begin
Semantics.C_empabs (c, c')
end else begin
if (Semantics.pre_eapp c) then begin
Semantics.C_app_e1 (c, c')
end else begin
if ((AST.is_value c) && (AST.is_sframe c AST.is_F_app_e1)) then begin
Semantics.C_app_e2 (c, c')
end else begin
if ((AST.is_value c) && (AST.is_sframe c AST.is_F_app_e2)) then begin
Semantics.C_app_red (c, c')
end else begin
if (Semantics.pre_app c) then begin
Semantics.C_app_beta (c, c')
end else begin
if (Semantics.pre_effi c) then begin
Semantics.C_ffi_e (c, c')
end else begin
if ((AST.is_value c) && (AST.is_sframe c AST.is_F_ffi)) then begin
Semantics.C_ffi_l (c, c')
end else begin
if ((Semantics.pre_ffi c) = Semantics.Do) then begin
Semantics.C_ffi_beta (c, c')
end else begin
if (Semantics.pre_econd c) then begin
Semantics.C_cond_e (c, c')
end else begin
if ((AST.is_value c) && (AST.is_sframe c AST.is_F_cond)) then begin
Semantics.C_cond_red (c, c')
end else begin
if (Semantics.pre_cond c) then begin
Semantics.C_cond_beta (c, c')
end else begin
if (Semantics.pre_eassec c) then begin
Semantics.C_assec_ps (c, c')
end else begin
if ((AST.is_value_ps c) && (AST.is_sframe c AST.is_F_assec_ps)) then begin
Semantics.C_assec_e (c, c')
end else begin
if ((AST.is_value c) && (AST.is_sframe c AST.is_F_assec_e)) then begin
Semantics.C_assec_red (c, c')
end else begin
if (not (((Semantics.pre_assec c) = Semantics.NA))) then begin
Semantics.C_assec_beta (c, c')
end else begin
Semantics.C_assec_ret (c, c')
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end))

let rec step_star = (fun c -> (let c' = (step c)
in (match (c') with
| Some (c') -> begin
(step_star c')
end
| None -> begin
(let _23_12 = (FStar_IO.print_string "Could not sstep\n")
in Some (c))
end)))

let do_sec_comp = (fun p r -> (let _23_20 = (Runtime.open_connection 8888)
in (match (_23_20) with
| (c_in, c_out) -> begin
(let _23_21 = (Runtime.client_write c_out p r)
in (Runtime.client_read c_in))
end)))

let tstep = (fun c -> (let _23_31 = c
in (match (_23_31) with
| AST.Conf (l, m, s, en, t, _23_25) -> begin
if ((AST.is_T_red t) && (AST.is_R_assec (AST.___T_red___r t))) then begin
(let dv = (do_sec_comp (Prims.___Some___v (FStar_OrdSet.choose ((fun c _23_31 l m s en t _23_25 -> Prins.p_cmp) c _23_31 l m s en t ()) (AST.___Mode___ps m))) (AST.___T_red___r t))
in Some (AST.Conf (l, m, s, en, AST.T_val ((AST.___D_v___meta dv), (AST.___D_v___v dv)), ())))
end else begin
(step c)
end
end)))

let rec tstep_star = (fun c -> (let c' = (tstep c)
in (match (c') with
| Some (c') -> begin
(tstep_star c')
end
| None -> begin
(let _23_38 = (FStar_IO.print_string "Could not step\n")
in Some (c))
end)))




