
open Prims
exception Comp_error

let is_Comp_error = (fun _discr_ -> (match (_discr_) with
| Comp_error -> begin
true
end
| _ -> begin
false
end))

type en_map =
(Prins.prin, AST.env, Prims.unit) FStar_OrdMap.ordmap

type out_map =
(Prins.prin, Runtime.chan_out, Prims.unit) FStar_OrdMap.ordmap

type psmap_v =
(en_map * out_map * AST.varname * AST.exp)

type psmap =
(Prins.prins, psmap_v, Prims.unit) FStar_OrdMap.ordmap

type psmap_ref_t =
| Mk_ref of (Prins.prins, psmap_v, Prims.unit) FStar_OrdMap.ordmap FStar_ST.ref

let is_Mk_ref = (fun _discr_ -> (match (_discr_) with
| Mk_ref (_) -> begin
true
end
| _ -> begin
false
end))

let ___Mk_ref___r = (fun projectee -> (match (projectee) with
| Mk_ref (_24_3) -> begin
_24_3
end))

let psmap_ref = (let _52_8 = (FStar_ST.alloc (FStar_OrdMap.empty Prins.ps_cmp))
in Mk_ref (_52_8))

let rec send_output = (fun meta ps out_m v -> (let _24_14 = (FStar_OrdSet.choose ((fun meta ps out_m v -> Prins.p_cmp) meta ps out_m v) ps)
in (match (_24_14) with
| Some (p) -> begin
(let _24_16 = (FStar_OrdMap.select ((fun meta ps out_m v _24_14 p -> Prins.p_cmp) meta ps out_m v _24_14 p) p out_m)
in (match (_24_16) with
| Some (out) -> begin
(let ps_rest = (FStar_OrdSet.remove ((fun meta ps out_m v _24_14 p _24_16 out -> Prins.p_cmp) meta ps out_m v _24_14 p _24_16 out) p ps)
in (let out_m' = (FStar_OrdMap.remove ((fun meta ps out_m v _24_14 p _24_16 out ps_rest -> Prins.p_cmp) meta ps out_m v _24_14 p _24_16 out ps_rest) p out_m)
in (let _24_19 = (Runtime.server_write out (Semantics.slice_v ((fun meta ps out_m v _24_14 p _24_16 out ps_rest out_m' -> meta) meta ps out_m v _24_14 p _24_16 out ps_rest out_m') p v))
in if (ps_rest = (FStar_OrdSet.empty ((fun meta ps out_m v _24_14 p _24_16 out ps_rest out_m' -> Prins.p_cmp) meta ps out_m v _24_14 p _24_16 out ps_rest out_m'))) then begin
()
end else begin
(send_output meta ps_rest out_m' v)
end)))
end))
end)))

let is_sterminal = (fun _24_31 -> (match (_24_31) with
| AST.Conf (_24_30, _24_28, s, _24_25, t, _24_22) -> begin
((s = []) && (AST.is_T_val t))
end))

let do_sec_comp = (fun ps env_m out_m x e _24_42 -> (let en = (AST.update_env ((fun ps env_m out_m x e _24_42 -> AST.Meta ((FStar_OrdSet.empty Prins.p_cmp), AST.Can_b, (FStar_OrdSet.empty Prins.p_cmp), AST.Can_w)) ps env_m out_m x e ()) (Semantics.compose_envs_m ps env_m) x AST.V_unit)
in (let conf = AST.Conf (AST.Target, AST.Mode (AST.Sec, ps), [], en, AST.T_exp (e), ())
in (let c_opt = (Interpreter.step_star conf)
in if ((Semantics.is_Some c_opt) && (is_sterminal (Prims.___Some___v c_opt))) then begin
(let _24_47 = (send_output ((fun ps env_m out_m x e _24_42 en conf c_opt -> (AST.___T_val___meta (AST.___Conf___t (Prims.___Some___v c_opt)))) ps env_m out_m x e () en conf c_opt) ps out_m (AST.___T_val___v (AST.___Conf___t (Prims.___Some___v c_opt))))
in ())
end else begin
(Prims.raise Comp_error)
end))))

let handle_connection = (fun c_in c_out -> (let _24_51 = (FStar_IO.print_string "Received a connection\n")
in (let _24_58 = (Runtime.server_read c_in)
in (match (_24_58) with
| (p, AST.R_assec (meta, ps, v)) -> begin
(let _24_59 = (FStar_IO.print_string "Received inputs\n")
in (let _24_64 = (AST.get_en_b ((fun c_in c_out _24_58 p meta ps v -> meta) c_in c_out _24_58 p meta ps v) v)
in (match (_24_64) with
| (en, x, e) -> begin
(let psmap_ref = (___Mk_ref___r psmap_ref)
in (let _24_78 = if (let _52_85 = (FStar_ST.read psmap_ref)
in (FStar_OrdMap.contains ((fun c_in c_out _24_58 p meta ps v _24_64 en x e psmap_ref -> Prins.ps_cmp) c_in c_out _24_58 p meta ps v _24_64 en x e psmap_ref) ps _52_85)) then begin
(let _24_71 = (let _52_89 = (FStar_ST.read psmap_ref)
in (FStar_OrdMap.select ((fun c_in c_out _24_58 p meta ps v _24_64 en x e psmap_ref -> Prins.ps_cmp) c_in c_out _24_58 p meta ps v _24_64 en x e psmap_ref) ps _52_89))
in (match (_24_71) with
| Some (env_m', out_m', x', e') -> begin
(let env_m' = (FStar_OrdMap.update ((fun c_in c_out _24_58 p meta ps v _24_64 en x e psmap_ref _24_71 env_m' out_m' x' e' -> Prins.p_cmp) c_in c_out _24_58 p meta ps v _24_64 en x e psmap_ref _24_71 env_m' out_m' x' e') p en env_m')
in (let out_m' = (FStar_OrdMap.update ((fun c_in c_out _24_58 p meta ps v _24_64 en x e psmap_ref _24_71 env_m' out_m' x' e' env_m' -> Prins.p_cmp) c_in c_out _24_58 p meta ps v _24_64 en x e psmap_ref _24_71 env_m' out_m' x' e' env_m') p c_out out_m')
in (env_m', out_m', x', e')))
end))
end else begin
((FStar_OrdMap.update ((fun c_in c_out _24_58 p meta ps v _24_64 en x e psmap_ref -> ((fun c_in c_out _24_58 p meta ps v _24_64 en x e psmap_ref -> Prins.p_cmp) c_in c_out _24_58 p meta ps v _24_64 en x e psmap_ref)) c_in c_out _24_58 p meta ps v _24_64 en x e psmap_ref) p en (FStar_OrdMap.empty ((fun c_in c_out _24_58 p meta ps v _24_64 en x e psmap_ref -> ((fun c_in c_out _24_58 p meta ps v _24_64 en x e psmap_ref -> Prins.p_cmp) c_in c_out _24_58 p meta ps v _24_64 en x e psmap_ref)) c_in c_out _24_58 p meta ps v _24_64 en x e psmap_ref))), (FStar_OrdMap.update ((fun c_in c_out _24_58 p meta ps v _24_64 en x e psmap_ref -> ((fun c_in c_out _24_58 p meta ps v _24_64 en x e psmap_ref -> Prins.p_cmp) c_in c_out _24_58 p meta ps v _24_64 en x e psmap_ref)) c_in c_out _24_58 p meta ps v _24_64 en x e psmap_ref) p c_out (FStar_OrdMap.empty ((fun c_in c_out _24_58 p meta ps v _24_64 en x e psmap_ref -> ((fun c_in c_out _24_58 p meta ps v _24_64 en x e psmap_ref -> Prins.p_cmp) c_in c_out _24_58 p meta ps v _24_64 en x e psmap_ref)) c_in c_out _24_58 p meta ps v _24_64 en x e psmap_ref))), x, e)
end
in (match (_24_78) with
| (env_m', out_m', x', e') -> begin
if ((FStar_OrdMap.size ((fun c_in c_out _24_58 p meta ps v _24_64 en x e psmap_ref _24_78 env_m' out_m' x' e' -> Prins.p_cmp) c_in c_out _24_58 p meta ps v _24_64 en x e psmap_ref _24_78 env_m' out_m' x' e') env_m') = (FStar_OrdSet.size ((fun c_in c_out _24_58 p meta ps v _24_64 en x e psmap_ref _24_78 env_m' out_m' x' e' -> Prins.p_cmp) c_in c_out _24_58 p meta ps v _24_64 en x e psmap_ref _24_78 env_m' out_m' x' e') ps)) then begin
(let _24_79 = ()
in (let _24_81 = ()
in (let _24_83 = (FStar_IO.print_string "Running secure computation\n")
in (let _24_85 = (Runtime.create_thread (do_sec_comp ps env_m' out_m' x e))
in (let _52_166 = (let _52_165 = (FStar_ST.read psmap_ref)
in (FStar_OrdMap.remove ((fun c_in c_out _24_58 p meta ps v _24_64 en x e psmap_ref _24_78 env_m' out_m' x' e' _24_79 _24_81 -> Prins.ps_cmp) c_in c_out _24_58 p meta ps v _24_64 en x e psmap_ref _24_78 env_m' out_m' x' e' () ()) ps _52_165))
in (FStar_ST.op_Colon_Equals psmap_ref _52_166))))))
end else begin
(let _52_178 = (let _52_177 = (FStar_ST.read psmap_ref)
in (FStar_OrdMap.update ((fun c_in c_out _24_58 p meta ps v _24_64 en x e psmap_ref _24_78 env_m' out_m' x' e' -> Prins.ps_cmp) c_in c_out _24_58 p meta ps v _24_64 en x e psmap_ref _24_78 env_m' out_m' x' e') ps (env_m', out_m', x', e') _52_177))
in (FStar_ST.op_Colon_Equals psmap_ref _52_178))
end
end)))
end)))
end))))




