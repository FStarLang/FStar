
open Prims
exception Invalid_arg

let is_Invalid_arg = (fun _discr_ -> (match (_discr_) with
| Invalid_arg -> begin
true
end
| _ -> begin
false
end))

let _ = (let b = (Runtime.is_server ())
in if b then begin
(Runtime.establish_server SecServer.handle_connection 8888)
end else begin
(let const_meta = AST.Meta ((FStar_OrdSet.empty ((fun b -> Prins.p_cmp) b)), AST.Can_b, (FStar_OrdSet.empty ((fun b -> Prins.p_cmp) b)), AST.Can_w)
in (let init_env = (fun x -> if (x = "alice") then begin
Some (AST.D_v (const_meta, AST.V_prin (Prins.Alice)))
end else begin
if (x = "bob") then begin
Some (AST.D_v (const_meta, AST.V_prin (Prins.Bob)))
end else begin
if (x = "charlie") then begin
Some (AST.D_v (const_meta, AST.V_prin (Prins.Charlie)))
end else begin
None
end
end
end)
in (let pname = (Runtime.me ())
in (match ((init_env pname)) with
| Some (AST.D_v (_27_9, AST.V_prin (p))) -> begin
(let c = AST.Conf (AST.Target, AST.Mode (AST.Par, (FStar_OrdSet.singleton ((fun b const_meta init_env pname _27_9 p -> Prins.p_cmp) b const_meta init_env pname _27_9 p) p)), [], init_env, AST.T_exp (Prog.program), ())
in (let c' = (Interpreter.tstep_star c)
in ()))
end
| _27_17 -> begin
(Prims.raise Invalid_arg)
end))))
end)




