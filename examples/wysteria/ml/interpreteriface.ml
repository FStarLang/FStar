open Prins
open AST
open Prog

let init_env =
  fun x ->
    if name_of_var x = "alice" then Some (D_v (const_meta, V_prin Alice))
    else if name_of_var x = "bob" then Some (D_v (const_meta, V_prin Bob))
    else if name_of_var x = "charlie" then Some (D_v (const_meta, V_prin Charlie))
    else None
           
let run (p:prin) (fn:string) (t:typ) (l:exp list) :dvalue =
  let e_main = mk_app (mk_var fn t) (List.hd l) in
  let e_main = List.fold_left (fun acc e -> mk_app acc e) e_main (List.tl l) in
  let e = List.fold_left (fun acc (x, t, e) ->
    mk_let (mk_varname x t) e acc
  ) e_main (List.rev program) in
  let dv_opt = Interpreter.run p init_env e in
  match dv_opt with
    | None    -> raise Not_found
    | Some dv -> dv
