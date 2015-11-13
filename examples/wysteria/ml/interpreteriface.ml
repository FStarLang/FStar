open Prins
open AST
open Prog

exception Interpreteriface_error of string

let cast x = Obj.magic x

let project_value_content (dv:dvalue) :Obj.t =
  let D_v (_, v) = dv in
  let content =
    match v with
      | V_prin p -> cast p
      | V_eprins eps -> cast eps
      | V_unit -> cast ()
      | V_bool b -> cast b
      | V_opaque (_, v, _, _, _, _) -> cast v
      | _ -> raise (Interpreteriface_error ("Interpreteriface does not handle this value type"))
  in
  content


let init_env =
  fun x ->
    if name_of_var x = "alice" then Some (D_v (const_meta, V_prin Alice))
    else if name_of_var x = "bob" then Some (D_v (const_meta, V_prin Bob))
    else if name_of_var x = "charlie" then Some (D_v (const_meta, V_prin Charlie))
    else None
           
let run (p:prin) (fn:string) (t:typ) (l:exp list) :dvalue =
  let e_main = mk_app (mk_var fn t) (List.hd l) in
  let e_main = List.fold_left (fun acc e -> mk_app acc e) e_main (List.tl l) in
  let e_c = List.fold_left (fun acc (x, t, e) ->
    mk_let (mk_varname x t) e acc
  ) e_main (List.rev program) in
  let e = mk_projwire (mk_const (C_prin p)) e_c in
  let dv_opt = Interpreter.run p init_env e in
  match dv_opt with
    | None    -> raise Not_found
    | Some dv -> dv
