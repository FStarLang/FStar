module Bug1840

open FStar.Tactics

(* Simpler repro *)
let resolve bs : Tac unit =
  let rec try_namedv (vs: list namedv): Tac unit =
    match vs with
    | [] -> ()
    | v :: vs -> try_namedv vs
  in
  try_namedv bs

(* Original *)
let resolve' (): Tac unit =
  // dump "blah"
  let rec try_namedv (vs: list binding): Tac unit =
    match vs with
    | [] -> fail "found no suitable type class"
    | v :: vs ->
        try exact (pack (Tv_Var (binding_to_namedv v)))
        with | TacticFailure _ -> try_namedv vs
             | _ -> ()
  in
  try_namedv (vars_of_env (cur_env ()))
