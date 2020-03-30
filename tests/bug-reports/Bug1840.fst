module Bug1840

open FStar.Tactics

(* Simpler repro *)
let resolve bs : Tac unit =
  let rec try_binders (bs: binders): Tac unit =
    match bs with
    | [] -> ()
    | b :: bs -> try_binders bs
  in
  try_binders bs

(* Original *)
let resolve' (): Tac unit =
  // dump "blah"
  let rec try_binders (bs: binders): Tac unit =
    match bs with
    | [] -> fail "found no suitable type class"
    | b :: bs ->
        let b, _ = inspect_binder b in
        try exact (pack_ln (Tv_BVar b))
        with | TacticFailure _ -> try_binders bs
             | _ -> ()
  in
  try_binders (binders_of_env (cur_env ()))
