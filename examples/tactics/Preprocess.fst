module Preprocess

open FStar.Tactics

let incr_lits_by_1 (t:term) : Tac term =
    match t with
    | Tv_Const (C_Int x) -> Tv_Const (C_Int (x+1))
    | _ -> t

let test_add_1 (x:int) : int =
    _ by (exact (visit_tm incr_lits_by_1 (quote (x + 1))))

[@(preprocess_with (visit_tm incr_lits_by_1))]
let test_add_1' (x:int) : int =
    x + 1

let test () =
  assert (test_add_1' 5 == 7)

let is_fv (fv:string) (t:term) : Tac bool =
  match t with
  | Tv_FVar fv' ->
    String.concat "." (inspect_fv fv') = fv
  | _ -> false

let inst_fv_with (fv:string) (def:term) (t:term) : Tac term =
    print ("t = " ^ term_to_string t);
    match t with
    | Tv_App l (r, Q_Explicit) ->
      if is_fv fv l
      then
        let l : term = Tv_App l (def, Q_Implicit) in
        Tv_App l (r, Q_Explicit)
      else t

    | Tv_App l (r, Q_Implicit) -> t
    | _ -> t

let add_imp #x y = x + y

open FStar.Mul

[@(preprocess_with (visit_tm (inst_fv_with (`%add_imp) (`42))))]
let test3 x y z =
  let x = add_imp x in
  let y = add_imp #0 z in
  let z = add_imp y in
  x + y + z

let _ = assert_norm (test3 0 0 0 == 84)
