module Part5.IsConj

open FStar.Tactics

exception NotEq
let checkeq (#a:eqtype) (x y : a) : Tac unit =
  if x = y then () else raise NotEq

let isconj_t0 (t:term) : Tac bool =
  match inspect (maybe_unsquash_term t) with
  | Tv_App l a2 ->
    begin match inspect l with
    | Tv_App h a1 ->
      begin match inspect h with
      | Tv_FVar fv -> term_eq h (`(/\))
      | _ -> false
      end
    | _ -> false
    end
  | _ -> false

let isconj_0 () : Tac bool = isconj_t0 (cur_goal ())

let _ = assert (True /\ True)   by (checkeq (isconj_0 ()) true)
let _ = assert (True \/ True)   by (checkeq (isconj_0 ()) false)
let _ = assert (True ==> True) by (checkeq (isconj_0 ()) false)

let isconj_t1 (t:term) : Tac bool =
  match collect_app (maybe_unsquash_term t) with
  | h, [_; _] -> term_eq h (`(/\))
  | _ -> false

let isconj_1 () : Tac bool = isconj_t1 (cur_goal ())

let _ = assert (True /\ True)   by (checkeq (isconj_1 ()) true)
let _ = assert (True \/ True)   by (checkeq (isconj_1 ()) false)
let _ = assert (True ==> True) by (checkeq (isconj_1 ()) false)

//SNIPPET_START: isconj_2
(* Check if a given term is a conjunction, via term_as_formula. *)
let isconj_t (t:term) : Tac bool =
  match term_as_formula t with
  | And _ _ -> true
  | _ -> false

(* Check if the goal is a conjunction. *)
let isconj () : Tac bool = isconj_t (cur_goal ())
//SNIPPET_END: isconj_2

let _ = assert (True /\ True)  by (checkeq (isconj ()) true)
let _ = assert (True \/ True)  by (checkeq (isconj ()) false)
let _ = assert (True ==> True) by (checkeq (isconj ()) false)
