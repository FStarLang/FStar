module NormLHS

open FStar.Tactics

private
let trans (#t:Type) (b a c : t)
          (_ : squash (a == b))
          (_ : squash (b == c)) : squash (a == c) = ()

let norm_lhs steps : Tac unit =
    match cur_formula () with
    | Comp (Eq _) lhs _ ->
      let lhs' = norm_term steps lhs in
      apply_lemma (`trans (`#lhs'));
      trefl ()
    | _ ->
      fail "not an eq"

type unit_t = unit

let tau () = norm_lhs [delta; hnf; weak]; trefl ()

[@(postprocess_with tau)]
let test = unit_t

(* ^ defined as unit, not unit_t *)
