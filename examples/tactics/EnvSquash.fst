module EnvSquash

open FStar.Tactics

assume val p : int -> prop

(* Testing that the binders introduced into the context when
 * splitting a VC do not have their types squashed, which causes
 * a less efficient SMT encoding, and is unneeded anyhow. *)

let test () =
    let tau () : Tac unit =
      let bs = binders_of_env (cur_env ()) in
      guard (Cons? (List.Tot.rev bs));
      let b = List.Tot.hd (List.Tot.rev bs) in
      match term_as_formula' (type_of_binder b) with
      | Exists _ _ -> ()
      | _ -> fail ("unexpected type for last binder: " ^ term_to_string (type_of_binder b))
    in
    assume (exists x. p x);
    assert_by_tactic True tau
