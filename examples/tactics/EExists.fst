module EExists

open FStar.Tactics
open FStar.Classical
open FStar.Squash

let pack_fv' (n:name) : Tac term = pack (Tv_FVar (pack_fv n))

let eexists (a:Type) (t:unit -> Tac a) : Tac a =
  apply_lemma (`exists_intro); later(); norm[];
  fst (divide (ngoals()-1) t dismiss)

let f1 =
  assert_by_tactic (exists x. x == 42 ==> x + 1 == 43)
  (fun _ -> eexists unit (fun _ ->
            let b = implies_intro() in
            let _ = tcut (mk_e_app (pack_fv' squash_qn) [type_of_binder b]) in
            flip();
            trefl();
            norm [primops]; trefl()
   ))

// inlining this tactic below causes the end of the world
let foo () : Tac unit =
            eexists unit (fun _ ->
            let b = implies_intro() in
            (match term_as_formula' (type_of_binder b) with
            | Comp (Eq (Some t)) x y ->
              (match inspect x, inspect y with
              | Tv_Uvar _ _, _ | _, Tv_Uvar _ _ ->
                if unify x y then (norm [primops]; trefl())
                             else fail "unexpected1"
              | _, _ -> fail "unexpected2")
            | _ -> fail "unexpected3"))

let f2 = assert_by_tactic (exists x. x == 42 ==> x + 1 == 43) foo
