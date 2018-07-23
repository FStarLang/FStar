module Bug1256

open FStar.Tactics
open FStar.Squash

let my_cut (t:unit -> Tac term) : Tac unit =
    let qq = pack (Tv_FVar (pack_fv ["FStar";"Tactics";"Derived";"__cut"])) in
    let tt = pack (Tv_App qq (t (), Q_Explicit)) in
    apply tt

assume val aug : (unit -> Type0) -> Type0

let test (p:(unit -> Type0)) (q:(unit -> Type0))
   = assert_by_tactic
            (p == q ==>
             aug p ==>
             aug q)
             (fun () ->
               let eq = implies_intro () in
               let h = implies_intro () in
               (* dump "A"; *)
               my_cut (fun () -> type_of_binder h);
               (* dump "B"; *)
               rewrite eq;
               norm [];
               (* dump "C"; *)
               let hh = intro () in
               apply (quote return_squash);
               exact (pack (Tv_Var (bv_of_binder hh)));
               (* dump "D"; *)
               exact (pack (Tv_Var (bv_of_binder h))) )

[@expect_failure]
let test2 (post:(unit -> Type0))
   = assert_by_tactic
            ((post ==  (fun x -> post ())) ==>
             aug post ==>
             aug (fun x -> post ()))
             (fun () ->
               let eq = implies_intro () in
               let h = implies_intro () in
               (* dump "A"; *)
               my_cut (fun () -> type_of_binder h);
               (* dump "B"; *)
               rewrite eq;
               norm [];
               (* dump "C"; *)
               let hh = intro () in
               (* fail "HERE"; *)
               () )
