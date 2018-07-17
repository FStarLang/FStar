module AnnoyingVCs
open FStar.Tactics

assume val p : nat -> Type

let dump s =
    (* dump s; *)
    ()

assume val f : n:nat{n > 20} -> Lemma (p n)
assume val g : n:nat -> Lemma (p n)

// This must fail, we don't know if i > 20
[@expect_failure]
let test1 (i:int) =
    assume (i >= 0);
    assert (True ==> p i) by
           (fun () -> dump "1";
                   let _ = implies_intro () in
                   dump "2";
                   apply_lemma (`f)
                   )

// This should work without a guard
let test2 (i:int) =
    assume (i >= 0);
    assert (True ==> p i) by
           (fun () -> dump "1";
                   let _ = implies_intro () in
                   dump "2";
                   apply_lemma (`g);
                   dump "3";
                   qed ()
                   )
