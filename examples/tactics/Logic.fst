module Logic

open FStar.Tactics


let tau () : Tac unit =
    let h = implies_intro () in
    right ();
    and_elim (binder_to_term h);
    let h1 = implies_intro () in
    let _  = implies_intro () in
    apply (`FStar.Squash.return_squash);
    exact (binder_to_term h1);
    qed ()

let test phi psi xi =
   assert (phi /\ xi ==> psi \/ phi) by tau ()
