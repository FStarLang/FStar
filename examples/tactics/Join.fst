module Join

open FStar.Tactics

let hard = pow2 20 == 1048576

assume val phi : Type
assume val psi : Type
assume val lem : squash hard -> Lemma phi

(* Making sure it can be proven *)
let _ = assert hard

let dump m =
    (* dump m; *)
    ()

let repeat' t = let _ = repeat t in ()
let implies_intro' () = let _ = implies_intro () in ()

let formula =
   (phi /\ (psi ==> phi) /\ phi /\ phi /\ phi /\ phi
 /\ phi /\ phi /\ phi /\ phi /\ phi /\ phi
 /\ phi /\ phi /\ phi /\ phi /\ phi /\ phi
 /\ phi /\ phi /\ phi /\ phi /\ phi /\ (False ==> phi)
 /\ phi /\ phi /\ phi /\ phi /\ phi /\ phi
 /\ phi /\ phi /\ phi /\ phi /\ phi /\ (phi ==> True)
 /\ phi /\ phi /\ phi /\ phi /\ phi /\ phi
 /\ phi /\ phi /\ phi /\ phi /\ phi /\ phi
 /\ phi /\ phi /\ phi /\ phi /\ phi /\ phi )

let tau b =
    norm [delta];
    repeatseq (fun () -> first [split; implies_intro'; (fun () -> apply_lemma (`lem))]);
    if b then
        repeat' join; // this line makes the thing 20 times faster
    dump "Final state"

let test1 (x y z : nat) =
    assert formula by (tau false)

let test2 (x y z : nat) =
    assert formula by (tau true)
