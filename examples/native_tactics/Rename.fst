module Rename

(* Testing the new printing based on the static environment *)

open FStar.Tactics

assume val phi : Type
assume val psi : Type
assume val xi : Type

assume val p : squash xi

[@plugin]
let tau =
  fun () ->
    let h0 = implies_intro () in
    let h1 = implies_intro () in
    dump "Test";
    exact (`p)

let l1 (x : bool) (y : int) (z : unit) =
    assert_by_tactic (phi ==> (psi ==> xi)) tau

// this error should show pretty binders too
(* let _ = *)
(*     assert_by_tactic (False ==> True) *)
(*             (fun () -> *)
(*                 let h0 = implies_intro () in *)
(*                 let x = quote (fun x -> 1 + x) in *)
(*                 let t = mk_e_app x [pack (Tv_Const C_Unit)] in *)
(*                 let _ = tc t in *)
(*                 trivial ()) *)
