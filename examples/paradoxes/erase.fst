(*--build-config
    other-files: FStar.Ghost.fst FStar.Constructive.fst;
  --*)
module Erase

open FStar.Ghost
open FStar.Constructive

val hide0_hide1_smt : unit -> Lemma (ensures (~(hide 0 = hide 1)))
let hide0_hide1_smt () = ()

val false_elim : u:unit{False} -> Tot 'a
let false_elim () = ()

val neq01 : ceq 0 1 -> Tot cfalse
let neq01 h = false_elim ()

val reveal_hide : #a:Type -> x:a -> GTot (ceq (reveal (hide x)) x)
let reveal_hide (a:Type) x = Refl 

val hide0_hide1_constr : ceq (hide 0) (hide 1) -> GTot cfalse
let hide0_hide1_constr h =
  let h0 : (ceq (reveal (hide 0)) 0) = reveal_hide 0 in
  let h1 : (ceq (reveal (hide 1)) 1) = reveal_hide 1 in
  let h' : (ceq (reveal (hide 0))
                (reveal (hide 1))) = ceq_congruence h reveal in
  let h'' : (ceq 0 1) = ceq_trans (ceq_trans (ceq_symm h0) h') h1 in
  neq01 h''
