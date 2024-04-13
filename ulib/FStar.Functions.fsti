module FStar.Functions

(* This module contains basic definitions and lemmas
about functions and sets. *)

let is_inj (#a #b : _) (f : a -> b) : prop =
  forall (x1 x2 : a). f x1 == f x2 ==> x1 == x2

let is_surj (#a #b : _) (f : a -> b) : prop =
  forall (y:b). exists (x:a). f x == y

let in_image (#a #b : _) (f : a -> b) (y : b) : prop =
  exists (x:a). f x == y

let image_of (#a #b : _) (f : a -> b) : Type =
  y:b{in_image f y}

let powerset (a:Type u#aa) : Type u#aa = a -> bool

val inj_comp (#a #b #c : _) (f : a -> b) (g : b -> c)
  : Lemma (requires is_inj f /\ is_inj g)
          (ensures is_inj (fun x -> g (f x)))

val surj_comp (#a #b #c : _) (f : a -> b) (g : b -> c)
  : Lemma (requires is_surj f /\ is_surj g)
          (ensures is_surj (fun x -> g (f x)))

val lem_surj (#a #b : _) (f : a -> b) (y : b)
  : Lemma (requires is_surj f) (ensures in_image f y)

(* An injective function has an inverse (as long as the domain is non-empty),
and this inverse is surjective. *)
val inverse_of_inj (#a #b : _) (f : a -> b{is_inj f}) (def : a)
  : GTot (g : (b -> a){is_surj g})
