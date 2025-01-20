module FStar.Functions

(* This module contains basic definitions and lemmas
about functions and sets. *)

let is_inj (#a #b : _) (f : a -> GTot b) : prop =
  forall (x1 x2 : a). f x1 == f x2 ==> x1 == x2

let is_surj (#a #b : _) (f : a -> GTot b) : prop =
  forall (y:b). exists (x:a). f x == y

let is_bij (#a #b : _) (f : a -> GTot b) : prop =
  is_inj f /\ is_surj f

let in_image (#a #b : _) (f : a -> GTot b) (y : b) : prop =
  exists (x:a). f x == y

let image_of (#a #b : _) (f : a -> GTot b) : Type =
  y:b{in_image f y}

(* g inverses f *)
let is_inverse_of (#a #b : _) (g : b -> GTot a) (f : a -> GTot b)  =
  forall (x:a). g (f x) == x

let powerset (a:Type u#aa) : Type u#aa = a -> GTot bool

val inj_comp (#a #b #c : _) (f : a -> GTot b) (g : b -> GTot c)
  : Lemma (requires is_inj f /\ is_inj g)
          (ensures is_inj (fun x -> g (f x)))

val surj_comp (#a #b #c : _) (f : a -> GTot b) (g : b -> GTot c)
  : Lemma (requires is_surj f /\ is_surj g)
          (ensures is_surj (fun x -> g (f x)))

val bij_comp (#a #b #c : _) (f : a -> GTot b) (g : b -> GTot c) :
 Lemma (requires is_bij f /\ is_bij g)
       (ensures is_bij (fun x -> g (f x)))

val lem_surj (#a #b : _) (f : a -> GTot b) (y : b)
  : Lemma (requires is_surj f) (ensures in_image f y)

(* An bijection has a perfect inverse. *)
val inverse_of_bij (#a #b : _) (f : a -> GTot b)
  : Ghost (b -> GTot a)
          (requires is_bij f)
          (ensures fun g -> is_bij g /\ g `is_inverse_of` f /\ f `is_inverse_of` g)

(* An injective function has an inverse (as long as the domain is non-empty),
and this inverse is surjective. *)
val inverse_of_inj (#a #b : _) (f : a -> GTot b{is_inj f}) (def : a)
  : Ghost (b -> GTot a)
          (requires is_inj f)
          (ensures fun g -> is_surj g /\ g `is_inverse_of` f)
