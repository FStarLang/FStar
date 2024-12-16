module FStar.Functions

let inj_comp (#a #b #c : _) (f : a -> GTot b) (g : b -> GTot c)
  : Lemma (requires is_inj f /\ is_inj g)
          (ensures is_inj (fun x -> g (f x)))
  = ()

let surj_comp (#a #b #c : _) (f : a -> GTot b) (g : b -> GTot c)
  : Lemma (requires is_surj f /\ is_surj g)
          (ensures is_surj (fun x -> g (f x)))
  = ()

let bij_comp (#a #b #c : _) (f : a -> GTot b) (g : b -> GTot c) :
 Lemma (requires is_bij f /\ is_bij g)
       (ensures is_bij (fun x -> g (f x)))
= ()

let lem_surj (#a #b : _) (f : a -> GTot b) (y : b)
  : Lemma (requires is_surj f) (ensures in_image f y)
  = ()

let inverse_of_bij #a #b f =
  (* Construct the inverse from indefinite description + choice. *)
  let g0 (y:b) : GTot (x:a{f x == y})  =
    FStar.IndefiniteDescription.indefinite_description_ghost a
      (fun (x:a) -> f x == y)
  in
  (* Prove it's surjective *)
  let aux (x:a) : Lemma (exists (y:b). g0 y == x) =
    assert (g0 (f x) == x)
  in
  Classical.forall_intro aux;
  g0

let inverse_of_inj #a #b f def =
  (* f is a bijection into its image, obtain its inverse *)
  let f' : a -> GTot (image_of f) = fun x -> f x in
  let g_partial = inverse_of_bij #a #(image_of f) f' in
  (* extend the inverse to the full domain b *)
  let g : b -> GTot a =
    fun (y:b) ->
      if FStar.StrongExcludedMiddle.strong_excluded_middle (in_image f y)
      then g_partial y
      else def
  in
  g
