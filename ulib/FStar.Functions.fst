module FStar.Functions

let inj_comp (#a #b #c : _) (f : a -> b) (g : b -> c)
  : Lemma (requires is_inj f /\ is_inj g)
          (ensures is_inj (fun x -> g (f x)))
  = ()

let surj_comp (#a #b #c : _) (f : a -> b) (g : b -> c)
  : Lemma (requires is_surj f /\ is_surj g)
          (ensures is_surj (fun x -> g (f x)))
  = ()

let lem_surj (#a #b : _) (f : a -> b) (y : b)
  : Lemma (requires is_surj f) (ensures in_image f y)
  = ()

let inverse_of_inj (#a #b : _) (f : a -> b{is_inj f}) (def : a) : GTot (g : (b -> a){is_surj g}) =
  (* Construct the inverse from indefinite description + choice. *)
  let g0 (y:b) : GTot (x:a{in_image f y ==> f x == y})  =
    FStar.IndefiniteDescription.indefinite_description_tot a
      (fun (x:a) -> (in_image f y ==> f x == y))
  in
  let g : (b -> a) = Ghost.Pull.pull g0 in
  (* Prove it's surjective *)
  let aux (x:a) : Lemma (exists (y:b). g y == x) =
    assert (in_image f (f x))
  in
  Classical.forall_intro aux;
  g
