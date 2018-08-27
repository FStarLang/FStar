module FStar.Classical

open FStar.Squash

let give_witness #a x = return_squash x

let give_witness_from_squash #a x = x

val get_squashed (#b a:Type) : Pure a (requires (a /\ a == squash b)) (ensures (fun _ -> True))
let get_squashed #b a =
  let p = get_proof a in
  join_squash #b p

let get_equality #t a b = get_squashed #(equals a b) (a == b)

let get_forall #a p = get_squashed #(x:a -> GTot (p x)) (forall (x:a). p x)

let impl_to_arrow #a #b impl sx =
  bind_squash #(a -> GTot b) impl (fun f ->
  bind_squash sx (fun x ->
  return_squash (f x)))

let arrow_to_impl #a #b f = squash_double_arrow (return_squash (fun x -> f (return_squash x)))

(* TODO: Maybe this should move to FStar.Squash.fst *)
let forall_intro_gtot #a #p $f = 
  let id (#a:Type) (x:a) = x in
  let h : (x:a -> GTot (id (p x))) = fun x -> f x in
  return_squash #(forall (x:a). id (p x)) ()

let lemma_forall_intro_gtot #a #p $f = give_witness (forall_intro_gtot #a #p f)

let gtot_to_lemma #a #p $f x = give_proof #(p x) (return_squash (f x))

let lemma_to_squash_gtot #a #p $f x = f x; get_proof (p x)

let forall_intro_squash_gtot #a #p $f =
  bind_squash #(x:a -> GTot (p x)) #(forall (x:a). p x)
	      (squash_double_arrow #a #p (return_squash f))
	      (fun f -> lemma_forall_intro_gtot #a #p f)

let forall_intro_squash_gtot_join #a #p $f =
  join_squash
    (bind_squash #(x:a -> GTot (p x)) #(forall (x:a). p x)
	      (squash_double_arrow #a #p (return_squash f))
	      (fun f -> lemma_forall_intro_gtot #a #p f))

let forall_intro #a #p $f = give_witness (forall_intro_squash_gtot (lemma_to_squash_gtot #a #p f))

let forall_intro_with_pat #a #c #p $pat #f = forall_intro #a #p f

let forall_intro_sub #a #p f = forall_intro f

(* val forall_elim : #a:Type -> #p:(a -> GTot Type) -> (forall (x:a). p x) -> v:a -> Lemma (p v) *)

(* Some basic stuff, should be moved to FStar.Squash, probably *)
let forall_intro_2 #a #b #p $f
  = let g : x:a -> Lemma (forall (y:b x). p x y) = fun x -> forall_intro (f x) in
    forall_intro g

let forall_intro_2_with_pat #a #b #c #p $pat $f
  = forall_intro_2 #a #b #p f

let forall_intro_3 #a #b #c #p #f
  = let g : x:a -> Lemma (forall (y:b x) (z:c x y). p x y z) = fun x -> forall_intro_2 (f x) in
    forall_intro g

let forall_intro_3_with_pat #a #b #c #d #p $pat $f
  = forall_intro_3 #a #b #c #p f

let forall_intro_4 #a #b #c #d #p #f
  = let g : x:a -> Lemma (forall (y:b x) (z:c x y) (w:d x y z). p x y z w) = fun x -> forall_intro_3 (f x) in
    forall_intro g

let exists_intro #a p witness = ()

let forall_to_exists #a #p #r $f = forall_intro f

let forall_to_exists_2 #a #p #b #q #r $f = forall_intro_2 f

let impl_intro_gtot #p #q $f = return_squash f

let impl_intro #p #q $f =
  give_witness #(p ==> q) (squash_double_arrow (return_squash (lemma_to_squash_gtot f)))

let exists_elim goal #a #p have f =
  bind_squash #_ #goal (join_squash have) (fun (| x, pf |) -> return_squash pf; f x)

let move_requires #a #p #q $f x =
      give_proof
        (bind_squash (get_proof (l_or (p x) (~(p x))))
        (fun (b : l_or (p x) (~(p x))) ->
          bind_squash b (fun (b' : c_or (p x) (~(p x))) ->
            match b' with
            | Left hp -> give_witness hp; f x; get_proof (p x ==> q x)
            | Right hnp -> give_witness hnp
          )))

let forall_impl_intro #a #p #q $f =
  let f' (x:a) : Lemma (requires (p x)) (ensures (q x)) = f x (get_proof (p x)) in
  forall_intro (move_requires f')

// Thanks KM, CH and SZ
let impl_intro_gen #p #q f =
  let g () : Lemma
    (requires p)
    (ensures (p ==> q ()))
  =
   give_proof #(q ()) (f (get_proof p))
  in
  move_requires g ()

let ghost_lemma #a #p #q $f =
 let lem : x:a -> Lemma (p x ==> q x ()) =
  (fun x ->
      (* basically, the same as above *)
      give_proof
        (bind_squash (get_proof (l_or (p x) (~(p x))))
        (fun (b : l_or (p x) (~(p x))) ->
          bind_squash b (fun (b' : c_or (p x) (~(p x))) ->
            match b' with
            | Left hp -> give_witness hp; f x; get_proof (p x ==> q x ())
            | Right hnp -> give_witness hnp
          ))))
 in forall_intro lem
 
let or_elim #l #r #goal hl hr
  = impl_intro_gen #l #(fun _ -> goal ()) hl;
    impl_intro_gen #r #(fun _ -> goal ()) hr

////////////////////////////////////////////////////////////////////////////////
(* the most standard variant of excluded middle is provable by SMT *)
let excluded_middle (p:Type) = ()
