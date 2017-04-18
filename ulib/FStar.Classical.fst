module FStar.Classical
open FStar.Squash

val give_witness: #a:Type -> a -> Lemma (ensures a)
let give_witness #a x = return_squash x

val get_squashed (#b a:Type) : Pure a (requires (a /\ a == squash b)) (ensures (fun _ -> True))
let get_squashed #b a =
  let p = get_proof a in
  join_squash #b p

val get_equality (#t:Type) (a b:t) : Pure (a == b) (requires (a == b)) (ensures (fun _ -> True))
let get_equality #t a b = get_squashed #(equals a b) (a == b)

val get_forall (#a:Type) (p:a -> GTot Type0) : Pure (forall (x:a). p x) (requires (forall (x:a). p x)) (ensures (fun _ -> True))
let get_forall #a p =
  get_squashed #(x:a -> GTot (p x)) (forall (x:a). p x)

val impl_to_arrow : #a:Type0 -> #b:Type0 -> impl:(a ==> b) -> sx:squash a -> GTot (squash b)
let impl_to_arrow #a #b impl sx =
  bind_squash #(a -> GTot b) impl (fun f ->
  bind_squash sx (fun x ->
  return_squash (f x)))

val arrow_to_impl : #a:Type0 -> #b:Type0 -> f:(squash a -> GTot (squash b)) -> GTot (a ==> b)
let arrow_to_impl #a #b f = squash_double_arrow (return_squash (fun x -> f (return_squash x)))

(* TODO: Maybe this should move to FStar.Squash.fst *)
val forall_intro_gtot  : #a:Type -> #p:(a -> GTot Type) -> $f:(x:a -> GTot (p x)) -> Tot (squash (forall (x:a). p x))
let forall_intro_gtot #a #p $f = return_squash #(forall (x:a). p x) ()

val lemma_forall_intro_gtot  : #a:Type -> #p:(a -> GTot Type) -> $f:(x:a -> GTot (p x)) -> Lemma (forall (x:a). p x)
let lemma_forall_intro_gtot #a #p $f = forall_intro_gtot #a #p f

val gtot_to_lemma  : #a:Type -> #p:(a -> GTot Type) -> $f:(x:a -> GTot (p x)) -> x:a -> Lemma (p x)
let gtot_to_lemma #a #p $f x = give_proof #(p x) (return_squash (f x))

val lemma_to_squash_gtot  : #a:Type -> #p:(a -> GTot Type) -> $f:(x:a -> Lemma (p x)) -> x:a -> GTot (squash (p x))
let lemma_to_squash_gtot #a #p $f x = f x; get_proof (p x)

val forall_intro_squash_gtot  : #a:Type -> #p:(a -> GTot Type) -> $f:(x:a -> GTot (squash (p x))) -> Tot (squash (forall (x:a). p x))
let forall_intro_squash_gtot #a #p $f =
  bind_squash #(x:a -> GTot (p x)) #(forall (x:a). p x)
	      (squash_double_arrow #a #p (return_squash f))
	      (fun f -> lemma_forall_intro_gtot #a #p f)

//This one seems more generally useful than the one above
val forall_intro_squash_gtot_join  : #a:Type -> #p:(a -> GTot Type) -> $f:(x:a -> GTot (squash (p x))) -> Tot (forall (x:a). p x)
let forall_intro_squash_gtot_join #a #p $f =
  join_squash
    (bind_squash #(x:a -> GTot (p x)) #(forall (x:a). p x)
	      (squash_double_arrow #a #p (return_squash f))
	      (fun f -> lemma_forall_intro_gtot #a #p f))

val forall_intro  : #a:Type -> #p:(a -> GTot Type) -> $f:(x:a -> Lemma (p x)) -> Lemma (forall (x:a). p x)
let forall_intro #a #p $f = forall_intro_squash_gtot (lemma_to_squash_gtot #a #p f)

val forall_intro'  : #a:Type -> #p:(a -> GTot Type) -> f:(x:a -> Lemma (p x)) -> Lemma (forall (x:a). p x)
let forall_intro' #a #p f = forall_intro f

(* val forall_elim : #a:Type -> #p:(a -> GTot Type) -> (forall (x:a). p x) -> v:a -> Lemma (p v) *)

(* Some basic stuff, should be moved to FStar.Squash, probably *)
let forall_intro_2 (#a:Type) (#b:(a -> Type)) (#p:(x:a -> b x -> GTot Type0))
                  ($f: (x:a -> y:b x -> Lemma (p x y)))
  : Lemma (forall (x:a) (y:b x). p x y)
  = let g : x:a -> Lemma (forall (y:b x). p x y) = fun x -> forall_intro (f x) in
    forall_intro g

let forall_intro_3 (#a:Type) (#b:(a -> Type)) (#c:(x:a -> y:b x -> Type)) (#p:(x:a -> y:b x -> z:c x y -> Type0))
		  ($f: (x:a -> y:b x -> z:c x y -> Lemma (p x y z)))
  : Lemma (forall (x:a) (y:b x) (z:c x y). p x y z)
  = let g : x:a -> Lemma (forall (y:b x) (z:c x y). p x y z) = fun x -> forall_intro_2 (f x) in
    forall_intro g

let exists_intro (#a:Type) (p:(a -> Type)) (witness:a)
  : Lemma (requires (p witness))
	  (ensures (exists (x:a). p x))
  = ()

let forall_to_exists (#a:Type) (#p:(a -> Type)) (#r:Type) ($f:(x:a -> Lemma (p x ==> r)))
  : Lemma ((exists (x:a). p x) ==> r)
  = forall_intro f

let forall_to_exists_2 (#a:Type) (#p:(a -> Type)) (#b:Type) (#q:(b -> Type)) (#r:Type)
		 ($f:(x:a -> y:b -> Lemma ((p x /\ q y) ==> r)))
  : Lemma (((exists (x:a). p x) /\ (exists (y:b). q y)) ==> r)
  = forall_intro_2 f

let impl_intro_gtot (#p:Type0) (#q:Type0) ($f:p -> GTot q) : GTot (p ==> q) = return_squash f

let impl_intro (#p:Type0) (#q:Type0) ($f: p -> Lemma q) : Lemma (p ==> q)  =
    give_witness #(p ==> q) (squash_double_arrow (return_squash (lemma_to_squash_gtot f)))

val exists_elim: goal:Type -> #a:Type -> #p:(a -> Type) -> $have:squash (exists (x:a). p x) -> f:(x:a{p x} -> GTot (squash goal)) ->
  Lemma goal
let exists_elim goal #a #p have f =
  let open FStar.Squash in
  bind_squash #_ #goal (join_squash have) (fun (| x, pf |) -> return_squash pf; f x)

let move_requires (#a:Type) (#p:a -> Type) (#q:a -> Type)
  ($f:x:a -> Lemma (requires (p x)) (ensures (q x))) (x:a)
  : Lemma (p x ==> q x) =
      give_proof
        (bind_squash (get_proof (l_or (p x) (~(p x))))
        (fun (b : l_or (p x) (~(p x))) ->
          bind_squash b (fun (b' : c_or (p x) (~(p x))) ->
            match b' with
            | Left hp -> give_witness hp; f x; get_proof (p x ==> q x)
            | Right hnp -> give_witness hnp
          )))

val forall_impl_intro :
  #a:Type ->
  #p:(a -> GTot Type) ->
  #q:(a -> GTot Type) ->
  $f:(x:a -> (squash(p x)) -> Lemma (q x)) ->
  Lemma (forall x. p x ==> q x)
let forall_impl_intro #a #p #q $f =
  let f' (x:a) : Lemma (requires (p x)) (ensures (q x)) = f x (get_proof (p x)) in
  forall_intro (move_requires f')

// Thanks KM, CH and SZ
val impl_intro_gen
  (#p: Type0)
  (#q: (h: squash p) -> Tot Type0)
  (f: (x: squash p) -> Lemma (q ()))
: Lemma (p ==> q ())
let impl_intro_gen #p #q f =
  let g () : Lemma
    (requires p)
    (ensures (p ==> q ()))
  =
   give_proof #(q ()) (f (get_proof p))
  in
  move_requires g ()

val ghost_lemma: #a:Type -> #p:(a -> GTot Type0) -> #q:(a -> unit -> GTot Type0) ->
  $f:(x:a -> Ghost unit (p x) (q x)) -> Lemma (forall (x:a). p x ==> q x ())
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
 
let or_elim
  (#l #r: Type0)
  (#goal: (squash (l \/ r) -> Tot Type0))
  (hl: squash l -> Lemma (goal ()))
  (hr: squash r -> Lemma (goal ()))
: Lemma
  ((l \/ r) ==> goal ())
= impl_intro_gen #l #(fun _ -> goal ()) hl;
  impl_intro_gen #r #(fun _ -> goal ()) hr

////////////////////////////////////////////////////////////////////////////////
(* the most standard variant of excluded middle is provable by SMT *)
val excluded_middle : p:Type -> Lemma (requires (True))
                                       (ensures (p \/ ~p))
let excluded_middle (p:Type) = ()
