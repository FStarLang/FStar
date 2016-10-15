module FStar.Classical
open FStar.Squash
#set-options "--initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0"
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

val forall_intro  : #a:Type -> #p:(a -> GTot Type) -> $f:(x:a -> Lemma (p x)) -> Lemma (forall (x:a). p x)
let forall_intro #a #p $f = forall_intro_squash_gtot (lemma_to_squash_gtot #a #p f)

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


val give_proof: #a:Type -> a -> Lemma (ensures a)
let give_proof #a x = return_squash x

////////////////////////////////////////////////////////////////////////////////
(* one variant of excluded middle is provable by SMT *)
val excluded_middle' : p:Type -> Lemma (requires (True))
                                       (ensures (p \/ ~p))
let excluded_middle' (p:Type) = ()

(* WARNING: this breaks parametricity; use with care *)
assume val excluded_middle : p:Type -> GTot (b:bool{b = true <==> p})

val ghost_lemma: #a:Type -> #p:(a -> GTot Type) -> #q:(a -> unit -> GTot Type) ->
  $f:(x:a -> Ghost unit (p x) (q x)) -> Lemma (forall (x:a). p x ==> q x ())
let ghost_lemma #a #p #q $f = 
 let lem : x:a -> Lemma (p x ==> q x ()) =
  fun x -> 
      let b = excluded_middle (p x) in  
      if b then f x else () in 
 forall_intro lem

let move_requires (#a:Type) (#p:a -> Type) (#q:a -> Type) ($f:x:a -> Lemma (requires (p x)) (ensures (q x))) (x:a)
   : Lemma (p x ==> q x)
   = if excluded_middle (p x)
     then f x
     else ()

val exists_elim: goal:Type -> #a:Type -> #p:(a -> Type) -> $have:squash (exists (x:a). p x) -> f:(x:a{p x} -> GTot (squash goal)) -> 
  Lemma goal
let exists_elim goal #a #p have f = 
  let open FStar.Squash in 
  bind_squash #_ #goal (join_squash have) (fun (| x, pf |) -> return_squash pf; f x)
