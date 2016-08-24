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
