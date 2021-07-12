module ID2

unfold
let sat (w : pure_wp 'a) : Type0 = w (fun _ -> True)

open FStar.Monotonic.Pure

let repr (a : Type u#aa) (wp : pure_wp a) : Type u#aa =
  squash (sat wp) -> v:a{forall p. wp p ==> p v}

let return (a : Type) (x : a) : repr a (pure_return a x) =
  fun () -> x

let bind (a b : Type)
  (wp_v : pure_wp a) (wp_f: a -> pure_wp b)
  (v : repr a wp_v)
  (f : (x:a -> repr b (wp_f x)))
  : repr b (pure_bind_wp a b wp_v wp_f)
   // Fun fact: using () instead of _ below makes us
   // lose the refinement and then this proof fails.
   // Keep that in mind all ye who enter here.
  = elim_pure_wp_monotonicity_forall ();
    fun _ -> f (v ()) ()

let subcomp (a:Type)
  (wp1 wp2: pure_wp a)
  (f : repr a wp1)
  : Pure (repr a wp2)
      (requires (forall p. wp2 p ==> wp1 p))
      (ensures fun _ -> True)
  = f

unfold
let if_then_else_wp (#a:Type) (wp1 wp2:pure_wp a) (p:bool) : pure_wp a =
  elim_pure_wp_monotonicity_forall ();
  as_pure_wp (fun post -> (p ==> wp1 post) /\ ((~p) ==> wp2 post))

let if_then_else (a : Type)
  (wp1 wp2 : pure_wp a)
  (f : repr a wp1)
  (g : repr a wp2) (p : bool)
  : Type
  = repr a (if_then_else_wp wp1 wp2 p)

// requires to prove that
// p  ==> f <: (if_then_else p f g)
// ~p ==> g <: (if_then_else p f g)
// if the effect definition fails, add lemmas for the
// above with smtpats
total
reifiable
reflectable
effect {
  ID (a:Type) (wp:pure_wp a)
  with { repr; return; bind; subcomp; if_then_else }
}

let lift_pure_nd (a:Type) (wp:pure_wp a) (f:eqtype_as_type unit -> PURE a wp)
  : repr a wp
  = elim_pure_wp_monotonicity wp;
    fun _ -> f ()

sub_effect PURE ~> ID = lift_pure_nd

// this requires using a good if_then_else, but why?
let rec count (n:nat) : ID int (as_pure_wp (fun p -> forall r. p r)) =
  if n = 0 then 0 else count (n-1)

(* Checking that it's kind of usable *)

val test_f : unit -> ID int (as_pure_wp (fun p -> p 5 /\ p 3))
let test_f () = 5

let test_2 () : ID int (as_pure_wp (fun p -> p 5)) = 5

let l () : int = reify (test_f ()) ()

effect Id (a:Type) (pre:pure_pre) (post:pure_post' a pre) =
  ID a (as_pure_wp (fun (p:pure_post a) -> pre /\ (forall (pure_result:a). post pure_result ==> p pure_result)))

effect IdT (a:Type) = Id a True (fun _ -> True)

let rec sum (l : list int) : IdT int =
  match l with
  | [] -> 0
  | x::xs -> x + sum xs
