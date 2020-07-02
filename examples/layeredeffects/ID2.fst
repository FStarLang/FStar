module ID2

// The base type of WPs
val w0 (a : Type u#a) : Type u#(max 1 a)
let w0 a = (a -> Type0) -> Type0

// We require monotonicity of them
let monotonic (w:w0 'a) =
  forall p1 p2. (forall x. p1 x ==> p2 x) ==> w p1 ==> w p2

val w (a : Type u#a) : Type u#(max 1 a)
let w a = w:(w0 a){monotonic w}

let repr (a : Type) (wp : w a) : Type =
  squash (exists p. wp p) -> v:a{forall p. wp p ==> p v}

unfold let return_wp (#a:Type) (x:a) : w a = fun p -> p x

let return (a : Type) (x : a) : repr a (return_wp x) =
  fun () -> x

unfold let bind_wp (#a:Type) (#b:Type) (wp_f:w a) (wp_g:a -> w b) : w b =
  fun p -> wp_f (fun x -> wp_g x p)

let bind (a b : Type) (wp_v : w a) (wp_f: a -> w b)
    (v : repr a wp_v)
    (f : (x:a -> repr b (wp_f x)))
: repr b (bind_wp wp_v wp_f)
 // Fun fact: using () instead of _ below makes us
 // lose the refinement and then this proof fails.
 // Keep that in mind all ye who enter here.
= fun _ -> f (v ()) () // explicit post is annoying

let subcomp (a:Type) (wp1 wp2: w a)
    (f : repr a wp1)
: Pure (repr a wp2)
       (requires (forall p. wp2 p ==> wp1 p))
       (ensures fun _ -> True)
= f

unfold let if_then_else_wp (#a:Type) (wp1 wp2:w a) (p:bool) : w a =
  fun post -> (p ==> wp1 post) /\ ((~p) ==> wp2 post)


let if_then_else (a : Type) (wp1 wp2 : w a) (f : repr a wp1) (g : repr a wp2) (p : bool) : Type =
  repr a (if_then_else_wp wp1 wp2 p)

// requires to prove that
// p  ==> f <: (if_then_else p f g)
// ~p ==> g <: (if_then_else p f g)
// if the effect definition fails, add lemmas for the
// above with smtpats
total
reifiable
reflectable
layered_effect {
  ID : a:Type -> wp : w a -> Effect
  with repr         = repr;
       return       = return;
       bind         = bind;
       subcomp      = subcomp;
       if_then_else = if_then_else
}

#push-options "--admit_smt_queries true"
unfold let coerce (#a:Type) (wp:pure_wp a) : w a =  wp

let lift_pure_nd (a:Type) (wp:pure_wp a) (f:(eqtype_as_type unit -> PURE a wp)) :
  Pure (repr a (coerce wp)) (requires True)
                   (ensures (fun _ -> True))
  = fun _ -> f ()
#pop-options
  
sub_effect PURE ~> ID = lift_pure_nd

(* Checking that it's kind of usable *)

val test_f : unit -> ID int (fun p -> p 5 /\ p 3)
let test_f () = 3

module T = FStar.Tactics

let l () : int =
  assert (exists p. p 5 /\ p 3) by (T.witness (`(fun _ -> True))); // sigh
  reify (test_f ()) ()

effect Id (a:Type) (pre:pure_pre) (post:pure_post' a pre) =
        ID a (fun (p:pure_post a) -> pre /\ (forall (pure_result:a). post pure_result ==> p pure_result))

effect IdT (a:Type) = Id a True (fun _ -> True)

let rec sum (l : list int) : IdT int
 =
  match l with
  | [] -> 0
  | x::xs -> x + sum xs
