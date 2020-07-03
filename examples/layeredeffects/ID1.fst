module ID1

// The base type of WPs
val wp0 (a : Type u#a) : Type u#(max 1 a)
let wp0 a = (a -> Type0) -> Type0

// We require monotonicity of them
let monotonic (w:wp0 'a) =
  forall p1 p2. (forall x. p1 x ==> p2 x) ==> w p1 ==> w p2

val wp (a : Type u#a) : Type u#(max 1 a)
let wp a = w:(wp0 a){monotonic w}

let repr (a : Type) (w : wp a) : Type =
  p:_ -> squash (w p) -> v:a{p v}

let return_wp #a (x:a) : wp a =
  fun p -> p x

let return (a : Type) (x : a) : repr a (return_wp x) =
 // Fun fact: using () instead of _ below makes us
 // lose the refinement and then this proof fails.
 // Keep that in mind all ye who enter here.
  fun p _ -> x

let bind_wp #a #b
  (wp_v : wp a)
  (wp_f : (x:a -> wp b))
  : wp b
  = fun p -> wp_v (fun x -> wp_f x p)

let bind (a b : Type) (wp_v : wp a) (wp_f: a -> wp b)
    (v : repr a wp_v)
    (f : (x:a -> repr b (wp_f x)))
: repr b (bind_wp wp_v wp_f)
//= fun p _ -> f (v (fun x -> wp_f x p) ()) p ()
  // explicit post is annoying
= fun p _ -> let x = v (fun x -> wp_f x p) () in
          f x p ()

let subcomp (a:Type) (w1 w2: wp a)
    (f : repr a w1)
: Pure (repr a w2)
       (requires (forall p. w2 p ==> w1 p))
       (ensures fun _ -> True)
= f

let ite_wp #a (wp1 wp2 : wp a) (b : bool) : wp a =
  (fun (p:a -> Type) -> (b ==> wp1 p) /\ ((~b) ==> wp2 p))

let if_then_else (a : Type) (wp1 wp2 : wp a) (f : repr a wp1) (g : repr a wp2) (p : bool) : Type =
  repr a (ite_wp wp1 wp2 p)

let strengthen #a #w (p:Type0) (f : squash p -> repr a w) : repr a (fun post -> p /\ w post) =
  fun post _ -> f () post ()
  
let weaken #a #w (p:Type0) (f : repr a w) : Pure (repr a (fun post -> p ==> w post))
                                                 (requires p)
                                                 (ensures (fun _ -> True))
  = fun post _ -> f post ()

let cut #a #w (p:Type0) (f : repr a w) : repr a (fun post -> p /\ (p ==> w post)) =
  strengthen p (fun _ -> weaken p f)
  

// requires to prove that
// p  ==> f <: (if_then_else p f g)
// ~p ==> g <: (if_then_else p f g)
// if the effect definition fails, add lemmas for the
// above with smtpats
total
reifiable
reflectable
layered_effect {
  ID : a:Type -> wp a -> Effect
  with repr         = repr;
       return       = return;
       bind         = bind;
       subcomp      = subcomp
}

let nomon #a (w : wp a) : pure_wp a = fun p -> w p

let lift_pure_nd (a:Type) (wp:wp a) (f:(eqtype_as_type unit -> PURE a (nomon wp))) :
  Pure (repr a wp) (requires True)
                   (ensures (fun _ -> True))
  = fun p _ ->
    let r = f () in
    assert (p r); // GM: needed to guide z3 apparently?
    r

//sub_effect PURE ~> ID = lift_pure_nd

(* Checking that it's kind of usable *)

val test_f : unit -> ID int (fun p -> p 5 /\ p 3)
let test_f () = 3

let l () : int = reify (test_f ()) (fun _ -> True) ()

effect Id (a:Type) (pre:pure_pre) (post:pure_post' a pre) =
        ID a (fun (p:pure_post a) -> pre /\ (forall (pure_result:a). post pure_result ==> p pure_result))

effect IdT (a:Type) = Id a True (fun _ -> True)

[@@expect_failure] // why?
let rec sum (l : list int) : IdT int
 =
  match l with
  | [] -> 0
  | x::xs -> x + sum xs
