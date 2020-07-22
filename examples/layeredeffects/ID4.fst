module ID4

open FStar.Ghost

// The base type of WPs
val wp0 (a : Type u#a) : Type u#(max 1 a)
let wp0 a = (a -> Type0) -> Type0

// We require monotonicity of them
let monotonic (w:wp0 'a) =
  forall p1 p2. (forall x. p1 x ==> p2 x) ==> w p1 ==> w p2

//val wp (a : Type u#a) : Type u#(max 1 a)
//let wp a = w:(wp0 a){monotonic w}

let repr (a : Type u#aa) (w : wp0 a) : Type u#(max 1 aa) =
  // Hmmm, the explicit post bumps the universe level
  ( squash (monotonic w) & (p:erased (a -> Type0) -> squash (w p) -> v:a{reveal p v}))

unfold
let return_wp #a (x:a) : wp0 a =
  fun p -> p x

let return (a : Type) (x : a) : repr a (return_wp x) =
 // Fun fact: using () instead of _ below makes us
 // lose the refinement and then this proof fails.
 // Keep that in mind all ye who enter here.
  (_, (fun p _ -> x))
  
unfold
let bind_wp #a #b
  (wp_v : wp0 a)
  (wp_f : (x:a -> wp0 b))
  : wp0 b
  = fun p -> wp_v (fun x -> wp_f x p)

let bind (a b : Type) (wp_v : wp0 a) (wp_f: a -> wp0 b)
    (v : repr a wp_v)
    (f : (x:a -> repr b (wp_f x)))
: repr b (bind_wp wp_v wp_f)
= let vf (p : erased (b -> Type0)) (_ : squash (bind_wp wp_v wp_f p)) : v:b{reveal p v} =
    let x = snd v (fun x -> wp_f x p) () in
    snd (f x) p ()
  in
  let l () : Lemma (monotonic (bind_wp wp_v wp_f)) =
    fst v;
    let aux (x:a) : Lemma (monotonic (wp_f x)) =
      fst (f x)
    in
    Classical.forall_intro aux
  in
  l ();
  (_, vf)

let subcomp (a:Type) (w1 w2: wp0 a)
    (f : repr a w1)
: Pure (repr a w2)
       (requires (forall p. w2 p ==> w1 p) /\ monotonic w2)
       (ensures fun _ -> True)
= let (m, r) = f in
  (m, r)

let ite_wp #a (wp1 wp2 : wp0 a) (b : bool) : wp0 a =
  (fun (p:a -> Type) -> (b ==> wp1 p) /\ ((~b) ==> wp2 p))

let if_then_else (a : Type) (wp1 wp2 : wp0 a) (f : repr a wp1) (g : repr a wp2) (p : bool) : Type =
  repr a (ite_wp wp1 wp2 p)

let default_if_then_else (a:Type u#aa) (wp:wp0 a) (f:repr a wp) (g:repr a wp) (p:bool)
: Type u#(max 1 aa)
= repr a wp

//let strengthen #a #w (p:Type0) (f : squash p -> repr a w) : repr a (fun post -> p /\ w post) =
//  fun post _ -> f () post ()
//  
//let weaken #a #w (p:Type0) (f : repr a w) : Pure (repr a (fun post -> p ==> w post))
//                                                 (requires p)
//                                                 (ensures (fun _ -> True))
//  = fun post _ -> f post ()
//
//let cut #a #w (p:Type0) (f : repr a w) : repr a (fun post -> p /\ (p ==> w post)) =
//  strengthen p (fun _ -> weaken p f)

total
reifiable
reflectable
layered_effect {
  ID : a:Type -> wp0 a -> Effect
  with repr         = repr;
       return       = return;
       bind         = bind;
       subcomp      = subcomp;
       if_then_else = if_then_else
}

let lift_pure_nd (a:Type) (wp:pure_wp a) (f:(eqtype_as_type unit -> PURE a wp)) :
  Pure (repr a wp) (requires monotonic wp)
                   (ensures (fun _ -> True))
  = (_, (fun (p:erased (a -> Type0)) _ -> // need the type annot
         let r = f () in
         assert (reveal p r);
         r))

sub_effect PURE ~> ID = lift_pure_nd

(* Checking that it's kind of usable *)

val test_f : unit -> ID int (fun p -> p 5 /\ p 3)
let test_f () = 3

let l () : int = snd (reify (test_f ())) (fun _ -> True) ()

effect Id (a:Type) (pre:pure_pre) (post:pure_post' a pre) =
        ID a (fun (p:pure_post a) -> pre /\ (forall (pure_result:a). post pure_result ==> p pure_result))

effect I (a:Type) = Id a True (fun _ -> True)

#set-options "--debug ID1 --debug_level SMTQuery"

open FStar.Tactics

let br (n:nat) : I bool =
 if n = 0 then true else false
  
let add1 (x:int) : Id int (requires (x > 0)) (ensures (fun r -> r == x+1)) = x + 1

[@@expect_failure]
let rec count (n:nat) : I int
 = if n = 0 then 0 else count (n-1)

[@@expect_failure [19]]
let rec fib (i:nat) : I nat by (compute (); dump "") =
  if i = 0 || i = 1
  then 1
  else fib (i-1) + fib (i-2)

[@@expect_failure [19]]
let rec idiv (a b : nat) : Id int (requires (a >= 0 /\ b > 0))
                              (ensures (fun r -> r >= 0)) 
                              (decreases a)
  =
  if a < b
  then 0
  else begin
   assume (a-b << a);
   let r = idiv (a-b) b in
   1 + r
  end

[@@expect_failure [19]] // same
let rec sum (l : list int) : I int
 = match l with
   | [] -> 0
   | x::xs -> sum xs
