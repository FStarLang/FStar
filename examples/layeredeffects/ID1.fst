module ID1

open FStar.Ghost

// The base type of WPs
val wp0 (a : Type u#a) : Type u#(max 1 a)
let wp0 a = (a -> Type0) -> Type0

// We require monotonicity of them
let monotonic (w:wp0 'a) =
  forall p1 p2. (forall x. p1 x ==> p2 x) ==> w p1 ==> w p2

val wp (a : Type u#a) : Type u#(max 1 a)
let wp a = w:(wp0 a){monotonic w}

let repr (a : Type u#aa) (w : wp a) : Type u#(max 1 aa) =
  // Hmmm, the explicit post bumps the universe level
  p:erased (a -> Type0) -> squash (w p) -> v:a{reveal p v}

unfold
let return_wp #a (x:a) : wp a =
  fun p -> p x

let return (a : Type) (x : a) : repr a (return_wp x) =
 // Fun fact: using () instead of _ below makes us
 // lose the refinement and then this proof fails.
 // Keep that in mind all ye who enter here.
  fun p _ -> x
  
unfold
let bind_wp #a #b
  (wp_v : wp a)
  (wp_f : (x:a -> wp b))
  : wp b
  = fun p -> wp_v (fun x -> wp_f x p)

let bind (a b : Type) (wp_v : wp a) (wp_f: a -> wp b)
    (v : repr a wp_v)
    (f : (x:a -> repr b (wp_f x)))
: repr b (bind_wp wp_v wp_f)
= fun p _ -> let x = v (fun x -> wp_f x p) () in
          f x p ()

let subcomp (a:Type u#uu) (w1 w2:wp a)
    (f : repr a w1)
: Pure (repr a w2)
       (requires (forall p. w2 p ==> w1 p))
       (ensures fun _ -> True)
= f

// useful?
//let subcomp (a b:Type u#uu) (w1:wp a) (w2: wp b)
//    (f : repr a w1)
//: Pure (repr b w2)
//       (requires a `subtype_of` b /\ (forall (p:b->Type0). w2 p ==> w1 (fun x -> p x)))
//       (ensures fun _ -> True)
//= fun p pf -> f (hide (fun x -> reveal p x)) ()

unfold
let ite_wp #a (wp1 wp2 : wp a) (b : bool) : wp a =
  (fun (p:a -> Type) -> (b ==> wp1 p) /\ ((~b) ==> wp2 p))

let if_then_else (a : Type) (wp1 wp2 : wp a) (f : repr a wp1) (g : repr a wp2) (p : bool) : Type =
  repr a (ite_wp wp1 wp2 p)

let default_if_then_else (a:Type) (wp:wp a) (f:repr a wp) (g:repr a wp) (p:bool)
: Type
= repr a  wp

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
       subcomp      = subcomp;
       if_then_else = if_then_else
}

effect Id (a:Type) (pre:Type0) (post:a->Type0) =
        ID a (fun p -> pre /\ (forall x. post x ==> p x))

effect I (a:Type) = Id a True (fun _ -> True)

open FStar.Tactics

let elim_pure #a #wp ($f : unit -> PURE a wp) p
 : Pure a (requires (wp p)) (ensures (fun r -> p r)) by (dump "")
 = FStar.Monotonic.Pure.wp_monotonic_pure ();
   f ()

unfold
let nomon #a (w:wp a) : pure_wp a = fun p -> w p

let lift_pure_nd (a:Type) (wp:wp a) (f:(eqtype_as_type unit -> PURE a (nomon wp))) :
  Pure (repr a wp) (requires True)
                   (ensures (fun _ -> True))
  = fun p _ -> elim_pure f p

sub_effect PURE ~> ID = lift_pure_nd

let iassert (q:Type0) : ID unit (fun p -> q /\ (q ==> p ())) = ()

assume
val iassume (q:Type0) : ID unit (fun p -> q ==> p ())

(* Checking that it's kind of usable *)

val test_f : unit -> ID int (fun p -> p 5 /\ p 3)
let test_f () = 3

let l () : int = reify (test_f ()) (fun _ -> True) ()


open FStar.List.Tot

let rec pmap #a #b #pre
  (f : (x:a -> Id b (requires (pre x)) (ensures (fun _ -> True))))
  (l : list a)
  : Id (list b)
       (requires (forall x. memP x l ==> pre x))
       (ensures (fun _ -> True))
  = match l with
    | [] -> []
    | x::xs ->
      // ha... without a trick like this one, we fail to prove termination.
      // not even assuming the precedes helps. tactics show an `l` unrelated
      // to `x` and `xs`.
      let xs () = xs in
      f x :: pmap #_ #_ #pre f (xs ())

let even x = x % 2 == 0

//let fmap (x:nat) : Id nat (requires (even x)) (ensures (fun r -> r > x)) =
// I cannot have a stronger post, subeffecting doesn't kick in in callmap?
let fmap (x:nat) : Id nat (requires (even x)) (ensures (fun r -> True)) =
  let r = x / 2 in
  (* need the binding *)
  r

let callmap () : Id (list nat) True (fun _ -> True) =
 let lmap : list nat = [2;4;6;8] in
 ID1.pmap #_ #_ #even fmap lmap

let rec count (n:nat) : I int
 = if n = 0 then 0 else count (n-1)
 
let rec pow2 (n:nat) : I int
 = if n = 0 then 1 else pow2 (n-1) + pow2 (n-1)
 
let rec fibl (i:nat) : I nat =
  if i = 0 || i = 1
  then 1
  else fibl (i-1)
  
let rec fibr (i:nat) : I nat =
  if i = 0 || i = 1
  then 1
  else fibr (i-2)

// TODO: I cannot use direct syntax and nat for the return type, or
// subtyping fails to kick in? "expected int, got nat".
let rec fib (i:nat) : I nat =
  if i < 2
  then 1
  else let x = fib (i-1) in
       let y = fib (i-2) in
       x+y
  //else fib (i-1) + fib (i-2)

let test_assert () : ID unit (fun p -> p ()) =
  ();
  iassume False;
  ();
  iassert False;
  ()

[@@expect_failure [19]]
let rec idiv (a b : nat) : Id int (requires (a >= 0 /\ b > 0))
                              (ensures (fun r -> r >= 0)) 
                              (decreases a)
  =
  if a < b
  then 0
  else 1 + idiv (a-b) b
  
[@@expect_failure [19]]
let rec ack (m n : nat) : I nat =
  match m, n with
  | 0, n -> n+1
  | m, 0 -> ack (m-1) 1
  | m, n -> ack (m-1) (ack m (n-1))

let add1 (x:int) : Id int (requires (x > 0)) (ensures (fun r -> r == x+1)) = x + 1

let tot_i #a (f : unit -> Tot a) : I a =
  f ()

let i_tot #a (f : unit -> I a) : Tot a =
  reify (f ()) (fun _ -> True) ()

[@@expect_failure [19]]
let rec sum (l : list int) : I int
 = match l with
   | [] -> 0
   | x::xs -> sum xs
