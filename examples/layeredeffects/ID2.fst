module ID2

// The base type of WPs
val w0 (a : Type u#a) : Type u#(max 1 a)
let w0 a = (a -> Type0) -> Type0

open FStar.Calc
module T = FStar.Tactics

// We require monotonicity of them
unfold
let monotonic (w:w0 'a) =
  forall p1 p2. (forall x. p1 x ==> p2 x) ==> w p1 ==> w p2

// And conjunctivity (in one direction: the way back is implied by monotonicity)
unfold
let conjunctive (w:w0 'a) =
  forall p1 p2. w p1 ==> w p2 ==> w (fun x -> p1 x /\ p2 x)

val w (a : Type u#a) : Type u#(max 1 a)
let w a = w:(w0 a){monotonic w} // /\ conjunctive w}

let sat_e (w : w 'a) : Type0 = exists p. w p

let sat (w : w 'a) : Type0 = w (fun _ -> True)

//let lem_conj #a (w : w a) (p1 p2 : a -> Type0)
//  : Lemma (requires (w p1 /\ w p2))
//          (ensures (w (fun x -> p1 x /\ p2 x)))
//  = ()

let satlem (w: w 'a) : Lemma (sat_e w <==> sat w) [SMTPat (sat w); SMTPat (sat_e w)] = ()

let repr (a : Type u#aa) (wp : w a) : Type u#aa =
  squash (sat wp) -> v:a{forall p. wp p ==> p v}

// useful to trigger `sat w`
let run (#a:Type) (#w : w a) (c : repr a w{sat w})
  : Tot (v:a{forall p. w p ==> p v})
  = c ()

let test (t : repr int (fun p -> p 42)) =
  let x1 = run t in
  let x2 = run t in
  assert (x1 == x2)

unfold let return_wp (#a:Type) (x:a) : w a = fun p -> p x

let return (a : Type) (x : a) : repr a (return_wp x) =
  fun () -> x

unfold let bind_wp (#a:Type) (#b:Type) (wp_f:w a) (wp_g:a -> w b) : w b =
  let r = fun p -> wp_f (fun x -> wp_g x p) in
  assert (monotonic r);
  //let aux (p1 p2 : b->Type0) : Lemma (requires (r p1 /\ r p2))
  //                                 (ensures (r (fun x -> p1 x /\ p2 x))) =
  //  calc (==>) {
  //    r p1 /\ r p2;
  //    ==> {}
  //    wp_f (fun x -> wp_g x p1) /\ wp_f (fun x -> wp_g x p2);
  //    ==> { lem_conj wp_f (fun x -> wp_g x p1) (fun x -> wp_g x p2) } // the step the SMT can't see apparently
  //    wp_f (fun x -> wp_g x p1 /\ wp_g x p2);
  //    ==> { () }
  //    r (fun x -> p1 x /\ p2 x);
  //  }
  //in
  //Classical.forall_intro_2 (fun x y -> Classical.move_requires (aux x) y);
  //assert (conjunctive r);
  r

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

let nomon #a (w : w a) : pure_wp a = fun p -> w p

let lift_pure_nd (a:Type) (wp:w a) (f:(eqtype_as_type unit -> PURE a (nomon wp))) :
  Pure (repr a wp) (requires True)
                   (ensures (fun _ -> True))
  = fun _ -> f ()

sub_effect PURE ~> ID = lift_pure_nd


// this requires using a good if_then_else, but why?
let rec count (n:nat) : ID int (fun p -> forall r. p r)
 = if n = 0 then 0 else count (n-1)

(* Checking that it's kind of usable *)

val test_f : unit -> ID int (fun p -> p 5 /\ p 3)
let test_f () = 5

// somehow needs to prove that (forall p. nomon (fun p -> p 5) p) ??
[@@expect_failure]
let test_2 () : ID int (fun p -> p 5) = admit () // 5

let l () : int =
  reify (test_f ()) ()

effect Id (a:Type) (pre:pure_pre) (post:pure_post' a pre) =
        ID a (fun (p:pure_post a) -> pre /\ (forall (pure_result:a). post pure_result ==> p pure_result))

effect IdT (a:Type) = Id a True (fun _ -> True)

[@@expect_failure]
let rec sum (l : list int) : IdT int
 =
  match l with
  | [] -> 0
  | x::xs -> x + sum xs
