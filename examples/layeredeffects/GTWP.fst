module GTWP

open FStar.Tactics

type idx =
 | T
 | G
 //| D

// GM: Force a type equality by SMT
let coerce #a #b (x:a{a == b}) : b = x

// GM: Warning: the [unfold]s here are important.

unfold
let monotonic #a (wp : pure_wp a) =
  forall p1 p2. (forall x. p1 x ==> p2 x) ==> wp p1 ==> wp p2

let wp (a:Type) =
 w:(pure_wp a){monotonic w}

unfold
let bind_wp #a #b (wc : wp a) (wf : a -> wp b) : wp b =
  fun p -> wc (fun x -> wf x p)

let m (a:Type u#aa) (i:idx) (w : wp a) : Type u#aa =
  match i with
  | T -> unit -> PURE  a w
  | G -> unit -> GHOST a w

let t_return #a (x:a) : m a T (fun p -> p x) = (fun () -> x)
let g_return #a (x:a) : m a G (fun p -> p x) = (fun () -> x)

let return (a:Type) (x:a) (i:idx) : m a i (fun p -> p x) =
  match i with
  | T -> t_return x
  | G -> g_return x

// these two rely on monotonicity since the computed WP is not exactly bind_wp
let t_bind #a #b #wc #wf (c : m a T wc) (f : (x:a -> m b T (wf x))) : m b T (bind_wp wc wf) = fun () -> f (c ()) ()
let g_bind #a #b #wc #wf (c : m a G wc) (f : (x:a -> m b G (wf x))) : m b G (bind_wp wc wf) = fun () -> f (c ()) ()

let bind (a b : Type) wc wf (i:idx) (c : m a i wc) (f : (x:a -> m b i (wf x))) : m b i (bind_wp wc wf) =
  match i with
  | T -> t_bind #_ #_ #wc #wf c f
  | G -> g_bind #_ #_ #wc #wf c f
// GM: would be nice to skip the annotations.

let subcomp (a:Type) (i:idx) (wp1 : wp a)
                             (wp2 : wp a)
                             (f : m a i wp1)
   : Pure (m a i wp2)
          (requires (forall p. wp2 p ==> wp1 p))
          (ensures (fun _ -> True))
   = f

let if_then_else (a:Type) (i:idx) (w1 w2 : wp a)
                          (f : m a i w1)
                          (g : m a i w2) (q : Type0)
    : Type
    //= m a i (fun p -> (q /\ w1 p) \/ ((~q) /\ w2 p))
    = m a i (fun p -> (q ==> w1 p) /\ ((~q) ==> w2 p))

// GM: Would be nice to not have to use all explicit args everywhere,
//     and to get better errors especially when args are out of order,
//     e.g. the [idx] in [return] needs to come after [x], otherwise
//     we get an assertion failure trying to prove [forall (a: Type). idx == a].

reifiable
reflectable
layered_effect {
  GTD : a:Type -> idx -> wp a -> Effect
  with
  repr         = m;
  return       = return;
  bind         = bind;
  subcomp      = subcomp;
  if_then_else = if_then_else
}

let lift_pure_gtd (a:Type) (w : wp a) (i : idx)
                  (f : unit -> PURE a w)
                 : Pure (m a i w)
                        (requires True)
                        (ensures (fun _ -> True))
 = f
 // GM: Surprised that this works actually... I expected that I would need to
 //     case analyze [i].

sub_effect PURE ~> GTD = lift_pure_gtd

// GM: This crashes F* if we forget to write the WPs.

//let rec map #a #b #i (f : a -> GTD b i) (xs : list a) : GTD (list b) i =
//  match xs with
//  | [] -> []
//  | x::xs -> (f x)::(map f xs)

unfold
let null_wp0 (a:Type) : pure_wp a = fun p -> forall x. p x

unfold
let null_wp  (a:Type) : wp a = 
  assert_norm (monotonic (null_wp0 a));
  null_wp0 a

effect Gtd (a:Type) (i:idx) = GTD a i (null_wp a)

let rec map #a #b #i (f : a -> Gtd b i) (xs : list a) : Gtd (list b) i (* by (explode (); dump "") *) =
  match xs with
  | [] -> []
  | x::xs -> (f x)::(map f xs)

let app #a #b #i #wp (f : a -> GTD b i wp) (x : a) : GTD b i wp = f x

// GM: This fails, but I'm not sure why. With tactica (after compute) I see
// the failing goal is
//
//  … @ …ido/r/fstar/layef/GT.fst(106,80-106,86)  Wed Jun 10 22:26:42 2020
//  Goal 1/26
//  a: Type
//  i: idx
//  n: nat
//  f: _: a -> GT.GTD a i
//  x: a
//  x'0: nat
//  uu___: l_True /\ l_True /\ ~(x'0 == 0)
//  x'1: nat
//  x'2: x'0 == x'1
//  x'3: unit
//  x'4: a
//  --------------------------------------------------------------------------------
//  squash (n - 1 >= 0)
//  (*?u509*) _
//
// which seems odd, since [n] and [x'0] are disconnected.

open FStar.Tactics

[@@expect_failure [19]]
let rec appn #a #i (n:nat) (f : a -> Gtd a i) (x : a) : Gtd a i =
  match n with 
  | 0 -> x
  | _ -> begin
    assume (n>0);
    appn (n-1) f (f x)
  end

// explodes
//[@@expect_failure]
//let test #a #i (n:int) : Gtd nat i =
//  let r = app abs n in
//  r

let labs0 #i (n:int) : Gtd int i =
  if n < 0
  then -n
  else n
  
let labs #i (n:int) : Gtd nat i =
  if n < 0
  then -n
  else n

// GM: This works now that we have WPs. (though we still can't prove the assume, which
//     is fine)
let test #a #i (n:int) : Gtd nat i =
  let r = labs0 n in
  assume (r >= 0);
  r
