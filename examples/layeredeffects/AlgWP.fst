module AlgWP

(* AlgWP: tracking operation labels and WPs. At the end, we show how we
can recover semantic facts from the labels alone, e.g. that interpreting
a tree will not change the state, effectively allowing to strengthen a
WP from intensional information about the operations in the tree. *)

open Common
open FStar.Calc
module WF = FStar.WellFounded
module FE = FStar.FunctionalExtensionality
module F = FStar.FunctionalExtensionality
module W = FStar.WellFounded
module T = FStar.Tactics
module ID5 = ID5
open Alg

let rwops = labs:ops{sublist labs [Read; Write]}

let noops : rwops = []

type rwtree a (l : ops{l `sublist` [Read;Write]}) = Alg.tree a l

(* Somehow did not need this in Alg! *)
let rec sublist_at_const (l1 l2 l3 : ops)
  : Lemma (requires (sublist l1 l3 /\ sublist l2 l3))
          (ensures (sublist (l1@l2) l3))
          [SMTPat (sublist (l1@l2) l3)]
  = match l1 with
    | [] -> ()
    | h::t -> sublist_at_const t l2 l3
    
let (@@) : rwops -> rwops -> rwops = fun l1 l2 -> l1@l2
let subops : rwops -> rwops -> Type0 = sublist

let sublist_at (l1 l2 : ops)
  : Lemma (sublist l1 (l1@l2) /\ sublist l2 (l1@l2))
          [SMTPat (l1@l2)]
  = Alg.sublist_at l1 l2

let rwtree_help a labs (t : rwtree a labs)
  : Lemma (forall l. l `List.Tot.memP` labs ==> l == Read \/ l == Write)
          [SMTPat (has_type t (rwtree a labs))]
  = ()
  
let tbind : #a:_ -> #b:_ ->
            #labs1:_ -> #labs2:_ ->
            rwtree a labs1 -> 
            (a -> rwtree b labs2) -> rwtree b (labs1@@labs2) = fun c f -> Alg.bind _ _ c f

let st_wp (a:Type) : Type = state -> (a & state -> Type0) -> Type0

unfold
let return_wp #a x : st_wp a = fun s0 p -> p (x, s0)

unfold
let bind_wp #a #b (w : st_wp a) (wf : a -> st_wp b)
  : st_wp b
  = fun s0 p -> w s0 (fun (y, s1) -> wf y s1 p)

unfold
let read_wp : st_wp state = fun s0 p -> p (s0, s0)

unfold
let write_wp : state -> st_wp unit = fun s _ p -> p ((), s)

(* Also doable with handlers *)
let rec interp_as_wp #a (t : Alg.tree a [Read;Write]) : st_wp a =
  match t with
  | Return x -> return_wp x
  | Op Read _ k ->
    bind_wp read_wp (fun s -> WF.axiom1 k s; interp_as_wp (k s))
  | Op Write s k ->
    bind_wp (write_wp s) (fun (o:unit) -> WF.axiom1 k o; interp_as_wp (k o))

(* With handlers. Can only be done into []? See the use of `run`. *)
let interp_as_wp2 #a #l (t : rwtree a l) : Alg (st_wp a) [] =
  handle_with #a #(st_wp a) #[Read; Write] #[]
              (fun () -> Alg?.reflect t)
              (fun x -> return_wp x)
              (function Read  -> (fun i k -> bind_wp read_wp (fun s -> run (fun () -> k s)))
                      | Write -> (fun i k -> bind_wp (write_wp i) (fun _ -> run k)))

(* Bug: defining this as a FStar.Preorder.preorder
causes stupid failures ahead *)
val stronger : (#a:Type) -> st_wp a -> st_wp a -> Type0
let stronger w1 w2 = forall p s. w1 p s ==> w2 p s

let equiv #a (w1 w2 : st_wp a) = w1 `stronger` w2 /\ w2 `stronger` w1

let (<<=) = stronger

val interp_ret (#a:Type) (#l:rwops) (x:a) : Lemma (return_wp x `stronger` interp_as_wp (Return x))
let interp_ret x = ()

val interp_ret' (#a:Type) (x:a) : Lemma (return_wp x == interp_as_wp (Return x))
let interp_ret' x = assert_norm (return_wp x == interp_as_wp (Return x))

let wp_is_monotonic #a (wp : st_wp a) : Type0 =
  forall p1 p2 s0. (forall x s1. p1 (x, s1) ==> p2 (x, s1)) ==> wp s0 p1 ==> wp s0 p2

let bind_preserves_mon #a #b (wp : st_wp a) (f : a -> st_wp b)
  : Lemma (requires (wp_is_monotonic wp /\ (forall x. wp_is_monotonic (f x))))
          (ensures (wp_is_monotonic (bind_wp wp f)))
  = ()

let rec interp_monotonic #a #l (c:rwtree a l) : Lemma (wp_is_monotonic (interp_as_wp c)) =
  match c with
  | Return x -> ()
  | Op Read _ k ->
    let aux (x:state) : Lemma (wp_is_monotonic (interp_as_wp (k x))) =
      WF.axiom1 k x;
      interp_monotonic #_ #l (k x)
    in
    Classical.forall_intro aux;
    bind_preserves_mon read_wp (fun x -> interp_as_wp (k x))
  | Op Write s k ->
    let aux (x:unit) : Lemma (wp_is_monotonic (interp_as_wp (k x))) =
      WF.axiom1 k x;
      interp_monotonic #_ #l (k x)
    in
    Classical.forall_intro aux;
    bind_preserves_mon (write_wp s) (fun x -> interp_as_wp (k x))

let elim_str #a (w1 w2 : st_wp a) (p : (a & state -> Type0)) (s0:state)
  : Lemma (requires (w1 <<= w2))
          (ensures w1 s0 p ==> w2 s0 p)
  = ()

#set-options "--print_implicits"

(* Takes a while, known to fail sporadically *)
#push-options "--retry 10"
let rec interp_morph #a #b #l1 #l2 (c : rwtree a l1) (f : a -> rwtree b l2) (p:_) (s0:_)
  : Lemma (interp_as_wp c s0 (fun (y, s1) -> interp_as_wp (f y) s1 p)
                      == interp_as_wp (tbind #_ #_ #l1 #l2 c f) s0 p)
  = match c with
    | Return x -> interp_ret #_ #l2 x
    | Op Read _ k ->
      let aux (o:state) : Lemma (interp_as_wp (k o) s0 (fun (y, s1) -> interp_as_wp (f y) s1 p)
                                        == interp_as_wp (tbind #_ #_ #l1 #l2 (k o) f) s0 p) =
        WF.axiom1 k o;
        interp_morph #_ #_ #l1 #l2 (k o) f p s0
      in
      Classical.forall_intro aux

    | Op Write s k ->
      let aux (o:unit) : Lemma (interp_as_wp (k o) s (fun (y, s1) -> interp_as_wp (f y) s1 p)
                                        == interp_as_wp (tbind #_ #_ #l1 #l2 (k o) f) s p) =
        WF.axiom1 k o;
        interp_morph #_ #_ #l1 #l2 (k o) f p s
      in
      Classical.forall_intro aux

    | _ ->
      unreachable ()
#pop-options

val interp_bind (#a #b:Type) (#l1 #l2 : rwops)
  (c : rwtree a l1) (f : a -> rwtree b l2)
  (w1 : st_wp a) (w2 : a -> st_wp b)
  : Lemma (requires w1 <<= interp_as_wp c /\ (forall x. w2 x <<= interp_as_wp (f x)))
          (ensures bind_wp w1 w2 `stronger` interp_as_wp (tbind c f))
let interp_bind #a #b c f w1 w2 =
  let aux (p: (b & state -> Type0)) (s0:state) : Lemma (bind_wp w1 w2 s0 p ==> interp_as_wp (tbind c f) s0 p) =
    calc (==>) {
      bind_wp w1 w2 s0 p;
      ==> {}
      w1 s0 (fun (y, s1) -> w2 y s1 p);
      ==> { (* hyp *)}
      interp_as_wp c s0 (fun (y, s1) -> w2 y s1 p);
      ==> { interp_monotonic c }
      interp_as_wp c s0 (fun (y, s1) -> interp_as_wp (f y) s1 p);
      ==> { interp_morph c f p s0 }
      interp_as_wp (tbind c f) s0 p;
    }
  in
  Classical.forall_intro_2 aux

let repr (a : Type) (l : rwops) (w: st_wp a) = c:(rwtree a l){w `stronger` interp_as_wp c}

let return (a:Type) (x:a) : repr a noops (return_wp x) =
  interp_ret #_ #[] x;
  Return x

let bind (a : Type) (b : Type)
  (#l1 #l2 : rwops)
  (#wp_v : st_wp a) (#wp_f: a -> st_wp b)
  (v : repr a l1 wp_v) (f : (x:a -> repr b l2 (wp_f x)))
  : repr b (l1@@l2) (bind_wp wp_v wp_f)
  = interp_bind v f wp_v wp_f;
    tbind v f

let subcomp (a:Type) (#l1 #l2 : rwops) (#w1 #w2: st_wp a)
  (f : repr a l1 w1)
  : Pure (repr a l2 w2)
         (requires w2 `stronger` w1 /\ l1 `subops` l2)
         (ensures fun _ -> True)
  = f

let if_then_else (a : Type)
  (l1 l2 : rwops)
  (w1 w2 : st_wp a)
  (f : repr a l1 w1)
  (g : repr a l2 w2)
  (b : bool)
  : Type
  = repr a (l1@@l2) (if b then w1 else w2)

[@@allow_informative_binders]
total
reifiable
reflectable
layered_effect {
  AlgWP : a:Type -> rwops -> st_wp a -> Effect
  with repr         = repr;
       return       = return;
       bind         = bind;
       subcomp      = subcomp;
       if_then_else = if_then_else
}

let get () : AlgWP state [Read] read_wp =
  AlgWP?.reflect (Op Read () Return)

let put (s:state) : AlgWP unit [Write] (write_wp s) =
  AlgWP?.reflect (Op Write s Return)

unfold
let lift_pure_wp (#a:Type) (wp : pure_wp a) : st_wp a =
  fun s0 p -> wp (fun x -> p (x, s0))

let lift_pure_algwp (a:Type) wp (f:(eqtype_as_type unit -> PURE a wp))
  : Pure (repr a noops (lift_pure_wp wp)) // can't call f() here, so lift its wp instead
         (requires (wp (fun _ -> True)))
         (ensures (fun _ -> True))
  =
    let v : a = elim_pure f (fun _ -> True) in
    FStar.Monotonic.Pure.wp_monotonic_pure (); // need this lemma
    assert (forall p. wp p ==> p v); // this is key fact needed for the proof
    assert_norm (stronger (lift_pure_wp wp) (return_wp v));
    Return v

sub_effect PURE ~> AlgWP = lift_pure_algwp

let addx (x:int) : AlgWP unit [Read; Write] (fun s0 p -> p ((), (s0+x))) =
  let y = get () in
  put (x+y)

(* GM: this used to require a call to T.norm [delta] when I had curry/uncurry going on.
I now realize they were not marked unfold, but that is pretty tricky... we should try
to find some general solution for these things. *)
let add_via_state (x y : int) : AlgWP int [Read;Write] (fun s0 p -> p ((x+y), s0)) =
  let o = get () in
  put x;
  addx y;
  let r = get () in
  put o;
  r


// Why does this admit fail? Only with the 'rec'...
//
// let rec interp_sem #a #wp (t : repr a wp) (s0:state)
//   : PURE (a & state) (fun p -> wp s0 p)
//   = admit ()
//
// literally zero difference in the VC a tactic sees. Also, seems only
// for the builtin Pure???

let rec interp_sem #a (t : rwtree a [Read; Write]) (s0:state)
  : ID5.ID (a & state) (interp_as_wp t s0)
  = match t with
    | Return x -> (x, s0)
    | Op Read i k -> 
      WF.axiom1 k s0;
      interp_sem (k s0) s0
    | Op Write i k ->
      WF.axiom1 k ();
      interp_sem (k ()) i

let quotient_ro #a (w : st_wp a) : st_wp a =
  fun s0 p -> w s0 (fun (y, s1) -> s0 == s1 ==> p (y, s1))

let is_mono #a (w : st_wp a) : Type0 = forall s0 p1 p2. (forall x. p1 x ==> p2 x) ==> w s0 p1 ==> w s0 p2

let is_ro #a (w : st_wp a) : Type0 =
  quotient_ro w `stronger` w

let sanity_1 = assert (forall s0 p. quotient_ro read_wp s0 p <==> read_wp s0 p)
let sanity_2 = assert (forall s0 p s1. p ((), s0) ==> quotient_ro (write_wp s1) s0 p)

let rec interp_ro #a (t : rwtree a [Read]) (s0:state)
  : ID5.ID (a & state) (quotient_ro (interp_as_wp t) s0)
  = match t with
    | Return x -> (x, s0)
    | Op Read i k -> 
      WF.axiom1 k s0;
      interp_ro (k s0) s0

let st_soundness #a #wp (t : unit -> AlgWP a [Read; Write] wp)
  : Tot (s0:state -> ID5.ID (a & state) (wp s0))
  = let c = reify (t ()) in interp_sem c

(* This guarantees the final state is unchanged, but see below
for an alternative statement. *)
let ro_soundness #a #wp (t : unit -> AlgWP a [Read] wp)
  : Tot (s0:state -> ID5.ID (a & state) (quotient_ro wp s0))
  = let c = reify (t ()) in interp_ro c



(****** Internalizing the relation between the labels
and the WP. *)

(* Relies on monotonicity sadly... If we were to carry the refinement
that every wp in an AlgWP was monotonic, then this would be trivial.
It's the old headache in a new effect. *)
let quotient_lemma #a (wp : st_wp a) (s0 : state) : 
  Lemma (quotient_ro wp s0 (fun (r, s1) -> s1 == s0) <==> wp s0 (fun _ -> True))
  = assume (is_mono wp);
    ()

let ro_soundness_pre_post #a #wp (t : unit -> AlgWP a [Read] wp)
  (s0:state)
  : ID5.Id (a & state) (requires (wp s0 (fun _ -> True)))
                       (ensures (fun (r, s1) -> s0 == s1))
  = let reified = reify (ro_soundness #a #wp t s0) in
    quotient_lemma wp s0;
    let r = reified (fun (r, s1) -> s1 == s0) () in
    r

(* Same thing here sadly *)
let bind_ro #a #b (w : st_wp a) (f : a -> st_wp b)
  : Lemma (requires is_ro w /\ (forall x. is_ro (f x)))
          (ensures is_ro (bind_wp w f))
  = assume (is_mono w)
  
let quot_mono #a #b (w1 w2 : st_wp a)
  : Lemma (requires w1 `stronger` w2)
          (ensures quotient_ro w1 `stronger` quotient_ro w2)
  = ()

let rec ro_tree_wp #a (t : tree a [Read])
  : Lemma (is_ro (interp_as_wp t))
  = match t with
    | Return x -> ()
    | Op Read i k ->
      let aux (x:state) : Lemma (is_ro (interp_as_wp (k x))) =
        WF.axiom1 k x;
        ro_tree_wp (k x)
      in
      Classical.forall_intro aux;
      bind_ro read_wp (fun x -> interp_as_wp (k x))

let quot_tree #a #wp (c : repr a [Read] wp)
  : repr a [Read] (quotient_ro wp)
  = ro_tree_wp c;
    c

let quot #a #wp (f : unit -> AlgWP a [Read] wp)
  : AlgWP a [Read] (quotient_ro wp)
  = AlgWP?.reflect (quot_tree (reify (f ())))

effect AlgPP (a:Type) (ll:rwops) (pre : state -> Type0) (post : state -> a -> state -> Type0) =
  AlgWP a ll (fun h0 p -> pre h0 /\ (forall y h1. post h0 y h1 ==> p (y, h1)))
  
let quotPP #a #pre #post (f : unit -> AlgPP a [Read] pre post)
  : AlgPP a [Read] pre (fun h0 x h1 -> post h0 x h1 /\ h0 == h1)
  = quot #_ #(fun h0 p -> pre h0 /\ (forall y h1. post h0 y h1 ==> p (y, h1))) f

let null #a : st_wp a = fun s0 p -> forall r. p r
let null_ro #a : st_wp a = quotient_ro null
let null_ro1 #a : st_wp a = fun s0 p -> forall x. p (x, s0)
let null_equiv_sanity a = assert (null_ro #a `equiv` null_ro1 #a)

//let null_ro_strongest_ro #a (w : st_wp a)
//  : Lemma (requires (is_ro w))
//          (ensures (null_ro `stronger` w))
//  = assert (quotient_ro w `stronger` w);
//    assert (quotient_ro w `stronger` quotient_ro w);
//    admit ()
//
//
//    assume (is_mono w);
//    ()

let bind_null_ro #a #b (w : st_wp a) (f : a -> st_wp b)
  : Lemma (requires (null_ro `stronger` w) /\ (forall x. null_ro `stronger` f x))
          (ensures null_ro `stronger` (bind_wp w f))
  = ()
  
(* Similar to ro_tree_wp *)
let rec null_ro_tree_wp #a (t : tree a [Read])
  : Lemma (null_ro `stronger` (interp_as_wp t))
    by (T.compute ()) // need this to trigger some unfoldings
  = match t with
    | Return x -> ()
    | Op Read i k ->
      let aux (x:state) : Lemma (null_ro `stronger` interp_as_wp (k x)) =
        WF.axiom1 k x;
        null_ro_tree_wp (k x)
      in
      Classical.forall_intro aux;
      bind_null_ro read_wp (fun x -> interp_as_wp (k x))

  (* Could this work automatically too? *)
  //  ro_tree_wp (reify (f ()));
  //  f ()

let __tree_handle_into_ro #a (#l:rwops{~(List.Tot.memP Write l)}) #wp (f : repr a (Write::l) wp)
  : repr a l null_ro
  = let f' : tree a (Write::l) = f in
    let h : tree a l =
      handle_tree f' (fun x -> Return x)
                     (function Write -> fun i k -> k ()
                             | op -> fun i k -> Op op i k)
    in
    assert (sublist l [Read]);
    let h : tree a [Read] = h in
    null_ro_tree_wp h;
    h

(* Take any computation, ignore its Writes, you get a read only WP *)
let handle_into_ro #a (#l:rwops{~(List.Tot.memP Write l)}) #wp (f : unit -> AlgWP a (Write::l) wp)
  : AlgWP a l null_ro
  = AlgWP?.reflect (__tree_handle_into_ro (reify (f ())))

let ignore_writes #a (#l:rwops{~(List.Tot.memP Write l)}) #pre #post (f : unit -> AlgPP a (Write::l) pre post)
  : AlgPP a l pre (fun h0 x h1 -> h0 == h1)
  = handle_into_ro #a #l #(fun h0 p -> pre h0 /\ (forall y h1. post h0 y h1 ==> p (y, h1))) f
