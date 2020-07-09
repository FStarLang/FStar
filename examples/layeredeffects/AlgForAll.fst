module AlgForAll

open Common
open FStar.Calc
module WF = FStar.WellFounded
module FE = FStar.FunctionalExtensionality
module F = FStar.FunctionalExtensionality
module W = FStar.WellFounded
module T = FStar.Tactics
module ID5 = ID5
open Alg

type rwtree a = Alg.tree a [Read; Write]
let tbind : #a:_ -> #b:_ -> rwtree a -> (a -> rwtree b) -> rwtree b = fun c f -> Alg.bind _ _ c f

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
let rec interp_as_wp #a (t : rwtree a) : st_wp a =
  match t with
  | Return x -> return_wp x
  | Op Read _ k ->
    bind_wp read_wp (fun s -> WF.axiom1 k s; interp_as_wp (k s))
  | Op Write s k ->
    bind_wp (write_wp s) (fun (o:unit) -> WF.axiom1 k o; interp_as_wp (k o))

(* With handlers. Can only be done into []? See the use of `run`. *)
let interp_as_wp2 #a (t : rwtree a) : Alg (st_wp a) [] =
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

val interp_ret (#a:Type) (x:a) : Lemma (return_wp x `stronger` interp_as_wp (Return x))
let interp_ret x = ()

let wp_is_monotonic #a (wp : st_wp a) : Type0 =
  forall p1 p2 s0. (forall x s1. p1 (x, s1) ==> p2 (x, s1)) ==> wp s0 p1 ==> wp s0 p2

let bind_preserves_mon #a #b (wp : st_wp a) (f : a -> st_wp b)
  : Lemma (requires (wp_is_monotonic wp /\ (forall x. wp_is_monotonic (f x))))
          (ensures (wp_is_monotonic (bind_wp wp f)))
  = ()

let rec interp_monotonic #a (c:rwtree a) : Lemma (wp_is_monotonic (interp_as_wp c)) =
  match c with
  | Return x -> ()
  | Op Read _ k ->
    let aux (x:state) : Lemma (wp_is_monotonic (interp_as_wp (k x))) =
      WF.axiom1 k x;
      interp_monotonic (k x)
    in
    Classical.forall_intro aux;
    bind_preserves_mon read_wp (fun x -> interp_as_wp (k x))
  | Op Write s k ->
    let aux (x:unit) : Lemma (wp_is_monotonic (interp_as_wp (k x))) =
      WF.axiom1 k x;
      interp_monotonic (k x)
    in
    Classical.forall_intro aux;
    bind_preserves_mon (write_wp s) (fun x -> interp_as_wp (k x))

let elim_str #a (w1 w2 : st_wp a) (p : (a & state -> Type0)) (s0:state)
  : Lemma (requires (w1 <<= w2))
          (ensures w1 s0 p ==> w2 s0 p)
  = ()

(* Takes a while *)
let rec interp_morph #a #b (c : rwtree a) (f : a -> rwtree b) (p:_) (s0:_)
  : Lemma (interp_as_wp c s0 (fun (y, s1) -> interp_as_wp (f y) s1 p) == interp_as_wp (tbind c f) s0 p)
  = match c with
    | Return x -> ()
    | Op Read _ k ->
      let aux (o:state) : Lemma (interp_as_wp (k o) s0 (fun (y, s1) -> interp_as_wp (f y) s1 p)
                                        == interp_as_wp (tbind (k o) f) s0 p) =
        WF.axiom1 k o;
        interp_morph (k o) f p s0
      in
      Classical.forall_intro aux

    | Op Write s k ->
      let aux (o:unit) : Lemma (interp_as_wp (k o) s (fun (y, s1) -> interp_as_wp (f y) s1 p)
                                        == interp_as_wp (tbind (k o) f) s p) =
        WF.axiom1 k o;
        interp_morph (k o) f p s
      in
      Classical.forall_intro aux

    | _ ->
      unreachable ()

val interp_bind (#a #b:Type)
  (c : rwtree a) (f : a -> rwtree b)
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

let repr (a : Type) (w: st_wp a) = c:(rwtree a){w `stronger` interp_as_wp c}

let return (a:Type) (x:a) : repr a (return_wp x) =
  interp_ret x;
  Return x

let bind (a : Type) (b : Type)
  (#wp_v : st_wp a) (#wp_f: a -> st_wp b)
  (v : repr a wp_v) (f : (x:a -> repr b (wp_f x)))
  : repr b (bind_wp wp_v wp_f) =
  interp_bind v f wp_v wp_f;
  tbind v f

let subcomp (a:Type) (w1 w2: st_wp a)
  (f : repr a w1)
  : Pure (repr a w2)
         (requires w2 `stronger` w1)
         (ensures fun _ -> True)
  = f

let if_then_else (a : Type) (w1 w2 : st_wp a) (f : repr a w1) (g : repr a w2) (b : bool) : Type =
  repr a (if b then w1 else w2)

total
reifiable
reflectable
layered_effect {
  AlgWP : a:Type -> st_wp a -> Effect
  with repr         = repr;
       return       = return;
       bind         = bind;
       subcomp      = subcomp;
       if_then_else = if_then_else
}

let get () : AlgWP state read_wp =
  AlgWP?.reflect (Op Read () Return)

let put (s:state) : AlgWP unit (write_wp s) =
  AlgWP?.reflect (Op Write s Return)

unfold
let lift_pure_wp (#a:Type) (wp : pure_wp a) : st_wp a =
  fun s0 p -> wp (fun x -> p (x, s0))

let lift_pure_algwp (a:Type) wp (f:(eqtype_as_type unit -> PURE a wp))
  : Pure (repr a (lift_pure_wp wp)) // can't call f() here, so lift its wp instead
         (requires (wp (fun _ -> True)))
         (ensures (fun _ -> True))
  =
    let v : a = elim_pure f (fun _ -> True) in
    FStar.Monotonic.Pure.wp_monotonic_pure (); // need this lemma
    assert (forall p. wp p ==> p v); // this is key fact needed for the proof
    assert_norm (stronger (lift_pure_wp wp) (return_wp v));
    Return v

sub_effect PURE ~> AlgWP = lift_pure_algwp

let addx (x:int) : AlgWP unit (fun s0 p -> p ((), (s0+x))) =
  let y = get () in
  put (x+y)

(* GM: this used to require a call to T.norm [delta] when I had curry/uncurry going on.
I now realize they were not marked unfold, but that is pretty tricky... we should try
to find some general solution for these things. *)
let add_via_state (x y : int) : AlgWP int (fun s0 p -> p ((x+y), s0)) =
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

let rec interp_sem #a (t : rwtree a) (s0:state)
  : ID5.ID (a & state) (interp_as_wp t s0)
  = match t with
    | Return x -> (x, s0)
    | Op Read i k -> 
      WF.axiom1 k s0;
      interp_sem (k s0) s0
    | Op Write i k ->
      WF.axiom1 k ();
      interp_sem (k ()) i
    
let soundness #a #wp (t : unit -> AlgWP a wp)
  : Tot (s0:state -> ID5.ID (a & state) (wp s0))
  = let c = reify (t ()) in
    interp_sem c
