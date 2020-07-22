module AlgHeap

(* Essentially a copy of AlgForAll but using a heap for the state *)

open Common
open FStar.Tactics
open FStar.List.Tot
open FStar.Universe
module WF = FStar.WellFounded
module L = Lattice
module Ghost = FStar.Ghost
module Map = FStar.Map
module T = FStar.Tactics

type loc = int
type state = Map.t loc int

type empty : Type u#aa =

type op =
  | Read
  | Write
  | Raise
  | Other of int

assume val other_inp : int -> Type u#0
let op_inp : op -> Type u#0 =
 function
 | Read -> unit
 | Write -> state
 | Raise -> exn
 | Other i -> other_inp i

assume val other_out : int -> Type u#0
let op_out : op -> Type =
 function
 | Read -> state
 | Write -> unit
 | Raise -> empty
 | Other i -> other_inp i

noeq
type tree0 (a:Type u#aa) : Type u#aa =
  | Return : a -> tree0 a
  | Op     : op:op -> i:(op_inp op) -> k:(op_out op -> tree0 a) -> tree0 a

type ops = list op

let rec abides #a (labs:ops) (f : tree0 a) : prop =
  begin match f with
  | Op a i k ->
    mem a labs /\ (forall o. (WF.axiom1 k o; abides labs (k o)))
  | Return _ -> True
  end

type tree (a:Type u#aa)
          (labs : list u#0 op)
  : Type u#aa
  =
  r:(tree0 a){abides labs r}

let rec interp_at (l1 l2 : ops) (l : op)
  : Lemma (mem l (l1@l2) == (mem l l1 || mem l l2))
          [SMTPat (mem l (l1@l2))]
  = match l1 with
    | [] -> ()
    | _::l1 -> interp_at l1 l2 l

let sublist (l1 l2 : ops) = forall x. mem x l1 ==> mem x l2

let rec sublist_at
  (l1 l2 : ops)
  : Lemma (sublist l1 (l1@l2) /\ sublist l2 (l1@l2))
          [SMTPatOr [[SMTPat (sublist l1 (l1@l2))];
                     [SMTPat (sublist l2 (l1@l2))]]]
  = match l1 with
    | [] -> ()
    | _::l1 -> sublist_at l1 l2

let sublist_at_self
  (l : ops)
  : Lemma (sublist l (l@l))
          [SMTPat (sublist l (l@l))]
  = ()
  
let rec abides_sublist_nopat #a (l1 l2 : ops) (c : tree0 a)
  : Lemma (requires (abides l1 c) /\ sublist l1 l2)
          (ensures (abides l2) c)
  = match c with
    | Return _ -> ()
    | Op a i k ->
      let sub o : Lemma (abides l2 (k o)) =
        FStar.WellFounded.axiom1 k o;
        abides_sublist_nopat l1 l2 (k o)
      in
      Classical.forall_intro sub

let abides_sublist #a (l1 l2 : ops) (c : tree0 a)
  : Lemma (requires (abides l1 c) /\ sublist l1 l2)
          (ensures (abides l2 c))
          [SMTPat (abides l2 c); SMTPat (sublist l1 l2)]
  = abides_sublist_nopat l1 l2 c
  
let abides_at_self #a
  (l : ops)
  (c : tree0 a)
  : Lemma (abides (l@l) c <==>  abides l c)
          [SMTPat (abides (l@l) c)]
  = (* Trigger some patterns *)
    assert (sublist l (l@l));
    assert (sublist (l@l) l)

let abides_app #a (l1 l2 : ops) (c : tree0 a)
  : Lemma (requires (abides l1 c \/ abides l2 c))
          (ensures (abides (l1@l2) c))
          [SMTPat (abides (l1@l2) c)]
  = sublist_at l1 l2

(* Folding a computation tree *)
val fold_with (#a #b:_) (#labs : ops)
           (f:tree a labs)
           (v : a -> b)
           (h: (o:op{mem o labs} -> op_inp o -> (op_out o -> b) -> b))
           : b
let rec fold_with #a #b #labs f v h =
  match f with
  | Return x -> v x
  | Op act i k ->
    let k' (o : op_out act) : b =
        WF.axiom1 k o;
       fold_with #_ #_ #labs (k o) v h
    in
    h act i k'

let handler_ty_l (o:op) (b:Type) (labs:ops) =
  op_inp o -> (op_out o -> tree b labs) -> tree b labs

let handler_ty (labs0 : ops) (b:Type) (labs1 : ops) : Type =
  o:op{mem o labs0} -> handler_ty_l o b labs1

(* The most generic handling construct, we use it to implement bind.
It is actually just a special case of folding. *)
val handle_with (#a #b:_) (#labs0 #labs1 : ops)
           (f:tree a labs0)
           (v : a -> tree b labs1)
           (h: handler_ty labs0 b labs1)
           : tree b labs1
let handle_with f v h = fold_with f v h

let return (a:Type) (x:a)
  : tree a []
  = Return x

let bind (a b : Type)
  (#labs1 #labs2 : ops)
  (c : tree a labs1)
  (f : (x:a -> tree b labs2))
  : Tot (tree b (labs1@labs2))
  = handle_with #_ #_ #labs1 #(labs1@labs2) c f (fun act i k -> Op act i k)
  
let subcomp (a:Type)
  (labs1 labs2 : ops)
  (f : tree a labs1)
  : Pure (tree a labs2)
         (requires (sublist labs1 labs2))
         (ensures (fun _ -> True))
  = f

let if_then_else
  (a : Type)
  (labs1 labs2 : ops)
  (f : tree a labs1)
  (g : tree a labs2)
  (p : bool)
  : Type
  = tree a (labs1@labs2)

let _get : tree state [Read] = Op Read () Return

let _put (s:state) : tree unit [Write] = Op Write s Return

[@@allow_informative_binders]
total // need this for catch!!
reifiable
reflectable
layered_effect {
  Alg : a:Type -> ops  -> Effect
  with
  repr         = tree;
  return       = return;
  bind         = bind;
  subcomp      = subcomp;
  if_then_else = if_then_else
}

let get () : Alg state [Read] =
  Alg?.reflect _get

unfold
let pure_monotonic #a (wp : pure_wp a) : Type =
  forall p1 p2. (forall x. p1 x ==> p2 x) ==> wp p1 ==> wp p2

//unfold
//let sp #a (wp : pure_wp a) : pure_post a =
//  fun x -> ~ (wp (fun y -> ~(x == y)))

let lift_pure_eff
 (a:Type)
 (wp : pure_wp a)
 (f : eqtype_as_type unit -> PURE a wp)
 : Pure (tree a [])
        (requires (wp (fun _ -> True) /\ pure_monotonic wp))
        (ensures (fun _ -> True))
 = Return (f ())

sub_effect PURE ~> Alg = lift_pure_eff

let put (s:state) : Alg unit [Write] =
  Alg?.reflect (_put s)

let raise #a (e:exn) : Alg a [Raise] =  
  Alg?.reflect (Op Raise e (fun e -> match e with))
  // funnily enough, the version below also succeeds from concluding
  // a==empty under the lambda since the context becomes inconsistent
  //Alg?.reflect (Op Raise e Return

type rwtree a = tree a [Read;Write]

let tbind : #a:_ -> #b:_ -> rwtree a -> (a -> rwtree b) -> rwtree b = fun c f -> bind _ _ c f

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

let rec interp_rdwr_tree #a (t : tree a [Read;Write]) (s:state) : Tot (a & state) =
  match t with
  | Return x -> (x, s)
  | Op Read _ k ->
    FStar.WellFounded.axiom1 k s;
    interp_rdwr_tree (k s) s
  | Op Write s k ->
    FStar.WellFounded.axiom1 k ();
    interp_rdwr_tree (k ()) s

let interp_as_fun #a (t : rwtree a) : (state -> a & state) =
  interp_rdwr_tree t

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

let repr (a : Type) (w: st_wp a) =
  c:(rwtree a){w `stronger` interp_as_wp c}

let return2 (a:Type) (x:a) : repr a (return_wp x) =
  interp_ret x;
  Return x

let bind2 (a : Type) (b : Type)
  (wp_v : st_wp a) (wp_f: a -> st_wp b)
  (v : repr a wp_v) (f : (x:a -> repr b (wp_f x)))
  : repr b (bind_wp wp_v wp_f) =
  interp_bind v f wp_v wp_f;
  tbind v f

let subcomp2 (a:Type) (w1 w2: st_wp a)
  (f : repr a w1)
  : Pure (repr a w2)
         (requires w2 `stronger` w1)
         (ensures fun _ -> True)
  = f

let if_then_else2 (a : Type) (w1 w2 : st_wp a)
    (f : repr a w1) (g : repr a w2) (b : bool) : Type =
  repr a (if b then w1 else w2)

total
reifiable
reflectable
layered_effect {
  AlgWP : a:Type -> st_wp a -> Effect
  with repr         = repr;
       return       = return2;
       bind         = bind2;
       subcomp      = subcomp2;
       if_then_else = if_then_else2
}

let get2 () : AlgWP state read_wp =
  AlgWP?.reflect _get

let put2 (s:state) : AlgWP unit (write_wp s) =
  AlgWP?.reflect (_put s)

unfold
let lift_pure_wp (#a:Type) (wp : pure_wp a) : st_wp a =
  fun s0 p -> wp (fun x -> p (x, s0))

let lift_pure_algwp (a:Type) wp (f:(eqtype_as_type unit -> PURE a wp))
  : Pure (repr a (lift_pure_wp wp)) // can't call f() here, so lift its wp instead
         (requires (wp (fun _ -> True)))
         (ensures (fun _ -> True))
  = let v : a = elim_pure f (fun _ -> True) in
    FStar.Monotonic.Pure.wp_monotonic_pure (); // need this lemma
    assert (forall p. wp p ==> p v); // this is key fact needed for the proof
    assert_norm (stronger (lift_pure_wp wp) (return_wp v));
    Return v

sub_effect PURE ~> AlgWP = lift_pure_algwp

let sel (r:loc) : AlgWP int (fun h0 p -> p (Map.sel h0 r, h0)) =
  let h = get2 () in
  Map.sel h r

let upd (r:loc) (v:int) : AlgWP unit (fun h0 p -> p ((), Map.upd h0 r v)) =
  let h = get2 () in
  put2 (Map.upd h r v)

let (!) = sel
let (:=) = upd

let modifies1 (l:loc) (h0 h1 : state) : Type0 =
  forall y. y <> l ==> Map.sel h0 y == Map.sel h1 y
 
let modifies (ls: list loc) (h0 h1 : state) : Type0 = 
  forall y. mem y ls \/ (Map.sel h0 y == Map.sel h1 y)

effect AlgPP (a:Type) (pre : state -> Type0) (post : state -> a -> state -> Type0) =
  AlgWP a (fun h0 p -> pre h0 /\ (forall y h1. post h0 y h1 ==> p (y, h1)))

let addx (l:loc) (x:int) : AlgPP unit (fun _ -> True) (fun h0 _ h1 -> modifies1 l h0 h1
                                                          /\ (Map.sel h1 l == x + Map.sel h0 l)) =
  l := !l + x

let swap (l1 l2 : loc) : AlgPP unit (fun _ -> l1 <> l2)
                                    (fun h0 _ h1 -> 
                                       modifies [l1;l2] h0 h1 /\
                                       Map.sel h1 l1 == Map.sel h0 l2 /\
                                       Map.sel h1 l2 == Map.sel h0 l1)
  =
  let r = !l2 in
  l2 := !l1;
  l1 := r

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

(* Same as above, but one doesn't have to think about WPs *)
let soundnessPP #a #pre #post (t : unit -> AlgPP a pre post)
  : s0:state{pre s0} -> r:(a & state){post s0 (fst r) (snd r)}
  = fun s0 -> reify (soundness #a #(fun h0 p -> pre h0 /\ (forall y h1. post h0 y h1 ==> p (y, h1))) t s0)
                 (fun r -> post s0 (fst r) (snd r))
                 ()
