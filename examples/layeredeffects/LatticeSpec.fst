module LatticeSpec

open FStar.Tactics
open FStar.List.Tot

#set-options "--print_universes --print_implicits --print_effect_args"

// GM: Force a type equality by SMT
let coerce #a #b (x:a{a == b}) : b = x

let unreachable #a () : Pure a (requires False) (ensures (fun _ -> False)) = coerce "whatever"

type eff_label =
  | RD
  | WR
  | EXN

type annot = eff_label -> bool

// warning: if this is not annotated, `eqtype` is inferred
// as its type and the effect definition fails for some reason.
type state : Type = int

type pre_t    = state -> Type0
type post_t a = state -> option a -> state -> Type0

// this repr doesn't seem to work too well
type repr0 (a:Type u#aa)
           (pre : pre_t)
           (post : post_t u#aa a) // #2074
           : Type u#aa =
  s0:state{pre s0} -> Tot (r:(option a & state){post s0 (fst r) (snd r)})

let abides #a #pre #post (f : repr0 a pre post) (ann:annot) : Type0 =
    (ann RD  = false ==> (forall s0 s1. fst (f s0) == fst (f s1)))
  /\ (ann WR  = false ==> (forall s0. snd (f s0) == s0))
  /\ (ann EXN = false ==> (forall s0. Some? (fst (f s0))))

let interp (l : list eff_label) : annot =
  fun lab -> mem lab l

let rec interp_at (l1 l2 : list eff_label) (l : eff_label)
  : Lemma (interp (l1@l2) l == (interp l1 l || interp l2 l))
          [SMTPat (interp (l1@l2) l)]
  = match l1 with
    | [] -> ()
    | _::l1 -> interp_at l1 l2 l
    
let sublist (l1 l2 : list eff_label) =
  forall x. mem x l1 ==> mem x l2

let sublist_refl
  (l : list eff_label)
  : Lemma (sublist l l)
          [SMTPat (sublist l l)]
  = ()

let rec interp_sublist (l1 l2 : list eff_label) (l : eff_label)
  : Lemma (requires (sublist l1 l2))
          (ensures (interp l1 l ==> interp l2 l))
          [SMTPat (interp l1 l); SMTPat (sublist l1 l2)]
  = match l1 with
    | [] -> ()
    | _::l1 -> interp_sublist l1 l2 l

let rec sublist_at
  (l1 l2 : list eff_label)
  : Lemma (sublist l1 (l1@l2) /\ sublist l2 (l1@l2))
          [SMTPatOr [[SMTPat (sublist l1 (l1@l2))];
                     [SMTPat (sublist l2 (l1@l2))]]]
  = match l1 with
    | [] -> ()
    | _::l1 -> sublist_at l1 l2

type repr (a:Type u#aa)
          (pre : pre_t)
          (post : post_t u#aa a) // #2074
          (labs : list u#0 eff_label) // #2074
  : Type u#aa
  =
  r:(repr0 a pre post){abides r (interp labs)}

let ann_le (ann1 ann2 : annot) : Type0 =
  forall x. ann1 x ==> ann2 x
  
let return (a:Type u#aa) (x:a)
  : Tot (repr a (fun _ -> True) (fun s0 y s1 -> s0 == s1 /\ y == Some x) [])
  =
  // GM: Need to write it like this.. why?
  let r (s0:state) : Tot (r:(option a & state){snd r == s0 /\ fst r == Some x}) = (Some x, s0) in
  r

let bind_pre
 (a:Type) (pre1:pre_t) (post1:post_t a)
 (b:Type) (pre2:a -> pre_t) (post2:a -> post_t b)
 : pre_t
 = fun s0 -> pre1 s0 /\ (forall y s1. post1 s0 (Some y) s1 ==> pre2 y s1)
 
let bind_post
 (a:Type) (pre1:pre_t) (post1:post_t a)
 (b:Type) (pre2:a -> pre_t) (post2:a -> post_t b)
 : post_t b
 = fun s0 z s2 -> (exists s1 y. post1 s0 (Some y) s1 /\ post2 y s1 z s2)
                    \/ (post1 s0 None s2)

let bind (a b : Type)
  pre1 post1 pre2 post2
  (labs1 labs2 : list eff_label)
  (c : repr a pre1 post1 labs1)
  (f : (x:a -> repr b (pre2 x) (post2 x) labs2))
  : Tot (repr b (bind_pre  a pre1 post1 b pre2 post2)
                (bind_post a pre1 post1 b pre2 post2)
                (labs1@labs2))
  = let pre  = bind_pre  a pre1 post1 b pre2 post2 in
    let post = bind_post a pre1 post1 b pre2 post2 in
    let r (s0:state{pre s0}) : Tot (r:(option b & state){post s0 (fst r) (snd r)}) =
      match c s0 with
      | Some x, s1 ->
        assert (post1 s0 (Some x) s1);
        assert (pre2 x s1);
        f x s1
      | None, s1 -> None, s1
    in
    r

let subcomp (a:Type)
  (pre1 pre2 : pre_t)
  (post1 post2 : post_t a)
  (labs1 labs2 : list eff_label)
  (f : repr a pre1 post1 labs1)
  : Pure (repr a pre2 post2 labs2)
         (requires ((forall s0. pre2 s0 ==> pre1 s0) /\
                    (forall s0 r s1. post1 s0 r s1 ==> post2 s0 r s1) /\
                    sublist labs1 labs2))
         (ensures (fun _ -> True))
  = f

let ite (p q r : Type0) = (p ==> q) /\ ((~p) ==> r)

let if_then_else
  (a : Type)
  (pre1 pre2 : pre_t)
  (post1 post2 : post_t a)
  (labs1 labs2 : list eff_label)
  (f : repr a pre1 post1 labs1)
  (g : repr a pre2 post2 labs2)
  (b : bool)
  : Type
  = repr a (fun s0 -> ite b (pre1 s0) (pre2 s0))
           (fun s0 y s1 -> ite b (post1 s0 y s1) (post2 s0 y s1))
           (labs1@labs2)

[@@allow_informative_binders]
total // need this for catch!!
reifiable
reflectable
layered_effect {
  EFF : a:Type -> pre_t -> post_t a -> list eff_label -> Effect
  with
  repr         = repr;
  return       = return;
  bind         = bind;
  subcomp      = subcomp;
  if_then_else = if_then_else
}

unfold
let pure_monotonic #a (wp : pure_wp a) : Type =
  forall p1 p2. (forall x. p1 x ==> p2 x) ==> wp p1 ==> wp p2

unfold
let sp #a (wp : pure_wp a) : pure_post a =
  fun x -> ~ (wp (fun y -> ~(x == y)))

let post_of_wp #a (wp : pure_wp a) : post_t a =
  fun s0 r s1 -> s0 == s1 /\ Some? r /\ sp wp (Some?.v r)

let lift_pure_eff
 (a:Type)
 (wp : pure_wp a)
 (f : eqtype_as_type unit -> PURE a wp)
 : Pure (repr a (fun _ -> wp (fun _ -> True)) (post_of_wp wp) [])
        (requires pure_monotonic wp)
        (ensures (fun _ -> True))
 = let r (s0:state{wp (fun _ -> True)})
      : Tot (r:(option a & state){snd r == s0 /\ Some? (fst r) /\ sp wp (Some?.v (fst r))})
   =
    (Some (f ()), s0)
   in
   r
 
sub_effect PURE ~> EFF = lift_pure_eff

let _get : repr state (fun _ -> True) (fun s0 y s1 -> s1 == s0 /\ y == Some s0) [RD] =
  let ff (s0:state) : Tot (r:(option state & state){fst r == Some s0 /\ snd r == s0}) =
    (Some s0, s0)
  in
  ff
  
let get () : EFF int (fun _ -> True) (fun s0 y s1 -> s1 == s0 /\ y == Some s0) [RD] by (compute (); dump"") =
  EFF?.reflect _get
  
let _put (s:state) : repr unit (fun _ -> True) (fun _ y s1 -> s1 == s /\ y == Some ()) [WR] =
  // GM: pretty odd that I have to add `r == Some ()` here....
  let ff (_:state) : Tot (r:(option unit & state){fst r == Some () /\ snd r == s}) =
    (Some (), s)
  in
  ff
  
let put (s:state) : EFF unit (fun _ -> True) (fun _ y s1 -> s1 == s) [WR] =
  EFF?.reflect (_put s)

let _raise #a : repr a (fun _ -> True) (fun s0 _ s1 -> s1 == s0) [EXN] =
  let ff (s0:state) : Tot (r:(option a & state){fst r == None /\ snd r == s0}) =
    (None, s0)
  in
  ff

let raise #a () : EFF a (fun _ -> True) (fun s0 _ s1 -> s1 == s0) [EXN] =
  EFF?.reflect _raise

effect EFFT (a:Type) (labs:list eff_label) = EFF a (fun _ -> True) (fun _ _ _ -> True) labs

let test0 (x y : int) : EFFT int [RD; EXN] =
  let z = get () in
  if x + z > 0
  then raise ()
  else y - z

// need compute
let test1 (x y : int) : EFFT int [EXN; RD; WR] by (compute ())=
  let z = get () in
  if x + z > 0
  then raise ()
  else (put 42; y - z)

let sublist_at_self (l1 : list eff_label)
  : Lemma (sublist (l1@l1) l1)
          [SMTPat (l1@l1)]
  = Classical.forall_intro (List.Tot.Properties.append_mem l1 l1)

let labpoly #labs (f g : unit -> EFFT int labs) : EFFT  int labs =
  f () + g ()

(* no rollback *)
let catch #a #labs
  (f : unit -> EFFT a (EXN::labs))
  (g : unit -> EFFT a labs)
  : EFFT a labs
= EFF?.reflect begin
  let reif : repr a (fun _ -> True) (fun _ _ _ -> True) labs =
    fun s0 ->
      let reif_r : repr a (fun _ -> True) (fun _ _ _ -> True) (EXN::labs) = reify (f ()) in
      let r0 : option a & state = reif_r s0 in
      let r1 : option a & state =
        match r0 with
        | (Some v, s1) -> (Some v, s1)
        | (None, s1) -> reify (g ()) s1
        | _ -> unreachable ()
      in
      r1
  in
  reif
  end

let g #labs () : EFFT int labs = 42

let test_catch #labs (f : unit -> EFFT int [EXN;WR]) : EFFT int [WR] =
  catch f g

let test_catch2 (f : unit -> EFFT int [EXN;EXN;WR]) : EFFT int [EXN;WR] =
  catch f g
