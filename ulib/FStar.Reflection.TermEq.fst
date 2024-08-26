module FStar.Reflection.TermEq

open FStar.Stubs.Reflection.Types
open FStar.Stubs.Reflection.V2.Data
open FStar.Stubs.Reflection.V2.Builtins
module L = FStar.List.Tot


(* "SMT may not be able to prove the types of ... and ... to be equal,
if the proof fails, try annotating these with the same type" *)
#set-options "--warn_error -290"

(*
This file raised several limitations of the SMT encoding. Lines marked
with #2908 are seemingly consequences of issue #2908 and should be removed.
In fact many auxiliary lemmas should be removed as they should become
obvious. Lines marked with *** should not be needed.
*)

let rec memP_allP #a #b (top:b) (pred : (x:a{x << top}) -> Type) (x : a) (l : list a{l << top})
  : Lemma (requires allP top pred l /\ L.memP x l)
          (ensures x << top /\ pred x)
          [SMTPat (allP top pred l); SMTPat (L.memP x l)]
  = match l with
    | [] -> ()
    | y::ys ->
      if StrongExcludedMiddle.strong_excluded_middle (x == y) then () else memP_allP top pred x ys

let rec memP_allP0 #a (pred : a -> Type) (x : a) (l : list a)
  : Lemma (requires allP0 pred l /\ L.memP x l)
          (ensures pred x)
          [SMTPat (allP0 pred l); SMTPat (L.memP x l)]
  = match l with
    | [] -> ()
    | y::ys ->
      if StrongExcludedMiddle.strong_excluded_middle (x == y) then () else memP_allP0 pred x ys

let rec memP_dec #a (x : a) (l : list a)
  : Lemma (requires L.memP x l)
          (ensures x << l)
          [SMTPat (L.memP x l)]
  = match l with
    | [] -> ()
    | y::ys ->
      if StrongExcludedMiddle.strong_excluded_middle (x == y) then () else memP_dec x ys

(* FIXME: the only reason these are not exposed is to not contaminate
the namespace for most users, especially as `Eq` is already used in
Reflection.Formula. But there should not be a problem with using this
name fully-qualified. *)
private
type _cmpres =
  | Eq
  | Neq
  | Unknown

// Would it be easier for the proofs to be embedded in the _cmpres?
let valid #t (c:_cmpres) (x y : t) =
  match c with
  | Eq -> x == y
  | Neq -> x =!= y
  | Unknown -> True

type cmpres #t (x y : t) = c:_cmpres{valid c x y}

type comparator_for (t:Type) = x:t -> y:t -> cmpres x y

let (&&&) (#s : Type u#ss) (#t : Type u#tt) (#x #y : s) (#w #z : t)
  ($c1 : cmpres x y)
  ($c2 : cmpres w z)
  : cmpres (x,w) (y,z) =
  match c1, c2 with
  | Eq, Eq -> Eq
  | Neq, _
  | _, Neq -> Neq
  | _ -> Unknown

val bv_cmp : comparator_for bv
let bv_cmp x1 x2 =
  let v1 = inspect_bv x1 in
  let v2 = inspect_bv x2 in
  pack_inspect_bv x1;
  pack_inspect_bv x2;
  sealed_singl v1.sort v2.sort;
  if v1.index = v2.index then Eq else Neq

val namedv_cmp : comparator_for namedv
let namedv_cmp x1 x2 =
  let v1 = inspect_namedv x1 in
  let v2 = inspect_namedv x2 in
  pack_inspect_namedv x1;
  pack_inspect_namedv x2;
  sealed_singl v1.sort v2.sort;
  if v1.uniq = v2.uniq then Eq else Neq

val fv_cmp : comparator_for fv
let fv_cmp f1 f2 =
    pack_inspect_fv f1;
    pack_inspect_fv f2;
    let n1 = inspect_fv f1 in
    let n2 = inspect_fv f2 in
    if n1 = n2 then Eq else Neq

val opt_cmp : #a:Type -> comparator_for a -> comparator_for (option a)
let opt_cmp cmp o1 o2 =
  match o1, o2 with
  | None, None -> Eq
  | Some x, Some y -> cmp x y
  | _ -> Neq

val either_cmp : #a:Type -> #b:Type -> comparator_for a -> comparator_for b -> comparator_for (either a b)
let either_cmp cmpa cmpb e1 e2 =
  match e1, e2 with
  | Inl x, Inl y -> cmpa x y
  | Inr x, Inr y -> cmpb x y
  | _ -> Neq

val pair_cmp : #a:Type -> #b:Type -> comparator_for a -> comparator_for b -> comparator_for (a & b)
let pair_cmp cmpa cmpb (a1, b1) (a2, b2) =
  cmpa a1 a2 &&& cmpb b1 b2

val list_cmp : #a:Type u#aa -> comparator_for a -> comparator_for (list a)
let rec list_cmp #a cmp l1 l2 =
  match l1, l2 with
  | [], [] -> Eq
  | x::xs, y::ys -> cmp x y &&& list_cmp cmp xs ys
  | _ -> Neq

val list_dec_cmp :
#a:Type u#aa -> #b:Type u#bb -> top1:b -> top2:b ->
  f:(x:a -> y:a{x << top1 /\ y << top2} -> cmpres x y) ->
  l1:(list a) -> l2:(list a){l1 << top1 /\ l2 << top2} ->
  cmpres l1 l2
let rec list_dec_cmp #a top1 top2 cmp l1 l2 =
  match l1, l2 with
  | [], [] -> Eq
  | x::xs, y::ys -> cmp x y &&& list_dec_cmp top1 top2 cmp xs ys
  | _ -> Neq

val opt_dec_cmp : #a:Type -> #b:Type -> top1:b -> top2:b ->
  (f : (x:a -> y:a{x << top1 /\ y << top2} -> cmpres x y)) ->
  o1:(option a){o1 << top1} -> o2:(option a){o2 << top2} ->
  cmpres o1 o2
let opt_dec_cmp top1 top2 cmp o1 o2 =
  match o1, o2 with
  | None, None -> Eq
  | Some x, Some y -> cmp x y
  | _ -> Neq

val either_dec_cmp : #a:Type -> #b:Type -> #c:Type -> top1:c -> top2:c ->
  (x:a -> y:a{x<<top1 /\ y<<top2} -> cmpres x y) ->
  (x:b -> y:b{x<<top1 /\ y<<top2} -> cmpres x y) ->
  e1 :(either a b){e1 << top1} ->
  e2 :(either a b){e2 << top2} ->
  cmpres e1 e2
let either_dec_cmp top1 top2 cmpa cmpb e1 e2 =
  match e1, e2 with
  | Inl x, Inl y -> cmpa x y
  | Inr x, Inr y -> cmpb x y
  | _ -> Neq

val eq_cmp : #a:eqtype -> comparator_for a
let eq_cmp x y = if x = y then Eq else Neq

val range_cmp : comparator_for range
let range_cmp r1 r2 =
  Sealed.sealed_singl r1 r2;
  Eq

val ident_cmp : comparator_for ident
let ident_cmp i1 i2 =
  let iv1 = inspect_ident i1 in
  let iv2 = inspect_ident i2 in
  pack_inspect_ident i1;
  pack_inspect_ident i2;
  Sealed.sealed_singl (snd iv1) (snd iv2);
  eq_cmp (fst iv1) (fst iv2)

val univ_cmp : comparator_for universe
let rec univ_cmp (u1 u2 : universe) =
  pack_inspect_universe u1;
  pack_inspect_universe u2;
  let uv1 = inspect_universe u1 in
  let uv2 = inspect_universe u2 in
  match uv1, uv2 with
  | Uv_Zero, Uv_Zero -> Eq
  | Uv_Succ u1, Uv_Succ u2 -> univ_cmp u1 u2
  | Uv_Max us1, Uv_Max us2 -> list_dec_cmp u1 u2 univ_cmp us1 us2
  | Uv_BVar v1, Uv_BVar v2 -> eq_cmp v1 v2
  | Uv_Name n1, Uv_Name n2 -> ident_cmp n1 n2
  | Uv_Unif u1, Uv_Unif u2 -> Unknown
  | Uv_Unk, Uv_Unk -> Eq
  | _ -> Neq

val const_cmp : comparator_for vconst
let const_cmp c1 c2 =
  match c1, c2 with
  | C_Unit, C_Unit -> Eq
  | C_Int i1, C_Int i2 -> eq_cmp i1 i2
  | C_True, C_True -> Eq
  | C_False, C_False -> Eq
  | C_String s1, C_String s2 -> eq_cmp s1 s2
  | C_Range r1, C_Range r2 -> range_cmp r1 r2
  | C_Reify, C_Reify -> Eq
  | C_Reflect n1, C_Reflect n2 -> eq_cmp n1 n2
  | C_Real s1, C_Real s2 -> eq_cmp s1 s2
  | _ -> Neq

(* TODO. Or seal...? *)
val ctxu_cmp : comparator_for ctx_uvar_and_subst
let ctxu_cmp _ _ = Unknown

val term_cmp         : comparator_for term
val binder_cmp       : comparator_for binder
val aqual_cmp        : comparator_for aqualv
val arg_cmp          : comparator_for argv
val comp_cmp         : comparator_for comp
val pat_cmp          : comparator_for pattern
val pat_arg_cmp      : comparator_for (pattern & bool)
val br_cmp           : comparator_for branch
val match_returns_ascription_cmp : comparator_for match_returns_ascription

let rec term_cmp t1 t2 =
  pack_inspect_inv t1;
  pack_inspect_inv t2;
  let tv1 = inspect_ln t1 in
  let tv2 = inspect_ln t2 in
  match tv1, tv2 with
  | Tv_Unsupp, _
  | _, Tv_Unsupp -> Unknown
  | Tv_Var v1, Tv_Var v2 -> namedv_cmp v1 v2
  | Tv_BVar v1, Tv_BVar v2 -> bv_cmp v1 v2
  | Tv_FVar f1, Tv_FVar f2 -> fv_cmp f1 f2
  | Tv_UInst f1 u1, Tv_UInst f2 u2 ->
    fv_cmp f1 f2 &&& list_dec_cmp t1 t2 univ_cmp u1 u2

  | Tv_App h1 a1, Tv_App h2 a2 ->
    term_cmp h1 h2 &&& arg_cmp a1 a2

  | Tv_Abs b1 e1, Tv_Abs b2 e2 ->
    binder_cmp b1 b2
     &&& term_cmp e1 e2

  | Tv_Arrow b1 c1, Tv_Arrow b2 c2 ->
    binder_cmp b1 b2
     &&& comp_cmp c1 c2

  | Tv_Type u1, Tv_Type u2 ->
    univ_cmp u1 u2

  | Tv_Refine sb1 r1, Tv_Refine sb2 r2 ->
    binder_cmp sb1 sb2
     &&& term_cmp r1 r2

  | Tv_Const c1, Tv_Const c2 ->
    const_cmp c1 c2

  | Tv_Uvar n1 u1, Tv_Uvar n2 u2 ->
    eq_cmp n1 n2 &&& ctxu_cmp u1 u2

  | Tv_Let r1 attrs1 sb1 e1 b1, Tv_Let r2 attrs2 sb2 e2 b2 ->
    eq_cmp r1 r2
     &&& list_dec_cmp t1 t2 term_cmp attrs1 attrs2
     &&& binder_cmp sb1 sb2
     &&& term_cmp e1 e2
     &&& term_cmp b1 b2

  | Tv_Match sc1 o1 brs1, Tv_Match sc2 o2 brs2 ->
    term_cmp sc1 sc2
     &&& opt_dec_cmp t1 t2 match_returns_ascription_cmp o1 o2
     &&& list_dec_cmp t1 t2 br_cmp brs1 brs2

  | Tv_AscribedT e1 ta1 tacopt1 eq1, Tv_AscribedT e2 ta2 tacopt2 eq2 ->
    term_cmp e1 e2
     &&& term_cmp ta1 ta2
     &&& opt_dec_cmp t1 t2 term_cmp tacopt1 tacopt2
     &&& eq_cmp eq1 eq2

  | Tv_AscribedC e1 c1 tacopt1 eq1, Tv_AscribedC e2 c2 tacopt2 eq2 ->
    term_cmp e1 e2
     &&& comp_cmp c1 c2
     &&& opt_dec_cmp t1 t2 term_cmp tacopt1 tacopt2
     &&& eq_cmp eq1 eq2

  | Tv_Unknown, Tv_Unknown -> Eq

  | _ -> Neq

and arg_cmp (a1, q1) (a2, q2) =
  term_cmp a1 a2 &&& aqual_cmp q1 q2

and aqual_cmp a1 a2 =
  match a1, a2 with
  | Q_Implicit, Q_Implicit -> Eq
  | Q_Explicit, Q_Explicit -> Eq
  | Q_Equality, Q_Equality -> Eq
  | Q_Meta m1, Q_Meta m2 -> term_cmp m1 m2
  | _ -> Neq

and match_returns_ascription_cmp asc1 asc2 =
  let (b1, (tc1, tacopt1, eq1)) = asc1 in
  let (b2, (tc2, tacopt2, eq2)) = asc2 in
  binder_cmp b1 b2
   &&& either_dec_cmp asc1 asc2 term_cmp comp_cmp tc1 tc2
   &&& opt_dec_cmp asc1 asc2 term_cmp tacopt1 tacopt2
   &&& eq_cmp eq1 eq2

and binder_cmp b1 b2 =
  let bv1 = inspect_binder b1 in
  let bv2 = inspect_binder b2 in
  pack_inspect_binder b1;
  pack_inspect_binder b2;
  term_cmp bv1.sort bv2.sort
   &&& aqual_cmp bv1.qual bv2.qual
   &&& list_dec_cmp b1 b2 term_cmp bv1.attrs bv2.attrs

and comp_cmp c1 c2 =
  let cv1 = inspect_comp c1 in
  let cv2 = inspect_comp c2 in
  pack_inspect_comp_inv c1;
  pack_inspect_comp_inv c2;
  match cv1, cv2 with
  | C_Total t1, C_Total t2
  | C_GTotal t1, C_GTotal t2 ->
    term_cmp t1 t2

  | C_Lemma pre1 post1 pat1, C_Lemma pre2 post2 pat2 ->
    term_cmp pre1 pre2
     &&& term_cmp post1 post2
     &&& term_cmp pat1 pat2

  | C_Eff us1 ef1 t1 args1 dec1, C_Eff us2 ef2 t2 args2 dec2 ->
    list_dec_cmp c1 c2 univ_cmp us1 us2
     &&& eq_cmp ef1 ef2
     &&& term_cmp t1 t2
     &&& list_dec_cmp c1 c2 arg_cmp args1 args2
     &&& list_dec_cmp c1 c2 term_cmp dec1 dec2

  | _ -> Neq

and br_cmp br1 br2 =
  //pair_cmp pat_cmp term_cmp br1 br2
  pat_cmp (fst br1) (fst br2) &&& term_cmp (snd br1) (snd br2)

and pat_cmp p1 p2 =
  match p1, p2 with
  | Pat_Var x1 s1, Pat_Var x2 s2 ->
    sealed_singl x1 x2;
    sealed_singl s1 s2;
    Eq
  | Pat_Constant x1, Pat_Constant x2 -> const_cmp x1 x2
  | Pat_Dot_Term x1, Pat_Dot_Term x2 -> opt_dec_cmp p1 p2 term_cmp x1 x2
  | Pat_Cons head1 us1 subpats1, Pat_Cons head2 us2 subpats2 ->
    fv_cmp head1 head2
     &&& opt_dec_cmp p1 p2 (list_dec_cmp p1 p2 univ_cmp) us1 us2
     &&& list_dec_cmp p1 p2 pat_arg_cmp subpats1 subpats2

  | _ -> Neq

and pat_arg_cmp (p1, b1) (p2, b2) =
  pat_cmp p1 p2 &&& eq_cmp b1 b2

let defined r = ~(Unknown? r)

let def2 f l1 l2 =(forall x y. L.memP x l1 /\ L.memP y l2 ==> defined (f x y))

let rec defined_list #a (f : comparator_for a) (l1 l2 : list a)
  : Lemma (requires (def2 f l1 l2)) (ensures defined (list_cmp f l1 l2))
  = match l1, l2 with
    | [], [] -> ()
    | x::xs, y::ys -> defined_list f xs ys
    | _ -> ()

let rec defined_list_dec #a #b (t1 t2 : b) (f : comparator_for a)
  (l1 : list a{l1 << t1})
  (l2 : list a{l2 << t2})
  : Lemma (requires (def2 f l1 l2)) (ensures defined (list_dec_cmp t1 t2 f l1 l2))
  = match l1, l2 with
    | [], [] -> ()
    | x::xs, y::ys -> defined_list_dec t1 t2 f xs ys
    | _ -> ()

let faithful_univ_UvMax (u : universe) (us : list universe)
  : Lemma (requires inspect_universe u == Uv_Max us /\ faithful_univ u)
          (ensures allP u faithful_univ us)
  = assert_norm (faithful_univ u <==> allP u faithful_univ us) // #2908

let univ_eq_UvMax (u1 u2 : universe) (us1 us2 : list universe)
  : Lemma (requires inspect_universe u1 == Uv_Max us1 /\
                    inspect_universe u2 == Uv_Max us2)
          (ensures univ_cmp u1 u2 == list_dec_cmp u1 u2 univ_cmp us1 us2)
  = assert_norm (univ_cmp u1 u2 == list_dec_cmp u1 u2 univ_cmp us1 us2) // #2908

val univ_faithful_lemma (u1 u2 : universe) : Lemma (requires faithful_univ u1 /\ faithful_univ u2) (ensures defined (univ_cmp u1 u2))
let rec univ_faithful_lemma (u1 u2 : universe) =
  match inspect_universe u1, inspect_universe u2 with
  | Uv_Zero, Uv_Zero -> ()
  | Uv_Succ u1, Uv_Succ u2 -> univ_faithful_lemma u1 u2
  | Uv_Max us1, Uv_Max us2 ->
    (****)faithful_univ_UvMax u1 us1;
    (***)faithful_univ_UvMax u2 us2;
    univ_faithful_lemma_list u1 u2 us1 us2;
    (***)univ_eq_UvMax u1 u2 us1 us2;
    ()
  | Uv_BVar _, Uv_BVar _ -> ()
  | Uv_Name _, Uv_Name _ -> ()
  | _ -> ()

and univ_faithful_lemma_list #b (u1 u2 : b) (us1 : list universe{us1 << u1}) (us2 : list universe{us2 << u2})
  : Lemma (requires allP u1 faithful_univ us1 /\ allP u2 faithful_univ us2)
          (ensures defined (list_dec_cmp u1 u2 univ_cmp us1 us2))
          (decreases us1)
  =
    introduce forall x y. L.memP x us1 /\ L.memP y us2 ==> defined (univ_cmp x y) with
     (introduce forall y. L.memP x us1 /\ L.memP y us2 ==> defined (univ_cmp x y) with
      (introduce (L.memP x us1 /\ L.memP y us2) ==> (defined (univ_cmp x y)) with h. (
       univ_faithful_lemma x y
       )
      )
     )
    ;
    defined_list_dec u1 u2 univ_cmp us1 us2

(* Just a placeholder for now *)
val faithful_lemma (t1:term) (t2:term) : Lemma (requires faithful t1 /\ faithful t2) (ensures defined (term_cmp t1 t2))

#push-options "--z3rlimit 40"

let faithful_Tv_UInst (t : term) (f : fv) (us : list universe)
  : Lemma (requires inspect_ln t == Tv_UInst f us
                  /\ faithful t)
          (ensures allP t faithful_univ us)
  = ()

let faithful_Tv_Let (t : term) (recf : bool) (attrs : list term) (b:simple_binder) (ty:typ) (def body : term)
  : Lemma (requires inspect_ln t == Tv_Let recf attrs b def body
                  /\ faithful t)
          (ensures faithful_attrs attrs)
  = ()

let term_eq_Tv_Let (t1 t2 : term) (recf1 recf2 : bool) (attrs1 attrs2 : list term) (b1 b2:simple_binder)  (def1 def2 body1 body2: term)
  : Lemma (requires inspect_ln t1 == Tv_Let recf1 attrs1 b1 def1 body1
                  /\ inspect_ln t2 == Tv_Let recf2 attrs2 b2 def2 body2)
          (ensures term_cmp t1 t2 == (eq_cmp recf1 recf2 &&& list_dec_cmp t1 t2 term_cmp attrs1 attrs2 &&& binder_cmp b1 b2 &&& term_cmp def1 def2 &&& term_cmp body1 body2))
  = assume (term_cmp t1 t2 == (eq_cmp recf1 recf2 &&& list_dec_cmp t1 t2 term_cmp attrs1 attrs2 &&& binder_cmp b1 b2 &&& term_cmp def1 def2 &&& term_cmp body1 body2)) // #2908, somehow assert_norm also does not work

let faithful_Tv_Match (t : term) (sc : term) (o : option match_returns_ascription) (brs : list branch)
  : Lemma (requires inspect_ln t == Tv_Match sc o brs /\ faithful t)
          (ensures allP t faithful_branch brs)
  = assert_norm (faithful t ==> allP t faithful_branch brs)

let term_eq_Tv_Match (t1 t2 : term) (sc1 sc2 : term) (o1 o2 : option match_returns_ascription) (brs1 brs2 : list branch)
  : Lemma (requires inspect_ln t1 == Tv_Match sc1 o1 brs1
                  /\ inspect_ln t2 == Tv_Match sc2 o2 brs2)
          (ensures term_cmp t1 t2 == (term_cmp sc1 sc2
                    &&& opt_dec_cmp t1 t2 match_returns_ascription_cmp o1 o2
                    &&& list_dec_cmp t1 t2 br_cmp brs1 brs2))
  = assume (term_cmp t1 t2 == (term_cmp sc1 sc2
                    &&& opt_dec_cmp t1 t2 match_returns_ascription_cmp o1 o2
                   &&& list_dec_cmp t1 t2 br_cmp brs1 brs2)) // #2908, somehow assert_norm also does not work

let faithful_Pat_Cons (p : pattern) (f:fv) (ous : option universes) (subpats : list (pattern & bool))
  : Lemma (requires p == Pat_Cons f ous subpats /\ faithful_pattern p)
          (ensures allP p faithful_pattern_arg subpats)
  = assert_norm (faithful_pattern p ==> allP p faithful_pattern_arg subpats) // #2908

let pat_eq_Pat_Cons (p1 p2 : pattern) (f1 f2 : fv) (ous1 ous2 : option universes) (args1 args2 : list (pattern & bool))
  : Lemma (requires p1 == Pat_Cons f1 ous1 args1 /\ p2 == Pat_Cons f2 ous2 args2)
          (ensures pat_cmp p1 p2 == (fv_cmp f1 f2
                                    &&& opt_dec_cmp p1 p2 (list_dec_cmp p1 p2 univ_cmp) ous1 ous2
                                    &&& list_dec_cmp p1 p2 pat_arg_cmp args1 args2))
  = assert_norm (pat_cmp p1 p2 == (fv_cmp f1 f2
                                    &&& opt_dec_cmp p1 p2 (list_dec_cmp p1 p2 univ_cmp) ous1 ous2
                                    &&& list_dec_cmp p1 p2 pat_arg_cmp args1 args2))

let comp_eq_C_Eff (c1 c2 : comp) (us1 us2 : universes) (ef1 ef2 : name) (t1 t2 : typ) (args1 args2 : list argv) (dec1 dec2 : list term)
  : Lemma (requires inspect_comp c1 == C_Eff us1 ef1 t1 args1 dec1
                  /\ inspect_comp c2 == C_Eff us2 ef2 t2 args2 dec2)
          (ensures comp_cmp c1 c2 == (list_dec_cmp c1 c2 univ_cmp us1 us2
                                        &&& eq_cmp ef1 ef2
                                        &&& term_cmp t1 t2
                                        &&& list_dec_cmp c1 c2 arg_cmp args1 args2
                                        &&& list_dec_cmp c1 c2 term_cmp dec1 dec2))
  = assume (comp_cmp c1 c2 == (list_dec_cmp c1 c2 univ_cmp us1 us2
                                        &&& eq_cmp ef1 ef2
                                        &&& term_cmp t1 t2
                                        &&& list_dec_cmp c1 c2 arg_cmp args1 args2
                                        &&& list_dec_cmp c1 c2 term_cmp dec1 dec2)) // #2908, assert_norm doesn't work

let rec faithful_lemma (t1 t2 : term) =
  match inspect_ln t1, inspect_ln t2 with
  | Tv_Var _, Tv_Var _
  | Tv_BVar _, Tv_BVar _
  | Tv_FVar _, Tv_FVar _ -> ()
  | Tv_UInst f1 us1, Tv_UInst f2 us2 ->
    let tv1 = inspect_ln t1 in
    let tv2 = inspect_ln t2 in
    univ_faithful_lemma_list t1 t2 us1 us2;
    ()

  | Tv_Const c1, Tv_Const c2 -> ()
  | Tv_App h1 a1, Tv_App h2 a2 ->
    faithful_lemma h1 h2;
    faithful_lemma_arg a1 a2
  | Tv_Abs b1 t1, Tv_Abs b2 t2 ->
    faithful_lemma_binder b1 b2;
    faithful_lemma t1 t2
  | Tv_Arrow b1 c1, Tv_Arrow b2 c2 ->
    faithful_lemma_binder b1 b2;
    faithful_lemma_comp c1 c2
  | Tv_Type u1, Tv_Type u2 ->
    univ_faithful_lemma u1 u2
  | Tv_Refine b1 t1, Tv_Refine b2 t2 ->
    faithful_lemma_binder b1 b2;
    faithful_lemma t1 t2

  | Tv_Let r1 ats1 x1 e1 b1, Tv_Let r2 ats2 x2 e2 b2 ->
    faithful_lemma_attrs_dec t1 t2 ats1 ats2;
    faithful_lemma_binder x1 x2;
    faithful_lemma e1 e2;
    faithful_lemma b1 b2;
    (***)term_eq_Tv_Let t1 t2 r1 r2 ats1 ats2 x1 x2 e1 e2 b1 b2;
    ()

  | Tv_Match sc1 o1 brs1, Tv_Match sc2 o2 brs2 ->
    (***)faithful_Tv_Match t1 sc1 o1 brs1;
    (***)faithful_Tv_Match t2 sc2 o2 brs2;
    faithful_lemma sc1 sc2;
    faithful_lemma_branches t1 t2 brs1 brs2;
    (***)term_eq_Tv_Match t1 t2 sc1 sc2 o1 o2 brs1 brs2;
    ()

  | Tv_AscribedT e1 t1 tacopt1 eq1, Tv_AscribedT e2 t2 tacopt2 eq2 ->
    faithful_lemma e1 e2;
    faithful_lemma t1 t2;
    (match tacopt1, tacopt2 with | Some t1, Some t2 -> faithful_lemma t1 t2 | _ -> ());
    ()

  | Tv_AscribedC e1 c1 tacopt1 eq1, Tv_AscribedC e2 c2 tacopt2 eq2 ->
    faithful_lemma e1 e2;
    faithful_lemma_comp c1 c2;
    (match tacopt1, tacopt2 with | Some t1, Some t2 -> faithful_lemma t1 t2 | _ -> ());
    ()

  | Tv_Unknown, Tv_Unknown -> ()

  | _ -> assert (defined (term_cmp t1 t2)) (* rest of the cases trivial *)

and faithful_lemma_pattern (p1 p2 : pattern) : Lemma (requires faithful_pattern p1 /\ faithful_pattern p2) (ensures defined (pat_cmp p1 p2)) =
  match p1, p2 with
  | Pat_Var _ _, Pat_Var _ _ -> ()
  | Pat_Constant _, Pat_Constant _ -> ()
  | Pat_Dot_Term (Some t1), Pat_Dot_Term (Some t2) ->
    faithful_lemma t1 t2
  | Pat_Cons head1 univs1 subpats1, Pat_Cons head2 univs2 subpats2 ->
    (***)faithful_Pat_Cons p1 head1 univs1 subpats1;
    (***)faithful_Pat_Cons p2 head2 univs2 subpats2;
    let aux : squash (defined (opt_dec_cmp p1 p2 (list_dec_cmp p1 p2 univ_cmp) univs1 univs2)) =
      match univs1, univs2 with
      | Some us1, Some us2 ->
        univ_faithful_lemma_list p1 p2 us1 us2
      | _ -> ()
    in
    faithful_lemma_pattern_args p1 p2 subpats1 subpats2;
    (***)pat_eq_Pat_Cons p1 p2 head1 head2 univs1 univs2 subpats1 subpats2;
    ()

  | _ -> ()

and faithful_lemma_pattern_arg (pb1 pb2 : pattern & bool)
  : Lemma (requires faithful_pattern_arg pb1 /\ faithful_pattern_arg pb2)
          (ensures defined (pat_arg_cmp pb1 pb2))
  =
  let (p1, _) = pb1 in
  let (p2, _) = pb2 in
  faithful_lemma_pattern p1 p2

and faithful_lemma_pattern_args #b
  (top1 top2 : b)
  (pats1 : list (pattern & bool){pats1 << top1})
  (pats2 : list (pattern & bool){pats2 << top2})
  : Lemma (requires allP top1 faithful_pattern_arg pats1 /\ allP top2 faithful_pattern_arg pats2)
          (ensures defined (list_dec_cmp top1 top2 pat_arg_cmp pats1 pats2))
          (decreases pats1)
  =
  introduce forall x y. L.memP x pats1 /\ L.memP y pats2 ==> defined (pat_arg_cmp x y) with
   (introduce forall y. L.memP x pats1 /\ L.memP y pats2 ==> defined (pat_arg_cmp x y) with
    (introduce (L.memP x pats1 /\ L.memP y pats2) ==> (defined (pat_arg_cmp x y)) with h. (
     faithful_lemma_pattern_arg x y
     )
    )
   )
  ;
  defined_list_dec top1 top2 pat_arg_cmp pats1 pats2

and faithful_lemma_branch (br1 br2 : branch) : Lemma (requires faithful_branch br1 /\ faithful_branch br2) (ensures defined (br_cmp br1 br2)) =
  faithful_lemma_pattern (fst br1) (fst br2);
  faithful_lemma (snd br1) (snd br2)

and faithful_lemma_branches #b (top1 top2 : b)
  (brs1 : list branch{brs1 << top1})
  (brs2 : list branch{brs2 << top2})
  : Lemma (requires allP top1 faithful_branch brs1 /\ allP top2 faithful_branch brs2)
          (ensures defined (list_dec_cmp top1 top2 br_cmp brs1 brs2))
          (decreases brs1)
  =
  introduce forall x y. L.memP x brs1 /\ L.memP y brs2 ==> defined (br_cmp x y) with
   (introduce forall y. L.memP x brs1 /\ L.memP y brs2 ==> defined (br_cmp x y) with
    (introduce (L.memP x brs1 /\ L.memP y brs2) ==> (defined (br_cmp x y)) with h. (
     faithful_lemma_branch x y
     )
    )
   )
  ;
  defined_list_dec top1 top2 br_cmp brs1 brs2

and faithful_lemma_arg (a1 a2 : argv) : Lemma (requires faithful_arg a1 /\ faithful_arg a2) (ensures defined (arg_cmp a1 a2)) =
  faithful_lemma (fst a1) (fst a2);
  (match snd a1, snd a2 with | Q_Meta t1, Q_Meta t2 -> faithful_lemma t1 t2 | _ -> ())

and faithful_lemma_binder (b1 b2 : binder) : Lemma (requires faithful_binder b1 /\ faithful_binder b2) (ensures defined (binder_cmp b1 b2)) =
  let bv1 = inspect_binder b1 in
  let bv2 = inspect_binder b2 in
  faithful_lemma_qual bv1.qual bv2.qual;
  faithful_lemma bv1.sort bv2.sort;
  faithful_lemma_attrs_dec b1 b2 bv1.attrs bv2.attrs;
  assert_norm (
      (term_cmp bv1.sort bv2.sort
       &&& aqual_cmp bv1.qual bv2.qual
       &&& list_dec_cmp b1 b2 term_cmp bv1.attrs bv2.attrs) == binder_cmp b1 b2);
  ()

and faithful_lemma_qual (q1 q2 : aqualv) : Lemma (requires faithful_qual q1 /\ faithful_qual q2) (ensures defined (aqual_cmp q1 q2)) =
  match q1, q2 with
  | Q_Meta t1, Q_Meta t2 -> faithful_lemma t1 t2
  | _ -> ()

and faithful_lemma_attrs_dec #b (top1 top2 : b)
  (at1 : list term{at1 << top1})
  (at2 : list term{at2 << top2})
  : Lemma (requires faithful_attrs at1 /\ faithful_attrs at2)
          (ensures defined (list_dec_cmp top1 top2 term_cmp at1 at2))
          (decreases at1)
  =
  // TODO: factor out
  introduce forall x y. L.memP x at1 /\ L.memP y at2 ==> defined (term_cmp x y) with
   (introduce forall y. L.memP x at1 /\ L.memP y at2 ==> defined (term_cmp x y) with
    (introduce (L.memP x at1 /\ L.memP y at2) ==> (defined (term_cmp x y)) with h. (
     faithful_lemma x y
     )
    )
   )
  ;
  defined_list_dec top1 top2 term_cmp at1 at2

and faithful_lemma_comp (c1 c2 : comp) : Lemma (requires faithful_comp c1 /\ faithful_comp c2) (ensures defined (comp_cmp c1 c2)) =
  match inspect_comp c1, inspect_comp c2 with
  | C_Total t1, C_Total t2 -> faithful_lemma t1 t2
  | C_GTotal t1, C_GTotal t2 -> faithful_lemma t1 t2
  | C_Lemma pre1 post1 pat1, C_Lemma pre2 post2 pat2 ->
    faithful_lemma pre1 pre2;
    faithful_lemma post1 post2;
    faithful_lemma pat1 pat2
  | C_Eff us1 e1 r1 args1 dec1, C_Eff us2 e2 r2 args2 dec2 ->
    univ_faithful_lemma_list c1 c2 us1 us2;
    faithful_lemma r1 r2;
    introduce forall x y. L.memP x args1 /\ L.memP y args2 ==> defined (arg_cmp x y) with
     (introduce forall y. L.memP x args1 /\ L.memP y args2 ==> defined (arg_cmp x y) with
      (introduce (L.memP x args1 /\ L.memP y args2) ==> (defined (arg_cmp x y)) with h. (
       faithful_lemma_arg x y
       )
      )
     )
    ;
    defined_list_dec c1 c2 arg_cmp args1 args2;
    introduce forall x y. L.memP x dec1 /\ L.memP y dec2 ==> defined (term_cmp x y) with
     (introduce forall y. L.memP x dec1 /\ L.memP y dec2 ==> defined (term_cmp x y) with
      (introduce (L.memP x dec1 /\ L.memP y dec2) ==> (defined (term_cmp x y)) with h. (
       faithful_lemma x y
       )
      )
     )
    ;
    defined_list_dec c1 c2 term_cmp dec1 dec2;
    (***)comp_eq_C_Eff c1 c2 us1 us2 e1 e2 r1 r2 args1 args2 dec1 dec2;
    ()
  | _ -> ()
#pop-options


let term_eq (t1 t2 : term) : (b:bool{b ==> t1 == t2}) =
  Eq? (term_cmp t1 t2)

let term_eq_dec (t1 t2 : faithful_term) : (b:bool{b <==> t1 == t2}) =
  faithful_lemma t1 t2;
  Eq? (term_cmp t1 t2)

let univ_eq (u1 u2 : universe) : (b:bool{b ==> u1 == u2}) =
  Eq? (univ_cmp u1 u2)

let univ_eq_dec (u1 u2 : faithful_universe) : (b:bool{b <==> u1 == u2}) =
  univ_faithful_lemma u1 u2;
  Eq? (univ_cmp u1 u2)
