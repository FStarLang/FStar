module FStar.Reflection.TermEq

open FStar.Reflection.Types
open FStar.Reflection.Data
open FStar.Reflection.Builtins
open FStar.Ghost
module L = FStar.List.Tot

let rec allP #a (pred : a -> Type0) (l : list a) : Type0 =
  match l with
  | [] -> True
  | x::xs -> pred x /\ allP pred xs

let optP #a (pred : a -> Type0) (o : option a) : Type0 =
  match o with
  | None -> True
  | Some x -> pred x

let rec memP_allP #a (pred : a -> Type) (x : a) (l : list a)
  : Lemma (requires allP pred l /\ L.memP x l)
          (ensures pred x)
          [SMTPat (allP pred l); SMTPat (L.memP x l)]
  = match l with
    | [] -> ()
    | y::ys ->
      if StrongExcludedMiddle.strong_excluded_middle (x == y) then () else memP_allP pred x ys

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

val bv_eq : comparator_for bv
let bv_eq x1 x2 =
  let v1 = inspect_bv x1 in
  let v2 = inspect_bv x2 in
  assume (v1.bv_sort == v2.bv_sort); // FIXME: remove bv sorts
  pack_inspect_bv x1;
  pack_inspect_bv x2;
  if v1.bv_index = v2.bv_index then Eq else Neq

val fv_eq : comparator_for fv
let fv_eq f1 f2 =
    pack_inspect_fv f1;
    pack_inspect_fv f2;
    let n1 = inspect_fv f1 in
    let n2 = inspect_fv f2 in
    if n1 = n2 then Eq else Neq

// what? This must be provable
let dec_pair x y : Lemma (x << (x,y) /\ y << (x,y)) = admit ()

val opt_eq : #a:Type -> comparator_for a -> comparator_for (option a)
let opt_eq cmp o1 o2 =
  match o1, o2 with
  | None, None -> Eq
  | Some x, Some y -> cmp x y
  | _ -> Neq

val either_eq : #a:Type -> #b:Type -> comparator_for a -> comparator_for b -> comparator_for (either a b)
let either_eq cmpa cmpb e1 e2 =
  match e1, e2 with
  | Inl x, Inl y -> cmpa x y
  | Inr x, Inr y -> cmpb x y
  | _ -> Neq

val pair_eq : #a:Type -> #b:Type -> comparator_for a -> comparator_for b -> comparator_for (a & b)
let pair_eq cmpa cmpb (a1, b1) (a2, b2) =
  cmpa a1 a2 &&& cmpb b1 b2

val list_eq : #a:Type u#aa -> comparator_for a -> comparator_for (list a)
let rec list_eq #a cmp l1 l2 =
  match l1, l2 with
  | [], [] -> Eq
  | x::xs, y::ys -> cmp x y &&& list_eq cmp xs ys
  | _ -> Neq

val list_dec_eq :
#a:Type u#aa -> l1:(list a) -> l2:(list a) ->
  f:(x:a{x << l1} -> y:a{y << l2} -> cmpres x y) ->
  cmpres l1 l2
let rec list_dec_eq #a l1 l2 cmp =
  match l1, l2 with
  | [], [] -> Eq
  | x::xs, y::ys ->
    cmp x y &&& list_dec_eq xs ys cmp
  | _ -> Neq

val eq_eq : #a:eqtype -> comparator_for a
let eq_eq x y = if x = y then Eq else Neq

val range_eq : comparator_for range
let range_eq r1 r2 =
  Sealed.sealed_singl r1 r2;
  Eq

val ident_eq : comparator_for ident
let ident_eq i1 i2 =
  Sealed.sealed_singl (snd i1) (snd i2);
  eq_eq (fst i1) (fst i2)

(* Having a val for these somehow triggers #2894, and
using comparator_for insted of its unfolding gives #2895. *)
[@@admit_termination]
let rec univ_eq (u1 u2 : universe) : cmpres u1 u2 =
  pack_inspect_universe u1;
  pack_inspect_universe u2;
  let uv1 = inspect_universe u1 in
  let uv2 = inspect_universe u2 in
  match uv1, uv2 with
  | Uv_Unk, _
  | _, Uv_Unk -> Unknown
  | _ -> univ_view_eq uv1 uv2
and univ_view_eq (uv1 uv2 : universe_view) : cmpres uv1 uv2 =
  match uv1, uv2 with
  | Uv_Zero, Uv_Zero -> Eq
  | Uv_Succ u1, Uv_Succ u2 -> univ_eq u1 u2
  | Uv_Max us1, Uv_Max us2 -> list_eq univ_eq us1 us2
  | Uv_BVar v1, Uv_BVar v2 -> eq_eq v1 v2
  | Uv_Name n1, Uv_Name n2 -> ident_eq n1 n2
  | Uv_Unif u1, Uv_Unif u2 -> Unknown
  | Uv_Unk, Uv_Unk -> Eq

  | _ -> Neq

val const_eq : comparator_for vconst
let const_eq c1 c2 =
  match c1, c2 with
  | C_Unit, C_Unit -> Eq
  | C_Int i1, C_Int i2 -> eq_eq i1 i2
  | C_True, C_True -> Eq
  | C_False, C_False -> Eq
  | C_String s1, C_String s2 -> eq_eq s1 s2
  | C_Range r1, C_Range r2 -> range_eq r1 r2
  | C_Reify, C_Reify -> Eq
  | C_Reflect n1, C_Reflect n2 -> eq_eq n1 n2
  | _ -> Neq

(* TODO *)
val ctxu_eq : comparator_for ctx_uvar_and_subst
let ctxu_eq _ _ = Unknown

val term_eq         : t1:term -> t2:term -> cmpres t1 t2
val binder_eq       : b1:binder -> b2:binder -> cmpres b1 b2
val aqual_eq        : q1:aqualv -> q2:aqualv -> cmpres q1 q2
val term_view_eq    : x:term_view -> y:term_view -> cmpres x y
val arg_eq          : x:argv -> y:argv -> cmpres x y
val binding_bv_eq   : x:bv -> y:bv -> cmpres x y
val comp_eq         : x:comp -> y:comp -> cmpres x y
val pat_eq          : x:pattern -> y:pattern -> cmpres x y
val br_eq           : x:branch -> y:branch -> cmpres x y

// ^ FIXME! SMT encoding gets messed up when using abbreviated type.
//val term_view_eq    : comparator_for term_view
//val arg_eq          : comparator_for argv
//val binding_bv_eq   : comparator_for bv
//val comp_eq         : comparator_for comp
//val pat_eq          : comparator_for pattern
//val br_eq           : comparator_for branch
//val match_returns_ascription_eq : comparator_for match_returns_ascription

[@@admit_termination]
let rec term_eq t1 t2 =
  pack_inspect_inv t1;
  pack_inspect_inv t2;
  let tv1 = inspect_ln t1 in
  let tv2 = inspect_ln t2 in
  match tv1, tv2 with
  | Tv_Unknown, _
  | _, Tv_Unknown -> Unknown
  | _ -> term_view_eq tv1 tv2

and term_view_eq tv1 tv2 =
  match tv1, tv2 with
  | Tv_Var v1, Tv_Var v2 -> bv_eq v1 v2
  | Tv_BVar v1, Tv_BVar v2 -> bv_eq v1 v2
  | Tv_FVar f1, Tv_FVar f2 -> fv_eq f1 f2
  | Tv_UInst f1 u1, Tv_UInst f2 u2 ->
    fv_eq f1 f2 &&& list_eq univ_eq u1 u2

  | Tv_App h1 a1, Tv_App h2 a2 ->
    term_eq h1 h2 &&& arg_eq a1 a2

  | Tv_Abs b1 e1, Tv_Abs b2 e2 ->
    binder_eq b1 b2
     &&& term_eq e1 e2

  | Tv_Arrow b1 c1, Tv_Arrow b2 c2 ->
    binder_eq b1 b2
     &&& comp_eq c1 c2

  | Tv_Type u1, Tv_Type u2 ->
    univ_eq u1 u2

  | Tv_Refine v1 r1, Tv_Refine v2 r2 ->
    binding_bv_eq v1 v2 &&& term_eq r1 r2

  | Tv_Const c1, Tv_Const c2 ->
    const_eq c1 c2

  | Tv_Uvar n1 u1, Tv_Uvar n2 u2 ->
    eq_eq n1 n2 &&& ctxu_eq u1 u2

  | Tv_Let r1 attrs1 bv1 e1 b1, Tv_Let r2 attrs2 bv2 e2 b2 ->
    eq_eq r1 r2
     &&& list_eq term_eq attrs1 attrs2
     &&& binding_bv_eq bv1 bv2
     &&& term_eq e1 e2
     &&& term_eq b1 b2

  | Tv_Match sc1 o1 brs1, Tv_Match sc2 o2 brs2 ->
    term_eq sc1 sc2
     &&& opt_eq match_returns_ascription_eq o1 o2
     &&& list_eq br_eq brs1 brs2

  | Tv_AscribedT e1 t1 tacopt1 eq1, Tv_AscribedT e2 t2 tacopt2 eq2 ->
    term_eq e1 e2
     &&& term_eq t1 t2
     &&& opt_eq term_eq tacopt1 tacopt2
     &&& eq_eq eq1 eq2

  | Tv_AscribedC e1 c1 tacopt1 eq1, Tv_AscribedC e2 c2 tacopt2 eq2 ->
    term_eq e1 e2
     &&& comp_eq c1 c2
     &&& opt_eq term_eq tacopt1 tacopt2
     &&& eq_eq eq1 eq2

  | Tv_Unknown, Tv_Unknown -> Eq

  | _ -> Neq

and arg_eq (a1, q1) (a2, q2) =
  term_eq a1 a2 &&& aqual_eq q1 q2

and aqual_eq a1 a2 =
  match a1, a2 with
  | Q_Implicit, Q_Implicit -> Eq
  | Q_Explicit, Q_Explicit -> Eq
  | Q_Meta m1, Q_Meta m2 -> term_eq m1 m2
  | _ -> Neq

and binding_bv_eq x1 x2 =
  let v1 = inspect_bv x1 in
  let v2 = inspect_bv x2 in
  pack_inspect_bv x1;
  pack_inspect_bv x2;
  if v1.bv_index = v2.bv_index
   then term_eq v1.bv_sort v2.bv_sort
   else Neq

and match_returns_ascription_eq (b1, (tc1, tacopt1, eq1)) (b2, (tc2, tacopt2, eq2)) =
  binder_eq b1 b2
   &&& either_eq term_eq comp_eq tc1 tc2
   &&& opt_eq term_eq tacopt1 tacopt2
   &&& eq_eq eq1 eq2

and binder_eq b1 b2 =
  let bv1 = inspect_binder b1 in
  let bv2 = inspect_binder b2 in
  pack_inspect_binder b1;
  pack_inspect_binder b2;
  binding_bv_eq bv1.binder_bv bv2.binder_bv
   &&& aqual_eq bv1.binder_qual bv2.binder_qual
   &&& list_eq term_eq bv1.binder_attrs bv2.binder_attrs

and comp_eq c1 c2 =
  let cv1 = inspect_comp c1 in
  let cv2 = inspect_comp c2 in
  pack_inspect_comp_inv c1;
  pack_inspect_comp_inv c2;
  match cv1, cv2 with
  | C_Total t1, C_Total t2
  | C_GTotal t1, C_GTotal t2 ->
    term_eq t1 t2

  | C_Lemma pre1 post1 pat1, C_Lemma pre2 post2 pat2 ->
    term_eq pre1 pre2
     &&& term_eq post1 post2
     &&& term_eq pat1 pat2

  | C_Eff us1 ef1 t1 args1 dec1, C_Eff us2 ef2 t2 args2 dec2 ->
    list_eq univ_eq us1 us2
     &&& eq_eq ef1 ef2
     &&& term_eq t1 t2
     &&& list_eq arg_eq args1 args2
     &&& list_eq term_eq dec1 dec2

  | _ -> Neq

and br_eq br1 br2 = pair_eq pat_eq term_eq br1 br2

and pat_eq p1 p2 =
  match p1, p2 with
  | Pat_Var v1, Pat_Var v2 -> bv_eq v1 v2
  | Pat_Constant c1, Pat_Constant c2 -> const_eq c1 c2
  | Pat_Wild v1, Pat_Wild v2 -> bv_eq v1 v2
  | Pat_Dot_Term t1, Pat_Dot_Term t2 -> opt_eq term_eq t1 t2
  | Pat_Cons f1 us1 args1, Pat_Cons f2 us2 args2 ->
    fv_eq f1 f2
     &&& opt_eq (list_eq univ_eq) us1 us2
     &&& list_eq (pair_eq pat_eq eq_eq) args1 args2

  | _ -> Neq

let defined r = ~(Unknown? r)

// does not trigger it seems
//val defined_and (t1 t2 : _) (a b : t1) (c d : t2)
// (c1 : cmpres a b) (c2 : cmpres c d)
// : Lemma (requires (defined c1 /\ defined c2)) (ensures (defined (c1 &&& c2)))
//   [SMTPat (defined (c1 &&& c2))]
//let defined_and _ _ _ _ _ _ _ _ = ()

let def2 f l1 l2 =(forall x y. L.memP x l1 /\ L.memP y l2 ==> defined (f x y))

let rec defined_list #a (f : comparator_for a) (l1 l2 : list a)
  : Lemma (requires (def2 f l1 l2)) (ensures defined (list_eq f l1 l2))
  = match l1, l2 with
    | [], [] -> ()
    | x::xs, y::ys -> defined_list f xs ys
    | _ -> ()

val faithful_univ : universe -> Type0
[@@admit_termination]
let rec faithful_univ (u : universe) =
  match inspect_universe u with
  | Uv_Unk -> False
  | Uv_Unif _ -> False
  | Uv_Zero -> True
  | Uv_Succ u -> faithful_univ u
  | Uv_BVar _ -> True
  | Uv_Name _ -> True
  | Uv_Max us -> allP faithful_univ us

(* TODO: Add precondition *)
val univ_faithful_lemma (u1 u2 : universe) : Lemma (requires faithful_univ u1 /\ faithful_univ u2) (ensures defined (univ_eq u1 u2))
[@@admit_termination]
let rec univ_faithful_lemma (u1 u2 : universe) =
  match inspect_universe u1, inspect_universe u2 with
  | Uv_Zero, Uv_Zero -> ()
  | Uv_Succ u1, Uv_Succ u2 -> univ_faithful_lemma u1 u2
  | Uv_Max us1, Uv_Max us2 ->
    assert (faithful_univ u1);
    assert (inspect_universe u1 == Uv_Max us1);
    assume (allP faithful_univ us1); // ?????????
    assume (allP faithful_univ us2);
    univ_faithful_lemma_list us1 us2;
    assume (defined (univ_eq u1 u2)); // FIXME, somehow the pack/inspect is tripping the solver?
    ()
  | Uv_BVar _, Uv_BVar _ -> ()
  | Uv_Name _, Uv_Name _ -> ()
  | _ -> ()

and univ_faithful_lemma_list (us1 us2 : list universe)
  : Lemma (requires allP faithful_univ us1 /\ allP faithful_univ us2)
          (ensures defined (list_eq univ_eq us1 us2))
  =
    introduce forall x y. L.memP x us1 /\ L.memP y us2 ==> defined (univ_eq x y) with
     (introduce forall y. L.memP x us1 /\ L.memP y us2 ==> defined (univ_eq x y) with
      (introduce (L.memP x us1 /\ L.memP y us2) ==> (defined (univ_eq x y)) with h. (
       univ_faithful_lemma x y
       )
      )
     )
    ;
    defined_list univ_eq us1 us2

val faithful : term -> Type0
[@@admit_termination]
let rec faithful t =
  match inspect_ln t with
  | Tv_Var _
  | Tv_BVar _
  | Tv_FVar _
  | Tv_Const _ -> True

  | Tv_UInst f us ->
    allP faithful_univ us

  | Tv_Unknown -> False
  | Tv_App h a ->
    faithful h /\ faithful_arg a
  | Tv_Abs b t  ->
    faithful_binder b /\ faithful t
  | Tv_Arrow b c ->
    faithful_binder b /\ faithful_comp c
  | Tv_Type u ->
    faithful_univ u
  | Tv_Refine b phi ->
    faithful_binding_bv b /\ faithful phi

  | Tv_Uvar n u -> False
  | Tv_Let r ats x e b ->
    faithful_attrs ats
     /\ faithful_binding_bv x
     /\ faithful e
     /\ faithful b

  | Tv_Match sc o brs ->
    faithful sc
     /\ None? o // stopgap
     /\ allP faithful_branch brs

  | Tv_AscribedT e t tacopt eq ->
    faithful e
     /\ faithful t
     /\ optP faithful tacopt

  | Tv_AscribedC e c tacopt eq ->
    faithful e
     /\ faithful_comp c
     /\ optP faithful tacopt

and faithful_arg (a : argv) : Type0 =
  faithful (fst a) /\ faithful_qual (snd a)

and faithful_qual (q:aqualv) : Type0 =
  match q with
  | Q_Implicit -> True
  | Q_Explicit -> True
  | Q_Meta m -> faithful m

and faithful_binder (b:binder) : Type0 =
  match inspect_binder b with
  | {binder_bv = bv; binder_qual = q; binder_attrs = attrs} ->
    faithful_qual q /\ faithful_binding_bv bv /\ faithful_attrs attrs

and faithful_binding_bv (bv:bv) : Type0 =
  match inspect_bv bv with
  | {bv_index = i; bv_sort = s} -> faithful s

and faithful_branch (b : branch) : Type0 =
  let (p, t) = b in
  faithful_pattern p /\ faithful t

and faithful_pattern (p : pattern) : Type0 =
  match p with
  | Pat_Constant _ -> True
  | Pat_Cons h usopt pats ->
    optP (allP faithful_univ) usopt
     /\ allP faithful_pattern_arg pats
  (* non-binding bvs are always OK *)
  | Pat_Var bv -> True
  | Pat_Wild bv -> True
  | Pat_Dot_Term None -> True
  | Pat_Dot_Term (Some t) -> faithful t

and faithful_pattern_arg (pb : pattern * bool) =
  faithful_pattern (fst pb)

and faithful_attrs ats = allP faithful ats

and faithful_comp c =
  match inspect_comp c with
  | C_Total t -> faithful t
  | C_GTotal t -> faithful t
  | C_Lemma pre post pats -> faithful pre /\ faithful post /\ faithful pats
  | C_Eff us ef r args decs ->
    allP faithful_univ us
     /\ faithful r
     /\ allP faithful_arg args
     /\ allP faithful decs

val faithful_lemma (t1:term) (t2:term) : Lemma (requires faithful t1 /\ faithful t2) (ensures defined (term_eq t1 t2))

#push-options "--z3rlimit 20"

[@@admit_termination]
let rec faithful_lemma (t1 t2 : term) =
  match inspect_ln t1, inspect_ln t2 with
  | Tv_Var _, Tv_Var _
  | Tv_BVar _, Tv_BVar _
  | Tv_FVar _, Tv_FVar _ -> ()
  | Tv_UInst f1 us1, Tv_UInst f2 us2 ->
    univ_faithful_lemma_list us1 us2;
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
    faithful_lemma_binding_bv b1 b2;
    faithful_lemma t1 t2

  | Tv_Let r1 ats1 x1 e1 b1, Tv_Let r2 ats2 x2 e2 b2 ->
    assert (defined (eq_eq r1 r2));
    faithful_lemma_attrs ats1 ats2;
    faithful_lemma_binding_bv x1 x2;
    faithful_lemma e1 e2;
    faithful_lemma b1 b2;
    assert (defined (eq_eq r1 r2));
    assert (defined (list_eq term_eq ats1 ats2));
    assert (defined (binding_bv_eq x1 x2));
    assert (defined (term_eq e1 e2));
    assert (defined (term_eq b1 b2));
    assert (defined (eq_eq r1 r2
     &&& list_eq term_eq ats1 ats2
     &&& binding_bv_eq x1 x2
     &&& term_eq e1 e2
     &&& term_eq b1 b2));
    assume (defined (term_eq t1 t2)); // ???
    ()

  | Tv_Match sc1 o1 brs1, Tv_Match sc2 o2 brs2 ->
    faithful_lemma sc1 sc2;
    assert (None? o1);
    assert (None? o2);
    assume (allP faithful_branch brs1); // FIXME trivial
    assume (allP faithful_branch brs2);
    faithful_lemma_branches brs1 brs2;
    assert (defined (list_eq br_eq brs1 brs2));
    assert (defined (term_eq sc1 sc2
     &&& opt_eq match_returns_ascription_eq o1 o2
     &&& list_eq br_eq brs1 brs2));
    assume (defined (term_eq t1 t2)); // FIXME trivial
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

  | _ -> assert (defined (term_eq t1 t2)) (* rest of the cases trivial *)

and faithful_lemma_pattern (p1 p2 : pattern) : Lemma (requires faithful_pattern p1 /\ faithful_pattern p2) (ensures defined (pat_eq p1 p2)) =
  match p1, p2 with
  | Pat_Var v1, Pat_Var v2 -> ()
  | Pat_Constant c1, Pat_Constant c2 -> ()
  | Pat_Wild v1, Pat_Wild v2 -> ()
  | Pat_Dot_Term (Some t1), Pat_Dot_Term (Some t2) -> faithful_lemma t1 t2
  | Pat_Cons f1 us1 args1, Pat_Cons f2 us2 args2 ->
    (match us1, us2 with | Some us1, Some us2 -> univ_faithful_lemma_list us1 us2 | _ -> ());
    assume (defined (list_eq (pair_eq pat_eq eq_eq) args1 args2));
    assert (defined (
        fv_eq f1 f2
        &&& opt_eq (list_eq univ_eq) us1 us2
        &&& list_eq (pair_eq pat_eq eq_eq) args1 args2));
    assume (defined (pat_eq p1 p2));
    ()

  | _ -> ()

and faithful_lemma_branch (br1 br2 : branch) : Lemma (requires faithful_branch br1 /\ faithful_branch br2) (ensures defined (br_eq br1 br2)) =
  faithful_lemma_pattern (fst br1) (fst br2);
  faithful_lemma (snd br1) (snd br2)

and faithful_lemma_branches (brs1 brs2 : list branch) : Lemma (requires allP faithful_branch brs1 /\ allP faithful_branch brs2) (ensures defined (list_eq br_eq brs1 brs2)) =
  introduce forall x y. L.memP x brs1 /\ L.memP y brs2 ==> defined (br_eq x y) with
   (introduce forall y. L.memP x brs1 /\ L.memP y brs2 ==> defined (br_eq x y) with
    (introduce (L.memP x brs1 /\ L.memP y brs2) ==> (defined (br_eq x y)) with h. (
     faithful_lemma_branch x y
     )
    )
   )
  ;
  defined_list br_eq brs1 brs2

and faithful_lemma_arg (a1 a2 : argv) : Lemma (requires faithful_arg a1 /\ faithful_arg a2) (ensures defined (arg_eq a1 a2)) =
  faithful_lemma (fst a1) (fst a2);
  (match snd a1, snd a2 with | Q_Meta t1, Q_Meta t2 -> faithful_lemma t1 t2 | _ -> ())

and faithful_lemma_binder (b1 b2 : binder) : Lemma (requires faithful_binder b1 /\ faithful_binder b2) (ensures defined (binder_eq b1 b2)) =
  let bv1 = inspect_binder b1 in
  let bv2 = inspect_binder b2 in
  faithful_lemma_qual bv1.binder_qual bv2.binder_qual;
  faithful_lemma_binding_bv bv1.binder_bv bv2.binder_bv;
  faithful_lemma_attrs bv1.binder_attrs bv2.binder_attrs;
  assert (defined (binding_bv_eq bv1.binder_bv bv2.binder_bv));
  assert (defined (aqual_eq bv1.binder_qual bv2.binder_qual));
  assert (defined (binding_bv_eq bv1.binder_bv bv2.binder_bv &&& aqual_eq bv1.binder_qual bv2.binder_qual));
  assert (defined (list_eq term_eq bv1.binder_attrs bv2.binder_attrs));
  assert (defined (binding_bv_eq bv1.binder_bv bv2.binder_bv &&& aqual_eq bv1.binder_qual bv2.binder_qual &&& list_eq term_eq bv1.binder_attrs bv2.binder_attrs));
  assume (defined (binder_eq b1 b2)); // huh?
  ()

and faithful_lemma_qual (q1 q2 : aqualv) : Lemma (requires faithful_qual q1 /\ faithful_qual q2) (ensures defined (aqual_eq q1 q2)) =
  match q1, q2 with
  | Q_Meta t1, Q_Meta t2 -> faithful_lemma t1 t2
  | _ -> ()

and faithful_lemma_binding_bv (b1 b2 : bv) : Lemma (requires faithful_binding_bv b1 /\ faithful_binding_bv b2) (ensures defined (binding_bv_eq b1 b2)) =
  let v1 = inspect_bv b1 in
  let v2 = inspect_bv b2 in
  if v1.bv_index = v2.bv_index then faithful_lemma v1.bv_sort v2.bv_sort

and faithful_lemma_attrs (at1 at2 : list term) : Lemma (requires faithful_attrs at1 /\ faithful_attrs at2) (ensures defined (list_eq term_eq at1 at2)) =
  // TODO: factor out
  introduce forall x y. L.memP x at1 /\ L.memP y at2 ==> defined (term_eq x y) with
   (introduce forall y. L.memP x at1 /\ L.memP y at2 ==> defined (term_eq x y) with
    (introduce (L.memP x at1 /\ L.memP y at2) ==> (defined (term_eq x y)) with h. (
     faithful_lemma x y
     )
    )
   )
  ;
  defined_list term_eq at1 at2

and faithful_lemma_comp (c1 c2 : comp) : Lemma (requires faithful_comp c1 /\ faithful_comp c2) (ensures defined (comp_eq c1 c2)) =
  match inspect_comp c1, inspect_comp c2 with
  | C_Total t1, C_Total t2 -> faithful_lemma t1 t2
  | C_GTotal t1, C_GTotal t2 -> faithful_lemma t1 t2
  | C_Lemma pre1 post1 pat1, C_Lemma pre2 post2 pat2 ->
    faithful_lemma pre1 pre2;
    faithful_lemma post1 post2;
    faithful_lemma pat1 pat2
  | C_Eff us1 e1 r1 args1 dec1, C_Eff us2 e2 r2 args2 dec2 ->
    univ_faithful_lemma_list us1 us2;
    faithful_lemma r1 r2;
    introduce forall x y. L.memP x args1 /\ L.memP y args2 ==> defined (arg_eq x y) with
     (introduce forall y. L.memP x args1 /\ L.memP y args2 ==> defined (arg_eq x y) with
      (introduce (L.memP x args1 /\ L.memP y args2) ==> (defined (arg_eq x y)) with h. (
       faithful_lemma_arg x y
       )
      )
     )
    ;
    defined_list arg_eq args1 args2;
    introduce forall x y. L.memP x dec1 /\ L.memP y dec2 ==> defined (term_eq x y) with
     (introduce forall y. L.memP x dec1 /\ L.memP y dec2 ==> defined (term_eq x y) with
      (introduce (L.memP x dec1 /\ L.memP y dec2) ==> (defined (term_eq x y)) with h. (
       faithful_lemma x y
       )
      )
     )
    ;
    defined_list term_eq dec1 dec2;
    assert (defined(
    list_eq univ_eq us1 us2
     &&& eq_eq e1 e2
     &&& term_eq r1 r2
     &&& list_eq arg_eq args1 args2
     &&& list_eq term_eq dec1 dec2));
    assume (defined (comp_eq c1 c2)); // FIXME, trivial from above
    ()
  | _ -> ()
#pop-options

let faithful_term = t:term{faithful t}
let term_eq_dec (t1 t2 : faithful_term) : (b:bool{b <==> t1 == t2}) =
  faithful_lemma t1 t2;
  match term_eq t1 t2 with
  | Eq -> true
  | Neq -> false
