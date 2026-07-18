module FStar.Tactics.LaxTermEq

open FStar.Stubs.Reflection.Types
open FStar.Stubs.Reflection.V2.Builtins
open FStar.Stubs.Reflection.V2.Data
open FStar.Stubs.Tactics.V2.Builtins

type comparator_for (t:Type) = x:t -> y:t -> Tac bool

val opt_eq : #a:Type -> comparator_for a -> comparator_for (option a)
let opt_eq cmp o1 o2 =
  match o1, o2 with
  | None, None -> true
  | Some x, Some y -> cmp x y
  | _ -> false

val either_eq : #a:Type -> #b:Type -> comparator_for a -> comparator_for b -> comparator_for (either a b)
let either_eq cmpa cmpb e1 e2 =
  match e1, e2 with
  | Inl x, Inl y -> cmpa x y
  | Inr x, Inr y -> cmpb x y
  | _ -> false

val pair_eq : #a:Type -> #b:Type -> comparator_for a -> comparator_for b -> comparator_for (a & b)
let pair_eq cmpa cmpb (a1, b1) (a2, b2) =
  if cmpa a1 a2 then cmpb b1 b2 else false

val list_eq : #a:Type u#aa -> comparator_for a -> comparator_for (list a)
let rec list_eq #a cmp l1 l2 =
  match l1, l2 with
  | [], [] -> true
  | x::xs, y::ys -> if cmp x y then list_eq cmp xs ys else false
  | _ -> false

val univ_eq : comparator_for universe
let rec univ_eq (u1 u2 : universe) =
  let u1 = compress_univ u1 in
  let u2 = compress_univ u2 in
  let uv1 = inspect_universe u1 in
  let uv2 = inspect_universe u2 in
  match uv1, uv2 with
  | Uv_Zero, Uv_Zero -> true
  | Uv_Succ u1, Uv_Succ u2 -> univ_eq u1 u2
  | Uv_Max us1, Uv_Max us2 -> list_eq univ_eq us1 us2
  | Uv_BVar v1, Uv_BVar v2 -> v1 = v2
  | Uv_Name id1, Uv_Name id2 ->
    fst (inspect_ident id1) = fst (inspect_ident id2)
  | Uv_Unif u1, Uv_Unif u2 -> false // We can't tell.
  | Uv_Unk, Uv_Unk -> false
  | _ -> false

val const_eq : comparator_for vconst
let const_eq c1 c2 =
  match c1, c2 with
  | C_Unit, C_Unit -> true
  | C_Int i1, C_Int i2 -> i1 = i2
  | C_True, C_True -> true
  | C_False, C_False -> true
  | C_String s1, C_String s2 -> s1 = s2
  | C_Range r1, C_Range r2 -> true
  | C_Reify, C_Reify -> true
  | C_Reflect n1, C_Reflect n2 -> n1 = n2
  | C_Real s1, C_Real s2 -> s1 = s2
  | C_Char s1, C_Char s2 -> s1 = s2
  | _ -> false

val term_eq         : comparator_for term
val binder_eq       : comparator_for binder
val aqual_eq        : comparator_for aqualv
val arg_eq          : comparator_for argv
val comp_eq         : comparator_for comp
val pat_eq          : comparator_for pattern
val pat_arg_eq      : comparator_for (pattern & bool)
val br_eq           : comparator_for branch
val match_returns_ascription_eq : comparator_for match_returns_ascription

let rec term_eq (t1 t2 : term) : Tac bool =
  let t1 = compress t1 in
  let t2 = compress t2 in
  let tv1 = inspect_ln t1 in
  let tv2 = inspect_ln t2 in
  match tv1, tv2 with
  | Tv_Unsupp, _
  | _, Tv_Unsupp -> false

  | Tv_Var v1, Tv_Var v2 ->
    (inspect_namedv v1).uniq = (inspect_namedv v2).uniq
  | Tv_BVar v1, Tv_BVar v2 ->
    (inspect_bv v1).index = (inspect_bv v2).index

  (* Ignore universe annotations on fvs *)
  | Tv_FVar  f1,   Tv_FVar f2
  | Tv_UInst f1 _, Tv_FVar f2
  | Tv_FVar  f1,   Tv_UInst f2 _
  | Tv_UInst f1 _, Tv_UInst f2 _ ->
    inspect_fv f1 = inspect_fv f2

  | Tv_App h1 a1, Tv_App h2 a2 ->
    if term_eq h1 h2 then arg_eq a1 a2 else false

  | Tv_Abs b1 e1, Tv_Abs b2 e2 ->
    if binder_eq b1 b2 then term_eq e1 e2 else false

  | Tv_Arrow b1 c1, Tv_Arrow b2 c2 ->
    if binder_eq b1 b2 then comp_eq c1 c2 else false

  | Tv_Type u1, Tv_Type u2 ->
    // Ignoring universe annotations
    (* univ_eq u1 u2 *)
    true

  | Tv_Refine sb1 r1, Tv_Refine sb2 r2 ->
    if binder_eq sb1 sb2 then term_eq r1 r2 else false

  | Tv_Const c1, Tv_Const c2 ->
    const_eq c1 c2

  | Tv_Uvar n1 _u1, Tv_Uvar n2 _u2 ->
    (* This case is sketchy, as the substitutions u1/u2 could
       be different, but this is what term_eq_old used to do.
       Apparently some Steel examples rely on this. *)
    n1 = n2

  | Tv_Let r1 attrs1 sb1 e1 b1, Tv_Let r2 attrs2 sb2 e2 b2 ->
    if not <| r1 = r2 then false else
    (* if not <| list_eq term_eq attrs1 attrs2 then false else *)
    if not <| binder_eq sb1 sb2 then false else
    if not <| term_eq e1 e2 then false else
    term_eq b1 b2

  | Tv_Match sc1 o1 brs1, Tv_Match sc2 o2 brs2 ->
    if not <| term_eq sc1 sc2 then false else
    if not <| opt_eq match_returns_ascription_eq o1 o2 then false else
    list_eq br_eq brs1 brs2

  | Tv_AscribedT t1 _ _ _, _
  | Tv_AscribedC t1 _ _ _, _ ->
    term_eq t1 t2
  | _, Tv_AscribedT t2 _ _ _
  | _, Tv_AscribedC t2 _ _ _ ->
    term_eq t1 t2

  | Tv_Unknown, Tv_Unknown -> true

  | _ -> false

and arg_eq (a1, q1) (a2, q2) =
  if term_eq a1 a2 then aqual_eq q1 q2 else false

and aqual_eq a1 a2 =
  match a1, a2 with
  | Q_Implicit, Q_Implicit -> true
  | Q_Explicit, Q_Explicit -> true
  | Q_Equality, Q_Equality -> true
  | Q_Meta m1, Q_Meta m2 -> term_eq m1 m2
  | _ -> false

and match_returns_ascription_eq asc1 asc2 =
  let (b1, (tc1, tacopt1, eq1)) = asc1 in
  let (b2, (tc2, tacopt2, eq2)) = asc2 in
  if not <| binder_eq b1 b2 then false else
  if not <| either_eq term_eq comp_eq tc1 tc2 then false else
  if not <| opt_eq term_eq tacopt1 tacopt2 then false else
  eq1 = eq2

and binder_eq b1 b2 =
  let bv1 = inspect_binder b1 in
  let bv2 = inspect_binder b2 in
  if not <| term_eq bv1.sort bv2.sort then false else
  if not <| aqual_eq bv1.qual bv2.qual then false else
  list_eq term_eq bv1.attrs bv2.attrs

and comp_eq c1 c2 =
  let cv1 = inspect_comp c1 in
  let cv2 = inspect_comp c2 in
  match cv1, cv2 with
  | C_Total t1, C_Total t2
  | C_GTotal t1, C_GTotal t2 ->
    term_eq t1 t2

  | C_Lemma pre1 post1 pat1, C_Lemma pre2 post2 pat2 ->
    if not <| term_eq pre1 pre2 then false else
    if not <| term_eq post1 post2 then false else
    term_eq pat1 pat2

  | C_Eff us1 ef1 t1 args1 dec1, C_Eff us2 ef2 t2 args2 dec2 ->
    // Ignoring universes
    (* if not <| list_eq univ_eq us1 us2 then false else *)
    if not <| (ef1 = ef2) then false else
    if not <| term_eq t1 t2 then false else
    // Ignore effect args
    (* if not <| list_eq arg_eq args1 args2 then false else *)
    (* if not <| list_eq term_eq dec1 dec2 then false else *)
    true

  | _ -> false

and br_eq br1 br2 =
  //pair_eq pat_eq term_eq br1 br2
  if not <| pat_eq (fst br1) (fst br2) then false else
  term_eq (snd br1) (snd br2)

and pat_eq p1 p2 =
  match p1, p2 with
  | Pat_Var v1 sort1, Pat_Var v2 sort2 ->
    true
  | Pat_Constant x1, Pat_Constant x2 -> const_eq x1 x2
  | Pat_Dot_Term x1, Pat_Dot_Term x2 -> opt_eq term_eq x1 x2
  | Pat_Cons head1 us1 subpats1,
    Pat_Cons head2 us2 subpats2 ->
    if not <| (inspect_fv head1 = inspect_fv head2) then false else
    (* if not <| opt_eq (list_eq univ_eq) us1 us2 then false else *)
    list_eq pat_arg_eq subpats1 subpats2

  | _ -> false

and pat_arg_eq (p1, b1) (p2, b2) =
  if not <| pat_eq p1 p2 then false else
  b1 = b2

let lax_term_eq (t1 t2 : term) : Tac bool =
  let r = term_eq t1 t2 in
  // let r' = term_eq_old t1 t2 in
  // if r <> r' then
  //   print ("term_eq: answering " ^ (if r then "true" else "false") ^
  //         " for " ^ term_to_string t1 ^ " and " ^ term_to_string t2);
  r

let lax_univ_eq (u1 u2 : universe) : Tac bool =
  univ_eq u1 u2
