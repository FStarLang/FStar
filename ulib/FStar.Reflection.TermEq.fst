module FStar.Reflection.TermEq

open FStar.Stubs.Reflection.Types
open FStar.Stubs.Reflection.V2.Data
open FStar.Stubs.Reflection.V2.Builtins
open FStar.Reflection.TermSpec
module L = FStar.List.Tot


(* "SMT may not be able to prove the types of ... and ... to be equal,
if the proof fails, try annotating these with the same type" *)
#set-options "--warn_error -290"

(*
This module used to establish concrete term equality (==) via a
comparator, relying on the axiom [pack_inspect_inv]. It now establishes
*denotational* equality: [term_eq] guarantees that the two terms have the
same [denote_term] image, and [term_eq_dec] decides it for faithful
terms. Crucially, the term comparator no longer uses [pack_inspect_inv];
it only uses the [inspect]/[pack] round-trips on the leaves (bv, namedv,
fv, ident, universe, binder, comp), which remain valid.

The framework is generalized to carry, per type, a relation [r] that the
comparator establishes. Leaves keep the [==] relation ([eqrel]); the
mutual term block uses the denotational relations [teq], [aqeq], etc.
*)

let rec memP_allP #a #b (top:b) (pred : (x:a{x << top}) -> prop) (x : a) (l : list a{l << top})
  : Lemma (requires allP top pred l /\ L.memP x l)
          (ensures x << top /\ pred x)
          [SMTPat (allP top pred l); SMTPat (L.memP x l)]
  = match l with
    | [] -> ()
    | y::ys ->
      if x == y then () else memP_allP top pred x ys

let rec memP_allP0 #a (pred : a -> prop) (x : a) (l : list a)
  : Lemma (requires allP0 pred l /\ L.memP x l)
          (ensures pred x)
          [SMTPat (allP0 pred l); SMTPat (L.memP x l)]
  = match l with
    | [] -> ()
    | y::ys ->
      if x == y then () else memP_allP0 pred x ys

let rec memP_dec #a (x : a) (l : list a)
  : Lemma (requires L.memP x l)
          (ensures x << l)
          [SMTPat (L.memP x l)]
  = match l with
    | [] -> ()
    | y::ys ->
      if x == y then () else memP_dec x ys

(* FIXME: the only reason these are not exposed is to not contaminate
the namespace for most users, especially as `Eq` is already used in
Reflection.Formula. But there should not be a problem with using this
name fully-qualified. *)
private
type _cmpres =
  | Eq
  | Neq
  | Unknown

(* A comparison result, carrying a per-type relation [r]: [Eq] means the
two objects are related, [Neq] means they are not, [Unknown] is a
conservative "don't know". *)
let valid (#t:Type) (r : t -> t -> prop) (c:_cmpres) (x y : t) : prop =
  match c with
  | Eq -> r x y
  | Neq -> ~(r x y)
  | Unknown -> True

type cmpres' (#t:Type) (r : t -> t -> prop) (x y : t) = c:_cmpres{valid r c x y}

let eqrel (#t:Type) : t -> t -> prop = fun x y -> x == y

(* The [==] world, used by the leaves. *)
type cmpres (#t:Type) (x y : t) = cmpres' eqrel x y
type comparator_for (t:Type) = x:t -> y:t -> cmpres x y

(* The general, relation-carrying comparator. *)
type comparator_for' (#t:Type) (r : t -> t -> prop) = x:t -> y:t -> cmpres' r x y

(* Re-type a comparison result across relations/points given a
biconditional between the two relations at the two points. Matching on
[c] makes it robust: it is the identity on the underlying [_cmpres]. *)
let co (#a #b : Type)
       (#ra : a -> a -> prop) (#rb : b -> b -> prop)
       (#xa #ya : a) (#xb #yb : b)
       (c : cmpres' ra xa ya)
       (_ : squash (ra xa ya <==> rb xb yb))
  : cmpres' rb xb yb
  = match c with
    | Eq -> Eq
    | Neq -> Neq
    | Unknown -> Unknown

(* [co] preserves the underlying tag. *)
let co_defined (#a #b : Type)
       (#ra : a -> a -> prop) (#rb : b -> b -> prop)
       (#xa #ya : a) (#xb #yb : b)
       (c : cmpres' ra xa ya)
       (pf : squash (ra xa ya <==> rb xb yb))
  : Lemma (Unknown? (co c pf) == Unknown? c
        /\ Eq? (co c pf) == Eq? c
        /\ Neq? (co c pf) == Neq? c)
  = match c with
    | Eq -> ()
    | Neq -> ()
    | Unknown -> ()

let rel_pair (#s #t:Type) (rs : s -> s -> prop) (rt : t -> t -> prop)
  : (s & t) -> (s & t) -> prop
  = fun p q -> rs (fst p) (fst q) /\ rt (snd p) (snd q)

let (&&&) (#s : Type u#ss) (#t : Type u#tt)
          (#rs : s -> s -> prop) (#rt : t -> t -> prop)
          (#x #y : s) (#w #z : t)
  ($c1 : cmpres' rs x y)
  ($c2 : cmpres' rt w z)
  : cmpres' (rel_pair rs rt) (x, w) (y, z)
  = match c1, c2 with
    | Eq, Eq -> Eq
    | Neq, _
    | _, Neq -> Neq
    | _ -> Unknown

(* Pointwise relation lifting to lists/options/eithers. *)
let rec rel_list (#a:Type) (r : a -> a -> prop) (l1 l2 : list a) : prop =
  match l1, l2 with
  | [], [] -> True
  | x::xs, y::ys -> r x y /\ rel_list r xs ys
  | _ -> False

let rel_opt (#a:Type) (r : a -> a -> prop) (o1 o2 : option a) : prop =
  match o1, o2 with
  | None, None -> True
  | Some x, Some y -> r x y
  | _ -> False

let rel_either (#a #b:Type) (ra : a -> a -> prop) (rb : b -> b -> prop)
               (e1 e2 : either a b) : prop =
  match e1, e2 with
  | Inl x, Inl y -> ra x y
  | Inr x, Inr y -> rb x y
  | _ -> False

(* ----- The [==] combinators, used by the leaves. ----- *)

val opt_cmp : #a:Type -> comparator_for a -> comparator_for (option a)
let opt_cmp cmp o1 o2 =
  match o1, o2 with
  | None, None -> Eq
  | Some x, Some y -> cmp x y
  | _ -> Neq

val pair_cmp : #a:Type -> #b:Type -> comparator_for a -> comparator_for b -> comparator_for (a & b)
let pair_cmp cmpa cmpb (a1, b1) (a2, b2) =
  co (cmpa a1 a2 &&& cmpb b1 b2) ()

val list_cmp : #a:Type u#aa -> comparator_for a -> comparator_for (list a)
let rec list_cmp #a cmp l1 l2 =
  match l1, l2 with
  | [], [] -> Eq
  | x::xs, y::ys -> co (cmp x y &&& list_cmp cmp xs ys) ()
  | _ -> Neq

val list_dec_cmp :
#a:Type u#aa -> #b:Type u#bb -> top1:b -> top2:b ->
  f:(x:a -> y:a{x << top1 /\ y << top2} -> cmpres x y) ->
  l1:(list a) -> l2:(list a){l1 << top1 /\ l2 << top2} ->
  cmpres l1 l2
let rec list_dec_cmp #a top1 top2 cmp l1 l2 =
  match l1, l2 with
  | [], [] -> Eq
  | x::xs, y::ys -> co (cmp x y &&& list_dec_cmp top1 top2 cmp xs ys) ()
  | _ -> Neq

val eq_cmp : #a:eqtype -> comparator_for a
let eq_cmp x y = if x = y then Eq else Neq

(* ----- The relation-carrying combinators, used by the term block. ----- *)

val list_dec_cmp' :
  #a:Type u#aa -> #b:Type u#bb -> #r:(a -> a -> prop) -> top1:b -> top2:b ->
  f:(x:a -> y:a{x << top1 /\ y << top2} -> cmpres' r x y) ->
  l1:(list a) -> l2:(list a){l1 << top1 /\ l2 << top2} ->
  cmpres' (rel_list r) l1 l2
let rec list_dec_cmp' #a #b #r top1 top2 cmp l1 l2 =
  match l1, l2 with
  | [], [] -> Eq
  | x::xs, y::ys -> co (cmp x y &&& list_dec_cmp' top1 top2 cmp xs ys) ()
  | _ -> Neq

val opt_dec_cmp' : #a:Type -> #b:Type -> #r:(a -> a -> prop) -> top1:b -> top2:b ->
  (f : (x:a -> y:a{x << top1 /\ y << top2} -> cmpres' r x y)) ->
  o1:(option a){o1 << top1} -> o2:(option a){o2 << top2} ->
  cmpres' (rel_opt r) o1 o2
let opt_dec_cmp' #a #b #r top1 top2 cmp o1 o2 =
  match o1, o2 with
  | None, None -> Eq
  | Some x, Some y -> co (cmp x y) ()
  | _ -> Neq

val either_dec_cmp' : #a:Type -> #b:Type -> #c:Type ->
  #ra:(a -> a -> prop) -> #rb:(b -> b -> prop) -> top1:c -> top2:c ->
  (x:a -> y:a{x<<top1 /\ y<<top2} -> cmpres' ra x y) ->
  (x:b -> y:b{x<<top1 /\ y<<top2} -> cmpres' rb x y) ->
  e1 :(either a b){e1 << top1} ->
  e2 :(either a b){e2 << top2} ->
  cmpres' (rel_either ra rb) e1 e2
let either_dec_cmp' top1 top2 cmpa cmpb e1 e2 =
  match e1, e2 with
  | Inl x, Inl y -> co (cmpa x y) ()
  | Inr x, Inr y -> co (cmpb x y) ()
  | _ -> Neq

(* ----- Leaves: they keep the [==] relation. ----- *)

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

val range_cmp : comparator_for range
let range_cmp r1 r2 =
  eq_cmp r1 r2

val ident_cmp : comparator_for ident
let ident_cmp i1 i2 =
  let iv1 = inspect_ident i1 in
  let iv2 = inspect_ident i2 in
  pack_inspect_ident i1;
  pack_inspect_ident i2;
  co (eq_cmp (fst iv1) (fst iv2) &&& eq_cmp (snd iv1) (snd iv2)) ()

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
  | C_Char c1, C_Char c2 -> eq_cmp c1 c2
  | _ -> Neq

(* TODO. Or seal...? *)
val ctxu_cmp : comparator_for ctx_uvar_and_subst
let ctxu_cmp _ _ = Unknown

(* -------------------------------------------------------------------- *)
(* Relations for the mutual term block: these are the *denotational*
   relations. *)

let teq   (x y : term)     : prop = denote_term x == denote_term y
let aqeq  (q1 q2 : aqualv) : prop = denote_aqualv q1 == denote_aqualv q2
let argeq (a1 a2 : argv)   : prop =
  denote_term (fst a1) == denote_term (fst a2)
  /\ denote_aqualv (snd a1) == denote_aqualv (snd a2)
let beq   (b1 b2 : binder) : prop = denote_binder b1 == denote_binder b2
let ceq   (c1 c2 : comp)   : prop = denote_comp c1 == denote_comp c2
let peq   (p1 p2 : pattern): prop = denote_pattern p1 == denote_pattern p2
let breq  (r1 r2 : branch) : prop =
  denote_pattern (fst r1) == denote_pattern (fst r2)
  /\ denote_term (snd r1) == denote_term (snd r2)
let pareq (x y : pattern & bool) : prop =
  denote_pattern (fst x) == denote_pattern (fst y) /\ snd x == snd y
let maeq  (a1 a2 : match_returns_ascription) : prop =
  denote_ret (Some a1) == denote_ret (Some a2)

(* -------------------------------------------------------------------- *)
(* Injectivity of [denote_universe] (universes carry no ranges, so this
   is genuinely injective). Needed to bridge the [==] universe
   comparator into the denotational world. *)

let us_head (s:universe_spec) : GTot nat =
  match s with
  | Us_Zero -> 0 | Us_Succ _ -> 1 | Us_Max _ -> 2 | Us_BVar _ -> 3
  | Us_Name _ -> 4 | Us_Unif _ -> 5 | Us_Unk -> 6

let uv_head (u:universe) : GTot nat =
  match inspect_universe u with
  | Uv_Zero -> 0 | Uv_Succ _ -> 1 | Uv_Max _ -> 2 | Uv_BVar _ -> 3
  | Uv_Name _ -> 4 | Uv_Unif _ -> 5 | Uv_Unk -> 6

let univ_head_lemma (u:universe)
  : Lemma (us_head (denote_universe u) == uv_head u)
          [SMTPat (denote_universe u)]
  = match inspect_universe u with
    | Uv_Zero | Uv_Succ _ | Uv_Max _ | Uv_BVar _ | Uv_Name _ | Uv_Unif _ | Uv_Unk -> ()

let denote_universe_Max (u:universe) (us:list universe{us << u})
  : Lemma (requires inspect_universe u == Uv_Max us)
          (ensures denote_universe u == Us_Max (map_dec u denote_universe us))
  = FStar.Pervasives.norm_spec [zeta; iota; delta_only [`%denote_universe]] (denote_universe u)

let rec denote_universe_inj (u1 u2 : universe)
  : Lemma (requires denote_universe u1 == denote_universe u2)
          (ensures u1 == u2)
          (decreases u1)
  = pack_inspect_universe u1;
    pack_inspect_universe u2;
    match inspect_universe u1, inspect_universe u2 with
    | Uv_Zero, Uv_Zero -> ()
    | Uv_Succ a, Uv_Succ b -> denote_universe_inj a b
    | Uv_Max us1, Uv_Max us2 ->
      denote_universe_Max u1 us1;
      denote_universe_Max u2 us2;
      denote_universes_inj u1 u2 us1 us2
    | Uv_BVar _, Uv_BVar _ -> ()
    | Uv_Name _, Uv_Name _ -> ()
    | Uv_Unif _, Uv_Unif _ -> ()
    | Uv_Unk, Uv_Unk -> ()
    | _ -> ()

and denote_universes_inj (top1 top2 : universe)
  (us1 : list universe{us1 << top1}) (us2 : list universe{us2 << top2})
  : Lemma (requires map_dec top1 denote_universe us1 == map_dec top2 denote_universe us2)
          (ensures us1 == us2)
          (decreases us1)
  = match us1, us2 with
    | [], [] -> ()
    | x::xs, y::ys ->
      denote_universe_inj x y;
      denote_universes_inj top1 top2 xs ys
    | _ -> ()

let denote_universe_inj_iff (u1 u2 : universe)
  : Lemma (denote_universe u1 == denote_universe u2 <==> u1 == u2)
  = introduce (denote_universe u1 == denote_universe u2) ==> (u1 == u2)
    with _. denote_universe_inj u1 u2

(* -------------------------------------------------------------------- *)
(* Bridging lemmas: connect the pointwise relations produced by the
   combinators to the [denote_*] list/option functions. *)

let rec bridge_terms (l1 l2 : list term)
  : Lemma (ensures (rel_list teq l1 l2 <==> denote_terms l1 == denote_terms l2))
          (decreases l1)
  = match l1, l2 with
    | [], [] -> ()
    | x::xs, y::ys -> bridge_terms xs ys
    | _ -> ()

let rec bridge_args (l1 l2 : list argv)
  : Lemma (ensures (rel_list argeq l1 l2 <==> denote_args l1 == denote_args l2))
          (decreases l1)
  = match l1, l2 with
    | [], [] -> ()
    | (t1,q1)::xs, (t2,q2)::ys -> bridge_args xs ys
    | _ -> ()

let rec bridge_universes (l1 l2 : list universe)
  : Lemma (ensures (rel_list eqrel l1 l2 <==> denote_universes l1 == denote_universes l2))
          (decreases l1)
  = match l1, l2 with
    | [], [] -> ()
    | x::xs, y::ys ->
      denote_universe_inj_iff x y;
      bridge_universes xs ys
    | _ -> ()

let rec bridge_branches (l1 l2 : list branch)
  : Lemma (ensures (rel_list breq l1 l2 <==> denote_branches l1 == denote_branches l2))
          (decreases l1)
  = match l1, l2 with
    | [], [] -> ()
    | (p1,t1)::xs, (p2,t2)::ys -> bridge_branches xs ys
    | _ -> ()

let rec bridge_subpats (l1 l2 : list (pattern & bool))
  : Lemma (ensures (rel_list pareq l1 l2 <==> denote_subpats l1 == denote_subpats l2))
          (decreases l1)
  = match l1, l2 with
    | [], [] -> ()
    | (p1,b1)::xs, (p2,b2)::ys -> bridge_subpats xs ys
    | _ -> ()

let bridge_opt_term (o1 o2 : option term)
  : Lemma (rel_opt teq o1 o2 <==> denote_opt_term o1 == denote_opt_term o2)
  = match o1, o2 with
    | Some x, Some y -> ()
    | _ -> ()

let bridge_ret (o1 o2 : option match_returns_ascription)
  : Lemma (rel_opt maeq o1 o2 <==> denote_ret o1 == denote_ret o2)
  = match o1, o2 with
    | Some a1, Some a2 -> ()
    | _ -> ()

(* The [option (list universe)] that appears in [Pat_Cons]. *)
let denote_pat_univs (o : option (list universe)) : option (list universe_spec) =
  match o with
  | None -> None
  | Some us -> Some (denote_universes us)

let bridge_pat_univs (o1 o2 : option (list universe))
  : Lemma (rel_opt (rel_list eqrel) o1 o2 <==> denote_pat_univs o1 == denote_pat_univs o2)
  = match o1, o2 with
    | Some us1, Some us2 -> bridge_universes us1 us2
    | _ -> ()

(* The [either term comp] under a match ascription. *)
let denote_either (tc : either term comp) : either term_spec comp_spec =
  match tc with
  | Inl t -> Inl (denote_term t)
  | Inr c -> Inr (denote_comp c)

let bridge_either (e1 e2 : either term comp)
  : Lemma (rel_either teq ceq e1 e2 <==> denote_either e1 == denote_either e2)
  = match e1, e2 with
    | Inl x, Inl y -> ()
    | Inr x, Inr y -> ()
    | _ -> ()

(* -------------------------------------------------------------------- *)
(* Inspect-keyed denotation lemmas: [denote_term t] for a known view. *)

let denote_Var (t:term) (v:namedv)
  : Lemma (requires inspect_ln t == Tv_Var v)
          (ensures denote_term t == Ts_Var (inspect_namedv v).uniq) = ()

let denote_BVar (t:term) (v:bv)
  : Lemma (requires inspect_ln t == Tv_BVar v)
          (ensures denote_term t == Ts_BVar (inspect_bv v).index) = ()

let denote_FVar (t:term) (f:fv)
  : Lemma (requires inspect_ln t == Tv_FVar f)
          (ensures denote_term t == Ts_FVar (inspect_fv f)) = ()

let denote_UInst (t:term) (f:fv) (us:list universe)
  : Lemma (requires inspect_ln t == Tv_UInst f us)
          (ensures denote_term t == Ts_UInst (inspect_fv f) (denote_universes us)) = ()

let denote_App (t:term) (h:term) (a:argv)
  : Lemma (requires inspect_ln t == Tv_App h a)
          (ensures denote_term t == Ts_App (denote_term h) (denote_term (fst a)) (denote_aqualv (snd a))) = ()

let denote_Abs (t:term) (b:binder) (body:term)
  : Lemma (requires inspect_ln t == Tv_Abs b body)
          (ensures denote_term t == Ts_Abs (denote_binder b) (denote_term body)) = ()

let denote_Arrow (t:term) (b:binder) (c:comp)
  : Lemma (requires inspect_ln t == Tv_Arrow b c)
          (ensures denote_term t == Ts_Arrow (denote_binder b) (denote_comp c)) = ()

let denote_Type (t:term) (u:universe)
  : Lemma (requires inspect_ln t == Tv_Type u)
          (ensures denote_term t == Ts_Type (denote_universe u)) = ()

let denote_Refine (t:term) (sb:simple_binder) (r:term)
  : Lemma (requires inspect_ln t == Tv_Refine sb r)
          (ensures denote_term t == Ts_Refine (denote_term (inspect_binder sb).sort) (denote_term r)) = ()

let denote_Const (t:term) (c:vconst)
  : Lemma (requires inspect_ln t == Tv_Const c)
          (ensures denote_term t == Ts_Const c) = ()

let denote_Uvar (t:term) (n:nat) (ctx:ctx_uvar_and_subst)
  : Lemma (requires inspect_ln t == Tv_Uvar n ctx)
          (ensures denote_term t == Ts_Uvar n) = ()

let denote_Let (t:term) (recf:bool) (attrs:list term) (sb:simple_binder) (def body:term)
  : Lemma (requires inspect_ln t == Tv_Let recf attrs sb def body)
          (ensures denote_term t ==
                   Ts_Let recf (denote_terms attrs) (denote_term (inspect_binder sb).sort)
                          (denote_term def) (denote_term body)) = ()

let denote_Match (t:term) (sc:term) (ret:option match_returns_ascription) (brs:list branch)
  : Lemma (requires inspect_ln t == Tv_Match sc ret brs)
          (ensures denote_term t == Ts_Match (denote_term sc) (denote_ret ret) (denote_branches brs)) = ()

let denote_AscribedT (t:term) (e ta:term) (tac:option term) (eq:bool)
  : Lemma (requires inspect_ln t == Tv_AscribedT e ta tac eq)
          (ensures denote_term t == Ts_AscribedT (denote_term e) (denote_term ta) (denote_opt_term tac) eq) = ()

let denote_AscribedC (t:term) (e:term) (c:comp) (tac:option term) (eq:bool)
  : Lemma (requires inspect_ln t == Tv_AscribedC e c tac eq)
          (ensures denote_term t == Ts_AscribedC (denote_term e) (denote_comp c) (denote_opt_term tac) eq) = ()

let denote_Unknown (t:term)
  : Lemma (requires inspect_ln t == Tv_Unknown)
          (ensures denote_term t == Ts_Unknown) = ()

(* Binder / comp / pattern denotation lemmas. *)

let denote_binder_eq (b:binder)
  : Lemma (denote_binder b ==
           Bs (denote_term (inspect_binder b).sort) (denote_aqualv (inspect_binder b).qual)) = ()

let denote_comp_Total (c:comp) (t:term)
  : Lemma (requires inspect_comp c == C_Total t)
          (ensures denote_comp c == Cs_Total (denote_term t)) = ()

let denote_comp_GTotal (c:comp) (t:term)
  : Lemma (requires inspect_comp c == C_GTotal t)
          (ensures denote_comp c == Cs_GTotal (denote_term t)) = ()

let denote_comp_Lemma (c:comp) (pre post pats:term)
  : Lemma (requires inspect_comp c == C_Lemma pre post pats)
          (ensures denote_comp c == Cs_Lemma (denote_term pre) (denote_term post) (denote_term pats)) = ()

let denote_comp_Eff (c:comp) (us:universes) (eff:name) (res:term) (args:list argv) (decrs:list term)
  : Lemma (requires inspect_comp c == C_Eff us eff res args decrs)
          (ensures denote_comp c ==
                   Cs_Eff (denote_universes us) eff (denote_term res) (denote_args args) (denote_terms decrs)) = ()

let denote_Pat_Cons (head:fv) (us:option (list universe)) (subpats:list (pattern & bool))
  : Lemma (denote_pattern (Pat_Cons head us subpats) ==
           Ps_Cons (inspect_fv head) (denote_pat_univs us) (denote_subpats subpats)) = ()

(* Leaf-equality bridges to the components that [denote] keeps. *)

let namedv_eq_uniq (x1 x2 : namedv)
  : Lemma ((x1 == x2) <==> ((inspect_namedv x1).uniq == (inspect_namedv x2).uniq))
  = pack_inspect_namedv x1;
    pack_inspect_namedv x2;
    sealed_singl (inspect_namedv x1).sort (inspect_namedv x2).sort

let bv_eq_index (x1 x2 : bv)
  : Lemma ((x1 == x2) <==> ((inspect_bv x1).index == (inspect_bv x2).index))
  = pack_inspect_bv x1;
    pack_inspect_bv x2;
    sealed_singl (inspect_bv x1).sort (inspect_bv x2).sort

let fv_eq (f1 f2 : fv)
  : Lemma ((f1 == f2) <==> (inspect_fv f1 == inspect_fv f2))
  = pack_inspect_fv f1;
    pack_inspect_fv f2

(* [denote_ret (Some asc)] in terms of the component denotations. *)
let denote_ret_Some (asc:match_returns_ascription)
  : Lemma (denote_ret (Some asc) ==
           (let (b, (tc, tacopt, eq)) = asc in
            Some (denote_binder b, (denote_either tc, denote_opt_term tacopt, eq))))
  = let (b, (tc, tacopt, eq)) = asc in
    match tc with
    | Inl t -> ()
    | Inr c -> ()

(* -------------------------------------------------------------------- *)
(* Head tags, used to discharge the mismatched-constructor catch-alls. *)

let ts_head (s:term_spec) : GTot nat =
  match s with
  | Ts_Var _ -> 0 | Ts_BVar _ -> 1 | Ts_FVar _ -> 2 | Ts_UInst _ _ -> 3
  | Ts_App _ _ _ -> 4 | Ts_Abs _ _ -> 5 | Ts_Arrow _ _ -> 6 | Ts_Type _ -> 7
  | Ts_Refine _ _ -> 8 | Ts_Const _ -> 9 | Ts_Uvar _ -> 10 | Ts_Let _ _ _ _ _ -> 11
  | Ts_Match _ _ _ -> 12 | Ts_AscribedT _ _ _ _ -> 13 | Ts_AscribedC _ _ _ _ -> 14
  | Ts_Unknown -> 15 | Ts_Unsupp -> 16

let tv_head (t:term) : GTot nat =
  match inspect_ln t with
  | Tv_Var _ -> 0 | Tv_BVar _ -> 1 | Tv_FVar _ -> 2 | Tv_UInst _ _ -> 3
  | Tv_App _ _ -> 4 | Tv_Abs _ _ -> 5 | Tv_Arrow _ _ -> 6 | Tv_Type _ -> 7
  | Tv_Refine _ _ -> 8 | Tv_Const _ -> 9 | Tv_Uvar _ _ -> 10 | Tv_Let _ _ _ _ _ -> 11
  | Tv_Match _ _ _ -> 12 | Tv_AscribedT _ _ _ _ -> 13 | Tv_AscribedC _ _ _ _ -> 14
  | Tv_Unknown -> 15 | Tv_Unsupp -> 16

let head_lemma (t:term)
  : Lemma (ts_head (denote_term t) == tv_head t)
          [SMTPat (denote_term t)]
  = match inspect_ln t with
    | Tv_Var _ | Tv_BVar _ | Tv_FVar _ | Tv_UInst _ _ | Tv_App _ _ | Tv_Abs _ _
    | Tv_Arrow _ _ | Tv_Type _ | Tv_Refine _ _ | Tv_Const _ | Tv_Uvar _ _
    | Tv_Let _ _ _ _ _ | Tv_Match _ _ _ | Tv_AscribedT _ _ _ _ | Tv_AscribedC _ _ _ _
    | Tv_Unknown | Tv_Unsupp -> ()

let cs_head (s:comp_spec) : GTot nat =
  match s with
  | Cs_Total _ -> 0 | Cs_GTotal _ -> 1 | Cs_Lemma _ _ _ -> 2 | Cs_Eff _ _ _ _ _ -> 3

let cv_head (c:comp) : GTot nat =
  match inspect_comp c with
  | C_Total _ -> 0 | C_GTotal _ -> 1 | C_Lemma _ _ _ -> 2 | C_Eff _ _ _ _ _ -> 3

let comp_head_lemma (c:comp)
  : Lemma (cs_head (denote_comp c) == cv_head c)
          [SMTPat (denote_comp c)]
  = match inspect_comp c with
    | C_Total _ | C_GTotal _ | C_Lemma _ _ _ | C_Eff _ _ _ _ _ -> ()

let ps_head (s:pattern_spec) : GTot nat =
  match s with
  | Ps_Constant _ -> 0 | Ps_Cons _ _ _ -> 1 | Ps_Var -> 2 | Ps_Dot_Term _ -> 3

let pv_head (p:pattern) : GTot nat =
  match p with
  | Pat_Constant _ -> 0 | Pat_Cons _ _ _ -> 1 | Pat_Var _ _ -> 2 | Pat_Dot_Term _ -> 3

let pat_head_lemma (p:pattern)
  : Lemma (ps_head (denote_pattern p) == pv_head p)
          [SMTPat (denote_pattern p)]
  = match p with
    | Pat_Constant _ | Pat_Cons _ _ _ | Pat_Var _ _ | Pat_Dot_Term _ -> ()

let qs_head (s:aqualv_spec) : GTot nat =
  match s with
  | Qs_Implicit -> 0 | Qs_Explicit -> 1 | Qs_Equality -> 2 | Qs_Meta _ -> 3

let qv_head (q:aqualv) : GTot nat =
  match q with
  | Q_Implicit -> 0 | Q_Explicit -> 1 | Q_Equality -> 2 | Q_Meta _ -> 3

let aqual_head_lemma (q:aqualv)
  : Lemma (qs_head (denote_aqualv q) == qv_head q)
          [SMTPat (denote_aqualv q)]
  = match q with
    | Q_Implicit | Q_Explicit | Q_Equality | Q_Meta _ -> ()

(* -------------------------------------------------------------------- *)
(* The mutual term comparator, now over denotational relations. *)

val term_cmp         : comparator_for' teq
val binder_cmp       : comparator_for' beq
val aqual_cmp        : comparator_for' aqeq
val arg_cmp          : comparator_for' argeq
val comp_cmp         : comparator_for' ceq
val pat_cmp          : comparator_for' peq
val pat_arg_cmp      : comparator_for' pareq
val br_cmp           : comparator_for' breq
val match_returns_ascription_cmp : comparator_for' maeq

#push-options "--z3rlimit 40 --fuel 2 --ifuel 2"

let rec term_cmp t1 t2 =
  let tv1 = inspect_ln t1 in
  let tv2 = inspect_ln t2 in
  match tv1, tv2 with
  | Tv_Unsupp, _
  | _, Tv_Unsupp -> Unknown

  | Tv_Var v1, Tv_Var v2 ->
    co (namedv_cmp v1 v2)
       (denote_Var t1 v1; denote_Var t2 v2; namedv_eq_uniq v1 v2)

  | Tv_BVar v1, Tv_BVar v2 ->
    co (bv_cmp v1 v2)
       (denote_BVar t1 v1; denote_BVar t2 v2; bv_eq_index v1 v2)

  | Tv_FVar f1, Tv_FVar f2 ->
    co (fv_cmp f1 f2)
       (denote_FVar t1 f1; denote_FVar t2 f2; fv_eq f1 f2)

  | Tv_UInst f1 us1, Tv_UInst f2 us2 ->
    co (fv_cmp f1 f2 &&& list_dec_cmp' t1 t2 univ_cmp us1 us2)
       (denote_UInst t1 f1 us1; denote_UInst t2 f2 us2; fv_eq f1 f2;
        bridge_universes us1 us2)

  | Tv_App h1 a1, Tv_App h2 a2 ->
    co (term_cmp h1 h2 &&& arg_cmp a1 a2)
       (denote_App t1 h1 a1; denote_App t2 h2 a2)

  | Tv_Abs b1 e1, Tv_Abs b2 e2 ->
    co (binder_cmp b1 b2 &&& term_cmp e1 e2)
       (denote_Abs t1 b1 e1; denote_Abs t2 b2 e2)

  | Tv_Arrow b1 c1, Tv_Arrow b2 c2 ->
    co (binder_cmp b1 b2 &&& comp_cmp c1 c2)
       (denote_Arrow t1 b1 c1; denote_Arrow t2 b2 c2)

  | Tv_Type u1, Tv_Type u2 ->
    co (univ_cmp u1 u2)
       (denote_Type t1 u1; denote_Type t2 u2; denote_universe_inj_iff u1 u2)

  | Tv_Refine sb1 r1, Tv_Refine sb2 r2 ->
    co (term_cmp (inspect_binder sb1).sort (inspect_binder sb2).sort &&& term_cmp r1 r2)
       (denote_Refine t1 sb1 r1; denote_Refine t2 sb2 r2)

  | Tv_Const c1, Tv_Const c2 ->
    co (const_cmp c1 c2)
       (denote_Const t1 c1; denote_Const t2 c2)

  | Tv_Uvar n1 u1, Tv_Uvar n2 u2 ->
    co (eq_cmp n1 n2)
       (denote_Uvar t1 n1 u1; denote_Uvar t2 n2 u2)

  | Tv_Let r1 attrs1 sb1 e1 b1, Tv_Let r2 attrs2 sb2 e2 b2 ->
    co (eq_cmp r1 r2
        &&& list_dec_cmp' t1 t2 term_cmp attrs1 attrs2
        &&& term_cmp (inspect_binder sb1).sort (inspect_binder sb2).sort
        &&& term_cmp e1 e2
        &&& term_cmp b1 b2)
       (denote_Let t1 r1 attrs1 sb1 e1 b1; denote_Let t2 r2 attrs2 sb2 e2 b2;
        bridge_terms attrs1 attrs2)

  | Tv_Match sc1 o1 brs1, Tv_Match sc2 o2 brs2 ->
    co (term_cmp sc1 sc2
        &&& opt_dec_cmp' t1 t2 match_returns_ascription_cmp o1 o2
        &&& list_dec_cmp' t1 t2 br_cmp brs1 brs2)
       (denote_Match t1 sc1 o1 brs1; denote_Match t2 sc2 o2 brs2;
        bridge_ret o1 o2; bridge_branches brs1 brs2)

  | Tv_AscribedT e1 ta1 tacopt1 eq1, Tv_AscribedT e2 ta2 tacopt2 eq2 ->
    co (term_cmp e1 e2
        &&& term_cmp ta1 ta2
        &&& opt_dec_cmp' t1 t2 term_cmp tacopt1 tacopt2
        &&& eq_cmp eq1 eq2)
       (denote_AscribedT t1 e1 ta1 tacopt1 eq1; denote_AscribedT t2 e2 ta2 tacopt2 eq2;
        bridge_opt_term tacopt1 tacopt2)

  | Tv_AscribedC e1 c1 tacopt1 eq1, Tv_AscribedC e2 c2 tacopt2 eq2 ->
    co (term_cmp e1 e2
        &&& comp_cmp c1 c2
        &&& opt_dec_cmp' t1 t2 term_cmp tacopt1 tacopt2
        &&& eq_cmp eq1 eq2)
       (denote_AscribedC t1 e1 c1 tacopt1 eq1; denote_AscribedC t2 e2 c2 tacopt2 eq2;
        bridge_opt_term tacopt1 tacopt2)

  | Tv_Unknown, Tv_Unknown ->
    denote_Unknown t1; denote_Unknown t2; Eq

  | _ -> Neq

and arg_cmp (a1, q1) (a2, q2) =
  co (term_cmp a1 a2 &&& aqual_cmp q1 q2) ()

and aqual_cmp a1 a2 =
  match a1, a2 with
  | Q_Implicit, Q_Implicit -> Eq
  | Q_Explicit, Q_Explicit -> Eq
  | Q_Equality, Q_Equality -> Eq
  | Q_Meta m1, Q_Meta m2 -> co (term_cmp m1 m2) ()
  | _ -> Neq

and match_returns_ascription_cmp asc1 asc2 =
  let (b1, (tc1, tacopt1, eq1)) = asc1 in
  let (b2, (tc2, tacopt2, eq2)) = asc2 in
  co (binder_cmp b1 b2
      &&& either_dec_cmp' asc1 asc2 term_cmp comp_cmp tc1 tc2
      &&& opt_dec_cmp' asc1 asc2 term_cmp tacopt1 tacopt2
      &&& eq_cmp eq1 eq2)
     (denote_ret_Some asc1; denote_ret_Some asc2;
      bridge_either tc1 tc2; bridge_opt_term tacopt1 tacopt2)

and binder_cmp b1 b2 =
  let bv1 = inspect_binder b1 in
  let bv2 = inspect_binder b2 in
  co (term_cmp bv1.sort bv2.sort &&& aqual_cmp bv1.qual bv2.qual)
     (denote_binder_eq b1; denote_binder_eq b2)

and comp_cmp c1 c2 =
  let cv1 = inspect_comp c1 in
  let cv2 = inspect_comp c2 in
  match cv1, cv2 with
  | C_Total t1, C_Total t2 ->
    co (term_cmp t1 t2) (denote_comp_Total c1 t1; denote_comp_Total c2 t2)

  | C_GTotal t1, C_GTotal t2 ->
    co (term_cmp t1 t2) (denote_comp_GTotal c1 t1; denote_comp_GTotal c2 t2)

  | C_Lemma pre1 post1 pat1, C_Lemma pre2 post2 pat2 ->
    co (term_cmp pre1 pre2 &&& term_cmp post1 post2 &&& term_cmp pat1 pat2)
       (denote_comp_Lemma c1 pre1 post1 pat1; denote_comp_Lemma c2 pre2 post2 pat2)

  | C_Eff us1 ef1 t1 args1 dec1, C_Eff us2 ef2 t2 args2 dec2 ->
    co (list_dec_cmp' c1 c2 univ_cmp us1 us2
        &&& eq_cmp ef1 ef2
        &&& term_cmp t1 t2
        &&& list_dec_cmp' c1 c2 arg_cmp args1 args2
        &&& list_dec_cmp' c1 c2 term_cmp dec1 dec2)
       (denote_comp_Eff c1 us1 ef1 t1 args1 dec1;
        denote_comp_Eff c2 us2 ef2 t2 args2 dec2;
        bridge_universes us1 us2; bridge_args args1 args2; bridge_terms dec1 dec2)

  | _ -> Neq

and br_cmp br1 br2 =
  co (pat_cmp (fst br1) (fst br2) &&& term_cmp (snd br1) (snd br2)) ()

and pat_cmp p1 p2 =
  match p1, p2 with
  | Pat_Var x1 s1, Pat_Var x2 s2 -> Eq

  | Pat_Constant x1, Pat_Constant x2 ->
    co (const_cmp x1 x2) ()

  | Pat_Dot_Term x1, Pat_Dot_Term x2 ->
    co (opt_dec_cmp' p1 p2 term_cmp x1 x2) (bridge_opt_term x1 x2)

  | Pat_Cons head1 us1 subpats1, Pat_Cons head2 us2 subpats2 ->
    co (fv_cmp head1 head2
        &&& opt_dec_cmp' p1 p2 (list_dec_cmp' p1 p2 univ_cmp) us1 us2
        &&& list_dec_cmp' p1 p2 pat_arg_cmp subpats1 subpats2)
       (denote_Pat_Cons head1 us1 subpats1; denote_Pat_Cons head2 us2 subpats2;
        fv_eq head1 head2; bridge_pat_univs us1 us2; bridge_subpats subpats1 subpats2)

  | _ -> Neq

and pat_arg_cmp (p1, b1) (p2, b2) =
  co (pat_cmp p1 p2 &&& eq_cmp b1 b2) ()

#pop-options

let defined r = ~(Unknown? r)

let def2 f l1 l2 =(forall x y. L.memP x l1 /\ L.memP y l2 ==> defined (f x y))

let rec defined_list_dec #a #b #r (t1 t2 : b) (f : comparator_for' r)
  (l1 : list a{l1 << t1})
  (l2 : list a{l2 << t2})
  : Lemma (requires (def2 f l1 l2)) (ensures defined (list_dec_cmp' t1 t2 f l1 l2))
  = match l1, l2 with
    | [], [] -> ()
    | x::xs, y::ys ->
      defined_list_dec t1 t2 f xs ys
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

let rec defined_list_dec_eqrel #a #b (t1 t2 : b) (f : comparator_for a)
  (l1 : list a{l1 << t1})
  (l2 : list a{l2 << t2})
  : Lemma (requires (def2 f l1 l2)) (ensures defined (list_dec_cmp t1 t2 f l1 l2))
  = match l1, l2 with
    | [], [] -> ()
    | x::xs, y::ys ->
      defined_list_dec_eqrel t1 t2 f xs ys
    | _ -> ()

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
    defined_list_dec_eqrel u1 u2 univ_cmp us1 us2

(* Just a placeholder for now *)
val faithful_lemma (t1:term) (t2:term) : Lemma (requires faithful t1 /\ faithful t2) (ensures defined (term_cmp t1 t2))

#push-options "--z3rlimit 40 --fuel 2 --ifuel 2"

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
          (ensures defined (term_cmp t1 t2) <==>
                   defined (eq_cmp recf1 recf2
                            &&& list_dec_cmp' t1 t2 term_cmp attrs1 attrs2
                            &&& term_cmp (inspect_binder b1).sort (inspect_binder b2).sort
                            &&& term_cmp def1 def2
                            &&& term_cmp body1 body2))
  = assume (defined (term_cmp t1 t2) <==>
            defined (eq_cmp recf1 recf2
                     &&& list_dec_cmp' t1 t2 term_cmp attrs1 attrs2
                     &&& term_cmp (inspect_binder b1).sort (inspect_binder b2).sort
                     &&& term_cmp def1 def2
                     &&& term_cmp body1 body2)) // #2908, somehow assert_norm also does not work

let faithful_Tv_Match (t : term) (sc : term) (o : option match_returns_ascription) (brs : list branch)
  : Lemma (requires inspect_ln t == Tv_Match sc o brs /\ faithful t)
          (ensures allP t faithful_branch brs)
  = assert_norm (faithful t ==> allP t faithful_branch brs)

let term_eq_Tv_Match (t1 t2 : term) (sc1 sc2 : term) (o1 o2 : option match_returns_ascription) (brs1 brs2 : list branch)
  : Lemma (requires inspect_ln t1 == Tv_Match sc1 o1 brs1
                  /\ inspect_ln t2 == Tv_Match sc2 o2 brs2)
          (ensures defined (term_cmp t1 t2) <==>
                   defined (term_cmp sc1 sc2
                            &&& opt_dec_cmp' t1 t2 match_returns_ascription_cmp o1 o2
                            &&& list_dec_cmp' t1 t2 br_cmp brs1 brs2))
  = assume (defined (term_cmp t1 t2) <==>
            defined (term_cmp sc1 sc2
                     &&& opt_dec_cmp' t1 t2 match_returns_ascription_cmp o1 o2
                     &&& list_dec_cmp' t1 t2 br_cmp brs1 brs2)) // #2908, somehow assert_norm also does not work

let faithful_Pat_Cons (p : pattern) (f:fv) (ous : option universes) (subpats : list (pattern & bool))
  : Lemma (requires p == Pat_Cons f ous subpats /\ faithful_pattern p)
          (ensures allP p faithful_pattern_arg subpats)
  = assert_norm (faithful_pattern p ==> allP p faithful_pattern_arg subpats) // #2908

let pat_eq_Pat_Cons (p1 p2 : pattern) (f1 f2 : fv) (ous1 ous2 : option universes) (args1 args2 : list (pattern & bool))
  : Lemma (requires p1 == Pat_Cons f1 ous1 args1 /\ p2 == Pat_Cons f2 ous2 args2)
          (ensures defined (pat_cmp p1 p2) <==>
                   defined (fv_cmp f1 f2
                            &&& opt_dec_cmp' p1 p2 (list_dec_cmp' p1 p2 univ_cmp) ous1 ous2
                            &&& list_dec_cmp' p1 p2 pat_arg_cmp args1 args2))
  = assert_norm (defined (pat_cmp p1 p2) <==>
            defined (fv_cmp f1 f2
                     &&& opt_dec_cmp' p1 p2 (list_dec_cmp' p1 p2 univ_cmp) ous1 ous2
                     &&& list_dec_cmp' p1 p2 pat_arg_cmp args1 args2)) // #2908

let comp_eq_C_Eff (c1 c2 : comp) (us1 us2 : universes) (ef1 ef2 : name) (t1 t2 : typ) (args1 args2 : list argv) (dec1 dec2 : list term)
  : Lemma (requires inspect_comp c1 == C_Eff us1 ef1 t1 args1 dec1
                  /\ inspect_comp c2 == C_Eff us2 ef2 t2 args2 dec2)
          (ensures defined (comp_cmp c1 c2) <==>
                   defined (list_dec_cmp' c1 c2 univ_cmp us1 us2
                            &&& eq_cmp ef1 ef2
                            &&& term_cmp t1 t2
                            &&& list_dec_cmp' c1 c2 arg_cmp args1 args2
                            &&& list_dec_cmp' c1 c2 term_cmp dec1 dec2))
  = assume (defined (comp_cmp c1 c2) <==>
            defined (list_dec_cmp' c1 c2 univ_cmp us1 us2
                     &&& eq_cmp ef1 ef2
                     &&& term_cmp t1 t2
                     &&& list_dec_cmp' c1 c2 arg_cmp args1 args2
                     &&& list_dec_cmp' c1 c2 term_cmp dec1 dec2)) // #2908, assert_norm doesn't work

let rec faithful_lemma (t1 t2 : term) =
  match inspect_ln t1, inspect_ln t2 with
  | Tv_Var _, Tv_Var _
  | Tv_BVar _, Tv_BVar _
  | Tv_FVar _, Tv_FVar _ -> ()
  | Tv_UInst f1 us1, Tv_UInst f2 us2 ->
    let tv1 = inspect_ln t1 in
    let tv2 = inspect_ln t2 in
    univ_faithful_lemma_list_dec t1 t2 us1 us2;
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

  | _ -> () (* rest of the cases trivial *)

and faithful_lemma_pattern (p1 p2 : pattern) : Lemma (requires faithful_pattern p1 /\ faithful_pattern p2) (ensures defined (pat_cmp p1 p2)) =
  match p1, p2 with
  | Pat_Var _ _, Pat_Var _ _ -> ()
  | Pat_Constant _, Pat_Constant _ -> ()
  | Pat_Dot_Term (Some t1), Pat_Dot_Term (Some t2) ->
    faithful_lemma t1 t2
  | Pat_Cons head1 univs1 subpats1, Pat_Cons head2 univs2 subpats2 ->
    (***)faithful_Pat_Cons p1 head1 univs1 subpats1;
    (***)faithful_Pat_Cons p2 head2 univs2 subpats2;
    let aux : squash (defined (opt_dec_cmp' p1 p2 (list_dec_cmp' p1 p2 univ_cmp) univs1 univs2)) =
      match univs1, univs2 with
      | Some us1, Some us2 ->
        univ_faithful_lemma_list_dec p1 p2 us1 us2
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
          (ensures defined (list_dec_cmp' top1 top2 pat_arg_cmp pats1 pats2))
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
          (ensures defined (list_dec_cmp' top1 top2 br_cmp brs1 brs2))
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
  ()

and faithful_lemma_qual (q1 q2 : aqualv) : Lemma (requires faithful_qual q1 /\ faithful_qual q2) (ensures defined (aqual_cmp q1 q2)) =
  match q1, q2 with
  | Q_Meta t1, Q_Meta t2 -> faithful_lemma t1 t2
  | _ -> ()

and faithful_lemma_attrs_dec #b (top1 top2 : b)
  (at1 : list term{at1 << top1})
  (at2 : list term{at2 << top2})
  : Lemma (requires faithful_attrs at1 /\ faithful_attrs at2)
          (ensures defined (list_dec_cmp' top1 top2 term_cmp at1 at2))
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
    univ_faithful_lemma_list_dec c1 c2 us1 us2;
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

and univ_faithful_lemma_list_dec #b (u1 u2 : b) (us1 : list universe{us1 << u1}) (us2 : list universe{us2 << u2})
  : Lemma (requires allP u1 faithful_univ us1 /\ allP u2 faithful_univ us2)
          (ensures defined (list_dec_cmp' u1 u2 univ_cmp us1 us2))
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
#pop-options


let term_eq (t1 t2 : term) : (b:bool{b ==> denote_term t1 == denote_term t2}) =
  Eq? (term_cmp t1 t2)

let term_eq_dec (t1 t2 : faithful_term) : (b:bool{b <==> denote_term t1 == denote_term t2}) =
  faithful_lemma t1 t2;
  Eq? (term_cmp t1 t2)

let univ_eq (u1 u2 : universe) : (b:bool{b ==> u1 == u2}) =
  Eq? (univ_cmp u1 u2)

let univ_eq_dec (u1 u2 : faithful_universe) : (b:bool{b <==> u1 == u2}) =
  univ_faithful_lemma u1 u2;
  Eq? (univ_cmp u1 u2)
