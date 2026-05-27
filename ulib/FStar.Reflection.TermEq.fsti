module FStar.Reflection.TermEq

open FStar.Stubs.Reflection.Types
open FStar.Stubs.Reflection.V2.Data
open FStar.Stubs.Reflection.V2.Builtins

(* Auxiliary... would be good to move. *)
let rec allP0 #a (pred : a -> prop) (l : list a) : prop =
  match l with
  | [] -> True
  | x::xs -> pred x /\ allP0 pred xs

let rec allP #a #b (top:b) (pred : (x:a{x << top}) -> prop) (l : list a{l << top \/ l === top}) : prop =
  match l with
  | [] -> True
  | x::xs -> pred x /\ allP top pred xs

let optP0 #a (pred : a -> prop) (o : option a) : prop =
  match o with
  | None -> True
  | Some x -> pred x

let optP #a #b (top:b) (pred : (x:a{x << top}) -> prop) (o : option a{o << top}) : prop =
  match o with
  | None -> True
  | Some x -> pred x
(* /Aux *)

let rec faithful_univ (u : universe) : prop =
  match inspect_universe u with
  | Uv_Unif _ -> False (* We just forbid this *)

  | Uv_Unk
  | Uv_Zero
  | Uv_BVar _
  | Uv_Name _ -> True

  | Uv_Succ u -> faithful_univ u
  | Uv_Max us -> allP u faithful_univ us

(* Just a placeholder for now *)
let faithful_const (c:vconst) : prop = True

let rec faithful (t:term) : prop =
  match inspect_ln t with
  | Tv_Var _
  | Tv_BVar _
  | Tv_FVar _
  | Tv_Unknown ->
    True

  | Tv_Const c ->
    faithful_const c

  | Tv_UInst f us ->
    allP t faithful_univ us

  | Tv_Unsupp -> False
  | Tv_App h a ->
    faithful h /\ faithful_arg a
  | Tv_Abs b t  ->
    faithful_binder b /\ faithful t
  | Tv_Arrow b c ->
    faithful_binder b /\ faithful_comp c
  | Tv_Type u ->
    faithful_univ u
  | Tv_Refine b phi ->
    faithful_binder b
     /\ faithful phi

  | Tv_Uvar n u -> False
  | Tv_Let r ats x e b ->
    faithful_attrs ats
     /\ faithful_binder x
     /\ faithful e
     /\ faithful b

  | Tv_Match sc o brs ->
    faithful sc
     /\ None? o // stopgap
     /\ allP t faithful_branch brs

  | Tv_AscribedT e ta tacopt eq ->
    faithful e
     /\ faithful ta
     /\ optP t faithful tacopt

  | Tv_AscribedC e c tacopt eq ->
    faithful e
     /\ faithful_comp c
     /\ optP t faithful tacopt

and faithful_arg (a : argv) : prop =
  faithful (fst a) /\ faithful_qual (snd a)

and faithful_qual (q:aqualv) : prop =
  match q with
  | Q_Implicit -> True
  | Q_Explicit -> True
  | Q_Equality -> True
  | Q_Meta m -> faithful m

and faithful_binder (b:binder) : prop =
  match inspect_binder b with
  | {sort=sort; qual=q; attrs=attrs} ->
    faithful sort /\ faithful_qual q /\ faithful_attrs attrs

and faithful_branch (b : branch) : prop =
  let (p, t) = b in
  faithful_pattern p /\ faithful t

and faithful_pattern (p : pattern) : prop =
  match p with
  | Pat_Constant c -> faithful_const c
  | Pat_Cons head univs subpats ->
    optP p (allP p faithful_univ) univs
     /\ allP p faithful_pattern_arg subpats

  (* non-binding bvs are always OK *)
  | Pat_Var _ _ -> True
  | Pat_Dot_Term None -> True
  | Pat_Dot_Term (Some t) -> faithful t

and faithful_pattern_arg (pb : pattern & bool) : prop =
  faithful_pattern (fst pb)

and faithful_attrs ats : prop =
  allP ats faithful ats

and faithful_comp c =
  match inspect_comp c with
  | C_Total t -> faithful t
  | C_GTotal t -> faithful t
  | C_Lemma pre post pats -> faithful pre /\ faithful post /\ faithful pats
  | C_Eff us ef r args decs ->
    allP c faithful_univ us
     /\ faithful r
     /\ allP c faithful_arg args
     /\ allP c faithful decs

let faithful_term     = t:term{faithful t}
let faithful_universe = u:universe{faithful_univ u}

(* A conservative version: works on all terms, returns `true` if they
are guaranteed to be equal. *)
[@@plugin]
val term_eq (t1 t2 : term) : (b:bool{b ==> t1 == t2})

(* A fully decidable version, for faithful terms. *)
[@@plugin]
val term_eq_dec (t1 t2 : faithful_term) : (b:bool{b <==> t1 == t2})

(* Idem for universes *)
[@@plugin]
val univ_eq (u1 u2 : universe) : (b:bool{b ==> u1 == u2})

[@@plugin]
val univ_eq_dec (u1 u2 : faithful_universe) : (b:bool{b <==> u1 == u2})
