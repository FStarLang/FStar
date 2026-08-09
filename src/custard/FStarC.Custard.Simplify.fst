(*
   Copyright 2008-2026 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)

module FStarC.Custard.Simplify

open FStarC
open FStarC.Effect
open FStarC.List
open FStarC.Class.Show
open FStarC.Custard.Syntax
open FStarC.Errors.Msg

module E      = FStarC.Errors
module SMap   = FStarC.SMap
module GenSym = FStarC.GenSym

(* Does [v] occur free in [e]?  Custard's variable names come from F* bound
   variables and so already carry a unique index, but this deliberately does
   not track shadowing: an over-count keeps a binding that could have been
   dropped, which is the safe direction. *)
let rec occurs (v:string) (x:expr) : ML bool =
  match x.e with
  | EVar w -> w = v
  | EConst _ | EQual _ -> false
  | ELet (_, _, e1, e2) -> occurs v e1 || occurs v e2
  | EApp (h, es) -> occurs v h || occurs_list v es
  | EFun (_, b) -> occurs v b
  | EMatch (s, brs) -> occurs v s || occurs_branches v brs
  | EIf (c, a, b) -> occurs v c || occurs v a || occurs v b
  | EAny | EAbort _ -> false
  | ESeq (a, b) -> occurs v a || occurs v b
  | ECtor (_, es) | ETuple es | EOp (_, es) -> occurs_list v es
  | ERaise e1 -> occurs v e1
  | ERecord (_, fs) -> occurs_list v (fs |> List.map snd)
  | EProj (e1, _, _) | EDiscrim (e1, _) | ECast (e1, _) -> occurs v e1
  | EWhile (a, b) -> occurs v a || occurs v b
  | ETry (a, brs) -> occurs v a || occurs_branches v brs

and occurs_list (v:string) (es:list expr) : ML bool =
  es |> List.existsb (occurs v)

and occurs_branches (v:string) (brs:list branch) : ML bool =
  brs |> List.existsb (fun (_, g, b) ->
    (match g with None -> false | Some g -> occurs v g) || occurs v b)

(* -------------------------------------------------------------------- *)
(* ANF                                                                  *)
(* -------------------------------------------------------------------- *)

(* Section 6, pass 1.  The invariant this establishes is: *every operand is
   pure*.  An impure computation may only appear as the right-hand side of an
   [ELet], the left of an [ESeq], or in tail position -- never as an argument,
   a constructor field, a scrutinee or a cast operand.

   That is what the purity discipline of section 7.3 is written against.
   Without it, "may I reorder these?" is a question about arbitrary subterm
   positions, and the answer has to be rediscovered by every rewrite that
   moves anything.  Three places in the existing passes show what that costs:

   - [Layout.hoist] sequences a dropped erased argument before the *whole*
     node it was dropped from, which steps over the arguments to its left;
   - [ctor_args_pure] refuses to fire iota at all when any field of the
     scrutinee is impure, because it cannot tell which fields the pattern
     discards;
   - [inline_call] can only substitute a pure argument, so an impure one
     blocks the beta-reduction that would have consumed it.

   After ANF all three become unconditional: the operands are variables, so
   they are pure, so nothing is ever moved past an effect.  The last two get
   strictly stronger as a result.

   Note that F* has already done most of this work.  An application whose
   arguments have an F* effect arrives in monadic normal form, because that is
   how the typechecker elaborates it; what does *not* arrive normalized is
   everything Custard alone considers impure -- the arrows promoted by
   [extract_as_impure_effect] (section 7.2), which F* sees as [Tot] -- plus
   whatever the extractor and the rules build. *)

(* Hoisting is only sound into a position that is evaluated unconditionally,
   exactly once, at the point the operand was.  So the traversal stops at
   every delayed position: the body of a lambda, the arms of an [EIf], the
   branches of an [EMatch] or [ETry], both parts of an [EWhile] (the condition
   is re-evaluated per iteration), and -- because the backends short-circuit
   them -- every operand but the first of [And] and [Or].

   The [po_int] guard is the whole point of taking a [prim_op] rather than an
   [op]: *at a width* [And] and [Or] are the bitwise operators, which are
   strict.  Treating those as delayed would leave an impure second operand in
   an operand position, and OCaml would then evaluate [logand a b] right to
   left -- exactly the reordering this pass exists to prevent. *)
let delayed_operands (o:prim_op) : bool =
  match o.po_int, o.po_op with
  | None, And
  | None, Or -> true
  | _ -> false

let anf_expr (x0:expr) : ML expr =
  (* Pending bindings for the operand group currently being normalized, most
     recent first. *)
  let rec norm (x:expr) : ML expr =
    match x.e with
    (* Statement and tail positions: nothing is hoisted *out* of these, since
       they are already where an effect is allowed to be. *)
    | ELet (v, t, e1, e2) ->
      let e1 = norm e1 in
      let e2 = norm e2 in
      { x with e = ELet (v, t, e1, e2) }
    | ESeq (a, b) ->
      let a = norm a in
      let b = norm b in
      { x with e = ESeq (a, b) }
    | EFun (bs, b) -> { x with e = EFun (bs, norm b) }
    | EWhile (c, b) ->
      let c = norm c in
      let b = norm b in
      { x with e = EWhile (c, b) }
    | EConst _ | EVar _ | EQual _ | EAny | EAbort _ -> x

    (* Everything else has operand positions, so it needs an accumulator. *)
    | _ ->
      let acc : ref (list (string & cty & expr)) = mk_ref [] in
      let operand (e:expr) : ML expr =
        let e = norm e in
        if is_pure e.eff then e
        else begin
          let v = uniq "tmp" (GenSym.next_id ()) in
          acc := (v, e.ty, e) :: !acc;
          { e with e = EVar v; eff = E_Pure }
        end in
      (* [List.map] is not usable here: the order in which the accumulator is
         filled *is* the evaluation order being fixed, and it must be left to
         right whatever the host language does with the argument of a cons. *)
      let rec ops (es:list expr) : ML (list expr) =
        match es with
        | [] -> []
        | e :: es ->
          let e = operand e in
          let rest = ops es in
          e :: rest in
      let rec fields (fs:list (string & expr)) : ML (list (string & expr)) =
        match fs with
        | [] -> []
        | (f, e) :: fs ->
          let e = operand e in
          let rest = fields fs in
          (f, e) :: rest in
      let body =
        match x.e with
        | EApp (h, es) ->
          let h = operand h in
          let es = ops es in
          { x with e = EApp (h, es) }
        | ECtor (n, es)  -> { x with e = ECtor (n, ops es) }
        | ETuple es      -> { x with e = ETuple (ops es) }
        | ERaise e1 -> { x with e = ERaise (norm e1) }
        | ERecord (n, fs) -> { x with e = ERecord (n, fields fs) }
        | EOp (o, es) ->
          if delayed_operands o
          then
            (match es with
             | e :: rest ->
               let e = operand e in
               let rest = rest |> List.map norm in
               { x with e = EOp (o, e :: rest) }
             | [] -> x)
          else { x with e = EOp (o, ops es) }
        | EProj (e, n, f)  -> { x with e = EProj (operand e, n, f) }
        | EDiscrim (e, n)  -> { x with e = EDiscrim (operand e, n) }
        | ECast (e, c)     -> { x with e = ECast (operand e, c) }
        | EIf (c, a, b) ->
          let c = operand c in
          let a = norm a in
          let b = norm b in
          { x with e = EIf (c, a, b) }
        | EMatch (s, brs) ->
          let s = operand s in
          { x with e = EMatch (s, brs |> List.map norm_branch) }
        | ETry (e, brs) ->
          { x with e = ETry (norm e, brs |> List.map norm_branch) }
        | _ -> x in
      List.fold_left (fun acc (v, t, e) ->
        { x with e = ELet (v, t, e, acc) }) body !acc

  and norm_branch (br:branch) : ML branch =
    let p, g, b = br in
    (* A guard is evaluated before the branch is chosen, so it is delayed too;
       [reduce] already refuses to fire iota through one. *)
    (p, (match g with None -> None | Some g -> Some (norm g)), norm b) in
  norm x0

let anf (prog:program) : ML program =
  prog |> List.map (fun d ->
    match d with
    | DLet dl -> DLet { dl with dl_body = anf_expr dl.dl_body }
    | d -> d)

(* [if c then a else b] reaches the IR as a match on a boolean, because that
   is how F* desugars it: [match c with | true -> a | _ -> b].  Left alone it
   stays a match, and karamel then has to emit a switch with an unreachable
   default -- noisy in the C, and a missed opportunity, since the IR has an
   [EIf] that every pass and both backends already handle.  Nothing else
   builds one. *)
let bool_alt (p:pat) (body:expr) : ML (option (option bool)) =
  match p with
  | PConst (CBool b) -> Some (Some b)
  | PWild -> Some None
  (* A catch-all that *names* the scrutinee would need the name bound to it;
     when the name is unused, which is the only shape F* produces here, there
     is nothing to bind. *)
  | PVar v -> if occurs v body then None else Some None
  | _ -> None

(* [Some (then_branch, else_branch)] when the branches are a boolean test. *)
let as_if (brs:list branch) : ML (option (expr & expr)) =
  match brs with
  | [(p1, None, b1); (p2, None, b2)] ->
    (match bool_alt p1 b1, bool_alt p2 b2 with
     (* The first branch has to be a literal: a catch-all there makes the
        second one dead, and two catch-alls are no evidence that the scrutinee
        is a boolean at all. *)
     | Some (Some c1), Some alt2 ->
       let complementary = match alt2 with
                           | None -> true
                           | Some c2 -> c1 <> c2 in
       if not complementary then None
       else if c1 then Some (b1, b2) else Some (b2, b1)
     | _ -> None)
  | _ -> None

let rec simpl (x:expr) : ML expr =
  match x.e with
  | ELet (v, ty, e1, e2) ->
    let e1 = simpl e1 in
    let e2 = simpl e2 in
    (* [let x = e in x] is just [e], whatever [e]'s effect: nothing moves. *)
    if (match e2.e with EVar w -> w = v | _ -> false) then e1
    else if occurs v e2 then { x with e = ELet (v, ty, e1, e2) }
    (* Section 7.3: an unused binding may only be deleted if evaluating it is
       unobservable; otherwise it becomes a statement, which keeps its effect
       and its position. *)
    else if is_pure e1.eff then e2
    else { x with e = ESeq (e1, e2) }

  | ESeq (e1, e2) ->
    let e1 = simpl e1 in
    let e2 = simpl e2 in
    if is_pure e1.eff then e2 else { x with e = ESeq (e1, e2) }

  | EConst _ | EVar _ | EQual _ | EAny | EAbort _ -> x
  | EApp (h, es) -> { x with e = EApp (simpl h, es |> List.map simpl) }
  | EFun (bs, b) -> { x with e = EFun (bs, simpl b) }
  | EMatch (s, brs) ->
    let s = simpl s in
    let brs = brs |> List.map simpl_branch in
    (match as_if brs with
     | Some (t, f) -> { x with e = EIf (s, t, f) }
     | None -> { x with e = EMatch (s, brs) })
  | EIf (c, a, b) -> { x with e = EIf (simpl c, simpl a, simpl b) }
  | ECtor (n, es) -> { x with e = ECtor (n, es |> List.map simpl) }
  | ETuple es -> { x with e = ETuple (es |> List.map simpl) }
  | EOp (o, es) -> { x with e = EOp (o, es |> List.map simpl) }
  | ERaise e1 -> { x with e = ERaise (simpl e1) }
  | ERecord (n, fs) -> { x with e = ERecord (n, fs |> List.map (fun (f, e) -> (f, simpl e))) }
  | EProj (e1, n, f) -> { x with e = EProj (simpl e1, n, f) }
  | EDiscrim (e1, n) -> { x with e = EDiscrim (simpl e1, n) }
  | ECast (e1, c) -> { x with e = ECast (simpl e1, c) }
  | EWhile (a, b) -> { x with e = EWhile (simpl a, simpl b) }
  | ETry (a, brs) -> { x with e = ETry (simpl a, brs |> List.map simpl_branch) }

and simpl_branch (br:branch) : ML branch =
  let p, g, b = br in
  (p, (match g with None -> None | Some g -> Some (simpl g)), simpl b)

(* -------------------------------------------------------------------- *)
(* Inlining                                                             *)
(* -------------------------------------------------------------------- *)

(* A substitution of expressions for variables, plus the renaming that keeps
   the copy's own bound variables distinct from the ones at the call site.
   Both are string maps because Custard variable names are already unique per
   definition; only *copying* a definition can break that. *)
let subst = SMap.t expr

let rename (x:string) : ML string = uniq (base_name x) (GenSym.next_id ())

let rec sub (sm:subst) (x:expr) : ML expr =
  let g = sub sm in
  match x.e with
  | EVar v ->
    (match SMap.try_find sm v with
     | Some e -> e
     | None -> x)
  | EConst _ | EQual _ | EAny | EAbort _ -> x
  | ELet (v, ty, e1, e2) ->
    let v' = rename v in
    let e1 = g e1 in
    SMap.add sm v { x with e = EVar v'; ty; eff = E_Pure };
    let e2 = sub sm e2 in
    { x with e = ELet (v', ty, e1, e2) }
  | EApp (h, es) -> { x with e = EApp (g h, es |> List.map g) }
  | EFun (bs, b) ->
    let bs = bs |> List.map (fun b ->
      let n = rename b.b_name in
      SMap.add sm b.b_name { e = EVar n; ty = b.b_ty; eff = E_Pure };
      { b with b_name = n }) in
    { x with e = EFun (bs, sub sm b) }
  | EMatch (s, brs) -> { x with e = EMatch (g s, brs |> List.map (sub_branch sm)) }
  | EIf (c, a, b) -> { x with e = EIf (g c, g a, g b) }
  | ESeq (a, b) -> { x with e = ESeq (g a, g b) }
  | ECtor (n, es) -> { x with e = ECtor (n, es |> List.map g) }
  | ETuple es -> { x with e = ETuple (es |> List.map g) }
  | EOp (o, es) -> { x with e = EOp (o, es |> List.map g) }
  | ERaise e1 -> { x with e = ERaise (g e1) }
  | ERecord (n, fs) -> { x with e = ERecord (n, fs |> List.map (fun (f, e) -> (f, g e))) }
  | EProj (e1, n, f) -> { x with e = EProj (g e1, n, f) }
  | EDiscrim (e1, n) -> { x with e = EDiscrim (g e1, n) }
  | ECast (e1, c) -> { x with e = ECast (g e1, c) }
  | EWhile (a, b) -> { x with e = EWhile (g a, g b) }
  | ETry (a, brs) -> { x with e = ETry (g a, brs |> List.map (sub_branch sm)) }

and sub_branch (sm:subst) (br:branch) : ML branch =
  let p, guard, b = br in
  let p = sub_pat sm p in
  (p, (match guard with None -> None | Some e -> Some (sub sm e)), sub sm b)

and sub_pat (sm:subst) (p:pat) : ML pat =
  match p with
  | PWild | PConst _ -> p
  | PVar v ->
    let v' = rename v in
    (* The type is unknown here, and nothing downstream reads it off a
       pattern variable's occurrence. *)
    SMap.add sm v { e = EVar v'; ty = TAny; eff = E_Pure };
    PVar v'
  | PCtor (n, ps) -> PCtor (n, ps |> List.map (sub_pat sm))
  | PTuple ps -> PTuple (ps |> List.map (sub_pat sm))
  | POr ps -> POr (ps |> List.map (sub_pat sm))

let imax (a b : int) : int = if a >= b then a else b
let imin (a b : int) : int = if a <= b then a else b

(* How many times does [v] occur in [x]?  Capped at 2, which is all the
   decision below needs. *)
let rec count (v:string) (x:expr) : ML int =
  if occurs v x then (match x.e with
    | EVar _ -> 1
    | ELet (_, _, e1, e2) -> imin 2 (count v e1 + count v e2)
    | EApp (h, es) -> imin 2 (count v h + count_list v es)
    | EFun (_, b) -> count v b
    | EMatch (s, brs) ->
      (* The branches are alternatives, so the worst one is the count. *)
      imin 2 (count v s + (brs |> List.fold_left (fun acc (_, g, b) ->
               imax acc (count v b + (match g with None -> 0 | Some g -> count v g))) 0))
    | EIf (c, a, b) -> imin 2 (count v c + imax (count v a) (count v b))
    | EAny | EAbort _ -> 0
    | ESeq (a, b) -> imin 2 (count v a + count v b)
    | ECtor (_, es) | ETuple es | EOp (_, es) -> count_list v es
    | ERaise e1 -> count v e1
    | ERecord (_, fs) -> count_list v (fs |> List.map snd)
    | EProj (e1, _, _) | EDiscrim (e1, _) | ECast (e1, _) -> count v e1
    | EWhile (a, b) -> imin 2 (count v a + count v b)
    | ETry (a, brs) -> imin 2 (count v a + (brs |> List.fold_left (fun acc (_, _, b) ->
                                imax acc (count v b)) 0))
    | _ -> 1)
  else 0

and count_list (v:string) (es:list expr) : ML int =
  es |> List.fold_left (fun acc e -> imin 2 (acc + count v e)) 0

(* Duplicating an argument is only sound when evaluating it is unobservable,
   and only desirable when it is trivial; otherwise it gets a [let], which the
   simplifier will drop again if the parameter turns out to be unused. *)
let is_atomic (e:expr) : bool =
  match e.e with
  | EVar _ | EConst _ | EQual _ -> true
  | _ -> false

let inline_call (bs : list binder) (body:expr) (args:list expr) (at:expr) : ML expr =
  let sm : subst = SMap.create 10 in
  let lets = List.zip bs args |> List.collect (fun (b, a) ->
    if is_atomic a || (is_pure a.eff && count b.b_name body <= 1)
    then (SMap.add sm b.b_name a; [])
    else
      let v = rename b.b_name in
      SMap.add sm b.b_name { a with e = EVar v };
      [(v, b.b_ty, a)]) in
  let r = sub sm body in
  let r = { r with ty = at.ty; eff = at.eff } in
  List.fold_right (fun (v, ty, a) acc ->
    { acc with e = ELet (v, ty, a, acc) }) lets r

(* Beta: [(fun bs -> body) args].  With more arguments than binders the
   surplus is re-applied to the result; with fewer, nothing happens, because a
   partial application is a closure and turning it into one would be a
   different program. *)
let beta (bs : list binder) (body:expr) (args:list expr) (at:expr) : ML expr =
  let n = List.length bs in
  if List.length args < n then at
  else
    let given, extra = List.splitAt n args in
    let r = inline_call bs body given at in
    match extra with
    | [] -> r
    | _ -> { at with e = EApp (r, extra) }

(* Iota: match a constructor application against a pattern, yielding the
   bindings it makes.  [None] means "cannot tell", which is the answer for
   anything the analysis does not model, and leaves the match alone. *)
let rec match_pat (p:pat) (e:expr) : ML (option (list (string & expr))) =
  match p, e.e with
  | PWild, _ -> Some []
  | PVar v, _ -> Some [(v, e)]
  | PCtor (n, ps), ECtor (m, es) ->
    if string_of_name n = string_of_name m then match_pats ps es else None
  | PTuple ps, ETuple es -> match_pats ps es
  | PConst c1, EConst c2 -> if c1 = c2 then Some [] else None
  | _, _ -> None

and match_pats (ps:list pat) (es:list expr) : ML (option (list (string & expr))) =
  match ps, es with
  | [], [] -> Some []
  | p :: ps, e :: es ->
    (match match_pat p e, match_pats ps es with
     | Some l1, Some l2 -> Some (l1 @ l2)
     | _ -> None)
  | _ -> None

(* Selecting a branch discards the scrutinee's other fields, so it is only
   sound when building them was unobservable. *)
let rec ctor_args_pure (e:expr) : ML bool =
  match e.e with
  | ECtor (_, es) -> es |> List.for_all (fun a -> is_pure a.eff)
  | ETuple es -> es |> List.for_all (fun a -> is_pure a.eff)
  | _ -> false

let rec iota (brs:list branch) (scrut:expr) (at:expr) : ML expr =
  match brs with
  | [] -> at
  | (p, None, body) :: brs ->
    (match match_pat p scrut with
     | None -> at
     (* The bindings go through [inline_call] rather than becoming [let]s: a
        field used once has to be *substituted*, or the head of the enclosing
        application is a [let] and the beta rule below never sees the function
        it is wrapping. *)
     | Some bnds ->
       inline_call (bnds |> List.map (fun (v, (a:expr)) -> { b_name = v; b_ty = a.ty }))
                   body (bnds |> List.map snd) at)
  (* A guard has to be evaluated before the branch is known. *)
  | _ -> at

(* Beta and iota to a fixed point.  This is what collapses a record of
   functions: inlining a projector leaves [(match C f g with C (p, s) -> s) x],
   which iota turns into [f x] and beta into [f]'s body.  Neither rule fires on
   its own, and each one exposes work for the other, so a rewritten node is
   re-examined rather than merely rebuilt. *)
let rec reduce (x:expr) : ML expr =
  match x.e with
  | EApp (h, args) ->
    let h = reduce h in
    let args = args |> List.map reduce in
    (match h.e with
     | EFun (bs, body) when List.length bs <= List.length args ->
       reduce (beta bs body args { x with e = EApp (h, args) })
     | _ -> { x with e = EApp (h, args) })

  | EMatch (scrut, brs) ->
    let scrut = reduce scrut in
    if ctor_args_pure scrut
    then
      let r = iota brs scrut { x with e = EMatch (scrut, brs |> List.map reduce_branch) } in
      (match r.e with
       | EMatch _ -> r
       | _ -> reduce r)
    else { x with e = EMatch (scrut, brs |> List.map reduce_branch) }

  | EConst _ | EVar _ | EQual _ | EAny | EAbort _ -> x
  | ELet (v, ty, e1, e2) -> { x with e = ELet (v, ty, reduce e1, reduce e2) }
  | EFun (bs, b) -> { x with e = EFun (bs, reduce b) }
  | EIf (c, a, b) -> { x with e = EIf (reduce c, reduce a, reduce b) }
  | ESeq (a, b) -> { x with e = ESeq (reduce a, reduce b) }
  | ECtor (n, es) -> { x with e = ECtor (n, es |> List.map reduce) }
  | ETuple es -> { x with e = ETuple (es |> List.map reduce) }
  | EOp (o, es) -> { x with e = EOp (o, es |> List.map reduce) }
  | ERaise e1 -> { x with e = ERaise (reduce e1) }
  | ERecord (n, fs) -> { x with e = ERecord (n, fs |> List.map (fun (f, e) -> (f, reduce e))) }
  | EProj (e1, n, f) -> { x with e = EProj (reduce e1, n, f) }
  | EDiscrim (e1, n) -> { x with e = EDiscrim (reduce e1, n) }
  | ECast (e1, c) -> { x with e = ECast (reduce e1, c) }
  | EWhile (a, b) -> { x with e = EWhile (reduce a, reduce b) }
  | ETry (a, brs) -> { x with e = ETry (reduce a, brs |> List.map reduce_branch) }

and reduce_branch (br:branch) : ML branch =
  let p, g, b = br in
  (p, (match g with None -> None | Some g -> Some (reduce g)), reduce b)

let reduce_decls (prog:program) : ML program =
  prog |> List.map (fun d ->
    match d with
    | DLet dl -> DLet { dl with dl_body = reduce dl.dl_body }
    | d -> d)

(* [Inline] declarations are substituted at their fully applied uses.  A use
   that is *not* fully applied keeps the declaration alive, so it is emitted
   after all; that is rare enough not to be worth eta-expanding. *)
let rec inline_expr (tbl : SMap.t (list binder & expr)) (used : SMap.t bool) (x:expr)
  : ML expr =
  (* [used] records the [Inline] declarations that had to be kept after all,
     either because a use was not fully applied or because it came before the
     definition (which a mutually recursive group can do). *)
  let g = inline_expr tbl used in
  match x.e with
  | EApp ({e = EQual (n, tys)}, args) ->
    let args = args |> List.map g in
    (match SMap.try_find tbl (string_of_name n) with
     (* Over-application is common and must be handled: F* stores the
        projector of an arrow-typed field as a one-binder function returning a
        function, so every use of it is applied to one argument too many. *)
     | Some (bs, body) when List.length bs <= List.length args ->
       let given, extra = List.splitAt (List.length bs) args in
       let r = inline_call bs body given x in
       (match extra with
        | [] -> r
        | _ -> { x with e = EApp (r, extra) })
     | _ -> SMap.add used (string_of_name n) true;
            { x with e = EApp ({ x with e = EQual (n, tys) }, args) })
  | EQual (n, _) ->
    (match SMap.try_find tbl (string_of_name n) with
     | Some ([], body) -> inline_call [] body [] x
     | _ -> SMap.add used (string_of_name n) true; x)
  | EConst _ | EVar _ | EAny | EAbort _ -> x
  | ELet (v, ty, e1, e2) -> { x with e = ELet (v, ty, g e1, g e2) }
  | EApp (h, es) -> { x with e = EApp (g h, es |> List.map g) }
  | EFun (bs, b) -> { x with e = EFun (bs, g b) }
  | EMatch (s, brs) -> { x with e = EMatch (g s, brs |> List.map (inline_branch tbl used)) }
  | EIf (c, a, b) -> { x with e = EIf (g c, g a, g b) }
  | ESeq (a, b) -> { x with e = ESeq (g a, g b) }
  | ECtor (n, es) -> { x with e = ECtor (n, es |> List.map g) }
  | ETuple es -> { x with e = ETuple (es |> List.map g) }
  | EOp (o, es) -> { x with e = EOp (o, es |> List.map g) }
  | ERaise e1 -> { x with e = ERaise (g e1) }
  | ERecord (n, fs) -> { x with e = ERecord (n, fs |> List.map (fun (f, e) -> (f, g e))) }
  | EProj (e1, n, f) -> { x with e = EProj (g e1, n, f) }
  | EDiscrim (e1, n) -> { x with e = EDiscrim (g e1, n) }
  | ECast (e1, c) -> { x with e = ECast (g e1, c) }
  | EWhile (a, b) -> { x with e = EWhile (g a, g b) }
  | ETry (a, brs) -> { x with e = ETry (g a, brs |> List.map (inline_branch tbl used)) }

and inline_branch (tbl : SMap.t (list binder & expr)) (used : SMap.t bool) (br:branch)
  : ML branch =
  let p, guard, b = br in
  (p, (match guard with None -> None | Some e -> Some (inline_expr tbl used e)),
   inline_expr tbl used b)

(* -------------------------------------------------------------------- *)
(* Eta reduction                                                        *)
(* -------------------------------------------------------------------- *)

(* F* stores the projector of a field whose type is an arrow eta-expanded:
   [let __proj__Mkht_t__item__hashf projectee x = (match projectee with ... ) x].
   Extraction faithfully reproduces that, and the extra binder then defeats
   both projector inlining (which needs an exactly saturated use) and the C
   backend (which sees a call with too few arguments).  Dropping a trailing
   binder that is applied to a pure head, and to nothing else, is always sound;
   the arrow it used to consume moves into the result type. *)

let rec split_last (es:list 'a) : ML (option (list 'a & 'a)) =
  match es with
  | [] -> None
  | [e] -> Some ([], e)
  | e :: es -> (match split_last es with
                | Some (pre, last) -> Some (e :: pre, last)
                | None -> None)

let rec eta_reduce (bs:list binder) (body:expr) (ret:cty) (ef:eff)
  : ML (list binder & expr & cty & eff) =
  match split_last bs, body.e with
  | Some (bs', b), EApp (f, args) when Cons? bs' ->
    (match split_last args with
     | Some (args', { e = EVar v }) when v = b.b_name
                                      && is_pure f.eff
                                      && not (occurs v f)
                                      && not (args' |> List.existsb (occurs v)) ->
       let ret' = TArrow (b.b_ty, ef, ret) in
       let body' = match args' with
                   | [] -> { f with ty = ret' }
                   | _ -> { body with e = EApp (f, args'); ty = ret'; eff = E_Pure } in
       eta_reduce bs' body' ret' E_Pure
     | _ -> (bs, body, ret, ef))
  | _ -> (bs, body, ret, ef)

let eta_reduce_decls (prog:program) : ML program =
  prog |> List.map (fun d ->
    match d with
    | DLet l ->
      let bs, body, ret, ef = eta_reduce l.dl_binders l.dl_body l.dl_ret l.dl_eff in
      DLet { l with dl_binders = bs; dl_body = body; dl_ret = ret; dl_eff = ef }
    | d -> d)

(* One left-to-right pass: the program is topologically sorted, so by the time
   an [Inline] body is stored it has already had its own callees inlined. *)
let inline_decls (prog:program) : ML program =
  let tbl : SMap.t (list binder & expr) = SMap.create 50 in
  let used : SMap.t bool = SMap.create 50 in
  let prog = prog |> List.map (fun d ->
    match d with
    | DLet dl ->
      let body = inline_expr tbl used dl.dl_body in
      if dl.dl_flags |> List.existsb Inline?
      then SMap.add tbl (string_of_name dl.dl_name) (dl.dl_binders, body);
      DLet { dl with dl_body = body }
    | d -> d) in
  prog |> List.filter (fun d ->
    match d with
    | DLet dl -> not (dl.dl_flags |> List.existsb Inline?)
              || Some? (SMap.try_find used (string_of_name dl.dl_name))
    | _ -> true)

(* -------------------------------------------------------------------- *)
(* Dead-declaration elimination                                         *)
(* -------------------------------------------------------------------- *)

(* Extraction requests a definition as soon as it meets one, including from
   positions that the layout analysis later erases -- the ghost model of a data
   structure, say.  What is left behind is a specification-only declaration
   that nothing reachable calls: harmless in OCaml, but karamel rejects it
   ("not Low*", because specifications use mathematical integers), so it has to
   go.  Reachability is computed after inlining, when the call graph is final. *)

let rec cty_deps (c:cty) : ML (list string) =
  match c with
  | TApp (n, args) -> string_of_name n :: List.collect cty_deps args
  | TArrow (a, _, b) -> cty_deps a @ cty_deps b
  | TTuple cs -> List.collect cty_deps cs
  | TBuf c | TRef c | TInline c -> cty_deps c
  | _ -> []

let rec pat_deps (p:pat) : ML (list string) =
  match p with
  | PCtor (n, ps) -> string_of_name n :: List.collect pat_deps ps
  | PTuple ps
  | POr ps -> List.collect pat_deps ps
  | _ -> []

let rec expr_deps (x:expr) : ML (list string) =
  let ds = cty_deps x.ty in
  let sub (es:list expr) : ML (list string) = List.collect expr_deps es in
  ds @ (match x.e with
        | EQual (n, tys) -> string_of_name n :: List.collect cty_deps tys
        | ECtor (n, es) -> string_of_name n :: sub es
        | ERaise e1 -> expr_deps e1
        | ERecord (n, fs) -> string_of_name n :: sub (List.map snd fs)
        | EDiscrim (e, n) -> string_of_name n :: expr_deps e
        | EProj (e, n, _) -> string_of_name n :: expr_deps e
        | EConst _ | EVar _ | EAny | EAbort _ -> []
        | ELet (_, t, e1, e2) -> cty_deps t @ sub [e1; e2]
        | EApp (h, es) -> sub (h :: es)
        | EFun (bs, b) -> List.collect (fun (b:binder) -> cty_deps b.b_ty) bs @ expr_deps b
        | EMatch (sc, brs) ->
          expr_deps sc @ (brs |> List.collect (fun (p, g, b) ->
            pat_deps p @ (match g with Some g -> expr_deps g | None -> []) @ expr_deps b))
        | EIf (c, a, b) -> sub [c; a; b]
        | ESeq (a, b) -> sub [a; b]
        | ETuple es | EOp (_, es) -> sub es
        | ECast (e, t) -> cty_deps t @ expr_deps e
        | EWhile (c, b) -> sub [c; b]
        | ETry (e, brs) ->
          expr_deps e @ (brs |> List.collect (fun (p, g, b) ->
            pat_deps p @ (match g with Some g -> expr_deps g | None -> []) @ expr_deps b)))

let decl_deps (d:decl) : ML (list string) =
  match d with
  | DLet l ->
    List.collect (fun (b:binder) -> cty_deps b.b_ty) l.dl_binders
    @ cty_deps l.dl_ret @ expr_deps l.dl_body
  | DType t ->
    (match t.dt_body with
     | TAbbrev c -> cty_deps c
     | TRecord fs -> List.collect (fun (_, c) -> cty_deps c) fs
     | TVariant cs -> cs |> List.collect (fun (_, fs) ->
                        List.collect (fun (_, c) -> cty_deps c) fs)
     | TAbstract -> [])
  | DExternal x -> cty_deps x.dx_ty
  | DExn e -> List.collect cty_deps e.de_args

(* A constructor or field name refers to its declaration, not to itself. *)
let owners (prog:program) : ML (SMap.t string) =
  let m : SMap.t string = SMap.create 50 in
  prog |> List.iter (fun d ->
    match d with
    | DType t ->
      let owner = string_of_name t.dt_name in
      (match t.dt_body with
       | TVariant cs -> cs |> List.iter (fun (cn, _) -> SMap.add m (string_of_name cn) owner)
       | _ -> ())
    | _ -> ());
  m

let dce (prog:program) : ML program =
  let own = owners prog in
  let resolve (n:string) : ML string =
    match SMap.try_find own n with Some o -> o | None -> n in
  let defs : SMap.t decl = SMap.create 50 in
  prog |> List.iter (fun d -> SMap.add defs (string_of_name (name_of_decl d)) d);
  let live : SMap.t bool = SMap.create 50 in
  let rec visit (n:string) : ML unit =
    let n = resolve n in
    if None? (SMap.try_find live n) then begin
      SMap.add live n true;
      match SMap.try_find defs n with
      | Some d -> decl_deps d |> List.iter visit
      | None -> ()
    end in
  prog |> List.iter (fun d ->
    if decl_flags d |> List.existsb (fun f -> Root? f || Entrypoint? f)
    then visit (string_of_name (name_of_decl d)));
  prog |> List.filter (fun d ->
    Some? (SMap.try_find live (string_of_name (name_of_decl d))))

(* Section 6, pass 7: unused type parameters.

   Monomorphization removes the type parameters a declaration is specialized
   on, but section 5.0's uniform compilation deliberately leaves the [Poly]
   ones behind, and some of those turn out not to describe any part of the
   runtime representation:

     type tagged (a:Type) (b:Type) = | L : a -> tagged a b | R : a -> tagged a b

   [b] is a phantom: no field mentions it, so every instantiation of [tagged]
   has the same layout and the parameter is pure noise.  Carrying it costs
   nothing in OCaml, where the parameter is only a name, but the direct-to-C
   backend has to instantiate what it is given, so a phantom parameter there is
   a fork in the monomorphization for no reason.

   "Used" is a least fixed point, because a parameter can be used solely by
   being passed on:

     type chain (p:Type) (q:Type) = tagged p q

   [q] occurs in [chain]'s body, but only in a position of [tagged] that is
   itself about to be dropped, so [q] is unused too.  Starting from "every
   parameter is unused" and only ever adding uses gets this right, and gets the
   recursive case ([type t (a:Type) = ... t a ...] where [a] reaches nothing
   but the recursive occurrence) right for the same reason.

   This is the analogue of the ML extraction's
   {!FStarC.Extraction.ML.RemoveUnusedParameters}, which needs the same
   transformation to satisfy F#.  Custard's version is both simpler and more
   aggressive: because the program is whole, every use site is in hand and
   there is no need to record the eliminated positions for a separately
   compiled client to agree with, and the same analysis extends from type
   abbreviations to inductives and to the type parameters of functions. *)
let unused_params (prog:program) : ML program =
  let params_of (d:decl) : list string =
    match d with
    | DType t -> t.dt_params
    | DLet l -> l.dl_typars
    | _ -> [] in
  let keep : SMap.t (list bool) = SMap.create 50 in
  prog |> List.iter (fun d ->
    match params_of d with
    | [] -> ()
    | ps -> SMap.add keep (string_of_name (name_of_decl d))
                          (ps |> List.map (fun _ -> false)));

  let rec select (ks:list bool) (xs:list cty) : list cty =
    match ks, xs with
    | k :: ks, x :: xs -> if k then x :: select ks xs else select ks xs
    | _ -> xs in
  (* Only rewrite an application whose shape we can vouch for: a reference to a
     declaration we have, saturated with exactly its parameters. *)
  let retained (n:name) (args:list cty) : ML (option (list bool)) =
    match SMap.try_find keep (string_of_name n) with
    | Some ks when List.length ks = List.length args -> Some ks
    | _ -> None in

  (* Phase 1: which parameters are used, as a fixed point. *)
  let changed : ref bool = mk_ref false in
  let acc : ref (list string) = mk_ref [] in
  let rec u_cty (c:cty) : ML unit =
    match c with
    | TVar v -> acc := v :: !acc
    | TApp (n, args) -> u_args n args
    | TArrow (a, _, b) -> u_cty a; u_cty b
    | TTuple cs -> cs |> List.iter u_cty
    | TBuf c | TRef c | TInline c -> u_cty c
    | TInt _ | TUnit | TExn | TAny -> ()
  and u_args (n:name) (args:list cty) : ML unit =
    match retained n args with
    | Some ks -> List.zip ks args |> List.iter (fun (k, a) -> if k then u_cty a)
    | None -> args |> List.iter u_cty in
  let rec u_expr (x:expr) : ML unit =
    u_cty x.ty;
    let sub (es:list expr) : ML unit = es |> List.iter u_expr in
    match x.e with
    | EConst _ | EVar _ | EAny | EAbort _ -> ()
    | EQual (n, tys) -> u_args n tys
    | ELet (_, t, e1, e2) -> u_cty t; sub [e1; e2]
    | EApp (h, es) -> sub (h :: es)
    | EFun (bs, b) -> bs |> List.iter (fun (b:binder) -> u_cty b.b_ty); u_expr b
    | EMatch (sc, brs) -> u_expr sc; brs |> List.iter u_branch
    | ETry (e, brs) -> u_expr e; brs |> List.iter u_branch
    | EIf (c, a, b) -> sub [c; a; b]
    | ESeq (a, b) -> sub [a; b]
    | ECtor (_, es) | ETuple es | EOp (_, es) -> sub es
    | ERaise e1 -> u_expr e1
    | ERecord (_, fs) -> sub (fs |> List.map snd)
    | EProj (e, _, _) | EDiscrim (e, _) -> u_expr e
    | ECast (e, t) -> u_cty t; u_expr e
    | EWhile (c, b) -> sub [c; b]
  and u_branch (br:branch) : ML unit =
    let _, g, b = br in
    (match g with Some g -> u_expr g | None -> ());
    u_expr b in
  let u_tydef (b:tydef) : ML unit =
    let fields (fs:list (string & cty)) : ML unit =
      fs |> List.iter (fun (_, c) -> u_cty c) in
    match b with
    | TAbbrev c -> u_cty c
    | TRecord fs -> fields fs
    | TVariant cs -> cs |> List.iter (fun (_, fs) -> fields fs)
    | TAbstract -> () in
  let visit (d:decl) : ML unit =
    match params_of d with
    | [] -> ()
    | ps ->
      acc := [];
      (match d with
       | DType t -> u_tydef t.dt_body
       | DLet l ->
         l.dl_binders |> List.iter (fun (b:binder) -> u_cty b.b_ty);
         u_cty l.dl_ret;
         u_expr l.dl_body
       | _ -> ());
      let seen = !acc in
      let n = string_of_name (name_of_decl d) in
      let old = match SMap.try_find keep n with Some ks -> ks | None -> [] in
      let ks = List.zip old ps |> List.map (fun (k, p) ->
                 k || List.existsb (fun v -> v = p) seen) in
      if ks <> old then (changed := true; SMap.add keep n ks) in
  let rec fixpoint (fuel:int) : ML unit =
    changed := false;
    prog |> List.iter visit;
    if !changed && fuel > 0 then fixpoint (fuel - 1) in
  (* The fixed point is monotone in a lattice whose height is the total number
     of parameters, so that many rounds always suffice. *)
  fixpoint (1 + List.fold_left (fun n d -> n + List.length (params_of d)) 0 prog);

  (* Phase 2: drop the parameters, and the arguments at their positions. *)
  let rec r_cty (c:cty) : ML cty =
    match c with
    | TApp (n, args) ->
      let args = args |> List.map r_cty in
      TApp (n, (match retained n args with Some ks -> select ks args | None -> args))
    | TArrow (a, e, b) -> TArrow (r_cty a, e, r_cty b)
    | TTuple cs -> TTuple (cs |> List.map r_cty)
    | TBuf c -> TBuf (r_cty c)
    | TRef c -> TRef (r_cty c)
    | TInline c -> TInline (r_cty c)
    | TVar _ | TInt _ | TUnit | TExn | TAny -> c in
  let r_binder (b:binder) : ML binder = { b with b_ty = r_cty b.b_ty } in
  let rec r_expr (x:expr) : ML expr =
    let go = r_expr in
    let e =
      match x.e with
      | EConst _ | EVar _ | EAny | EAbort _ -> x.e
      | EQual (n, tys) ->
        let tys = tys |> List.map r_cty in
        EQual (n, (match retained n tys with Some ks -> select ks tys | None -> tys))
      | ELet (v, t, e1, e2) -> ELet (v, r_cty t, go e1, go e2)
      | EApp (h, es) -> EApp (go h, es |> List.map go)
      | EFun (bs, b) -> EFun (bs |> List.map r_binder, go b)
      | EMatch (sc, brs) -> EMatch (go sc, brs |> List.map r_branch)
      | ETry (e, brs) -> ETry (go e, brs |> List.map r_branch)
      | EIf (c, a, b) -> EIf (go c, go a, go b)
      | ESeq (a, b) -> ESeq (go a, go b)
      | ECtor (n, es) -> ECtor (n, es |> List.map go)
      | ERaise e1 -> ERaise (go e1)
      | ETuple es -> ETuple (es |> List.map go)
      | EOp (o, es) -> EOp (o, es |> List.map go)
      | ERecord (n, fs) -> ERecord (n, fs |> List.map (fun (f, e) -> (f, go e)))
      | EProj (e, n, f) -> EProj (go e, n, f)
      | EDiscrim (e, n) -> EDiscrim (go e, n)
      | ECast (e, t) -> ECast (go e, r_cty t)
      | EWhile (c, b) -> EWhile (go c, go b)
    in
    { x with e = e; ty = r_cty x.ty }
  and r_branch (br:branch) : ML branch =
    let p, g, b = br in
    (p, (match g with Some g -> Some (r_expr g) | None -> None), r_expr b) in
  let r_tydef (b:tydef) : ML tydef =
    let fields (fs:list (string & cty)) : ML (list (string & cty)) =
      fs |> List.map (fun (f, c) -> (f, r_cty c)) in
    match b with
    | TAbbrev c -> TAbbrev (r_cty c)
    | TRecord fs -> TRecord (fields fs)
    | TVariant cs -> TVariant (cs |> List.map (fun (cn, fs) -> (cn, fields fs)))
    | TAbstract -> TAbstract in
  let survivors (d:decl) (ps:list string) : ML (list string) =
    match SMap.try_find keep (string_of_name (name_of_decl d)) with
    | Some ks when List.length ks = List.length ps ->
      List.zip ks ps |> List.collect (fun (k, p) -> if k then [p] else [])
    | _ -> ps in
  prog |> List.map (fun d ->
    match d with
    | DType t -> DType { t with dt_params = survivors d t.dt_params;
                                dt_body = r_tydef t.dt_body }
    | DLet l -> DLet { l with dl_typars = survivors d l.dl_typars;
                              dl_binders = l.dl_binders |> List.map r_binder;
                              dl_ret = r_cty l.dl_ret;
                              dl_body = r_expr l.dl_body }
    | DExternal x -> DExternal { x with dx_ty = r_cty x.dx_ty }
    | DExn e -> DExn { e with de_args = e.de_args |> List.map r_cty })

(* Section 6, pass 8: strongly connected components.

   The extraction loop appends a declaration once it has finished translating
   it, so everything a definition mentions is already in the list by the time
   the definition itself is -- a topological order, but only while the
   dependency graph is acyclic.  Recursion is exactly the case where no such
   order exists, and both of the target languages want the members of a cycle
   written as a single [let rec ... and ...] or [type ... and ...] group.  So
   we recover the cycles here, with Tarjan's algorithm, and reorder the program
   so that the members of a group are adjacent.

   This also makes the [Rec] flag mean what its comment in {!Syntax} says --
   "the SCC this declaration belongs to" -- rather than what the source said.
   [extract_lid] can only set it from F*'s [is_rec], which specialization and
   the passes above invalidate in both directions: unrolling a recursive
   definition against a [Mono] argument leaves a non-recursive body, and
   inlining can introduce a call that closes a cycle. *)
let scc (prog:program) : ML program =
  let own = owners prog in
  let key (d:decl) : ML string = string_of_name (name_of_decl d) in
  let defs : SMap.t decl = SMap.create 50 in
  prog |> List.iter (fun d -> SMap.add defs (key d) d);
  (* Original position, so that a component's members and the components
     themselves come out in an order a reader can predict. *)
  let pos : SMap.t int = SMap.create 50 in
  let _ = prog |> List.fold_left (fun i d -> SMap.add pos (key d) i; i + 1) 0 in
  let at (n:string) : ML int =
    match SMap.try_find pos n with Some i -> i | None -> 0 in
  let succs (n:string) : ML (list string) =
    match SMap.try_find defs n with
    | None -> []
    | Some d ->
      decl_deps d
      |> List.map (fun m -> match SMap.try_find own m with Some o -> o | None -> m)
      |> List.filter (fun m -> Some? (SMap.try_find defs m)) in

  let index : SMap.t int = SMap.create 50 in
  let low : SMap.t int = SMap.create 50 in
  let onstack : SMap.t bool = SMap.create 50 in
  let stack : ref (list string) = mk_ref [] in
  let counter : ref int = mk_ref 0 in
  (* Accumulated in reverse: Tarjan closes a component only once every
     component it depends on is closed, so prepending and reversing at the end
     puts dependencies first. *)
  let comps : ref (list (list string)) = mk_ref [] in
  let get (m:SMap.t int) (n:string) : ML int =
    match SMap.try_find m n with Some i -> i | None -> 0 in
  let rec strong (v:string) : ML unit =
    let i = !counter in
    counter := i + 1;
    SMap.add index v i;
    SMap.add low v i;
    stack := v :: !stack;
    SMap.add onstack v true;
    succs v |> List.iter (fun w ->
      match SMap.try_find index w with
      | None ->
        strong w;
        SMap.add low v (imin (get low v) (get low w))
      | Some iw ->
        if SMap.try_find onstack w = Some true
        then SMap.add low v (imin (get low v) iw));
    if get low v = get index v then begin
      let rec pop (acc:list string) (st:list string) : ML (list string & list string) =
        match st with
        | [] -> (acc, [])
        | w :: rest ->
          SMap.add onstack w false;
          if w = v then (w :: acc, rest) else pop (w :: acc) rest in
      let comp, rest = pop [] !stack in
      stack := rest;
      comps := List.sortWith (fun a b -> at a - at b) comp :: !comps
    end in
  prog |> List.iter (fun d ->
    let n = key d in
    if None? (SMap.try_find index n) then strong n);

  (* A component is recursive if it has more than one member, or if its single
     member refers to itself. *)
  let flags (comp:list string) : ML (list flag) =
    match comp with
    | [n] when not (succs n |> List.existsb (fun m -> m = n)) -> []
    | _ -> [Rec (comp |> List.collect (fun n ->
                   match SMap.try_find defs n with
                   | Some d -> [name_of_decl d]
                   | None -> []))] in
  let retag (fs:list flag) (d:decl) : ML decl =
    let keep gs = fs @ List.filter (fun f -> not (Rec? f)) gs in
    match d with
    | DLet l      -> DLet { l with dl_flags = keep l.dl_flags }
    | DType t     -> DType { t with dt_flags = keep t.dt_flags }
    | DExternal x -> DExternal { x with dx_flags = keep x.dx_flags }
    | DExn _      -> d in
  List.rev !comps |> List.collect (fun comp ->
    let fs = flags comp in
    comp |> List.collect (fun n ->
      match SMap.try_find defs n with
      | Some d -> [retag fs d]
      | None -> []))

(* -------------------------------------------------------------------- *)
(* Unreachable branches                                                 *)
(* -------------------------------------------------------------------- *)

(* [EAbort] says control does not reach here, and it means it: the only rule
   that introduces one is Pulse's [unreachable] (section 8.3), whose
   precondition F* has already proved false.  A branch whose body is nothing
   but an abort therefore contributes nothing to the value of the match, and
   testing for it is wasted work at run time and noise in the output.

   This was a C-backend peephole first, where dropping the branch also lets the
   one before it become unconditional.  But the reasoning has nothing to do
   with C: the branch is dead in every target, and OCaml's non-exhaustive-match
   warning is off in the generated file's header (and in the flags [--ocamlopt]
   passes) precisely because Custard relies on F*'s exhaustiveness check
   rather than on OCaml's. *)

let take (x:expr) (c:expr) (r:expr) : ML expr =
  (* [x] supplies the type and effect: both are over-approximations of [r]'s,
   which is the safe direction -- an effect that is too high only stops a
   later pass from moving something. *)
  if is_pure c.eff then { x with e = r.e } else { x with e = ESeq (c, r) }

let rec prune (x:expr) : ML expr =
  let g = prune in
  match x.e with
  | EMatch (s, brs) ->
    let s = g s in
    let brs = brs |> List.map prune_branch in
    let live = brs |> List.filter (fun (_, _, b) -> not (EAbort? b.e)) in
    (* A match all of whose branches abort cannot be entered at all, so there
       is nothing to choose between them: it is just the abort, with the
       scrutinee kept only if evaluating it is observable. *)
    (match live, brs with
     | [], (_, _, b) :: _ -> take x s b
     | _ -> { x with e = EMatch (s, (if Nil? live then brs else live)) })

  | EIf (c, a, b) ->
    let c = g c in
    let a = g a in
    let b = g b in
    if EAbort? b.e && not (EAbort? a.e) then take x c a
    else if EAbort? a.e && not (EAbort? b.e) then take x c b
    else { x with e = EIf (c, a, b) }

  | EConst _ | EVar _ | EQual _ | EAny | EAbort _ -> x
  | ELet (v, ty, a, b) -> { x with e = ELet (v, ty, g a, g b) }
  | ESeq (a, b) -> { x with e = ESeq (g a, g b) }
  | EWhile (a, b) -> { x with e = EWhile (g a, g b) }
  | EApp (h, es) -> { x with e = EApp (g h, es |> List.map g) }
  | EFun (bs, b) -> { x with e = EFun (bs, g b) }
  | ECtor (n, es) -> { x with e = ECtor (n, es |> List.map g) }
  | ETuple es -> { x with e = ETuple (es |> List.map g) }
  | EOp (o, es) -> { x with e = EOp (o, es |> List.map g) }
  | ERaise e1 -> { x with e = ERaise (g e1) }
  | ERecord (n, fs) -> { x with e = ERecord (n, fs |> List.map (fun (f, e) -> (f, g e))) }
  | EProj (e1, n, f) -> { x with e = EProj (g e1, n, f) }
  | EDiscrim (e1, n) -> { x with e = EDiscrim (g e1, n) }
  | ECast (e1, c) -> { x with e = ECast (g e1, c) }
  | ETry (a, brs) -> { x with e = ETry (g a, brs |> List.map prune_branch) }

and prune_branch (br:branch) : ML branch =
  let p, guard, b = br in
  (p, (match guard with None -> None | Some e -> Some (prune e)), prune b)

let prune_decls (prog:program) : ML program =
  prog |> List.map (fun d ->
    match d with
    | DLet dl -> DLet { dl with dl_body = prune dl.dl_body }
    | d -> d)

(* -------------------------------------------------------------------- *)
(* Record recovery                                                      *)
(* -------------------------------------------------------------------- *)

(* Extraction turns every inductive into a [TVariant], even the ones F* calls
   records, because the ML syntax it reads has already forgotten which is
   which.  A single-constructor variant is then matched to get at its fields,
   and every backend has to undo that for itself: the C one because a match on
   an irrefutable pattern is not a control-flow construct at all, the OCaml one
   because [Mkfoo (a, b, c)] is unreadable where [foo.b] was written.  Doing it
   once on the IR is both less code and better output everywhere.

   The pass has two halves.  The first rewrites a match on a single-constructor
   pattern into projections, which is what makes the second possible: once no
   [PCtor] of a type survives, the type can become a [TRecord], which every
   backend already prints natively. *)

noeq
type ctor_info = {
  ci_owner:  name;               (* the type this constructor belongs to *)
  ci_count:  int;                (* how many constructors that type has *)
  ci_fields: list (string & cty);
}

(* The imported types this run links against: each as the layout analysis left
   it, as its home unit finally emitted it, and with the record verdict that
   unit reached.  Both shapes are needed -- the questions this file asks are
   about the *pre*-simplification declaration, while the answers it must not
   contradict are visible only in the final one.  A [ref] rather than an
   argument threaded through a dozen functions, for the same reason
   {!FStarC.Custard.PrintOCaml.externals} is one: it is constant for a whole
   program.  Set by {!run}. *)
let imported_types : ref (list (dtype & dtype & bool)) = mk_ref []

(* The program as the *type*-inspecting passes should see it.  Imported types
   are visible to a question about a declaration and invisible to everything
   else: they contribute no body, they are not re-decided, and they are not
   emitted. *)
let with_imports (prog:program) : ML program =
  match !imported_types with
  | [] -> prog
  | ts -> (ts |> List.map (fun (dt, _, _) -> DType dt)) @ prog

let ctor_infos (prog:program) : ML (SMap.t ctor_info) =
  let m : SMap.t ctor_info = SMap.create 50 in
  prog |> List.iter (fun d ->
    match d with
    | DType ({ dt_name = tn; dt_body = TVariant cs }) ->
      let n = List.length cs in
      cs |> List.iter (fun (cn, fs) ->
        (* [TInline] is [inline_fields]'s business; the types this table hands
           out end up on [EProj] nodes, where the marker has no meaning. *)
        let fs = fs |> List.map (fun (f, c) -> (f, (match c with TInline c -> c | c -> c))) in
        SMap.add m (string_of_name cn) { ci_owner = tn; ci_count = n; ci_fields = fs })
    | _ -> ());
  m

let single_ctor (tbl:SMap.t ctor_info) (cn:name) : ML (option ctor_info) =
  match SMap.try_find tbl (string_of_name cn) with
  | Some ci when ci.ci_count = 1 -> Some ci
  | _ -> None

(* Reading a projection out of [e] once per field is only worth it when [e] is
   free to re-evaluate; anything else keeps its [let]. *)
let rec dup_ok (e:expr) : ML bool =
  match e.e with
  | EVar _ | EConst _ | EQual _ -> true
  | EProj (a, _, _) -> dup_ok a
  | _ -> false

(* Substitution for variables that does *not* rename the binders it passes
   under.  [sub] has to rename because it copies a definition into a scope that
   may already use the same names; here the body stays where it is, and the
   expressions substituted in are projections out of variables bound outside
   it, so the names cannot collide.  Not renaming keeps the output readable. *)
let rec psub (sm:subst) (x:expr) : ML expr =
  let g = psub sm in
  match x.e with
  | EVar v -> (match SMap.try_find sm v with Some e -> e | None -> x)
  | EConst _ | EQual _ | EAny | EAbort _ -> x
  | ELet (v, ty, e1, e2) -> { x with e = ELet (v, ty, g e1, g e2) }
  | EApp (h, es) -> { x with e = EApp (g h, es |> List.map g) }
  | EFun (bs, b) -> { x with e = EFun (bs, g b) }
  | EMatch (s, brs) -> { x with e = EMatch (g s, brs |> List.map (psub_branch sm)) }
  | EIf (c, a, b) -> { x with e = EIf (g c, g a, g b) }
  | ESeq (a, b) -> { x with e = ESeq (g a, g b) }
  | ECtor (n, es) -> { x with e = ECtor (n, es |> List.map g) }
  | ETuple es -> { x with e = ETuple (es |> List.map g) }
  | EOp (o, es) -> { x with e = EOp (o, es |> List.map g) }
  | ERaise e1 -> { x with e = ERaise (g e1) }
  | ERecord (n, fs) -> { x with e = ERecord (n, fs |> List.map (fun (f, e) -> (f, g e))) }
  | EProj (e1, n, f) -> { x with e = EProj (g e1, n, f) }
  | EDiscrim (e1, n) -> { x with e = EDiscrim (g e1, n) }
  | ECast (e1, c) -> { x with e = ECast (g e1, c) }
  | EWhile (a, b) -> { x with e = EWhile (g a, g b) }
  | ETry (a, brs) -> { x with e = ETry (g a, brs |> List.map (psub_branch sm)) }

and psub_branch (sm:subst) (br:branch) : ML branch =
  let p, guard, b = br in
  (p, (match guard with None -> None | Some e -> Some (psub sm e)), psub sm b)

(* A binding whose pattern cannot fail: one constructor, and no nested test. *)
let irrefutable (tbl:SMap.t ctor_info) (p:pat) : ML (option (name & list pat & ctor_info)) =
  match p with
  | PCtor (cn, ps) ->
    (match single_ctor tbl cn with
     | Some ci when List.length ps = List.length ci.ci_fields
                 && ps |> List.for_all (fun p -> PVar? p || PWild? p) -> Some (cn, ps, ci)
     | _ -> None)
  | _ -> None

let rec pat_ctors (p:pat) : ML (list string) =
  match p with
  | PCtor (n, ps) -> string_of_name n :: List.collect pat_ctors ps
  | PTuple ps | POr ps -> List.collect pat_ctors ps
  | _ -> []

(* The constructors the program matches on, ignoring the patterns [depat] is
   about to consume when [tbl] is given.  Run before [depat] it says which
   types will be free of [PCtor] afterwards, and hence which ones may become
   records; run after, with no [tbl], it confirms it. *)
let matched_ctors (tbl:option (SMap.t ctor_info)) (prog:program) : ML (SMap.t bool) =
  let m : SMap.t bool = SMap.create 50 in
  let mark (p:pat) : ML unit = pat_ctors p |> List.iter (fun n -> SMap.add m n true) in
  let consumed (p:pat) : ML bool =
    match tbl with
    | Some tbl -> Some? (irrefutable tbl p)
    | None -> false in
  let rec go (x:expr) : ML unit =
    let brs (bs:list branch) : ML unit =
      bs |> List.iter (fun (p, gd, b) ->
        mark p;
        (match gd with None -> () | Some g -> go g);
        go b) in
    match x.e with
    | EMatch (s, [(p, None, body)]) ->
      go s;
      if not (consumed p) then mark p;
      go body
    | EMatch (s, bs) -> go s; brs bs
    | ETry (s, bs) -> go s; brs bs
    | EConst _ | EVar _ | EQual _ | EAny | EAbort _ -> ()
    | ELet (_, _, a, b) | ESeq (a, b) | EWhile (a, b) -> go a; go b
    | EApp (h, es) -> go h; List.iter go es
    | EFun (_, b) -> go b
    | EIf (c, a, b) -> go c; go a; go b
    | ECtor (_, es) | ETuple es | EOp (_, es) -> List.iter go es
    | ERaise e1 -> go e1
    | ERecord (_, fs) -> fs |> List.iter (fun (_, e) -> go e)
    | EProj (e, _, _) | EDiscrim (e, _) | ECast (e, _) -> go e in
  prog |> List.iter (fun d ->
    match d with DLet dl -> go dl.dl_body | _ -> ());
  m

let rec depat (tbl:SMap.t ctor_info) (blocked:SMap.t bool) (x:expr) : ML expr =
  let g = depat tbl blocked in
  match x.e with
  | EMatch (s, [(p, None, body)]) ->
    let s = g s in
    let body = g body in
    (* Projecting is only sound if the type really does become a record: an
       [EProj] out of something still printed as a variant is not valid ML. *)
    let irr = (match irrefutable tbl p with
               | Some (cn, ps, ci) ->
                 if Some? (SMap.try_find blocked (string_of_name cn))
                 then None else Some (cn, ps, ci)
               | None -> None) in
    (match irr with
     | Some (cn, ps, ci) ->
       (* Re-reading the scrutinee for every field is what makes the match
          disappear entirely; when that is not free, one [let] stands in. *)
       let bound, s' =
         if dup_ok s then None, s
         else let v = rename "scrut" in
              Some v, { s with e = EVar v; eff = E_Pure } in
       let sm : subst = SMap.create 10 in
       List.iter2 (fun p (f, ft) ->
         match p with
         | PVar v -> SMap.add sm v (mk (EProj (s', cn, f)) ft E_Pure)
         | _ -> ()) ps ci.ci_fields;
       let body = psub sm body in
       (match bound with
        | None -> body
        | Some v -> { x with e = ELet (v, s.ty, s, body) })
     | None -> { x with e = EMatch (s, [(p, None, body)]) })

  (* The tag of a one-constructor value is known.  Nothing else in the pass
     depends on this, but leaving it in would force the type to stay a variant
     in the OCaml backend, which prints a discriminator as a match. *)
  | EDiscrim (e1, cn) ->
    let e1 = g e1 in
    (match single_ctor tbl cn with
     | Some _ when is_pure e1.eff -> { x with e = EConst (CBool true) }
     | _ -> { x with e = EDiscrim (e1, cn) })

  | EConst _ | EVar _ | EQual _ | EAny | EAbort _ -> x
  | ELet (v, ty, e1, e2) -> { x with e = ELet (v, ty, g e1, g e2) }
  | EApp (h, es) -> { x with e = EApp (g h, es |> List.map g) }
  | EFun (bs, b) -> { x with e = EFun (bs, g b) }
  | EMatch (s, brs) -> { x with e = EMatch (g s, brs |> List.map (depat_branch tbl blocked)) }
  | EIf (c, a, b) -> { x with e = EIf (g c, g a, g b) }
  | ESeq (a, b) -> { x with e = ESeq (g a, g b) }
  | ECtor (n, es) -> { x with e = ECtor (n, es |> List.map g) }
  | ETuple es -> { x with e = ETuple (es |> List.map g) }
  | EOp (o, es) -> { x with e = EOp (o, es |> List.map g) }
  | ERaise e1 -> { x with e = ERaise (g e1) }
  | ERecord (n, fs) -> { x with e = ERecord (n, fs |> List.map (fun (f, e) -> (f, g e))) }
  | EProj (e1, n, f) -> { x with e = EProj (g e1, n, f) }
  | ECast (e1, c) -> { x with e = ECast (g e1, c) }
  | EWhile (a, b) -> { x with e = EWhile (g a, g b) }
  | ETry (a, brs) -> { x with e = ETry (g a, brs |> List.map (depat_branch tbl blocked)) }

and depat_branch (tbl:SMap.t ctor_info) (blocked:SMap.t bool) (br:branch) : ML branch =
  let p, guard, b = br in
  (p, (match guard with None -> None | Some e -> Some (depat tbl blocked e)),
   depat tbl blocked b)

let depat_decls (prog:program) : ML program =
  let tbl = ctor_infos (with_imports prog) in
  let blocked = matched_ctors (Some tbl) prog in
  prog |> List.map (fun d ->
    match d with
    | DLet dl -> DLet { dl with dl_body = depat tbl blocked dl.dl_body }
    | d -> d)

(* Turn the qualifying single-constructor variants into records.  A [PCtor]
   left over anywhere disqualifies its type: there is no record pattern in the
   IR to rewrite it to. *)
let records (prog:program) : ML program =
  let matched = matched_ctors None prog in
  (* constructor name -> the record type it becomes *)
  let recs : SMap.t name = SMap.create 50 in
  prog |> List.iter (fun d ->
    match d with
    | DType ({ dt_name = tn; dt_body = TVariant [(cn, fs)] }) ->
      (* A constructor whose arguments F* did not name gets the positional
         names [_0], [_1], ...; those are perfectly good field names, and
         making the conversion unconditional means no [EProj] anywhere is
         left pointing at a variant. *)
      if Cons? fs
      && None? (SMap.try_find matched (string_of_name cn))
      then SMap.add recs (string_of_name cn) tn
    | _ -> ());
  (* An imported type's verdict is adopted, not re-derived.  This is the one
     decision in this file that really is a function of the whole program --
     the [matched] test above rejects a type any surviving pattern still
     matches on -- so the downstream program is the wrong program to ask.
     Note the asymmetry with the loop above: a type its home unit left as a
     variant must stay one here even if nothing in *this* program matches on
     it. *)
  !imported_types |> List.iter (fun (dt, _, is_record) ->
    match dt.dt_body with
    | TVariant [(cn, fs)] when is_record && Cons? fs ->
      (* A pattern this program still has for it cannot be rewritten: the IR
         has no record pattern.  [depat] removes the irrefutable single-branch
         ones, so what is left is a constructor nested inside another pattern.
         Reporting it beats miscompiling it; the fix is a record pattern in the
         IR, not a different verdict. *)
      if Some? (SMap.try_find matched (string_of_name cn)) then
        E.raise_error0 E.Error_CustardBadUnitInterface [
          text ("This program pattern-matches on " ^ string_of_name cn ^
                ", but the unit that compiled " ^ string_of_name dt.dt_name ^
                " gave it a record representation.");
          text "Custard's IR has no record pattern, so the match cannot be \
                translated. Bind the value and read its fields instead of \
                matching on it inside another pattern."
        ];
      SMap.add recs (string_of_name cn) dt.dt_name
    | _ -> ());
  if SMap.keys recs = [] then prog else begin
  let infos = ctor_infos (with_imports prog) in
  let as_record (cn:name) : ML (option name) = SMap.try_find recs (string_of_name cn) in
  let rec go (x:expr) : ML expr =
    match x.e with
    | ECtor (cn, es) ->
      let es = es |> List.map go in
      (match as_record cn with
       | Some tn ->
         (* the field names come from the declaration, which is unchanged here *)
         let fs = (match SMap.try_find infos (string_of_name cn) with
                   | Some ci -> ci.ci_fields |> List.map fst
                   | None -> []) in
         { x with e = ERecord (tn, List.zip fs es) }
       | None -> { x with e = ECtor (cn, es) })
    (* [Rename] keys a record's fields on the type name and a variant's on the
       constructor name, so the node has to be re-tagged along with the type. *)
    | EProj (e1, n, f) ->
      let e1 = go e1 in
      { x with e = EProj (e1, (match as_record n with Some tn -> tn | None -> n), f) }
    | EConst _ | EVar _ | EQual _ | EAny | EAbort _ -> x
    | ELet (v, ty, a, b) -> { x with e = ELet (v, ty, go a, go b) }
    | ESeq (a, b) -> { x with e = ESeq (go a, go b) }
    | EWhile (a, b) -> { x with e = EWhile (go a, go b) }
    | EApp (h, es) -> { x with e = EApp (go h, es |> List.map go) }
    | EFun (bs, b) -> { x with e = EFun (bs, go b) }
    | EIf (c, a, b) -> { x with e = EIf (go c, go a, go b) }
    | EMatch (s, brs) -> { x with e = EMatch (go s, brs |> List.map go_branch) }
    | ETry (s, brs) -> { x with e = ETry (go s, brs |> List.map go_branch) }
    | ETuple es -> { x with e = ETuple (es |> List.map go) }
    | EOp (o, es) -> { x with e = EOp (o, es |> List.map go) }
    | ERaise e1 -> { x with e = ERaise (go e1) }
    | ERecord (n, fs) -> { x with e = ERecord (n, fs |> List.map (fun (f, e) -> (f, go e))) }
    | EDiscrim (e1, n) -> { x with e = EDiscrim (go e1, n) }
    | ECast (e1, c) -> { x with e = ECast (go e1, c) }
  and go_branch (br:branch) : ML branch =
    let p, gd, b = br in
    (p, (match gd with None -> None | Some g -> Some (go g)), go b) in
  prog |> List.map (fun d ->
    match d with
    | DLet dl -> DLet { dl with dl_body = go dl.dl_body }
    | DType t ->
      (match t.dt_body with
       | TVariant [(cn, fs)] ->
         (match as_record cn with
          | Some _ -> DType { t with dt_body = TRecord fs }
          | None -> d)
       | _ -> d)
    | d -> d)
  end

(* -------------------------------------------------------------------- *)
(* Inline fields                                                        *)
(* -------------------------------------------------------------------- *)

(* [| Bar of a & b] is how F* source spells a two-argument constructor, but
   what it denotes is a constructor with *one* argument pointing at a pair, so
   every [Bar] costs an allocation and an indirection nobody asked for
   (FStarLang/FStar#4382).  An inline field says instead: keep the record's
   fields in the constructor itself.

   [Extract] marks such a field by wrapping its type in [TInline] -- tuples
   without being asked, anything else on [@@@custard_inline_field].  This pass
   is the only consumer, and it removes every marker it finds, whether or not
   it could act on it: no later pass and no backend knows the node exists. *)

noeq
type expansion = {
  ex_ty:    cty;                  (* the field's declared type, [TApp (R, _)] *)
  ex_type:  name;                 (* R *)
  ex_ctor:  option name;          (* R's constructor, when R is a variant *)
  ex_src:   list (string & cty);  (* R's fields, instantiated *)
  ex_dst:   list (string & cty);  (* what they become in the outer constructor *)
}

(* [ECtor]/[ERecord] and [EProj] are keyed on the constructor name for a
   variant and on the type name for a record; [Rename] relies on that, so the
   nodes this pass builds have to agree. *)
let ex_key (ex:expansion) : name =
  match ex.ex_ctor with Some c -> c | None -> ex.ex_type

(* A plan for one constructor, in field order: each field's name before and
   after, and what it expands to.  A field can be renamed without expanding,
   because expanding its neighbour shifts the positional names along. *)
type fplan = list (string & string & option expansion)

let pure_ (e:expr') (t:cty) : expr = mk e t E_Pure

(* Put one of R's values together out of its fields. *)
let ex_build (ex:expansion) (vs:list expr) : ML expr =
  match ex.ex_ctor with
  | Some c -> pure_ (ECtor (c, vs)) ex.ex_ty
  | None -> pure_ (ERecord (ex.ex_type, List.zip (ex.ex_src |> List.map fst) vs)) ex.ex_ty

(* The fields [e] holds, when it is a value of R that is right there. *)
let ex_take (ex:expansion) (e:expr) : ML (option (list expr)) =
  match e.e with
  | ECtor (c, vs) ->
    if (match ex.ex_ctor with
        | Some rc -> string_of_name c = string_of_name rc
        | None -> false)
       && List.length vs = List.length ex.ex_src
    then Some vs else None
  | ERecord (tn, fs) ->
    if string_of_name tn = string_of_name ex.ex_type
    then Some (ex.ex_src |> List.map (fun (g, gt) ->
                 match fs |> List.tryFind (fun (h, _) -> h = g) with
                 | Some (_, v) -> v
                 | None -> mk EAny gt E_Pure))
    else None
  | _ -> None

(* [_0], [_1], ... are the names a constructor's unnamed arguments get.  A
   constructor made only of those keeps them, renumbered, rather than growing
   [_0__1]-shaped ones. *)
let positional (f:string) : ML bool =
  String.strlen f > 1 && String.substring f 0 1 = "_"

let strip_inline (c:cty) : cty =
  match c with TInline c -> c | c -> c

(* R's declaration, when R is a type this pass can take the fields out of:
   exactly one constructor (or a record), and at least one field. *)
let record_body (prog:program) (n:name)
  : ML (option (list string & option name & list (string & cty))) =
  match prog |> List.tryFind (fun d -> string_of_name (name_of_decl d) = string_of_name n) with
  | Some (DType t) ->
    (match t.dt_body with
     | TRecord fs -> if Cons? fs then Some (t.dt_params, None, fs) else None
     | TVariant [(cn, fs)] -> if Cons? fs then Some (t.dt_params, Some cn, fs) else None
     | _ -> None)
  | _ -> None

(* The plan for every constructor with at least one marked field.  A field
   whose type turns out not to be a record keeps its place; only the marker
   goes. *)
let plan_of (prog:program) : ML (SMap.t fplan) =
  let m : SMap.t fplan = SMap.create 20 in
  prog |> List.iter (fun d ->
    match d with
    | DType ({ dt_body = TVariant cs }) ->
      cs |> List.iter (fun (cn, fs) ->
        if fs |> List.existsb (fun (_, c) -> TInline? c) then begin
          let allpos = fs |> List.for_all (fun (f, _) -> positional f) in
          let next : SMap.t int = SMap.create 1 in
          let fresh (f:string) (g:string) : ML string =
            if allpos
            then begin
              let i = (match SMap.try_find next "n" with Some i -> i | None -> 0) in
              SMap.add next "n" (i + 1);
              "_" ^ string_of_int i
            end
            else if g = "" then f else f ^ "_" ^ g in
          let plan = fs |> List.map (fun (f, c) ->
            match c with
            | TInline (TApp (rn, args)) ->
              (match record_body (with_imports prog) rn with
               | Some (ps, rc, rfs) ->
                 if List.length ps <> List.length args then (f, fresh f "", None)
                 else begin
                   let sm = List.zip ps args in
                   let src = rfs |> List.map (fun (g, gt) -> (g, subst_cty sm gt)) in
                   let dst = src |> List.map (fun (g, gt) -> (fresh f g, gt)) in
                   (f, f, Some { ex_ty = TApp (rn, args); ex_type = rn; ex_ctor = rc;
                                 ex_src = src; ex_dst = dst })
                 end
               | None -> (f, fresh f "", None))
            | _ -> (f, fresh f "", None)) in
          SMap.add m (string_of_name cn) plan
        end)
    | _ -> ());
  m

(* Only [PVar], [PWild] and R's own constructor can be flattened into the outer
   pattern; anything else at that position takes the field out of the plan,
   everywhere, before a single node is rewritten. *)
let blocked_fields (m:SMap.t fplan) (prog:program) : ML (SMap.t bool) =
  let bad : SMap.t bool = SMap.create 20 in
  let key (cn:name) (f:string) : ML string = string_of_name cn ^ "#" ^ f in
  let rec scan_pat (p:pat) : ML unit =
    (match p with
     | PCtor (cn, ps) ->
       (match SMap.try_find m (string_of_name cn) with
        | Some fs ->
          if List.length ps <> List.length fs
          then fs |> List.iter (fun (f, _, _) -> SMap.add bad (key cn f) true)
          else List.iter2 (fun (p:pat) (f, _, ex) ->
                 match ex with
                 | None -> ()
                 | Some ex ->
                   let ok = (match p with
                             | PVar _ -> true
                             | PWild -> true
                             | PCtor (c, qs) ->
                               (match ex.ex_ctor with
                                | Some rc -> string_of_name c = string_of_name rc
                                           && List.length qs = List.length ex.ex_src
                                | None -> false)
                             | _ -> false) in
                   if not ok then SMap.add bad (key cn f) true) ps fs
        | None -> ())
     | _ -> ());
    (match p with
     | PCtor (_, ps) -> List.iter scan_pat ps
     | PTuple ps -> List.iter scan_pat ps
     | POr ps -> List.iter scan_pat ps
     | _ -> ()) in
  let rec go (x:expr) : ML unit =
    let brs (bs:list branch) : ML unit =
      bs |> List.iter (fun (p, gd, b) ->
        scan_pat p; (match gd with None -> () | Some g -> go g); go b) in
    match x.e with
    | EMatch (s, bs) -> go s; brs bs
    | ETry (s, bs) -> go s; brs bs
    | EConst _ | EVar _ | EQual _ | EAny | EAbort _ -> ()
    | ELet (_, _, a, b) | ESeq (a, b) | EWhile (a, b) -> go a; go b
    | EApp (h, es) -> go h; List.iter go es
    | EFun (_, b) -> go b
    | EIf (c, a, b) -> go c; go a; go b
    | ECtor (_, es) | ETuple es | EOp (_, es) -> List.iter go es
    | ERaise e1 -> go e1
    | ERecord (_, fs) -> fs |> List.iter (fun (_, e) -> go e)
    | EProj (e, _, _) | EDiscrim (e, _) | ECast (e, _) -> go e in
  prog |> List.iter (fun d -> match d with DLet dl -> go dl.dl_body | _ -> ());
  bad

(* An [EProj] out of a value that is right there.  The rewrites below leave one
   behind wherever a field had to be put back together, and this is what makes
   the reconstruction cost nothing in the case that matters -- a projection out
   of a field that was itself projected out. *)
let rec unbuild (infos:SMap.t ctor_info) (x:expr) : ML expr =
  let g = unbuild infos in
  let pick (fs:list (string & expr)) (f:string) : ML (option expr) =
    if fs |> List.for_all (fun (h, (e:expr)) -> h = f || is_pure e.eff)
    then (match fs |> List.tryFind (fun (h, _) -> h = f) with
          | Some (_, e) -> Some e
          | None -> None)
    else None in
  match x.e with
  | EProj (e1, n, f) ->
    let e1 = g e1 in
    let alt = { x with e = EProj (e1, n, f) } in
    (match e1.e with
     | ERecord (_, fs) -> (match pick fs f with Some e -> e | None -> alt)
     | ECtor (cn, es) ->
       (match SMap.try_find infos (string_of_name cn) with
        | Some ci ->
          if List.length es <> List.length ci.ci_fields then alt
          else (match pick (List.zip (ci.ci_fields |> List.map fst) es) f with
                | Some e -> e
                | None -> alt)
        | None -> alt)
     | _ -> alt)
  | EConst _ | EVar _ | EQual _ | EAny | EAbort _ -> x
  | ELet (v, ty, a, b) -> { x with e = ELet (v, ty, g a, g b) }
  | ESeq (a, b) -> { x with e = ESeq (g a, g b) }
  | EWhile (a, b) -> { x with e = EWhile (g a, g b) }
  | EApp (h, es) -> { x with e = EApp (g h, es |> List.map g) }
  | EFun (bs, b) -> { x with e = EFun (bs, g b) }
  | EIf (c, a, b) -> { x with e = EIf (g c, g a, g b) }
  | EMatch (s, brs) -> { x with e = EMatch (g s, brs |> List.map (unbuild_branch infos)) }
  | ETry (s, brs) -> { x with e = ETry (g s, brs |> List.map (unbuild_branch infos)) }
  | ECtor (n, es) -> { x with e = ECtor (n, es |> List.map g) }
  | ETuple es -> { x with e = ETuple (es |> List.map g) }
  | EOp (o, es) -> { x with e = EOp (o, es |> List.map g) }
  | ERaise e1 -> { x with e = ERaise (g e1) }
  | ERecord (n, fs) -> { x with e = ERecord (n, fs |> List.map (fun (f, e) -> (f, g e))) }
  | EDiscrim (e1, n) -> { x with e = EDiscrim (g e1, n) }
  | ECast (e1, c) -> { x with e = ECast (g e1, c) }

and unbuild_branch (infos:SMap.t ctor_info) (br:branch) : ML branch =
  let p, gd, b = br in
  (p, (match gd with None -> None | Some e -> Some (unbuild infos e)), unbuild infos b)

(* Is every occurrence of [v] the target of a projection?  Then a record built
   out of pieces can be substituted for it however many times it is used:
   [unbuild] takes every copy apart again and none of them is ever built. *)
let rec only_projected (v:string) (x:expr) : ML bool =
  let g = only_projected v in
  match x.e with
  | EVar w -> w <> v
  | EProj (e1, _, _) -> (match e1.e with EVar w -> w = v || g e1 | _ -> g e1)
  | EConst _ | EQual _ | EAny | EAbort _ -> true
  | ELet (_, _, a, b) | ESeq (a, b) | EWhile (a, b) -> g a && g b
  | EApp (h, es) -> g h && es |> List.for_all g
  | EFun (_, b) -> g b
  | EIf (c, a, b) -> g c && g a && g b
  | EMatch (s, brs) | ETry (s, brs) ->
    g s && brs |> List.for_all (fun (_, gd, b) ->
      (match gd with None -> true | Some e -> g e) && g b)
  | ECtor (_, es) | ETuple es | EOp (_, es) -> es |> List.for_all g
  | ERaise e1 -> g e1
  | ERecord (_, fs) -> fs |> List.for_all (fun (_, e) -> g e)
  | EDiscrim (e1, _) | ECast (e1, _) -> g e1

(* The names an imported constructor ended up with in the unit that emitted it.
   This is the pinned answer: whatever plan is re-derived here has to agree
   with it, field by field. *)
let imported_ctor_fields (cn:string) : ML (option (list string)) =
  !imported_types |> List.tryPick (fun (pre, fin, _) ->
    let mine =
      match pre.dt_body with
      | TVariant cs -> cs |> List.existsb (fun (c, _) -> string_of_name c = cn)
      | _ -> false in
    if not mine then None else
    match fin.dt_body with
    | TVariant cs ->
      cs |> List.tryPick (fun (c, fs) ->
        if string_of_name c = cn then Some (fs |> List.map fst) else None)
    (* [records] turned the constructor into the type itself. *)
    | TRecord fs -> Some (fs |> List.map fst)
    | _ -> None)

let inline_fields (prog:program) : ML program =
  (* Imported types are visible so that a constructor this program *applies*
     gets the same plan the unit that declared it used.  They are not rewritten
     -- they are not in [prog] -- and their plans are pinned below rather than
     trusted. *)
  let m0 = plan_of (with_imports prog) in
  if SMap.keys m0 = [] then prog else begin
  (* Drop the expansions the patterns will not take.  Renaming stays: it was
     decided per constructor and the declaration follows it either way. *)
  let bad = blocked_fields m0 prog in
  (* An imported constructor's plan is settled by its home unit.  Re-deriving
     it here can disagree in either direction -- this program may have a
     pattern that blocked nothing there, or lack one that blocked something --
     so the fields it actually has are what decides, and a local pattern that
     cannot follow is an error rather than a reason to change the layout. *)
  SMap.keys m0 |> List.iter (fun k ->
    match SMap.try_find m0 k, imported_ctor_fields k with
    | Some fs, Some finals ->
      let pinned = fs |> List.map (fun (f, f', ex) ->
        match ex with
        | None -> (f, f', None)
        | Some e ->
          if e.ex_dst |> List.for_all (fun (g, _) -> List.mem g finals)
          then begin
            if Some? (SMap.try_find bad (k ^ "#" ^ f)) then
              E.raise_error0 E.Error_CustardBadUnitInterface [
                text ("This program matches on " ^ k ^ " in a way that its \
                      field " ^ f ^ " cannot follow, but the unit that \
                      compiled it expanded that field into the constructor.");
                text "Bind the field and read it, rather than matching through it."
              ];
            (f, f', Some e)
          end
          else (f, f', None)) in
      SMap.add m0 k pinned
    | _ -> ());
  let m : SMap.t fplan = SMap.create 20 in
  SMap.keys m0 |> List.iter (fun k ->
    match SMap.try_find m0 k with
    | None -> ()
    | Some fs ->
      (* Already settled above, and not by this program's patterns. *)
      if Some? (imported_ctor_fields k) then SMap.add m k fs else
      SMap.add m k (fs |> List.map (fun (f, f', ex) ->
        match ex with
        | Some _ ->
          if None? (SMap.try_find bad (k ^ "#" ^ f)) then (f, f', ex) else (f, f', None)
        | None -> (f, f', None))));
  let plan (cn:name) : ML (option fplan) = SMap.try_find m (string_of_name cn) in

  let rec go (x:expr) : ML expr =
    match x.e with
    | ECtor (cn, es) ->
      let es = es |> List.map go in
      let alt = { x with e = ECtor (cn, es) } in
      (match plan cn with
       | Some fs ->
         if List.length es <> List.length fs then alt
         else begin
           (* Splicing the pieces straight in is the whole point; anything
              else has to read them back out, which is correct but buys
              nothing. *)
           let binds, args =
             List.fold_left2 (fun (binds, acc) (e:expr) (_, _, ex) ->
               match ex with
               | None -> (binds, acc @ [e])
               | Some ex ->
                 (match ex_take ex e with
                  | Some vs -> (binds, acc @ vs)
                  | None ->
                    let binds, v =
                      if dup_ok e then binds, e
                      else let n = rename "fld" in
                           binds @ [(n, e.ty, e)], mk (EVar n) e.ty E_Pure in
                    (binds, acc @ (ex.ex_src |> List.map (fun (g, gt) ->
                       pure_ (EProj (v, ex_key ex, g)) gt)))))
               ([], []) es fs in
           let body = { x with e = ECtor (cn, args) } in
           List.fold_right (fun (n, t, e) acc -> { acc with e = ELet (n, t, e, acc) })
                           binds body
         end
       | None -> alt)

    (* Reading a field that is no longer there has to put it back together;
       [unbuild] takes it apart again wherever only a field of it was
       wanted, which is every chained projection. *)
    | EProj (e1, cn, f) ->
      let e1 = go e1 in
      let alt = { x with e = EProj (e1, cn, f) } in
      (match plan cn with
       | Some fs ->
         (match fs |> List.tryFind (fun (g, _, _) -> g = f) with
          | Some (_, f', None) -> { x with e = EProj (e1, cn, f') }
          | Some (_, _, Some ex) ->
            let bind, v =
              if dup_ok e1 then None, e1
              else let n = rename "whole" in Some n, mk (EVar n) e1.ty E_Pure in
            let vs = ex.ex_dst |> List.map (fun (g, gt) -> pure_ (EProj (v, cn, g)) gt) in
            let b = ex_build ex vs in
            (match bind with
             | None -> b
             | Some n -> { b with e = ELet (n, e1.ty, e1, b) })
          | None -> alt)
       | None -> alt)

    | EConst _ | EVar _ | EQual _ | EAny | EAbort _ -> x
    | ELet (v, ty, a, b) -> { x with e = ELet (v, ty, go a, go b) }
    | ESeq (a, b) -> { x with e = ESeq (go a, go b) }
    | EWhile (a, b) -> { x with e = EWhile (go a, go b) }
    | EApp (h, es) -> { x with e = EApp (go h, es |> List.map go) }
    | EFun (bs, b) -> { x with e = EFun (bs, go b) }
    | EIf (c, a, b) -> { x with e = EIf (go c, go a, go b) }
    | EMatch (s, brs) -> { x with e = EMatch (go s, brs |> List.map go_branch) }
    | ETry (s, brs) -> { x with e = ETry (go s, brs |> List.map go_branch) }
    | ETuple es -> { x with e = ETuple (es |> List.map go) }
    | EOp (o, es) -> { x with e = EOp (o, es |> List.map go) }
    | ERaise e1 -> { x with e = ERaise (go e1) }
    | ERecord (n, fs) -> { x with e = ERecord (n, fs |> List.map (fun (f, e) -> (f, go e))) }
    | EDiscrim (e1, n) -> { x with e = EDiscrim (go e1, n) }
    | ECast (e1, c) -> { x with e = ECast (go e1, c) }

  (* A branch is rewritten pattern first.  A nested constructor pattern is the
     case that pays: it flattens.  A [PVar] standing for the whole field
     becomes one variable per piece, and the body gets the field back as a
     value -- substituted when it is read at most once, so that [unbuild] can
     take it apart again, and behind a [let] otherwise, so that no allocation
     is duplicated. *)
  and go_branch (br:branch) : ML branch =
    let plain () : ML branch =
      let p, gd, b = br in
      (p, (match gd with None -> None | Some g -> Some (go g)), go b) in
    let p, gd, b = br in
    match p with
    | PCtor (cn, ps) ->
      (match plan cn with
       | Some fs ->
         if List.length ps <> List.length fs then plain ()
         else begin
           let sm : subst = SMap.create 10 in
           let lets, ps =
             List.fold_left2 (fun (lets, acc) (p:pat) (_, _, ex) ->
               match ex with
               | None -> (lets, acc @ [p])
               | Some ex ->
                 (match p with
                  | PCtor (_, qs) -> (lets, acc @ qs)
                  | PWild -> (lets, acc @ (ex.ex_dst |> List.map (fun _ -> PWild)))
                  | PVar v ->
                    let ns = ex.ex_src |> List.map (fun (g, gt) -> (rename g, gt)) in
                    let e = ex_build ex (ns |> List.map (fun (n, t) -> mk (EVar n) t E_Pure)) in
                    let uses = count v b + (match gd with None -> 0 | Some g -> count v g) in
                    let free = uses <= 1
                            || (only_projected v b
                                && (match gd with None -> true | Some g -> only_projected v g)) in
                    let lets = if free
                               then (SMap.add sm v e; lets)
                               else lets @ [(v, ex.ex_ty, e)] in
                    (lets, acc @ (ns |> List.map (fun (n, _) -> PVar n)))
                  | _ -> (lets, acc @ [p])))
               ([], []) ps fs in
           (* A guard cannot be wrapped in a [let], so it always substitutes. *)
           let gsm : subst = SMap.create 10 in
           SMap.keys sm |> List.iter (fun k ->
             match SMap.try_find sm k with Some e -> SMap.add gsm k e | None -> ());
           lets |> List.iter (fun (v, t, e) -> SMap.add gsm v e);
           let gd = (match gd with None -> None | Some g -> Some (go (psub gsm g))) in
           let b = go (psub sm b) in
           let b = List.fold_right (fun (v, t, e) acc -> { acc with e = ELet (v, t, e, acc) })
                                   lets b in
           (PCtor (cn, ps), gd, b)
         end
       | None -> plain ())
    | _ -> plain () in

  let prog = prog |> List.map (fun d ->
    match d with
    | DLet dl -> DLet { dl with dl_body = go dl.dl_body }
    | DType t ->
      (match t.dt_body with
       | TVariant cs ->
         DType { t with dt_body = TVariant (cs |> List.map (fun (cn, fs) ->
           match SMap.try_find m (string_of_name cn) with
           | Some pl ->
             if List.length pl <> List.length fs
             then (cn, fs |> List.map (fun (f, c) -> (f, strip_inline c)))
             else (cn, List.zip fs pl |> List.collect (fun ((_, c), (_, f', ex)) ->
                         match ex with
                         | Some ex -> ex.ex_dst
                         | None -> [(f', strip_inline c)]))
           | None -> (cn, fs |> List.map (fun (f, c) -> (f, strip_inline c))))) }
       | TRecord fs -> DType { t with dt_body = TRecord (fs |> List.map (fun (f, c) -> (f, strip_inline c))) }
       | _ -> d)
    | d -> d) in
  let infos = ctor_infos (with_imports prog) in
  prog |> List.map (fun d ->
    match d with
    | DLet dl -> DLet { dl with dl_body = unbuild infos dl.dl_body }
    | d -> d)
  end

let run (imports:list (dtype & dtype & bool)) (prog:program) : ML program =
  imported_types := imports;
  let prog = eta_reduce_decls prog in
  let prog = inline_decls prog in
  let prog = reduce_decls prog in
  (* Before [depat]: dropping a branch can leave a match with a single
     irrefutable one, which is exactly what [depat] removes entirely. *)
  let prog = prune_decls prog in
  let prog = depat_decls prog in
  (* After [depat]: a field of the record being inlined is read with an
     [EProj] only once [depat] has run, and that is what tells the pass a
     reconstructed value will never actually be built. *)
  let prog = inline_fields prog in
  let prog = prog |> List.map (fun d ->
    match d with
    | DLet dl -> DLet { dl with dl_body = simpl dl.dl_body }
    | d -> d) in
  records (scc (dce (unused_params (dce prog))))
