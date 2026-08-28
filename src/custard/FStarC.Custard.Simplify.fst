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
module Format = FStarC.Format
module Prof   = FStarC.Custard.Prof
module Options = FStarC.Options

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
  | EProj (e1, _, _) | EDiscrim (e1, _) | ECast (e1, _)
  | ECoerce (e1, _) -> occurs v e1
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
        | ECoerce (e, c)   -> { x with e = ECoerce (operand e, c) }
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

(* Let-floating.  ANF hoists every impure operand into a binding of its own,
   and an operand that was itself an application arrives already carrying the
   bindings *its* operands needed, so the definiens of a binding is very often
   another binding: [let x = (let y = (let z = ... in ...) in ...) in ...],
   nested as deep as the original expression was.  That is the same program as
   [let z = ... in let y = ... in let x = ... in ...] -- the bindings run in
   that order either way -- and the flat spelling is the one a reader can
   follow, which is why the C backend has always emitted it.

   [k] receives the definiens with its leading bindings stripped and builds
   whatever the caller was going to build; the spine is rebuilt around the
   result.  Every rebuilt node reuses [x], so it carries the type of the whole
   original expression (which is what each of these nodes now returns) and its
   effect (an over-approximation for the inner ones, in the safe direction).

   This relies on variable names being unique within a definition, which they
   are (see {!sub}): floating [y] outward extends its scope over the outer
   body, and a *different* [y] there would be captured. *)
let rec float_lets (x:expr) (e1:expr) (k : expr -> ML expr) : ML expr =
  match e1.e with
  | ELet (w, t, a, b) -> { x with e = ELet (w, t, a, float_lets x b k) }
  | ESeq (a, b) -> { x with e = ESeq (a, float_lets x b k) }
  | _ -> k e1

let rec simpl (x:expr) : ML expr =
  match x.e with
  | ELet (v, ty, e1, e2) ->
    let e1 = simpl e1 in
    let e2 = simpl e2 in
    float_lets x e1 (fun e1 ->
    (* [let x = e in x] is just [e], whatever [e]'s effect: nothing moves. *)
    if (match e2.e with EVar w -> w = v | _ -> false) then e1
    else if occurs v e2 then { x with e = ELet (v, ty, e1, e2) }
    (* Section 7.3: an unused binding may only be deleted if evaluating it is
       unobservable; otherwise it becomes a statement, which keeps its effect
       and its position. *)
    else if is_pure e1.eff then e2
    else { x with e = ESeq (e1, e2) })

  | ESeq (e1, e2) ->
    let e1 = simpl e1 in
    let e2 = simpl e2 in
    float_lets x e1 (fun e1 ->
      if is_pure e1.eff then e2 else { x with e = ESeq (e1, e2) })

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
  | ECoerce (e1, c) -> { x with e = ECoerce (simpl e1, c) }
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
  | ECoerce (e1, c) -> { x with e = ECoerce (g e1, c) }
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
  | PRecord (n, fs) -> PRecord (n, fs |> List.map (fun (f, q) -> (f, sub_pat sm q)))
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
    | EProj (e1, _, _) | EDiscrim (e1, _) | ECast (e1, _)
    | ECoerce (e1, _) -> count v e1
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
  | PRecord (_, fs), ERecord (_, es) ->
    (* A record pattern need not mention every field, and the fields need not
       be in declaration order, so this pairs them up by name rather than by
       position.  A field the value does not have means "cannot tell". *)
    fs |> List.fold_left (fun acc (f, q) ->
      match acc, es |> List.tryFind (fun (g, _) -> g = f) with
      | Some bs, Some (_, e1) ->
        (match match_pat q e1 with Some bs' -> Some (bs @ bs') | None -> None)
      | _ -> None) (Some [])
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
(* Does every occurrence of [v] in [x] sit in the head position of an
   application?  ([v] not occurring at all counts.) *)
let rec called_only (v:string) (x:expr) : ML bool =
  if not (occurs v x) then true
  else match x.e with
  | EVar _ -> false
  | EConst _ | EQual _ | EAny | EAbort _ -> true
  | EApp (h, es) ->
    (match h.e with
     | EVar w -> w = v && called_only_list v es
     | _ -> called_only v h && called_only_list v es)
  | ELet (_, _, e1, e2) -> called_only v e1 && called_only v e2
  | EFun (_, b) -> called_only v b
  | EMatch (s, brs) -> called_only v s && called_only_branches v brs
  | EIf (c, a, b) -> called_only v c && called_only v a && called_only v b
  | ESeq (a, b) | EWhile (a, b) -> called_only v a && called_only v b
  | ECtor (_, es) | ETuple es | EOp (_, es) -> called_only_list v es
  | ERaise e1 -> called_only v e1
  | ERecord (_, fs) -> called_only_list v (fs |> List.map snd)
  | EProj (e1, _, _) | EDiscrim (e1, _) | ECast (e1, _)
  | ECoerce (e1, _) -> called_only v e1
  | ETry (a, brs) -> called_only v a && called_only_branches v brs

and called_only_list (v:string) (es:list expr) : ML bool =
  es |> List.for_all (called_only v)

and called_only_branches (v:string) (brs:list branch) : ML bool =
  brs |> List.for_all (fun (_, g, b) ->
    (match g with None -> true | Some g -> called_only v g) && called_only v b)

(* A *forwarder* is a pure, non-recursive definition whose body is exactly one
   of its own binders -- [let id_fn phi = phi], and, in EverParse's CDDL
   library, [CDDL.Spec.EqTest.mk_eq_test], which lowers to [return phi;].
   Applied to all its arguments it is the identity on one of them, so a
   saturated call reduces to that argument.

   Doing this is what turns [let wrapped = id_fn band] into [let wrapped =
   band], which the [EQual] case of [eta_expand_decl] then expands into a real
   function.  Without it the definition stays a *variable* of function-pointer
   type, initialized in [custard_init_globals] -- and section 27 is what that
   costs: a pure, total, compile-time-constant function becomes runtime state,
   and the public entry point calling it segfaults on a null pointer if the
   initializer has not run.

   Unlike widening [cheap_expr], this cannot duplicate work: it *removes* a
   call rather than moving one into every call site.  That distinction is the
   whole reason to prefer it -- [cheap_expr] admits [EApp] of arbitrary named
   functions, so relaxing the arity bound in [eta_expand_decl] would let
   [let table : int -> int = build_table 1000000] be re-evaluated per call. *)
let forwarders : ref (SMap.t (int & int)) = mk_ref (SMap.create 0)

let forwarder_table (prog:program) : ML (SMap.t (int & int)) =
  let t : SMap.t (int & int) = SMap.create 50 in
  prog |> List.iter (fun d ->
    match d with
    | DLet l when Cons? l.dl_binders && is_pure l.dl_eff
               && not (l.dl_flags |> List.existsb Rec?) ->
      (match l.dl_body.e with
       | EVar v ->
         let n = List.length l.dl_binders in
         let found =
           l.dl_binders |> List.fold_left (fun (acc, k) (b:binder) ->
             ((if b.b_name = v && acc < 0 then k else acc), k + 1)) (-1, 0) in
         let found = fst found in
         if found >= 0 then SMap.add t (string_of_name l.dl_name) (n, found)
       | _ -> ())
    | _ -> ());
  t

let rec reduce (x:expr) : ML expr =
  match x.e with
  | EApp (h, args) ->
    let h = reduce h in
    let args = args |> List.map reduce in
    (match h.e with
     | EFun (bs, body) when List.length bs <= List.length args ->
       reduce (beta bs body args { x with e = EApp (h, args) })
     (* Every argument must be pure, because the ones not returned are
        dropped.  ANF has already made each operand pure, so this holds in
        practice and costs nothing to check. *)
     | EQual (n, _) when (match SMap.try_find !forwarders (string_of_name n) with
                          | Some (a, _) -> a = List.length args
                                        && args |> List.for_all (fun (e:expr) -> is_pure e.eff)
                          | None -> false) ->
       let _, i = Some?.v (SMap.try_find !forwarders (string_of_name n)) in
       let arg = List.nth args i in
       (* The call site's type, not the argument's: they denote the same type
          but the caller's is the one the surrounding code was built against,
          and an abbreviation is the better name for it. *)
       { arg with ty = x.ty }
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
  (* Section 3.1: the backends have no closures, so a let-bound lambda that is
     only ever *called* has to reach its call, where beta can fire.  A lambda
     is a value, so moving it duplicates no work, and a single occurrence
     duplicates no code.  Pulse's [with_invariants] produces exactly this
     shape: a thunk bound to a name and applied to [()] two lines later, twice
     over.

     Restricted to occurrences in head position, and to the direct-to-C
     backend.  A lambda that is *passed* rather than called is a closure
     however it is bound, so moving it buys nothing; and beta gives the result
     the type of the application node it replaces, which is not always as
     precise as the body's own -- on the OCaml path that turned a [ref] into
     [any], and an [any] prints as an array rather than as a [ref].  C has no
     closures at all, so there the inlining is not an optimization but the
     only way the program compiles. *)
  | ELet (v, ty, e1, e2) ->
    let e1 = reduce e1 in
    if Options.custard_backend () = "C"
       && EFun? e1.e && count v e2 <= 1 && called_only v e2 then
      let sm : subst = SMap.create 5 in
      SMap.add sm v e1;
      reduce (sub sm e2)
    else { x with e = ELet (v, ty, e1, reduce e2) }
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
  | ECoerce (e1, c) -> { x with e = ECoerce (reduce e1, c) }
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
  | ECoerce (e1, c) -> { x with e = ECoerce (g e1, c) }
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

(* -------------------------------------------------------------------- *)
(* Eta expansion                                                        *)
(* -------------------------------------------------------------------- *)

(* The opposite direction, and for the opposite reason.  A definition whose
   result type is still an arrow is a partial application, which OCaml is happy
   with and C is not: karamel reports "cannot enforce arity at call-site" and
   emits a call through a function pointer that no longer type-checks.  Three
   shapes in the dice example are exactly this -- [let hacl_hash = hacl_hash0],
   a Pulse [fn] whose last argument [eta_reduce] had just removed, and a
   wrapper that forwards a field.

   Only a *cheap* body may be expanded, because expansion re-evaluates it on
   every call.  An under-applied call allocates a closure and runs nothing, so
   it qualifies; anything that computes before returning a function does not,
   which is the hazard section 13.5 records for specialization.  Effects are
   excluded for the same reason, and that is also what keeps a top-level
   stateful value from being turned into a function. *)
let rec cheap_expr (x:expr) : ML bool =
  is_pure x.eff &&
  (match x.e with
   | EConst _ | EVar _ | EQual _ -> true
   | EApp (f, args) -> cheap_expr f && List.for_all cheap_expr args
   | ECast (e, _) | ECoerce (e, _) | EProj (e, _, _) -> cheap_expr e
   | _ -> false)

let rec arrow_arity (c:cty) : ML int =
  match c with
  | TArrow (_, _, b) -> 1 + arrow_arity b
  | _ -> 0

(* How many arguments the callee still wants.  Bounding the expansion by this
   rather than by the result type is what makes the pass safe: a definition
   whose declared result type carries more arrows than its body has room for
   -- which [eta_reduce] and the abbreviation peeling of section 7.3 can both
   produce -- would otherwise be expanded into an over-application.

   How many arguments the emitted object accepts.  For a definition with
   binders that is its binder count; for a *parameterless* one of arrow type
   it is the arity of that type, because such a definition is lowered to a
   variable of function-pointer type and a call through it supplies every
   argument at once.  Getting the second case wrong is what let section 26's
   [let e : bool -> bool -> bool = ap band] escape: read as arity 0, its
   callers were owed nothing and stayed eta-short. *)
let decl_arity (prog:program) : ML (SMap.t int) =
  let tbl : SMap.t int = SMap.create 100 in
  prog |> List.iter (fun d ->
    match d with
    | DLet l ->
      SMap.add tbl (string_of_name l.dl_name)
        (if Cons? l.dl_binders then List.length l.dl_binders
         else arrow_arity l.dl_ret)
    | DExternal x -> SMap.add tbl (string_of_name x.dx_name) (arrow_arity x.dx_ty)
    | _ -> ());
  tbl

(* The fewest arguments any use of a name supplies.  Expansion raises a
   definition's arity, but it rewrites only the definition; every call site is
   left as it was.  That is fine when the callers were already asking for more
   than the definition accepted -- which is the whole point of section 25 --
   and a miscompilation when they were not.

   Section 30's [mk_arg (x: u8) : fixedb], where the one-field [fixedb]
   collapses to [u8 -> usize], is the second case: the definition returns a
   function pointer, which C is perfectly happy to do, and [fixedb]'s arrow
   made the pass read it as owing a second argument.  Expanded to arity two,
   its callers -- correct at arity one, and with nothing left to expand -- were
   rejected as partial applications.

   Only a use this pass cannot itself grow may pin a name.  The head call of
   an expandable definition's body is exactly the one that can: [go] appends
   to it, which is how the chain of section 25 resolves, so
   [let call_g_partial a : bool -> bool = g a] must not be read as pinning [g]
   to one argument -- it is about to be given its second.  Every other use --
   under a [let], in an argument, as a bare address -- is final, and that is
   the only kind [mk_arg] has. *)
let rec expr_uses (acc : SMap.t int) (x:expr) : ML unit =
  let note (n:name) (k:int) : ML unit =
    let s = string_of_name n in
    match SMap.try_find acc s with
    | Some m when m <= k -> ()
    | _ -> SMap.add acc s k in
  let sub (es:list expr) : ML unit = List.iter (expr_uses acc) es in
  match x.e with
  | EApp ({ e = EQual (n, _) }, es) -> note n (List.length es); sub es
  | EQual (n, _) -> note n 0
  | EConst _ | EVar _ | EAny | EAbort _ -> ()
  | ERaise e1 | EDiscrim (e1, _) | EProj (e1, _, _)
  | ECast (e1, _) | ECoerce (e1, _) -> expr_uses acc e1
  | ECtor (_, es) | ETuple es | EOp (_, es) -> sub es
  | ERecord (_, fs) -> sub (List.map snd fs)
  | ELet (_, _, e1, e2) | ESeq (e1, e2) | EWhile (e1, e2) -> sub [e1; e2]
  | EApp (h, es) -> sub (h :: es)
  | EFun (_, b) -> expr_uses acc b
  | EIf (c, a, b) -> sub [c; a; b]
  | EMatch (sc, brs) | ETry (sc, brs) ->
    expr_uses acc sc;
    brs |> List.iter (fun (_, g, b) ->
      (match g with Some g -> expr_uses acc g | None -> ()); expr_uses acc b)

let use_arity (prog:program) : ML (SMap.t int) =
  let tbl : SMap.t int = SMap.create 100 in
  prog |> List.iter (fun d ->
    match d with
    | DLet l ->
      let growable =
        is_pure l.dl_eff && cheap_expr l.dl_body && arrow_arity l.dl_ret > 0 in
      (match l.dl_body.e with
       | EQual _ when growable -> ()
       | EApp ({ e = EQual _ }, es) when growable -> List.iter (expr_uses tbl) es
       | _ -> expr_uses tbl l.dl_body)
    | _ -> ());
  tbl

let eta_expand_decl (tbl : SMap.t int) (uses : SMap.t int) (l:dlet) : ML dlet =
  (* Only a head this program declares, and only a *pure* body: expansion
     re-evaluates the body on every call, and an under-applied call allocates a
     closure and runs nothing, which is why it qualifies. *)
  let missing =
    if not (is_pure l.dl_eff) || not (cheap_expr l.dl_body) then 0
    else
      let head, nargs = match l.dl_body.e with
                        | EApp ({ e = EQual (n, _) }, args) -> (Some n, List.length args)
                        | EQual (n, _) -> (Some n, 0)
                        | _ -> (None, 0) in
      match head with
      | None -> 0
      | Some n ->
        (match SMap.try_find tbl (string_of_name n) with
         | Some a when a > nargs ->
           let want = a - nargs in
           let have = arrow_arity l.dl_ret in
           let room =
             (* Never past what the callers ask for. *)
             match SMap.try_find uses (string_of_name l.dl_name) with
             | Some k -> if k - List.length l.dl_binders < 0
                         then 0 else k - List.length l.dl_binders
             | None -> have in
           let m = if want < have then want else have in
           if room < m then room else m
         | _ -> 0) in
  let rec go (n:int) (bs:list binder) (body:expr) (ret:cty) (ef:eff)
    : ML (list binder & expr & cty & eff) =
    if n <= 0 then (bs, body, ret, ef)
    else match ret with
         | TArrow (a, e, b) ->
           let v = rename "eta" in
           let arg = mk (EVar v) a E_Pure in
           let body' = match body.e with
                       | EApp (f, args) -> mk (EApp (f, args @ [arg])) b e
                       | _ -> mk (EApp (body, [arg])) b e in
           go (n - 1) (bs @ [{ b_name = v; b_ty = a }]) body' b e
         | _ -> (bs, body, ret, ef) in
  let bs, body, ret, ef = go missing l.dl_binders l.dl_body l.dl_ret l.dl_eff in
  { l with dl_binders = bs; dl_body = body; dl_ret = ret; dl_eff = ef }

(* To a fixpoint, because expanding a definition changes *its* arity and so
   what its callers are owed.  [let g : bool -> bool -> bool = f] is
   source-parameterless, so one pass reads its arity as 0 and refuses to give
   [let call_g a b = g a b] -- which [eta_reduce] has already shortened to
   [fun a -> g a] -- its second argument back; the caller is then emitted as a
   partial application, which C cannot express and rejects as "too few
   arguments" (section 25).  Each round can only add binders, and never more
   than [arrow_arity dl_ret] of them, so the total is bounded and the loop
   terminates; the fuel is the chain length, one link consumed per round. *)
let eta_expand_decls (prog:program) : ML program =
  let width (p:program) : ML int =
    List.fold_left (fun n d -> match d with
                               | DLet l -> n + List.length l.dl_binders
                               | _ -> n) 0 p in
  let rec go (fuel:int) (p:program) : ML program =
    let tbl = decl_arity p in
    let uses = use_arity p in
    let p' = p |> List.map (fun d ->
      match d with
      | DLet l -> DLet (eta_expand_decl tbl uses l)
      | d -> d) in
    if fuel <= 0 || width p' = width p then p' else go (fuel - 1) p' in
  go (List.length prog) prog

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
    (* [Root] survives inlining.  A root was asked for by name, and what asks
       for it is outside the extracted program -- hand-written OCaml calling
       the compiler, which has nothing to inline into (section 12.13).  Every
       *use* inside the program is still substituted; only the declaration
       stays. *)
    | DLet dl -> not (dl.dl_flags |> List.existsb Inline?)
              || dl.dl_flags |> List.existsb Root?
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
  | PRecord (n, fs) -> string_of_name n :: List.collect (fun (_, q) -> pat_deps q) fs
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
        | ECast (e, t) | ECoerce (e, t) -> cty_deps t @ expr_deps e
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
let ctor_owners (prog:program) : ML (SMap.t string) =
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
  let own = ctor_owners prog in
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

(* Section 6, pass 7: strongly connected components.

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
  let own = ctor_owners prog in
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
     (* One live branch is the same situation one step on: the match was
        exhaustive before pruning, so if every other arm is unreachable this
        one is taken unconditionally, and testing the scrutinee against its
        pattern is a test whose answer is already known.  The pattern has to
        bind nothing beyond the scrutinee itself for the body to survive
        without it; a constructor pattern that does bind is left alone, since
        [depat] turns exactly that into projections. *)
     | [(p, None, b)], _ ->
       (match p with
        | PWild | PConst _ -> take x s b
        (* The name stands for the whole scrutinee, so a binding replaces the
           match -- and when the name is unused, not even that. *)
        | PVar v -> if occurs v b then { x with e = ELet (v, s.ty, s, b) }
                    else take x s b
        | _ -> { x with e = EMatch (s, live) })
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
  | ECoerce (e1, c) -> { x with e = ECoerce (g e1, c) }
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
  ci_params: list string;        (* that type's parameters, in order *)
  ci_fields: list (string & cty);
  ci_realized: bool;             (* realized, and a variant there (section 8.2) *)
}

(* The declarations this run links against rather than compiles, as the units
   that compiled them emitted them.  No pass here decides anything about them
   -- a type's representation is settled, and {!FStarC.Custard.Layout} hands it
   over in a [verdicts] -- but the passes that ask how many constructors a type
   has, what its fields are called, or what a function's declared argument
   types are, still have to be able to see them.  The last of those is not
   optional: a coercion is inserted where a declared type meets a value, and a
   call to an imported function whose signature is invisible is a boundary
   that silently disappears.  A [ref] rather than an argument threaded through
   a dozen functions, for the same reason
   {!FStarC.Custard.PrintOCaml.externals} is one: it is constant for a whole
   program.  Set by {!run}. *)
let imported_types : ref (list decl) = mk_ref []

(* The program as the *declaration*-inspecting passes should see it.  An
   imported declaration is visible to a question about a declaration and
   invisible to everything else: it is not rewritten, not re-decided, and not
   emitted. *)
let with_imports (prog:program) : ML program =
  match !imported_types with
  | [] -> prog
  | ds -> ds @ prog

let ctor_infos (prog:program) : ML (SMap.t ctor_info) =
  let m : SMap.t ctor_info = SMap.create 50 in
  prog |> List.iter (fun d ->
    match d with
    | DType ({ dt_name = tn; dt_params = ps; dt_body = TVariant cs; dt_flags = fl }) ->
      let n = List.length cs in
      cs |> List.iter (fun (cn, fs) ->
        (* [TInline] is [inline_fields]'s business; the types this table hands
           out end up on [EProj] nodes, where the marker has no meaning. *)
        let fs = fs |> List.map (fun (f, c) -> (f, (match c with TInline c -> c | c -> c))) in
        SMap.add m (string_of_name cn)
          { ci_owner = tn; ci_count = n; ci_params = ps; ci_fields = fs;
            ci_realized = has_flag fl Realized && not (has_flag fl SourceRecord) })
    (* A record is keyed on its type, which is what [ERecord], [EProj] and
       [PRecord] all name.  It has one "constructor" by construction. *)
    | DType ({ dt_name = tn; dt_params = ps; dt_body = TRecord fs; dt_flags = fl }) ->
      let fs = fs |> List.map (fun (f, c) -> (f, (match c with TInline c -> c | c -> c))) in
      SMap.add m (string_of_name tn)
        { ci_owner = tn; ci_count = 1; ci_params = ps; ci_fields = fs;
          ci_realized = has_flag fl Realized && not (has_flag fl SourceRecord) }
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
  | ECoerce (e1, c) -> { x with e = ECoerce (g e1, c) }
  | EWhile (a, b) -> { x with e = EWhile (g a, g b) }
  | ETry (a, brs) -> { x with e = ETry (g a, brs |> List.map (psub_branch sm)) }

and psub_branch (sm:subst) (br:branch) : ML branch =
  let p, guard, b = br in
  (p, (match guard with None -> None | Some e -> Some (psub sm e)), psub sm b)

(* A binding whose pattern cannot fail: one constructor, and no nested test.
   The result names the key an [EProj] on the scrutinee has to carry -- the
   constructor for a variant, the type for a record -- and pairs each field
   with the pattern standing for it. *)
let irrefutable (tbl:SMap.t ctor_info) (p:pat)
  : ML (option (name & list ((string & cty) & pat))) =
  let plain (ps:list pat) : ML bool = ps |> List.for_all (fun p -> PVar? p || PWild? p) in
  match p with
  (* Section 8.2: a realized type's OCaml declaration is the hand-written one,
     and [FStar.Pervasives.dtuple3] is a *variant* there, so it has no field to
     project.  [records] leaves it alone for the same reason, and turning its
     [match] into an [EProj] here would name a label the realization does not
     have.  A realized type the source wrote as a record is not one of these:
     its realization is an OCaml record, [records] does convert it, and its
     labels are exactly the source's. *)
  | PCtor (cn, ps) ->
    (match single_ctor tbl cn with
     | Some ci when not ci.ci_realized
                 && List.length ps = List.length ci.ci_fields && plain ps ->
       Some (cn, List.zip ci.ci_fields ps)
     | _ -> None)
  (* A record pattern is irrefutable whatever it leaves out, and it names the
     fields it does mention, so there is no arity to check. *)
  | PRecord (tn, fs) ->
    (match SMap.try_find tbl (string_of_name tn) with
     | Some ci when plain (fs |> List.map snd) ->
       Some (tn, fs |> List.collect (fun (f, q) ->
         match ci.ci_fields |> List.tryFind (fun (g, _) -> g = f) with
         | Some fd -> [(fd, q)]
         | None -> []))
     | _ -> None)
  | _ -> None

let rec depat (tbl:SMap.t ctor_info) (x:expr) : ML expr =
  let g = depat tbl in
  match x.e with
  | EMatch (s, [(p, None, body)]) ->
    let s = g s in
    let body = g body in
    (match irrefutable tbl p with
     | Some (cn, fps) ->
       (* Re-reading the scrutinee for every field is what makes the match
          disappear entirely; when that is not free, one [let] stands in. *)
       let bound, s' =
         if dup_ok s then None, s
         else let v = rename "scrut" in
              Some v, { s with e = EVar v; eff = E_Pure } in
       let sm : subst = SMap.create 10 in
       (* A field's declared type speaks of the type's *parameters*; the
          scrutinee says what they are here.  Left uninstantiated, the third
          component of an [ident & bv & ref bool] comes out typed ['c], and a
          [ref] the OCaml backend cannot see is printed as an array. *)
       let inst (ft:cty) : ML cty =
         match SMap.try_find tbl (string_of_name cn), s.ty with
         | Some ci, TApp (_, args)
             when Cons? ci.ci_params && List.length args = List.length ci.ci_params ->
           subst_cty (List.zip ci.ci_params args) ft
         | _ -> ft in
       fps |> List.iter (fun ((f, ft), p) ->
         match p with
         | PVar v -> SMap.add sm v (mk (EProj (s', cn, f)) (inst ft) E_Pure)
         | _ -> ());
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
  | EMatch (s, brs) -> { x with e = EMatch (g s, brs |> List.map (depat_branch tbl)) }
  | EIf (c, a, b) -> { x with e = EIf (g c, g a, g b) }
  | ESeq (a, b) -> { x with e = ESeq (g a, g b) }
  | ECtor (n, es) -> { x with e = ECtor (n, es |> List.map g) }
  | ETuple es -> { x with e = ETuple (es |> List.map g) }
  | EOp (o, es) -> { x with e = EOp (o, es |> List.map g) }
  | ERaise e1 -> { x with e = ERaise (g e1) }
  | ERecord (n, fs) -> { x with e = ERecord (n, fs |> List.map (fun (f, e) -> (f, g e))) }
  | EProj (e1, n, f) -> { x with e = EProj (g e1, n, f) }
  | ECast (e1, c) -> { x with e = ECast (g e1, c) }
  | ECoerce (e1, c) -> { x with e = ECoerce (g e1, c) }
  | EWhile (a, b) -> { x with e = EWhile (g a, g b) }
  | ETry (a, brs) -> { x with e = ETry (g a, brs |> List.map (depat_branch tbl)) }

and depat_branch (tbl:SMap.t ctor_info) (br:branch) : ML branch =
  let p, guard, b = br in
  (p, (match guard with None -> None | Some e -> Some (depat tbl e)),
   depat tbl b)

let depat_decls (prog:program) : ML program =
  let tbl = ctor_infos (with_imports prog) in
  prog |> List.map (fun d ->
    match d with
    | DLet dl -> DLet { dl with dl_body = depat tbl dl.dl_body }
    | d -> d)

(* An under-applied constructor.  `Extract` builds an [ECtor] out of whatever
   arguments the application node carried, so a constructor used as a function
   -- `List.map Mktuple2 xs` -- arrives with fewer arguments than it has
   fields.  No backend can print that: OCaml constructors are not first-class,
   and a record has no partial application at all.  So it is eta-expanded here,
   before anything reads a constructor's arity.  A full application is left
   exactly as it was, so this pass is invisible to the overwhelming majority of
   the program. *)
let eta_ctors (vd:verdicts) (prog:program) : ML program =
  let infos = ctor_infos (with_imports prog) in
  (* The arity a use site is written against, which for an *imported*
     constructor is not the arity of the declaration in hand: that one is
     final, so section 5.7 has already replaced a field by the pieces of the
     record it held, while the [ECtor] here has not been rewritten yet.  A
     plan is stated in the pre-expansion fields, so its length is the arity
     wanted -- and for a local constructor it agrees with the declaration. *)
  let imported : SMap.t unit = SMap.create 20 in
  !imported_types |> List.iter (fun (d:decl) ->
    match d with
    | DType t ->
      (match t.dt_body with
       | TVariant cs -> cs |> List.iter (fun (cn, _) -> SMap.add imported (string_of_name cn) ())
       | TRecord _ -> SMap.add imported (string_of_name t.dt_name) ()
       | _ -> ())
    | _ -> ());
  (* Walk the plan and the final fields together to recover the fields the
     constructor was declared with.  [ex_ty] is the type of the field that was
     expanded, and an unexpanded position consumes exactly one final field. *)
  let rec unplan (pl:fplan) (fs:list (string & cty)) : ML (list (string & cty)) =
    match pl with
    | [] -> []
    | (f, _, None) :: pl ->
      (match fs with
       | (_, t) :: fs -> (f, t) :: unplan pl fs
       | [] -> [])
    | (f, _, Some ex) :: pl ->
      let rec drop n l = if n <= 0 then l else (match l with [] -> [] | _ :: l -> drop (n - 1) l) in
      (f, ex.ex_ty) :: unplan pl (drop (List.length ex.ex_dst) fs) in
  let declared (cn:name) (ci:ctor_info) : ML (list (string & cty)) =
    match SMap.try_find vd.vd_plans (string_of_name cn) with
    | Some pl when Some? (SMap.try_find imported (string_of_name cn)) -> unplan pl ci.ci_fields
    | _ -> ci.ci_fields in
  let rec go (x:expr) : ML expr =
    let g = go in
    match x.e with
    | ECtor (cn, es) ->
      let es = es |> List.map g in
      let alt = { x with e = ECtor (cn, es) } in
      (match SMap.try_find infos (string_of_name cn) with
       | Some ci ->
         let n = List.length es in
         let fs = declared cn ci in
         if n >= List.length fs then alt
         else begin
           let missing = fs |> List.mapi (fun i f -> (i, f))
                         |> List.collect (fun (i, f) -> if i < n then [] else [f]) in
           let bs = missing |> List.map (fun (f, t) -> { b_name = rename f; b_ty = t }) in
           let args = bs |> List.map (fun b -> mk (EVar b.b_name) b.b_ty E_Pure) in
           (* [x.ty] is the datatype: `Extract` types an [ECtor] by its
              constructor's result, however many arguments it was given. *)
           let res = List.fold_right (fun (b:binder) t -> TArrow (b.b_ty, E_Pure, t))
                                     bs x.ty in
           mk (EFun (bs, { alt with e = ECtor (cn, es @ args) })) res E_Pure
         end
       | None -> alt)
    | EConst _ | EVar _ | EQual _ | EAny | EAbort _ -> x
    | ELet (v, ty, a, b) -> { x with e = ELet (v, ty, g a, g b) }
    | ESeq (a, b) -> { x with e = ESeq (g a, g b) }
    | EWhile (a, b) -> { x with e = EWhile (g a, g b) }
    | EApp (h, es) -> { x with e = EApp (g h, es |> List.map g) }
    | EFun (bs, b) -> { x with e = EFun (bs, g b) }
    | EIf (c, a, b) -> { x with e = EIf (g c, g a, g b) }
    | EMatch (s, brs) -> { x with e = EMatch (g s, brs |> List.map go_branch) }
    | ETry (s, brs) -> { x with e = ETry (g s, brs |> List.map go_branch) }
    | ETuple es -> { x with e = ETuple (es |> List.map g) }
    | EOp (o, es) -> { x with e = EOp (o, es |> List.map g) }
    | ERaise e1 -> { x with e = ERaise (g e1) }
    | ERecord (n, fs) -> { x with e = ERecord (n, fs |> List.map (fun (f, e) -> (f, g e))) }
    | EProj (e1, n, f) -> { x with e = EProj (g e1, n, f) }
    | EDiscrim (e1, n) -> { x with e = EDiscrim (g e1, n) }
    | ECast (e1, c) -> { x with e = ECast (g e1, c) }
    | ECoerce (e1, c) -> { x with e = ECoerce (g e1, c) }
  and go_branch (br:branch) : ML branch =
    let p, gd, b = br in
    (p, (match gd with None -> None | Some e -> Some (go e)), go b) in
  prog |> List.map (fun d ->
    match d with
    | DLet dl -> DLet { dl with dl_body = go dl.dl_body }
    | d -> d)

(* Turn the single-constructor variants the layout analysis chose into records
   (section 5.5).  This pass decides nothing: it applies [vd_records]. *)
let records (vd:verdicts) (prog:program) : ML program =
  (* The verdict says *whether*; the fields are read off the declaration the
     rewrite is about to change, because [inline_fields] has already replaced
     some of them with the pieces of the record they held (section 5.7). *)
  let fields : SMap.t (list string) = SMap.create 100 in
  let _ = with_imports prog |> List.iter (fun d ->
    match d with
    | DType t ->
      (match t.dt_body with
       | TRecord fs -> SMap.add fields (string_of_name t.dt_name) (fs |> List.map fst)
       | TVariant [(_, fs)] -> SMap.add fields (string_of_name t.dt_name) (fs |> List.map fst)
       | _ -> ())
    | _ -> ()) in
  let as_record (cn:name) : ML (option (name & list string)) =
    match SMap.try_find vd.vd_records (string_of_name cn) with
    | None -> None
    | Some tn ->
      (match SMap.try_find fields (string_of_name tn) with
       | Some fs -> Some (tn, fs)
       | None -> None) in
  let rec go (x:expr) : ML expr =
    match x.e with
    | ECtor (cn, es) ->
      let es = es |> List.map go in
      (match as_record cn with
       | Some (tn, fs) ->
         if List.length fs <> List.length es
         then failwith (Format.fmt3 "custard records: %s expects %s fields, applied to %s"
                          (string_of_name cn) (show (List.length fs)) (show (List.length es)))
         else { x with e = ERecord (tn, List.zip fs es) }
       | None -> { x with e = ECtor (cn, es) })
    (* [Rename] keys a record's fields on the type name and a variant's on the
       constructor name, so the node has to be re-tagged along with the type. *)
    | EProj (e1, n, f) ->
      let e1 = go e1 in
      { x with e = EProj (e1, (match as_record n with Some (tn, _) -> tn | None -> n), f) }
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
    | ECoerce (e1, c) -> { x with e = ECoerce (go e1, c) }
  (* A constructor pattern becomes a record pattern.  This is what the verdict
     used to have to be a whole-program decision for: without [PRecord] there
     was nothing to rewrite such a match to, so any surviving one disqualified
     the type -- and whether one survives is a fact about the program. *)
  and go_pat (p:pat) : ML pat =
    match p with
    | PCtor (cn, ps) ->
      let ps = ps |> List.map go_pat in
      (match as_record cn with
       | Some (tn, fs) ->
         if List.length fs <> List.length ps
         then failwith (Format.fmt3 "custard records pat: %s expects %s fields, matched %s"
                          (string_of_name cn) (show (List.length fs)) (show (List.length ps)))
         else PRecord (tn, List.zip fs ps)
       | None -> PCtor (cn, ps))
    | PRecord (n, fs) -> PRecord (n, fs |> List.map (fun (f, q) -> (f, go_pat q)))
    | PTuple ps -> PTuple (ps |> List.map go_pat)
    | POr ps -> POr (ps |> List.map go_pat)
    | p -> p
  and go_branch (br:branch) : ML branch =
    let p, gd, b = br in
    (go_pat p, (match gd with None -> None | Some g -> Some (go g)), go b) in
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

(* [ECtor]/[ERecord] and [EProj] are keyed on the constructor name for a
   variant and on the type name for a record; [Rename] relies on that, so the
   nodes this pass builds have to agree. *)
let ex_key (ex:expansion) : name =
  match ex.ex_ctor with Some c -> c | None -> ex.ex_type

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

let strip_inline (c:cty) : cty =
  match c with TInline c -> c | c -> c

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
  | ECoerce (e1, c) -> { x with e = ECoerce (g e1, c) }

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
  | EDiscrim (e1, _) | ECast (e1, _) | ECoerce (e1, _) -> g e1

let inline_fields (vd:verdicts) (prog:program) : ML program =
  if SMap.keys vd.vd_plans = [] then prog else begin
  let plan (cn:name) : ML (option fplan) = SMap.try_find vd.vd_plans (string_of_name cn) in

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
    | ECoerce (e1, c) -> { x with e = ECoerce (go e1, c) }

  (* A branch is rewritten pattern first, and *every* constructor pattern in
     it, not just the outermost: a plan applies wherever its constructor
     appears.  A nested constructor pattern at an inlined position is the case
     that pays -- it flattens.  A [PVar] standing for the whole field becomes
     one variable per piece, and the body gets the field back as a value:
     substituted when it is read at most once, so that [unbuild] takes it
     apart again, and behind a [let] otherwise, so that no allocation is
     duplicated. *)
  and go_branch (br:branch) : ML branch =
    let p, gd, b = br in
    let sm : subst = SMap.create 10 in
    let lets : ref (list (string & cty & expr)) = mk_ref [] in
    (* Whether the value bound to [v] can be substituted rather than let-bound:
       either it is read at most once, or every read of it is a projection,
       which [unbuild] undoes. *)
    let free (v:string) : ML bool =
      let uses = count v b + (match gd with None -> 0 | Some g -> count v g) in
      uses <= 1
      || (only_projected v b && (match gd with None -> true | Some g -> only_projected v g)) in
    let rec go_pat (p:pat) : ML pat =
      match p with
      | PCtor (cn, ps) ->
        let ps = ps |> List.map go_pat in
        (match plan cn with
         | Some fs ->
           if List.length ps <> List.length fs then PCtor (cn, ps)
           else PCtor (cn,
             List.fold_left2 (fun acc (p:pat) (_, _, ex) ->
               match ex with
               | None -> acc @ [p]
               | Some ex ->
                 (match p with
                  | PCtor (_, qs) -> acc @ qs
                  | PWild -> acc @ (ex.ex_dst |> List.map (fun _ -> PWild))
                  | PVar v ->
                    let ns = ex.ex_src |> List.map (fun (g, gt) -> (rename g, gt)) in
                    let e = ex_build ex (ns |> List.map (fun (n, t) -> mk (EVar n) t E_Pure)) in
                    (if free v then SMap.add sm v e
                     else lets := !lets @ [(v, ex.ex_ty, e)]);
                    acc @ (ns |> List.map (fun (n, _) -> PVar n))
                  | _ -> acc @ [p]))
               [] ps fs)
         | None -> PCtor (cn, ps))
      | PRecord (n, fs) -> PRecord (n, fs |> List.map (fun (f, q) -> (f, go_pat q)))
      | PTuple ps -> PTuple (ps |> List.map go_pat)
      | POr ps -> POr (ps |> List.map go_pat)
      | p -> p in
    let p = go_pat p in
    (* A guard cannot be wrapped in a [let], so it always substitutes. *)
    let gsm : subst = SMap.create 10 in
    SMap.keys sm |> List.iter (fun k ->
      match SMap.try_find sm k with Some e -> SMap.add gsm k e | None -> ());
    !lets |> List.iter (fun (v, t, e) -> SMap.add gsm v e);
    let gd = (match gd with None -> None | Some g -> Some (go (psub gsm g))) in
    let b = go (psub sm b) in
    let b = List.fold_right (fun (v, t, e) acc -> { acc with e = ELet (v, t, e, acc) })
                            !lets b in
    (p, gd, b) in

  prog |> List.map (fun d ->
    match d with
    | DLet dl -> DLet { dl with dl_body = go dl.dl_body }
    | DType t ->
      (match t.dt_body with
       | TVariant cs ->
         DType { t with dt_body = TVariant (cs |> List.map (fun (cn, fs) ->
           match plan cn with
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
    | d -> d)
  end

(* Wherever the rewrite above had to put a value back together, only to have a
   field of it read straight back out.  Runs at the end of the pipeline rather
   than as part of [inline_fields], because the projections it feeds on are
   mostly what [depat] leaves behind. *)
let unbuild_decls (prog:program) : ML program =
  let infos = ctor_infos (with_imports prog) in
  prog |> List.map (fun d ->
    match d with
    | DLet dl -> DLet { dl with dl_body = unbuild infos dl.dl_body }
    | d -> d)

(* A sub-pattern under a field whose declared type is [any] (section 5.4).  A
   coercion is an expression, and a pattern is not, so the [Obj.magic] that
   would make the two agree has nowhere to go: [Mkdtuple5 (y, g, (u, t), p, k)]
   asks OCaml to match a pair against the [any] that [dtuple5]'s third
   parameter compiles to, and it refuses.

   The field is bound to a fresh variable instead, and the pattern that was
   there becomes a [match] on a coercion of it -- which is exactly the same
   test, run one step later, where a coercion is allowed.  A branch with a
   guard is left alone: the guard is evaluated where the outer pattern binds,
   and the variables would no longer be in scope there. *)
let rec split_any (infos:SMap.t ctor_info) (p:pat) (body:expr) : ML (pat & expr) =
  let simple (p:pat) : bool = PVar? p || PWild? p in
  let field (t:cty) (p:pat) (body:expr) : ML (pat & expr) =
    if TAny? t && not (simple p)
    then let v = rename "any" in
         let sc = mk (ECoerce (mk (EVar v) TAny E_Pure, TAny)) TAny E_Pure in
         let p, body = split_any infos p body in
         (PVar v, { body with e = EMatch (sc, [(p, None, body)]) })
    else split_any infos p body in
  let many (ts:list cty) (ps:list pat) (body:expr) : ML (list pat & expr) =
    List.fold_right (fun (t, p) (ps, body) ->
      let p, body = field t p body in
      (p :: ps, body)) (List.zip ts ps) ([], body) in
  match p with
  | PCtor (cn, ps) ->
    (match SMap.try_find infos (string_of_name cn) with
     | Some ci when List.length ci.ci_fields = List.length ps ->
       let ps, body = many (ci.ci_fields |> List.map snd) ps body in
       (PCtor (cn, ps), body)
     | _ -> (p, body))
  | PRecord (tn, fps) ->
    (match SMap.try_find infos (string_of_name tn) with
     | Some ci ->
       let ts = fps |> List.map (fun (f, _) ->
         match ci.ci_fields |> List.tryFind (fun (g, _) -> g = f) with
         | Some (_, t) -> t
         | None -> TVar "?") in
       let ps, body = many ts (fps |> List.map snd) body in
       (PRecord (tn, List.zip (fps |> List.map fst) ps), body)
     | None -> (p, body))
  | PTuple ps ->
    let ps, body = List.fold_right (fun p (ps, body) ->
      let p, body = split_any infos p body in
      (p :: ps, body)) ps ([], body) in
    (PTuple ps, body)
  | POr _ | PVar _ | PWild | PConst _ -> (p, body)

let rec split_any_expr (infos:SMap.t ctor_info) (x:expr) : ML expr =
  let g = split_any_expr infos in
  let br (b0:branch) : ML branch =
    let p, gd, b = b0 in
    let b = g b in
    match gd with
    | Some gd -> (p, Some (g gd), b)
    | None -> let p, b = split_any infos p b in (p, None, b) in
  match x.e with
  | EConst _ | EVar _ | EQual _ | EAny | EAbort _ -> x
  | ELet (v, ty, a, b) -> { x with e = ELet (v, ty, g a, g b) }
  | ESeq (a, b) -> { x with e = ESeq (g a, g b) }
  | EWhile (a, b) -> { x with e = EWhile (g a, g b) }
  | EApp (h, es) -> { x with e = EApp (g h, es |> List.map g) }
  | EFun (bs, b) -> { x with e = EFun (bs, g b) }
  | EIf (c, a, b) -> { x with e = EIf (g c, g a, g b) }
  | EMatch (s, brs) -> { x with e = EMatch (g s, brs |> List.map br) }
  | ETry (s, brs) -> { x with e = ETry (g s, brs |> List.map br) }
  | ETuple es -> { x with e = ETuple (es |> List.map g) }
  | EOp (o, es) -> { x with e = EOp (o, es |> List.map g) }
  | ERaise e1 -> { x with e = ERaise (g e1) }
  | ECtor (n, es) -> { x with e = ECtor (n, es |> List.map g) }
  | ERecord (n, fs) -> { x with e = ERecord (n, fs |> List.map (fun (f, e) -> (f, g e))) }
  | EProj (e1, n, f) -> { x with e = EProj (g e1, n, f) }
  | EDiscrim (e1, n) -> { x with e = EDiscrim (g e1, n) }
  | ECast (e1, c) -> { x with e = ECast (g e1, c) }
  | ECoerce (e1, c) -> { x with e = ECoerce (g e1, c) }

let split_any_decls (prog:program) : ML program =
  let infos = ctor_infos (with_imports prog) in
  prog |> List.map (fun d ->
    match d with
    | DLet dl -> DLet { dl with dl_body = split_any_expr infos dl.dl_body }
    | d -> d)

(* {1 Coercions at the [TAny] boundary (section 5.4)}

   [TAny] is what is left when Custard cannot name a value's representation.
   Monomorphization removes almost every reason for that, but not all of them:
   a class over a type *constructor* -- [FStarC.Class.Monad], whose [m] is a
   [Type -> Type] -- has no counterpart in the IR's type language, so its
   dictionary fields come out [TAny], and OCaml, which has no counterpart for
   it either, has to be told to stop looking.  That is what [Obj.magic] is for,
   and there is no avoiding it: `m t` is genuinely not an OCaml type.

   What *can* be avoided is the ML extraction's habit of coercing a term and
   then coercing it straight back -- a magic around an [if] and another around
   each of its branches, unit to [Obj.t] to unit.  So this pass inserts a
   coercion only where a value crosses a boundary that the target language will
   actually see, and only when the two sides of that boundary genuinely
   disagree.

   Which boundaries those are is the whole subtlety, and it is not "wherever
   two [expr.ty] fields differ".  A node's [ty] is what [Extract] could work
   out at the time, and [TAny] there means two different things: sometimes the
   value really has no representation, and sometimes the type was simply not
   available -- a call to a not-yet-emitted recursive function, a head a
   builtin rule rewrote.  Coercing on the strength of one of those produces
   exactly the magic-everywhere output this pass exists to avoid.

   The types that are *not* guesses are the ones a backend prints: a
   declaration's parameter and result types, a constructor's or record's field
   types, an external's declared type.  Those are the boundaries, and they are
   what drives the walk.  It is bidirectional: [check] pushes an expectation
   down from one of them, [infer] pulls a type up towards one, and a coercion
   goes in where both are known and disagree.  Everywhere either side is
   unknown, nothing is inserted -- OCaml infers, and a coercion would only be
   noise.

   A node's own [ty] is still used, but only when it is [TAny]-free, which is
   the case where it is trustworthy: [Extract] falls back to [TAny], it never
   invents a type it does not have. *)

(* Do these two types disagree in a way the target language will notice?

   Only a [TAny] against a concrete type counts, structurally.  Two *different*
   concrete types are not this pass's business: either the IR is well-typed and
   they are the same up to something [Layout] resolved, or it is not, and
   papering over that with a coercion would hide the bug.  In particular a
   [TVar] against anything is not a disagreement -- a type variable that
   survived monomorphization stands for a value whose representation is
   uniform, which is precisely what agreeing means here. *)
let rec cty_mismatch (a b : cty) : ML bool =
  match a, b with
  | TAny, TAny -> false
  | TAny, _ | _, TAny -> true
  | TArrow (a1, _, a2), TArrow (b1, _, b2) -> cty_mismatch a1 b1 || cty_mismatch a2 b2
  | TApp (n, xs), TApp (m, ys) ->
    string_of_name n = string_of_name m && ctys_mismatch xs ys
  | TBuf x, TBuf y
  | TRef x, TRef y
  | TInline x, TInline y -> cty_mismatch x y
  | TTuple xs, TTuple ys -> ctys_mismatch xs ys
  | _ -> false
and ctys_mismatch (xs ys : list cty) : ML bool =
  match xs, ys with
  | [], [] -> false
  | x :: xs, y :: ys -> cty_mismatch x y || ctys_mismatch xs ys
  | _ -> false

(* The types of [n] arguments and the result, when [c] says enough to tell.  It
   may not: an over-application left behind by inlining, or a head whose own
   type was never worked out. *)
let rec peel_arrows (n:int) (c:cty) : option (list cty & cty) =
  if n <= 0 then Some ([], c)
  else match c with
       | TArrow (a, _, r) ->
         (match peel_arrows (n - 1) r with
          | Some (ps, res) -> Some (a :: ps, res)
          | None -> None)
       | _ -> None

let rec arrows (ts:list cty) (res:cty) : cty =
  match ts with
  | [] -> res
  | t :: ts -> TArrow (t, E_Pure, arrows ts res)

(* A local variable's type, when it is known.  [None] rather than a missing
   entry is deliberate: a lambda binder whose [b_ty] is [TAny] is bound to
   "unknown", because a lambda binder is not annotated in the output and so its
   [TAny] was never a claim about the representation. *)
type cenv = SMap.t (option cty)

let coerce_prog (prog:program) : ML program =
  let all = with_imports prog in
  let infos = ctor_infos all in
  let tparams : SMap.t (list string) = SMap.create 50 in
  (* A declaration's signature as the backend will print it, with its type
     parameters still abstract. *)
  let sigs : SMap.t (list string & cty) = SMap.create 100 in
  let _ = all |> List.iter (fun d ->
    match d with
    | DType dt -> SMap.add tparams (string_of_name dt.dt_name) dt.dt_params
    | DLet dl ->
      let rec build (bs:list binder) : cty =
        match bs with
        | [] -> dl.dl_ret
        | b :: bs -> TArrow (b.b_ty, E_Pure, build bs) in
      SMap.add sigs (string_of_name dl.dl_name) (dl.dl_typars, build dl.dl_binders)
    | DExternal dx -> SMap.add sigs (string_of_name dx.dx_name) (dx.dx_typars, dx.dx_ty)
    | DExn _ -> ()) in
  let params_of (n:name) : ML (list string) =
    match SMap.try_find tparams (string_of_name n) with
    | Some ps -> ps
    | None -> [] in
  let sig_of (n:name) (targs:list cty) : ML (option cty) =
    match SMap.try_find sigs (string_of_name n) with
    | None -> None
    | Some (ps, t) ->
      if List.length ps = List.length targs
      then Some (subst_cty (List.zip ps targs) t)
      else Some t in
  (* The type a value must have for [key] -- a constructor name, or a record
     type's own name -- to be read out of it.  Its arguments are unknown by
     construction: this is only asked of a value already known to be [TAny], so
     nothing about them can be recovered.  Saying [TAny] is honest, and the
     target needs only the head -- OCaml infers the rest from the pattern or
     the field name. *)
  let owner_of (key:string) : ML (option cty) =
    match SMap.try_find infos key with
    | None -> None
    | Some ci -> Some (TApp (ci.ci_owner, params_of ci.ci_owner |> List.map (fun _ -> TAny))) in
  (* The declared field types of [key], seen through a value of type [owner],
     which is where their type arguments come from.  When [owner] does not say,
     the declared types come back unsubstituted; their [TVar]s then agree with
     everything, which is the conservative answer. *)
  let fields_of (key:string) (owner:option cty) : ML (list (string & cty)) =
    match SMap.try_find infos key with
    | None -> []
    | Some ci ->
      let ps = params_of ci.ci_owner in
      let args = (match owner with Some (TApp (_, args)) -> args | _ -> []) in
      if List.length ps = List.length args && Cons? ps
      then (let s = List.zip ps args in
            ci.ci_fields |> List.map (fun (f, c) -> (f, subst_cty s c)))
      else ci.ci_fields in
  let field_of (key:string) (owner:option cty) (f:string) : ML (option cty) =
    match fields_of key owner |> List.tryFind (fun (g, _) -> g = f) with
    | Some (_, t) -> Some t
    | None -> None in
  (* What a set of branches says its scrutinee is.  A constant or tuple pattern
     names no declaration, so it contributes nothing; in practice a scrutinee
     of unknown type is always matched against constructors. *)
  let rec scrutinee_of (brs:list branch) : ML (option cty) =
    match brs with
    | [] -> None
    | (p, _, _) :: brs ->
      (match p with
       | PCtor (n, _) | PRecord (n, _) -> owner_of (string_of_name n)
       | _ -> scrutinee_of brs) in
  (* A node's own type, when it is worth believing: when it mentions no [TAny]
     at all.  [Extract] falls back to [TAny] and never invents a type it does
     not have, so a [TAny] anywhere in a node's type means "not worked out"
     just as often as it means "no representation", and acting on it is what
     produces magic everywhere. *)
  let rec has_any (c:cty) : ML bool =
    match c with
    | TAny -> true
    | TArrow (a, _, b) -> has_any a || has_any b
    | TApp (_, args) -> args |> List.existsb has_any
    | TTuple cs -> cs |> List.existsb has_any
    | TBuf c | TRef c | TInline c -> has_any c
    | TVar _ | TInt _ | TUnit | TExn -> false in
  let trust (c:cty) : ML (option cty) = if has_any c then None else Some c in
  (* Does this term obviously have *some* representation, whatever it is?  When
     a value of unknown type reaches a position declared [TAny], that is the
     one question worth asking: a coercion *to* [TAny] is well-typed in the
     target whatever the source turns out to be, so it can be inserted on this
     much weaker evidence, and it has to be -- [Some x] built at type
     [option Obj.t] is the [Class.Monad] case, and its node type mentions a
     [TAny] that says nothing about the [option]. *)
  let concrete_shape (x:expr) : ML bool =
    match x.e with
    | ECtor _ | ERecord _ | ETuple _ | EConst _ | EFun _ | EOp _ -> true
    | _ -> false in
  let lookup (env:cenv) (v:string) : ML (option (option cty)) = SMap.try_find env v in
  let extend (env:cenv) (v:string) (t:option cty) : ML cenv =
    let env' = SMap.copy env in
    let _ = SMap.add env' v t in
    env' in
  (* Bind the variables a pattern introduces, at the field types of the
     constructor it names as seen through [sc], the scrutinee's type. *)
  let rec bind_pat (env:cenv) (sc:option cty) (p:pat) : ML cenv =
    match p with
    | PWild | PConst _ -> env
    | PVar v -> extend env v sc
    | POr ps -> List.fold_left (fun env p -> bind_pat env sc p) env ps
    | PTuple ps ->
      let ts = (match sc with
                | Some (TTuple ts) when List.length ts = List.length ps -> ts |> List.map Some
                | _ -> ps |> List.map (fun _ -> None)) in
      List.fold_left (fun env (t, p) -> bind_pat env t p) env (List.zip ts ps)
    | PCtor (n, ps) ->
      let fs = fields_of (string_of_name n) sc in
      if List.length fs = List.length ps
      then List.fold_left (fun env ((_, t), p) -> bind_pat env (Some t) p) env (List.zip fs ps)
      else List.fold_left (fun env p -> bind_pat env None p) env ps
    | PRecord (n, fps) ->
      fps |> List.fold_left (fun env (f, p) ->
        bind_pat env (field_of (string_of_name n) sc f) p) env in
  (* Solve a polymorphic signature's type variables against the types of the
     arguments actually supplied.  Without this a call to [List.map] comes back
     as [list 'b] whatever it was applied to, and [list 'b] disagrees with
     nothing -- so a [list any] flowing into a [list comp] passes unnoticed.
     First-order and first-solution-wins: the signature is a declaration's, so
     each variable occurs in argument position, and there is nothing to
     backtrack over. *)
  let rec unify_cty (p:cty) (a:cty) (acc:list (string & cty)) : ML (list (string & cty)) =
    match p, a with
    | TVar v, _ -> if acc |> List.existsb (fun (w, _) -> w = v) then acc else (v, a) :: acc
    | TArrow (p1, _, p2), TArrow (a1, _, a2) -> unify_cty p2 a2 (unify_cty p1 a1 acc)
    | TApp (n, ps), TApp (m, qs) ->
      if string_of_name n = string_of_name m && List.length ps = List.length qs
      then unify_ctys ps qs acc else acc
    | TTuple ps, TTuple qs ->
      if List.length ps = List.length qs then unify_ctys ps qs acc else acc
    | TBuf p1, TBuf a1
    | TRef p1, TRef a1
    | TInline p1, TInline a1 -> unify_cty p1 a1 acc
    | _ -> acc
  and unify_ctys (ps qs : list cty) (acc:list (string & cty)) : ML (list (string & cty)) =
    match ps, qs with
    | p :: ps, q :: qs -> unify_ctys ps qs (unify_cty p q acc)
    | _ -> acc in
  let rec infer (env:cenv) (x:expr) : ML (option cty) =
    match x.e with
    | EVar v -> (match lookup env v with Some t -> t | None -> trust x.ty)
    | EQual (n, targs) ->
      (match sig_of n targs with Some t -> Some t | None -> trust x.ty)
    | ECast (_, t) | ECoerce (_, t) -> Some t
    | EApp (h, es) ->
      (match infer env h with
       | Some t ->
         (match peel_arrows (List.length es) t with
          | Some (ps, res) ->
            let sub =
              List.fold_left2 (fun acc p (e:expr) ->
                match infer env e with
                | Some a -> unify_cty p a acc
                | None -> acc) [] ps es in
            Some (subst_cty sub res)
          | None -> trust x.ty)
       | None -> trust x.ty)
    | EProj (e1, n, f) ->
      (match field_of (string_of_name n) (infer env e1) f with
       | Some t -> Some t
       | None -> trust x.ty)
    | ELet (v, t, e1, e2) -> infer (extend env v (binding env t e1)) e2
    | ESeq (_, b) -> infer env b
    (* A [match] is what projecting a method out of a runtime dictionary
       compiles to, and its own node type is [TAny] as often as not.  The
       branches know better: the scrutinee's type says what the pattern binds,
       and the body then says what the whole thing is.

       Only a branch that is itself a variable or a projection, and only the
       first one.  [infer] is called at every node of every declaration, so
       descending into a whole branch body would make it quadratic in a
       compiler full of nested matches; the dictionary projection this exists
       for is [| Mkc f -> f]. *)
    | EMatch (sc, (p, _, b) :: _) ->
      (match b.e with
       | EVar _ | EProj _ | EQual _ -> infer (bind_pat env (infer env sc) p) b
       | _ -> trust x.ty)
    | _ -> trust x.ty
  (* What a [let]-bound variable's type is.  The annotation is [Extract]'s and
     is not printed, so a [TAny] there is not a claim; the defining term is the
     better witness. *)
  and binding (env:cenv) (t:cty) (e1:expr) : ML (option cty) =
    match trust t with
    | Some t -> Some t
    | None -> infer env e1 in
  let first (a b : option cty) : option cty =
    match a with Some _ -> a | None -> b in
  (* Rewrite [x] so that every boundary inside it agrees, then coerce [x]
     itself if what it is meets what is expected of it. *)
  (* The nodes whose [go] hands the expectation straight to whatever produces
     their result.  Each of those results has already been coerced, so the node
     agrees with the expectation by construction, and asking again would put a
     second coercion around the [if] on top of the one inside each branch --
     the ML extraction's exact pathology. *)
  let pushes_down (x:expr) : ML bool =
    match x.e with
    | ELet _ | ESeq _ | EIf _ | EMatch _ | ETry _ -> true
    | _ -> false in
  let rec check (env:cenv) (exp:option cty) (x:expr) : ML expr =
    let x = go env exp x in
    if Some? exp && pushes_down x then x else
    match exp, infer env x with
    | Some e, Some t -> if cty_mismatch t e then mk (ECoerce (x, e)) e x.eff else x
    | Some TAny, None -> if concrete_shape x then mk (ECoerce (x, TAny)) TAny x.eff else x
    | _ -> x
  and go (env:cenv) (exp:option cty) (x:expr) : ML expr =
    let same (e':expr') : expr = { x with e = e' } in
    match x.e with
    | EConst _ | EVar _ | EQual _ | EAny | EAbort _ -> x
    | ECast (e1, t) -> same (ECast (go env None e1, t))
    | ECoerce (e1, t) -> same (ECoerce (go env None e1, t))
    (* A comparison's operands all have the one type, so an operand of unknown
       representation is a boundary against whichever of them *is* known.
       Nothing else says so: an operator has no declaration to push an
       expectation down from, and without this a [Mkdtuple3]'s second field --
       [any], the type being realized and its fields not Custard's to name --
       is compared against a constructor of the type it really has. *)
    | EOp (o, es) when (match o.po_op with
                        | Eq | Neq | Lt | Lte | Gt | Gte -> true
                        | _ -> false) ->
      let es = es |> List.map (go env None) in
      let ts = es |> List.map (infer env) in
      let known = ts |> List.tryFind (fun t -> match t with
                                               | Some c -> not (TAny? c)
                                               | None -> false) in
      (match known with
       | Some (Some c) ->
         same (EOp (o, List.map2 (fun t (e:expr) ->
           match t with
           | Some TAny -> mk (ECoerce (e, c)) c e.eff
           | _ -> e) ts es))
       | _ -> same (EOp (o, es)))
    | EOp (o, es) -> same (EOp (o, es |> List.map (go env None)))
    | EWhile (c, b) -> same (EWhile (go env None c, go env None b))
    | ERaise e1 -> same (ERaise (check env (Some TExn) e1))
    | ESeq (a, b) -> same (ESeq (go env None a, check env exp b))
    | ELet (v, t, e1, e2) ->
      let e1 = check env (trust t) e1 in
      let b = binding env t e1 in
      (* Section 30.7, for a local binding.  The annotation is a copy of the
         callee's declared result type, taken when the body was extracted and
         so from before `narrow_rets' recovered it; the inference here has the
         later answer.  Left alone it is the annotation that reaches the
         backend, and a `void *' local is the one place the recovered type
         would still be thrown away. *)
      let t = (match b with
               | Some bt when has_any t && not (has_any bt) -> bt
               | _ -> t) in
      same (ELet (v, t, e1, check (extend env v b) exp e2))
    | EIf (c, a, b) ->
      (* One expectation for both branches, so that a coercion goes on the one
         that needs it rather than on the [if]. *)
      let exp = first exp (first (infer env a) (infer env b)) in
      same (EIf (go env None c, check env exp a, check env exp b))
    | ETuple es ->
      let ts = (match exp with
                | Some (TTuple ts) when List.length ts = List.length es -> ts |> List.map Some
                | _ -> es |> List.map (fun _ -> None)) in
      same (ETuple (List.map2 (check env) ts es))
    | EFun (bs, body) ->
      (* The expectation, when there is one, is what the binders are; a lambda
         binder is not annotated in the output, so its own [b_ty] is only a
         hint. *)
      let ps, res =
        (match exp with
         | Some t ->
           (match peel_arrows (List.length bs) t with
            | Some (ps, res) -> (ps |> List.map Some, Some res)
            | None -> (bs |> List.map (fun (b:binder) -> trust b.b_ty), None))
         | None -> (bs |> List.map (fun (b:binder) -> trust b.b_ty), None)) in
      let env = List.fold_left (fun env ((b:binder), t) -> extend env b.b_name t)
                               env (List.zip bs ps) in
      same (EFun (bs, check env res body))
    | EApp (h, es) ->
      (match infer env h with
       | Some t ->
         (match peel_arrows (List.length es) t with
          | Some (ps, _) ->
            same (EApp (go env None h, List.map2 (fun p e -> check env (Some p) e) ps es))
          | None ->
            (* The head says nothing about its arguments, so the arguments say
               what the head must be.  One coercion, on the head. *)
            let es = es |> List.map (go env None) in
            let ts = es |> List.map (infer env) in
            let want =
              (match exp with
               | Some r when ts |> List.for_all Some? ->
                 Some (arrows (ts |> List.map (fun t -> match t with Some t -> t | None -> TAny)) r)
               | _ -> None) in
            (match want with
             | Some _ -> same (EApp (check env want h, es))
             | None ->
               (* Nothing says what the head should be, but if what it *is* is
                  [any] then it cannot be applied at all as it stands -- a
                  value of no representation is not a function.  A coercion
                  hands the target back a type it can infer from the
                  arguments.  This is a field of a realized dependent tuple,
                  whose parameters Custard cannot name (section 5.4). *)
               let h = go env None h in
               (match infer env h with
                | Some TAny -> same (EApp (mk (ECoerce (h, TAny)) TAny h.eff, es))
                | _ -> same (EApp (h, es)))))
       (* The head's own type is not worked out well enough to retype the
          call, but a parameter it declares [TAny] is a boundary all the same:
          a coercion *to* [TAny] is well-typed whatever the argument turns out
          to be, and without one the argument's own type escapes into a
          position that has none.  This is the method of a class over a type
          constructor reached through a runtime dictionary (section 5.4): the
          head is the [match] that projects it, so nothing but its own node
          type says anything.

          The converse boundary is a parameter the head declares with a real
          type, given an argument that has none: the second component of a
          dependent pair is realized as [any] -- its type mentions the first --
          so [dsnd r] read out of a local closure's result is an [any] flowing
          into a [comp] parameter.  Its type is untrusted as a whole, but each
          parameter that mentions no [any] is still the best claim there is
          about that position, and coercing to it is what the target needs. *)
       | None ->
         let ps = (match peel_arrows (List.length es) h.ty with
                   | Some (ps, _) -> ps |> List.map (fun p -> if TAny? p then Some TAny
                                                              else if has_any p then None
                                                              else Some p)
                   | None -> es |> List.map (fun _ -> None)) in
         same (EApp (go env None h, List.map2 (fun p e -> check env p e) ps es)))
    | ECtor (n, es) ->
      let fs = fields_of (string_of_name n) (first exp (trust x.ty)) in
      if List.length fs = List.length es
      then same (ECtor (n, List.map2 (fun (_, t) e -> check env (Some t) e) fs es))
      else same (ECtor (n, es |> List.map (go env None)))
    | ERecord (n, fs) ->
      let owner = first exp (trust x.ty) in
      same (ERecord (n, fs |> List.map (fun (f, e) ->
        (f, check env (field_of (string_of_name n) owner f) e))))
    (* A value known to have no representation cannot be taken apart until it
       has one.  The guard is [TAny] exactly: [list Obj.t] is matched and
       projected perfectly well as it stands. *)
    | EProj (e1, n, f) ->
      let e1 = go env None e1 in
      (match infer env e1, owner_of (string_of_name n) with
       | Some TAny, Some t -> same (EProj (mk (ECoerce (e1, t)) t e1.eff, n, f))
       | _ -> same (EProj (e1, n, f)))
    | EDiscrim (e1, n) ->
      let e1 = go env None e1 in
      (match infer env e1, owner_of (string_of_name n) with
       | Some TAny, Some t -> same (EDiscrim (mk (ECoerce (e1, t)) t e1.eff, n))
       | _ -> same (EDiscrim (e1, n)))
    | EMatch (sc, brs) ->
      let sc = go env None sc in
      let sc = (match infer env sc, scrutinee_of brs with
                | Some TAny, Some t -> mk (ECoerce (sc, t)) t sc.eff
                | _ -> sc) in
      let st = infer env sc in
      let exp = first exp (branches_ty env brs) in
      same (EMatch (sc, brs |> List.map (check_branch env st exp)))
    | ETry (e1, brs) ->
      let exp = first exp (first (infer env e1) (branches_ty env brs)) in
      same (ETry (check env exp e1, brs |> List.map (check_branch env None exp)))
  and check_branch (env:cenv) (sc:option cty) (exp:option cty) (br:branch) : ML branch =
    let p, g, b = br in
    let env = bind_pat env sc p in
    (p, (match g with Some g -> Some (go env None g) | None -> None), check env exp b)
  and branches_ty (env:cenv) (brs:list branch) : ML (option cty) =
    match brs with
    | [] -> None
    | (p, _, b) :: brs -> first (infer (bind_pat env None p) b) (branches_ty env brs) in
  prog |> List.map (fun d ->
    match d with
    | DLet dl ->
      (* A top-level binder and result *are* printed, so a [TAny] in one of
         them is a claim: the value really is an [Obj.t] there. *)
      let env : cenv = SMap.create 20 in
      dl.dl_binders |> List.iter (fun (b:binder) -> SMap.add env b.b_name (Some b.b_ty));
      DLet { dl with dl_body = check env (Some dl.dl_ret) dl.dl_body }
    | d -> d)

(* Section 19.12.  A lambda in a value position, lifted to a top level.

   C has no closures, so a lambda reaching the direct backend is rejected --
   and that is right only when the lambda *captures* something.  A closed one
   is a function that happens not to have been given a name, and giving it one
   is the whole of the fix: the address of a top-level function is a value C
   is perfectly happy to store in a struct or pass as an argument.  It is also
   exactly the model the karamel path already produces for this code, a struct
   of pointers to named functions and no closures anywhere.

   These are not written by anyone.  They come from an [inline_for_extraction]
   record of thunks -- [val cbor_det_share () : share_t ...] -- whose fields
   beta-reduce to bare lambdas when the record is built.  In EverParse's CDDL
   layer, eleven of one record's forty fields are of this shape and every one
   of them is closed.

   Free *type* variables are not an obstacle: the lifted declaration takes the
   enclosing one's type parameters and the reference instantiates them, which
   costs nothing where there are none (the direct backend, which is the only
   caller) and stays correct where there are.

   Only for [--custard_backend C].  OCaml has closures and karamel has its own
   treatment, so lifting there would churn the output to no purpose. *)
let lift_lambdas (prog:program) : ML program =
  (* Free term variables, minus the ones bound on the way in.  Unlike
     [occurs] this has to track binders, because the question is whether the
     lambda is closed and a name it binds itself does not count. *)
  let rec fvs (bound:list string) (x:expr) : ML (list string) =
    let l (es:list expr) : ML (list string) = List.collect (fvs bound) es in
    match x.e with
    | EVar v -> if List.mem v bound then [] else [v]
    | EConst _ | EQual _ | EAny | EAbort _ -> []
    | ELet (v, _, e1, e2) -> fvs bound e1 @ fvs (v :: bound) e2
    | EApp (h, es) -> fvs bound h @ l es
    | EFun (bs, b) -> fvs (List.map (fun (b:binder) -> b.b_name) bs @ bound) b
    | EMatch (sc, brs) -> fvs bound sc @ List.collect (fvs_branch bound) brs
    | ETry (a, brs) -> fvs bound a @ List.collect (fvs_branch bound) brs
    | EIf (a, b, c) -> l [a; b; c]
    | ESeq (a, b) | EWhile (a, b) -> l [a; b]
    | ECtor (_, es) | ETuple es | EOp (_, es) -> l es
    | ERaise e1 -> fvs bound e1
    | ERecord (_, fs) -> l (List.map snd fs)
    | EProj (a, _, _) | EDiscrim (a, _) | ECast (a, _)
    | ECoerce (a, _) -> fvs bound a
  and fvs_branch (bound:list string) (br:branch) : ML (list string) =
    let p, g, b = br in
    let bound = pat_vars p @ bound in
    (match g with Some g -> fvs bound g | None -> []) @ fvs bound b
  and pat_vars (p:pat) : ML (list string) =
    match p with
    | PWild | PConst _ -> []
    | PVar v -> [v]
    | PCtor (_, ps) -> List.collect pat_vars ps
    | PRecord (_, fs) -> List.collect pat_vars (List.map snd fs) in
  let taken : SMap.t bool = SMap.create 100 in
  prog |> List.iter (fun d ->
    match d with
    | DLet d -> SMap.add taken (string_of_name d.dl_name) true
    | DType d -> SMap.add taken (string_of_name d.dt_name) true
    | DExternal d -> SMap.add taken (string_of_name d.dx_name) true
    | DExn d -> SMap.add taken (string_of_name d.de_name) true);
  let lifted : ref (list decl) = mk_ref [] in
  (* One declaration at a time, so that a lifted function is emitted next to
     the definition it came out of and the names stay readable. *)
  let go_decl (dl:dlet) : ML dlet =
    let n = mk_ref 0 in
    let fresh_name () : ML name =
      let pick (i:int) : ML string =
        dl.dl_name.id ^ "__lam" ^ (if i = 0 then "" else "_" ^ show i) in
      let rec first (i:int) : ML name =
        let cand = { dl.dl_name with id = pick i } in
        if Some? (SMap.try_find taken (string_of_name cand))
        then first (i + 1)
        else (SMap.add taken (string_of_name cand) true; cand) in
      let r = first !n in
      n := !n + 1; r in
    let rec go (x:expr) : ML expr =
      let same (e':expr') : expr = { x with e = e' } in
      match x.e with
      | EFun (bs, body) ->
        let body = go body in
        let bound = List.map (fun (b:binder) -> b.b_name) bs in
        if Cons? (fvs bound body)
        then same (EFun (bs, body))
        else
          let nm = fresh_name () in
          lifted := DLet { dl_name = nm; dl_typars = dl.dl_typars;
                           dl_binders = bs; dl_ret = body.ty;
                           dl_eff = body.eff; dl_body = body;
                           dl_flags = [] } :: !lifted;
          { x with e = EQual (nm, dl.dl_typars |> List.map (fun v -> TVar v)) }
      | EConst _ | EVar _ | EQual _ | EAny | EAbort _ -> x
      | ELet (v, t, e1, e2) -> same (ELet (v, t, go e1, go e2))
      | EApp (h, es) -> same (EApp (go h, List.map go es))
      | EMatch (sc, brs) -> same (EMatch (go sc, List.map go_branch brs))
      | ETry (a, brs) -> same (ETry (go a, List.map go_branch brs))
      | EIf (a, b, c) -> same (EIf (go a, go b, go c))
      | ESeq (a, b) -> same (ESeq (go a, go b))
      | EWhile (a, b) -> same (EWhile (go a, go b))
      | ECtor (nm, es) -> same (ECtor (nm, List.map go es))
      | ETuple es -> same (ETuple (List.map go es))
      | EOp (o, es) -> same (EOp (o, List.map go es))
      | ERaise e1 -> same (ERaise (go e1))
      | ERecord (nm, fs) -> same (ERecord (nm, fs |> List.map (fun (f, e) -> (f, go e))))
      | EProj (a, nm, f) -> same (EProj (go a, nm, f))
      | EDiscrim (a, nm) -> same (EDiscrim (go a, nm))
      | ECast (a, t) -> same (ECast (go a, t))
      | ECoerce (a, t) -> same (ECoerce (go a, t))
    and go_branch (br:branch) : ML branch =
      let p, g, b = br in
      (p, (match g with Some g -> Some (go g) | None -> None), go b) in
    { dl with dl_body = go dl.dl_body } in
  (* A lifted function is emitted *before* the definition that refers to it,
     which is what the C backend's forward declarations expect and what keeps
     the [scc] pass from seeing a use ahead of its definition. *)
  prog |> List.collect (fun d ->
    match d with
    | DLet dl ->
      lifted := [];
      let dl = go_decl dl in
      List.rev !lifted @ [DLet dl]
    | d -> [d])

(* Section 30.7.  A declared result type of [TAny] is not a claim that the
   value has no representation; it is [Extract] reporting that it could not
   work one out.  The commonest cause is a record with a [Type0] field: the
   field erases, and a record that collapses to a sibling field *of* that type
   (section 5.2) collapses to something with no name left.  A specialized
   definition's *body*, though, is a concrete value, and by the time [records]
   has run its type is ground -- so where the declaration lost the answer and
   the body has it, the body wins.

   This has to run late, after [records], because that is the pass that turns
   the collapsed record into the field's own type; and it has to iterate,
   because a definition may return nothing more than a call to another one
   whose type is being recovered in the same fixpoint.  In the CDDL bundles
   this chain is as deep as the grammar derivation.

   Only the *declarations* are rewritten.  [coerce_prog] re-derives every
   [EQual]'s type from the signature rather than the node it sits in, so
   narrowing a signature is enough for the uses to follow, and the coercions
   that stood between them disappear on their own because the two sides now
   agree. *)
let narrow_rets (prog:program) : ML program =
  let rec has_any (c:cty) : ML bool =
    match c with
    | TAny -> true
    | TArrow (a, _, b) -> has_any a || has_any b
    | TApp (_, args) -> args |> List.existsb has_any
    | TTuple cs -> cs |> List.existsb has_any
    | TBuf c | TRef c | TInline c -> has_any c
    | TVar _ | TInt _ | TUnit | TExn -> false in
  (* Name -> the whole type, arguments included, so that a use of a name in
     head position can be peeled the same way [coerce_prog] peels it. *)
  let tbl : SMap.t cty = SMap.create 100 in
  let full (dl:dlet) (r:cty) : ML cty =
    arrows (dl.dl_binders |> List.map (fun (b:binder) -> b.b_ty)) r in
  prog |> List.iter (fun d ->
    match d with
    | DLet dl when Nil? dl.dl_typars ->
      SMap.add tbl (string_of_name dl.dl_name) (full dl dl.dl_ret)
    | _ -> ());
  (* What the body says it returns.  A bare name and a saturated call are the
     two shapes that carry the answer forward from another definition; a
     coercion to [TAny] is exactly the artefact this pass exists to undo, so it
     is looked through rather than believed. *)
  let rec body_ty (x:expr) : ML cty =
    match x.e with
    | ECoerce (e1, TAny) -> body_ty e1
    | EQual (n, []) ->
      (match SMap.try_find tbl (string_of_name n) with
       | Some t when not (has_any t) -> t
       | _ -> x.ty)
    | EApp ({ e = EQual (n, []) }, es) ->
      (match SMap.try_find tbl (string_of_name n) with
       | Some t ->
         (match peel_arrows (List.length es) t with
          | Some (_, res) when not (has_any res) -> res
          | _ -> x.ty)
       | None -> x.ty)
    | _ -> x.ty in
  let changed = mk_ref false in
  let round () : ML unit =
    prog |> List.iter (fun d ->
      match d with
      | DLet dl when Nil? dl.dl_typars && has_any dl.dl_ret ->
        let key = string_of_name dl.dl_name in
        let cur = (match SMap.try_find tbl key with
                   | Some t -> (match peel_arrows (List.length dl.dl_binders) t with
                                | Some (_, r) -> r
                                | None -> dl.dl_ret)
                   | None -> dl.dl_ret) in
        if has_any cur
        then (let r = body_ty dl.dl_body in
              if not (has_any r)
              then (SMap.add tbl key (full dl r); changed := true))
      | _ -> ()) in
  (* Bounded rather than run to exhaustion: each round can only replace a
     [TAny] by a ground type, so it converges, but a bound costs nothing and
     keeps a malformed program from turning into a hang. *)
  let rec loop (n:int) : ML unit =
    if n <= 0 then ()
    else (changed := false; round ();
          if !changed then loop (n - 1)) in
  loop 20;
  prog |> List.map (fun d ->
    match d with
    | DLet dl when Nil? dl.dl_typars && has_any dl.dl_ret ->
      (match SMap.try_find tbl (string_of_name dl.dl_name) with
       | Some t ->
         (match peel_arrows (List.length dl.dl_binders) t with
          | Some (_, r) when not (has_any r) -> DLet { dl with dl_ret = r }
          | _ -> d)
       | None -> d)
    | d -> d)

let run (imports:list decl) (vd:verdicts) (prog:program) : ML program =
  let pass (n:string) (f : program -> ML program) (p:program) : ML program =
    Prof.timed ("s." ^ n) (fun () -> f p) in
  imported_types := imports;
  (* First, because every pass below reads a constructor's arity. *)
  let prog = pass "eta_ctors" (eta_ctors vd) prog in
  let prog = pass "eta_reduce" eta_reduce_decls prog in
  let prog = pass "inline" inline_decls prog in
  let prog = pass "reduce" (fun prog ->
    forwarders := forwarder_table prog; reduce_decls prog) prog in
  (* Before [depat]: dropping a branch can leave a match with a single
     irrefutable one, which is exactly what [depat] removes entirely. *)
  let prog = pass "prune" prune_decls prog in
  let prog = pass "depat" depat_decls prog in
  (* After [depat]: a field of the record being inlined is read with an
     [EProj] only once [depat] has run, and that is what tells the pass a
     reconstructed value will never actually be built.  Neither this pass nor
     [records] decides anything any more -- both only apply a verdict the
     layout analysis already reached (section 5.5) -- so where they sit in the
     pipeline is a question of code quality alone.

     [inline_fields] before [records]: a plan is expressed in terms of the
     constructor holding the field, which is exactly what [records] removes. *)
  let prog = pass "inline_fields" (inline_fields vd) prog in
  let prog = pass "unbuild" unbuild_decls prog in
  let prog = pass "simpl" (fun prog -> prog |> List.map (fun d ->
    match d with
    | DLet dl -> DLet { dl with dl_body = simpl dl.dl_body }
    | d -> d)) prog in
  (* After every pass that can leave a definition eta-short, and before [dce],
     which reads the final call graph. *)
  let prog = pass "eta_expand" eta_expand_decls prog in
  (* Before [dce], which reads the final call graph and would otherwise drop
     every lifted function as unreachable, and before [scc], which orders
     them. *)
  let prog = if Options.custard_backend () = "C"
             then pass "lift_lambdas" lift_lambdas prog else prog in
  (* Last: a coercion is inserted where two types disagree, so every pass that
     can change a type has to have run.  Nothing below it may rewrite a term. *)
  let prog = pass "dce" dce prog in
  let prog = pass "scc" scc prog in
  let prog = pass "records" (records vd) prog in
  (* After [records], which is what gives a collapsed record's body a ground
     type in the first place, and before [coerce], which reads the signatures
     this rewrites. *)
  let prog = pass "narrow_rets" narrow_rets prog in
  let prog = pass "split_any" split_any_decls prog in
  pass "coerce" coerce_prog prog
