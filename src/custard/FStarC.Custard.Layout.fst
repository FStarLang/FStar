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

module FStarC.Custard.Layout

open FStarC
open FStarC.Effect
open FStarC.List
open FStarC.Custard.Syntax

module BU = FStarC.Util
module SMap = FStarC.SMap
module Options = FStarC.Options

open FStarC.Class.Show

let layout_to_string (l:layout) : ML string =
  match l with
  | L_erased -> "erased"
  | L_newtype nt -> "newtype(" ^ nt.nt_field ^ " : " ^ show nt.nt_ty ^ ")"
  | L_struct cs -> "struct(" ^ show (List.length cs) ^ " ctors)"
  | L_abbrev c -> "abbrev(" ^ show c ^ ")"
  | L_opaque -> "opaque"

(* -------------------------------------------------------------------- *)
(* The table                                                            *)
(* -------------------------------------------------------------------- *)

type tbl = {
  types:   SMap.t dtype;                (* type key   -> declaration     *)
  erased:  SMap.t bool;                 (* type key   -> erasure         *)
  layouts: SMap.t layout;               (* type key   -> layout          *)
  ctors:   SMap.t (string & ctor_layout); (* ctor key -> owner key, layout *)
  pinned:  SMap.t unit;                 (* type keys whose verdict is imported *)
  fresh:   ref int;
}

let key (n:name) : ML string = string_of_name n

(* The body of a record is a single anonymous constructor; we name it after the
   type so that the ctor table has a key for it.  The extractor does not emit
   [TRecord] yet, but the IR allows it and the backends print it. *)
let ctors_of_tydef (d:dtype) : ML (list (name & list (string & cty))) =
  match d.dt_body with
  | TVariant cs -> cs
  | TRecord fs -> [(d.dt_name, fs)]
  | _ -> []

(* -------------------------------------------------------------------- *)
(* 5.1 Erasure                                                          *)
(* -------------------------------------------------------------------- *)

(* Section 5.0: a type *variable* is always treated as relevant.  A layout is a
   function of the declaration, not of an instantiation, so a field whose type
   is a variable can never be erased -- at [foo prop] it would be, at
   [foo bool] it would not, and [foo] is compiled once. *)
let rec cty_erased (t:tbl) (c:cty) : ML bool =
  match c with
  | TUnit -> true
  | TVar _ -> false
  | TAny -> false
  (* An exception value is a value; and raising one is observable whether or
     not anything reads it. *)
  | TExn -> false
  (* A machine integer's representation is fixed by its builtin rule
     (section 8), so nothing about it is ours to erase. *)
  | TInt _ -> false
  | TArrow (_, e, r) ->
    (* An arrow into an impure effect is not erasable even if its result is:
       calling it is observable. *)
    is_pure e && cty_erased t r
  | TTuple cs -> cs |> List.for_all (fun c -> cty_erased t c)
  (* A pointer is a machine word whether or not its contents are erased, and
     the allocation that produced it is an observable effect. *)
  | TBuf _ | TRef _ -> false
  | TInline c -> cty_erased t c
  | TApp (n, _) ->
    (match SMap.try_find t.erased (key n) with
     | Some b -> b
     | None -> false)

let dtype_erased (t:tbl) (d:dtype) : ML bool =
  if has_flag d.dt_flags Erased then true
  (* A realized type's representation is the hand-written OCaml one, whatever
     F* thinks its fields are worth. *)
  else if has_flag d.dt_flags Realized then false
  else
    match d.dt_body with
    | TAbbrev c -> cty_erased t c
    | TRecord fs -> fs |> List.for_all (fun (_, c) -> cty_erased t c)
    | TVariant [] -> true
    | TVariant [(_, fs)] -> fs |> List.for_all (fun (_, c) -> cty_erased t c)
    (* A multi-constructor variant still carries a tag, even when every field
       is erased: [type c = | A | B] is an enum, not nothing. *)
    | TVariant _ -> false
    | TAbstract -> false

(* Least fixpoint, starting from "nothing is erased".  A recursive type is
   therefore never erased, which is the safe answer. *)
let erasure_fixpoint (t:tbl) : ML unit =
  let step () : ML bool =
    let changed = mk_ref false in
    SMap.iter t.types (fun k d ->
      let old = match SMap.try_find t.erased k with
                | Some b -> b
                | None -> false in
      if Some? (SMap.try_find t.pinned k) then () else
      let nw = dtype_erased t d in
      if nw <> old then (changed := true; SMap.add t.erased k nw));
    !changed
  in
  (* Erasure only ever grows, so the number of type declarations bounds the
     number of iterations. *)
  let rec loop (fuel:int) : ML unit =
    if fuel <= 0 then ()
    else if step () then loop (fuel - 1)
    else ()
  in
  loop (SMap.fold t.types (fun _ _ n -> n + 1) 1)

(* A collapsed newtype has no constructor left to inline a field into, so its
   payload must shed the [TInline] marker of section 5.7 before it is
   substituted for the type everywhere.  Left on, the marker escapes into
   binder types and type arguments, where [Simplify.inline_fields] -- which
   only ever looks at constructor fields -- can no longer take it away, and
   the backends see a node they have no representation for. *)
let uninline (c:cty) : cty =
  match c with TInline c -> c | c -> c

(* -------------------------------------------------------------------- *)
(* 5.2 Constructor layouts and newtype collapse                         *)
(* -------------------------------------------------------------------- *)

let slots_of_fields (t:tbl) (fs:list (string & cty))
  : ML (list slot & int & list (string & cty)) =
  let slots, next, kept =
    fs |> List.fold_left (fun (slots, next, kept) (f, c) ->
            if cty_erased t c
            then (S_erased :: slots, next, kept)
            else (S_at next :: slots, next + 1, (f, c) :: kept))
          ([], 0, []) in
  (List.rev slots, next, List.rev kept)

let ctor_layouts (t:tbl) (d:dtype) : ML (list ctor_layout) =
  let cs = ctors_of_tydef d in
  let single = List.length cs = 1 in
  cs |> List.mapi (fun i (cn, fs) ->
    let slots, arity, kept = slots_of_fields t fs in
    { cl_name   = cn;
      cl_tag    = (if single then None else Some i);
      cl_slots  = slots;
      cl_arity  = arity;
      cl_fields = kept })

(* All type names occurring anywhere in a [cty]. *)
let rec names_of_cty (c:cty) : ML (list string) =
  match c with
  | TArrow (a, _, b) -> names_of_cty a @ names_of_cty b
  | TTuple cs -> cs |> List.collect names_of_cty
  | TBuf c | TRef c | TInline c -> names_of_cty c
  | TApp (n, args) -> key n :: (args |> List.collect names_of_cty)
  | _ -> []

(* Collapsing [type t = | C of t] would produce an infinite type, so a
   candidate that can reach itself through other candidates' representations is
   rejected (section 5.2, third guard). *)
let acyclic_candidates (cands:SMap.t cty) : ML (SMap.t cty) =
  let ok = SMap.create 20 in
  SMap.iter cands (fun k rep ->
    let seen = SMap.create 10 in
    (* Depth-first search through the representations of other candidates; a
       non-candidate name is a leaf, because it keeps its own declaration and
       so breaks the cycle. *)
    let rec go (work:list string) : ML bool =
      match work with
      | [] -> false
      | m :: rest ->
        if m = k then true
        else
          match SMap.try_find seen m with
          | Some _ -> go rest
          | None ->
            SMap.add seen m true;
            match SMap.try_find cands m with
            | Some rep' -> go (names_of_cty rep' @ rest)
            | None -> go rest
    in
    if not (go (names_of_cty rep)) then SMap.add ok k rep);
  ok

let compute_layouts (t:tbl) : ML unit =
  (* Pass 1: constructor layouts, and the newtype candidates. *)
  let cands = SMap.create 20 in
  SMap.iter t.types (fun k d ->
    if Some? (SMap.try_find t.pinned k) then () else
    let erased = match SMap.try_find t.erased k with
                 | Some b -> b
                 | None -> false in
    if erased then SMap.add t.layouts k L_erased
    else
      match d.dt_body with
      | TAbstract -> SMap.add t.layouts k L_opaque
      | TAbbrev c -> SMap.add t.layouts k (L_abbrev c)
      | _ ->
        let cls = ctor_layouts t d in
        SMap.add t.layouts k (L_struct cls);
        if not (has_flag d.dt_flags NoNewtype) then
          match cls with
          | [cl] ->
            if cl.cl_arity = 1 then
              (match cl.cl_fields with
               | [(_, c)] -> SMap.add cands k (uninline c)
               | _ -> ())
          | _ -> ());
  (* Pass 2: reject the candidates whose representation is cyclic. *)
  let cands = acyclic_candidates cands in
  SMap.iter cands (fun k _ ->
    match SMap.try_find t.layouts k with
    | Some (L_struct [cl]) ->
      let idx =
        cl.cl_slots |> List.fold_left (fun (i, found) s ->
          match s, found with
          | S_at _, None -> (i + 1, Some i)
          | _ -> (i + 1, found)) (0, None) |> snd in
      (match idx, cl.cl_fields with
       | Some i, [(f, c)] ->
         SMap.add t.layouts k
           (L_newtype { nt_ctor = cl.cl_name; nt_field = f;
                        nt_index = i; nt_ty = uninline c })
       | _ -> ())
    | _ -> ())

(* Every constructor gets an entry, including those of erased and collapsed
   types: their applications and patterns still have to be rewritten, and the
   rewriter finds them through this table. *)
let register_ctors (t:tbl) : ML unit =
  SMap.iter t.types (fun k d ->
    (* A pinned type's constructor layouts came from the interface and were
       registered when the table was seeded.  Recomputing them here would be
       the same computation over a different program, which is precisely what
       pinning exists to prevent. *)
    if Some? (SMap.try_find t.pinned k) then () else
    ctor_layouts t d |> List.iter (fun cl -> SMap.add t.ctors (key cl.cl_name) (k, cl)))

let ctor_owner (t:tbl) (n:name) : ML (option (layout & ctor_layout)) =
  match SMap.try_find t.ctors (key n) with
  | None -> None
  | Some (owner, cl) ->
    match SMap.try_find t.layouts owner with
    | None -> None
    | Some l -> Some (l, cl)

(* -------------------------------------------------------------------- *)
(* Resolving types                                                      *)
(* -------------------------------------------------------------------- *)

(* Erased types become [TUnit] (the residual position of section 5.1) and
   collapsed types become their payload.  [fuel] bounds the unfolding; the
   cycle check above makes exhaustion unreachable, but a bound is cheaper than
   a hang if it is ever wrong. *)
let rec resolve (t:tbl) (fuel:int) (c:cty) : ML cty =
  if fuel <= 0 then c
  else
    match c with
    | TArrow (a, e, b) -> TArrow (resolve t fuel a, e, resolve t fuel b)
    | TTuple cs -> TTuple (cs |> List.map (resolve t fuel))
    | TBuf c -> TBuf (resolve t fuel c)
    | TRef c -> TRef (resolve t fuel c)
    | TInline c -> TInline (resolve t fuel c)
    | TApp (n, args) ->
      let args = args |> List.map (resolve t fuel) in
      (match SMap.try_find t.layouts (key n) with
       | Some L_erased -> TUnit
       | Some (L_newtype nt) ->
         let params = match SMap.try_find t.types (key n) with
                      | Some d -> d.dt_params
                      | None -> [] in
         let s = (try List.zip params args with _ -> []) in
         resolve t (fuel - 1) (subst_cty s nt.nt_ty)
       (* A type abbreviation carries no representation of its own, and the
          backends need to see the machine integer behind, say, [pos_us]. *)
       | _ ->
         (match SMap.try_find t.types (key n) with
          (* A realized abbreviation is not one: the hand-written OCaml gives
             the *name* a definition of its own ([FStar.Dyn.dyn] is [Obj.t],
             not the [unit -> value_type_bundle] the F* source says), and
             expanding it would replace a type the target has with one it does
             not. *)
          | Some d when has_flag d.dt_flags Realized -> TApp (n, args)
          | Some d ->
            (match d.dt_body with
             | TAbbrev c ->
               (* An eta-contracted abbreviation -- [type psmap = t], which
                  binds nothing and stands for a type constructor -- is applied
                  to more arguments than it has parameters.  The surplus
                  belongs to whatever the body resolves to. *)
               let np = List.length d.dt_params in
               let used, extra =
                 if List.length args > np then List.splitAt np args else (args, []) in
               let s = (try List.zip d.dt_params used with _ -> []) in
               let body = subst_cty s c in
               (* The surplus has to be attached *before* the body is resolved.
                  [uvars = FlatSet.t ctx_uvar] goes through [t = flat_set],
                  which binds nothing, to [flat_set], which binds one thing:
                  resolving that on its own would unfold it with its own
                  parameter still free and then apply the surplus to the
                  result, yielding [(t, ctx_uvar) list]. *)
               let body = match extra, body with
                          | [], _ -> body
                          | _, TApp (m, a) -> TApp (m, a @ extra)
                          | _ -> body in
               resolve t (fuel - 1) body
             | _ -> TApp (n, args))
          | _ -> TApp (n, args)))
    | c -> c

(* -------------------------------------------------------------------- *)
(* 5.2 / 5.4 Term rewriting                                             *)
(* -------------------------------------------------------------------- *)

let nth_opt (#a:Type) (xs:list a) (i:int) : ML (option a) =
  let rec go (xs:list a) (i:int) : ML (option a) =
    match xs with
    | [] -> None
    | x :: xs -> if i <= 0 then Some x else go xs (i - 1)
  in
  if i < 0 then None else go xs i

(* [slots] and [xs] should have the same length; a mismatch can only come from
   a malformed constructor application, and keeping the extra arguments is the
   least surprising recovery. *)
let keep_by_slots (#a:Type) (slots:list slot) (xs:list a) : ML (list a & list a) =
  let rec go (slots:list slot) (xs:list a) (kept:list a) (dropped:list a)
    : ML (list a & list a) =
    match slots, xs with
    | _, [] -> (List.rev kept, List.rev dropped)
    | [], x :: xs -> go [] xs (x :: kept) dropped
    | S_erased :: slots, x :: xs -> go slots xs kept (x :: dropped)
    | S_at _ :: slots, x :: xs -> go slots xs (x :: kept) dropped
  in
  go slots xs [] []

let fresh_var (t:tbl) : ML string =
  t.fresh := !t.fresh + 1;
  uniq "_dropped" !t.fresh

(* Dropping an argument is only sound when it cannot have an effect; an impure
   one is sequenced before the result instead (section 5.2, last guard). *)
let hoist (dropped:list expr) (result:expr) : ML expr =
  List.fold_right (fun d acc ->
    if is_pure d.eff then acc
    else { acc with e = ESeq (d, acc) }) dropped result

let rec rw_pat (t:tbl) (p:pat) : ML pat =
  match p with
  | PCtor (n, ps) ->
    let ps = ps |> List.map (rw_pat t) in
    (match ctor_owner t n with
     | Some (L_erased, _) -> PWild
     | Some (L_newtype nt, _) ->
       (match nth_opt ps nt.nt_index with
        | Some p' -> p'
        | None -> PWild)
     | Some (_, cl) -> PCtor (n, keep_by_slots cl.cl_slots ps |> fst)
     | None -> PCtor (n, ps))
  (* The mirror of [ERecord] in [rw_expr]: a record has one shape, so there is
     no tag to collapse, and a field the layout dropped is simply not matched
     on. *)
  | PRecord (n, fs) ->
    let fs = fs |> List.map (fun (f, q) -> (f, rw_pat t q)) in
    (match SMap.try_find t.layouts (key n) with
     | Some L_erased -> PWild
     | Some (L_newtype nt) ->
       (match fs |> List.tryFind (fun (f, _) -> f = nt.nt_field) with
        | Some (_, q) -> q
        | None -> PWild)
     | Some (L_struct [cl]) ->
       PRecord (n, fs |> List.filter (fun (f, _) ->
         cl.cl_fields |> List.existsb (fun (g, _) -> g = f)))
     | _ -> PRecord (n, fs))
  | PTuple ps -> PTuple (ps |> List.map (rw_pat t))
  | POr ps -> POr (ps |> List.map (rw_pat t))
  | p -> p

let rec rw_expr (t:tbl) (x:expr) : ML expr =
  let ty = resolve t 100 x.ty in
  let x = { x with ty = ty } in
  match x.e with
  | EConst _ | EVar _ | EAny | EAbort _ -> x
  | EQual (n, cs) -> { x with e = EQual (n, cs |> List.map (resolve t 100)) }
  | ELet (v, c, e1, e2) ->
    { x with e = ELet (v, resolve t 100 c, rw_expr t e1, rw_expr t e2) }
  | EApp (h, args) -> { x with e = EApp (rw_expr t h, args |> List.map (rw_expr t)) }
  | EFun (bs, b) ->
    { x with e = EFun (bs |> List.map (fun b -> { b with b_ty = resolve t 100 b.b_ty }),
                       rw_expr t b) }
  | EMatch (s, brs) ->
    { x with e = EMatch (rw_expr t s, brs |> List.map (rw_branch t)) }
  | EIf (c, a, b) -> { x with e = EIf (rw_expr t c, rw_expr t a, rw_expr t b) }
  | ESeq (a, b) -> { x with e = ESeq (rw_expr t a, rw_expr t b) }
  | ETuple es -> { x with e = ETuple (es |> List.map (rw_expr t)) }
  | EOp (o, es) -> { x with e = EOp (o, es |> List.map (rw_expr t)) }
  | EWhile (a, b) -> { x with e = EWhile (rw_expr t a, rw_expr t b) }
  | ERaise e1 -> { x with e = ERaise (rw_expr t e1) }
  | ETry (a, brs) -> { x with e = ETry (rw_expr t a, brs |> List.map (rw_branch t)) }

  | ECtor (n, es) ->
    let es = es |> List.map (rw_expr t) in
    (match ctor_owner t n with
     | Some (L_erased, _) -> hoist es { unit_expr with eff = x.eff }
     | Some (L_newtype nt, _) ->
       (match nth_opt es nt.nt_index with
        | Some payload ->
          let dropped = es |> List.mapi (fun i e -> (i, e))
                           |> List.collect (fun (i, e) -> if i = nt.nt_index then [] else [e]) in
          hoist dropped payload
        | None -> hoist es { unit_expr with eff = x.eff })
     | Some (_, cl) ->
       let kept, dropped = keep_by_slots cl.cl_slots es in
       hoist dropped { x with e = ECtor (n, kept) }
     | None -> { x with e = ECtor (n, es) })

  | ERecord (n, fs) ->
    let fs = fs |> List.map (fun (f, e) -> (f, rw_expr t e)) in
    (match SMap.try_find t.layouts (key n) with
     | Some L_erased -> hoist (fs |> List.map snd) { unit_expr with eff = x.eff }
     | Some (L_newtype nt) ->
       (match fs |> List.tryFind (fun (f, _) -> f = nt.nt_field) with
        | Some (_, payload) ->
          hoist (fs |> List.collect (fun (f, e) -> if f = nt.nt_field then [] else [e])) payload
        | None -> hoist (fs |> List.map snd) { unit_expr with eff = x.eff })
     | Some (L_struct [cl]) ->
       let keep (f:string) : ML bool =
         cl.cl_fields |> List.existsb (fun (g, _) -> g = f) in
       let kept = fs |> List.collect (fun (f, e) -> if keep f then [(f, e)] else []) in
       let dropped = fs |> List.collect (fun (f, e) -> if keep f then [] else [e]) in
       hoist dropped { x with e = ERecord (n, kept) }
     | _ -> { x with e = ERecord (n, fs) })

  | EProj (e1, n, f) ->
    let e1 = rw_expr t e1 in
    (match ctor_owner t n with
     | Some (L_erased, _) -> hoist [e1] { unit_expr with eff = x.eff }
     (* The other fields are erased, so their projections were deleted along
        with them; only the surviving field can be projected. *)
     | Some (L_newtype _, _) -> e1
     | _ -> { x with e = EProj (e1, n, f) })

  | EDiscrim (e1, n) ->
    let e1 = rw_expr t e1 in
    (match ctor_owner t n with
     | Some (_, cl) when None? cl.cl_tag ->
       hoist [e1] { x with e = EConst (CBool true) }
     | _ -> { x with e = EDiscrim (e1, n) })

  (* Section 5.4: a cast that has become the identity after collapse is
     dropped, and nested casts are fused. *)
  | ECast (e1, c) ->
    let c = resolve t 100 c in
    let e1 = rw_expr t e1 in
    let e1 = match e1.e with
             | ECast (e2, _) -> e2
             | _ -> e1 in
    if e1.ty = c then e1 else { x with e = ECast (e1, c) }

and rw_branch (t:tbl) (br:branch) : ML branch =
  let p, g, b = br in
  (rw_pat t p, (match g with None -> None | Some g -> Some (rw_expr t g)), rw_expr t b)

(* -------------------------------------------------------------------- *)
(* Declarations                                                         *)
(* -------------------------------------------------------------------- *)

(* The type variables a [cty] mentions. *)
let rec cty_vars (c:cty) : ML (list string) =
  match c with
  | TVar x -> [x]
  | TArrow (a, _, b) -> cty_vars a @ cty_vars b
  | TApp (_, args) -> List.collect cty_vars args
  | TBuf c | TInline c | TRef c -> cty_vars c
  | TTuple cs -> List.collect cty_vars cs
  | _ -> []

(* The type constructors a [cty] applies. *)
let rec cty_names (c:cty) : ML (list string) =
  match c with
  | TArrow (a, _, b) -> cty_names a @ cty_names b
  | TApp (n, args) -> key n :: List.collect cty_names args
  | TBuf c | TInline c | TRef c -> cty_names c
  | TTuple cs -> List.collect cty_names cs
  | _ -> []

(* A collapsed type is replaced by its payload everywhere, so nothing in the
   emitted program refers to it by name any more.  A hand-written realization
   still can, though, and the name costs nothing: emit it as an abbreviation
   for the payload, which says exactly what the collapse decided and changes
   no representation.  Not when a parameter would be left unconstrained --
   OCaml rejects [type 'a t = int] -- in which case there is nothing to say. *)
let collapsed_abbrev (dt:dtype) (payload:cty) : ML (option decl) =
  let vars = cty_vars payload in
  if dt.dt_params |> List.for_all (fun p -> List.mem p vars)
     && not (List.mem (key dt.dt_name) (cty_names payload))
  then Some (DType { dt with dt_body = TAbbrev payload })
  else None

let rw_decl (t:tbl) (d:decl) : ML (list decl) =
  match d with
  | DType dt ->
    let k = key dt.dt_name in
    (match SMap.try_find t.layouts k with
     (* An erased type has no runtime representation and no remaining
        references: every [TApp] of it resolved to [TUnit]. *)
     | Some L_erased -> []
     | Some (L_newtype nt) ->
       (match collapsed_abbrev dt (resolve t 100 nt.nt_ty) with
        | Some d -> [d]
        | None -> [])
     | Some (L_struct cls) ->
       let body =
         match dt.dt_body with
         | TRecord _ ->
           (match cls with
            | [cl] -> TRecord (cl.cl_fields |> List.map (fun (f, c) -> (f, resolve t 100 c)))
            | _ -> dt.dt_body)
         | TVariant _ ->
           TVariant (cls |> List.map (fun cl ->
             (cl.cl_name, cl.cl_fields |> List.map (fun (f, c) -> (f, resolve t 100 c)))))
         | b -> b in
       [DType { dt with dt_body = body }]
     | Some (L_abbrev c) -> [DType { dt with dt_body = TAbbrev (resolve t 100 c) }]
     | _ -> [DType dt])
  | DLet dl ->
    [DLet { dl with
            dl_binders = dl.dl_binders |> List.map (fun b -> { b with b_ty = resolve t 100 b.b_ty });
            dl_ret     = resolve t 100 dl.dl_ret;
            dl_body    = rw_expr t dl.dl_body }]
  | DExternal dx -> [DExternal { dx with dx_ty = resolve t 100 dx.dx_ty }]
  | DExn de -> [DExn { de with de_args = de.de_args |> List.map (resolve t 100) }]

(* -------------------------------------------------------------------- *)
(* 5.5 Representation: records and inline fields                        *)
(* -------------------------------------------------------------------- *)

(* Two more verdicts, and the reason they are here rather than in
   {!FStarC.Custard.Simplify}, where the rewriting that applies them still
   lives: a type's representation must be a function of the type and of the
   types it is built out of, and of nothing else.  Anything derived from the
   program as a whole is a different answer in a different unit, and two units
   that disagree about a representation while agreeing about a name is a
   miscompilation no signature check can catch.

   Both used to be whole-program.  [records] refused to convert a type that
   any surviving pattern matched on, which the record pattern in the IR made
   unnecessary; [inline_fields] refused a field whose patterns could not follow
   the expansion, which cannot arise, since [Extract] emits only [PWild],
   [PVar], [PConst] and [PCtor] and the first three impose nothing. *)

(* A one-constructor type is a record.  Unconditionally: a constructor whose
   arguments F* did not name gets the positional names [_0], [_1], ..., which
   are perfectly good field names, and making the conversion unconditional
   means no [EProj] anywhere is left pointing at a variant. *)
let record_verdict (dt:dtype) : ML bool =
  (* Section 5.0.1: a realized type's OCaml shape is the hand-written one, so
     the question is not what Custard would choose but what the source said,
     which is what a realization mirrors.  [FStar.Pervasives.dtuple4] is a
     one-constructor *variant* in F* and in [FStar_Pervasives.ml]; making a
     record of it would name fields the realization does not have.
     [FStarC.Parser.ParseIt.code_fragment] is a record in both, and leaving it
     a variant would emit a constructor pattern for an OCaml record. *)
  if has_flag dt.dt_flags Realized then has_flag dt.dt_flags SourceRecord else
  match dt.dt_body with
  | TVariant [(_, fs)] -> Cons? fs
  | _ -> false

(* [_0], [_1], ... are the names a constructor's unnamed arguments get.  A
   constructor made only of those keeps them, renumbered, rather than growing
   [_0__1]-shaped ones. *)
let positional (f:string) : ML bool =
  String.strlen f > 1 && String.substring f 0 1 = "_"

(* R's declaration, when R is a type whose fields can be taken out of it:
   exactly one constructor (or a record), and at least one field. *)
let record_body (look:name -> ML (option dtype)) (n:name)
  : ML (option (list string & option name & list (string & cty))) =
  match look n with
  | Some t ->
    (match t.dt_body with
     | TRecord fs -> if Cons? fs then Some (t.dt_params, None, fs) else None
     | TVariant [(cn, fs)] -> if Cons? fs then Some (t.dt_params, Some cn, fs) else None
     | _ -> None)
  | None -> None

(* The plan for each of [dt]'s constructors that has at least one marked field.
   A field whose type turns out not to be a record keeps its place; only the
   marker goes.

   [ex_ctor] names R's constructor, because the rewriting runs before the
   record conversion above is applied and so still sees R as a variant. *)
let ctor_plans (look:name -> ML (option dtype)) (dt:dtype) : ML (list (name & fplan)) =
  if has_flag dt.dt_flags Realized then [] else
  match dt.dt_body with
  | TVariant cs ->
    cs |> List.collect (fun (cn, fs) ->
      if not (fs |> List.existsb (fun (_, c) -> TInline? c)) then [] else begin
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
            (match record_body look rn with
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
        [(cn, plan)]
      end)
  | _ -> []

(* A field whose type mentions a type variable the declaration does not bind
   is a *polymorphic* field: [FStarC.Class.Monad.monad] is a class over
   [m : Type -> Type], so its [return] has type [#a:Type -> a -> m a] and the
   [a] is bound by the field, not by [monad].  Neither the IR's type language
   nor an OCaml record field without an explicit universal can say that, and
   [m a] is already [TAny] for the same reason, so the honest reading is that
   the field has no representation on either side.

   This has to happen before anything reads a field's type: the layout
   analysis, the verdicts, and section 5.4's coercion insertion all take a
   declared field type at its word. *)
let close_fields (d:decl) : ML decl =
  match d with
  | DType dt ->
    let bound (v:string) : ML bool = dt.dt_params |> List.existsb (fun p -> p = v) in
    let rec close (c:cty) : ML cty =
      match c with
      | TVar v -> if bound v then c else TAny
      | TApp (n, args) -> TApp (n, List.map close args)
      | TArrow (a, e, b) -> TArrow (close a, e, close b)
      | TTuple cs -> TTuple (List.map close cs)
      | TBuf c -> TBuf (close c)
      | TRef c -> TRef (close c)
      | TInline c -> TInline (close c)
      | c -> c in
    let fields (fs : list (string & cty)) : ML (list (string & cty)) =
      fs |> List.map (fun (f, c) -> (f, close c)) in
    DType { dt with dt_body =
      match dt.dt_body with
      | TAbbrev c -> TAbbrev (close c)
      | TRecord fs -> TRecord (fields fs)
      | TVariant cs -> TVariant (cs |> List.map (fun (cn, fs) -> (cn, fields fs)))
      | TAbstract -> TAbstract }
  | d -> d

let run (imports:list (dtype & type_info)) (prog:program)
  : ML (program & list (name & type_info) & verdicts) =
  let prog = List.map close_fields prog in
  let t = { types   = SMap.create 100;
            erased  = SMap.create 100;
            layouts = SMap.create 100;
            ctors   = SMap.create 100;
            pinned  = SMap.create 10;
            fresh   = mk_ref 0 } in
  prog |> List.iter (fun d ->
    match d with
    | DType dt -> SMap.add t.types (key dt.dt_name) dt
    | _ -> ());
  (* Seed the imported verdicts *before* the analysis, and mark them pinned.
     Seeding rather than excluding is the point: [rw_decl] below looks every
     type and constructor up in these same tables, so a use of an imported
     type is rewritten by the upstream unit's decisions instead of being left
     alone or, worse, rewritten by a locally re-derived guess. *)
  imports |> List.iter (fun (dt, ti) ->
    let k = key dt.dt_name in
    SMap.add t.pinned k ();
    SMap.add t.erased k ti.ti_erased;
    SMap.add t.layouts k ti.ti_layout;
    ti.ti_ctors |> List.iter (fun cl -> SMap.add t.ctors (key cl.cl_name) (k, cl)));
  erasure_fixpoint t;
  compute_layouts t;
  register_ctors t;
  if Options.custard_dump_layouts () then begin
    FStarC.Format.print_string "Custard layouts:\n";
    SMap.iter t.layouts (fun k l ->
      FStarC.Format.print2 "  %s : %s\n" k (layout_to_string l))
  end;
  let prog' = prog |> List.collect (rw_decl t) in

  (* The representation verdicts are read off the program as this pass leaves
     it -- erasure has already deleted the fields it deletes, and a plan must
     describe the fields that are actually there. *)
  let final : SMap.t dtype = SMap.create 100 in
  (* An imported declaration is the one its interface carries, which is the
     one the backend will print; a local one is what [rw_decl] just produced.
     Each is what the rewriter that applies the plan will actually see. *)
  imports |> List.iter (fun (dt, _) -> SMap.add final (key dt.dt_name) dt);
  prog' |> List.iter (fun d ->
    match d with
    | DType dt -> SMap.add final (key dt.dt_name) dt
    | _ -> ());
  let look (n:name) : ML (option dtype) = SMap.try_find final (key n) in

  let vd = { vd_records = SMap.create 50; vd_plans = SMap.create 50 } in
  (* An imported type's verdict is adopted rather than re-derived.  It would
     come out the same either way -- that is the whole point of computing it
     here -- but an interface should say what it means, and pinning keeps that
     true across a future change to the functions above. *)
  imports |> List.iter (fun (dt, ti) ->
    (* The declaration an interface carries is the one its unit finally
       printed, so a type that became a record arrives as [TRecord] and the
       constructor the verdict is keyed on is only in [ti_ctors]. *)
    (if ti.ti_record then
       match dt.dt_body, ti.ti_ctors with
       | TRecord _, [cl] -> SMap.add vd.vd_records (key cl.cl_name) dt.dt_name
       | TVariant [(cn, _)], _ -> SMap.add vd.vd_records (key cn) dt.dt_name
       | _ -> ());
    ti.ti_plans |> List.iter (fun (cn, pl) -> SMap.add vd.vd_plans (key cn) pl));
  let derived : SMap.t (bool & list (name & fplan)) = SMap.create 50 in
  prog' |> List.iter (fun d ->
    match d with
    | DType dt when None? (SMap.try_find t.pinned (key dt.dt_name)) ->
      let is_rec = record_verdict dt in
      let plans = ctor_plans look dt in
      SMap.add derived (key dt.dt_name) (is_rec, plans);
      (match dt.dt_body with
       | TVariant [(cn, _)] when is_rec -> SMap.add vd.vd_records (key cn) dt.dt_name
       | _ -> ());
      plans |> List.iter (fun (cn, pl) -> SMap.add vd.vd_plans (key cn) pl)
    | _ -> ());

  (* The verdicts this run *derived*, which is what an interface exports; a
     pinned one came from somewhere else and is that unit's to export. *)
  let infos =
    SMap.keys t.types |> List.collect (fun k ->
      if Some? (SMap.try_find t.pinned k) then [] else
      match SMap.try_find t.types k, SMap.try_find t.layouts k with
      | Some d, Some l ->
        let is_rec, plans =
          match SMap.try_find derived k with
          | Some v -> v
          | None -> (false, []) in
        [(d.dt_name,
          { ti_erased = (match SMap.try_find t.erased k with Some b -> b | None -> false);
            ti_layout = l;
            ti_ctors  = ctor_layouts t d;
            ti_record = is_rec;
            ti_plans  = plans })]
      | _ -> []) in
  (prog', infos, vd)
