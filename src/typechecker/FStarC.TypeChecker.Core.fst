(*
   Copyright Microsoft Research

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
module FStarC.TypeChecker.Core
open FStarC.TypeChecker.CommonBase
(*

This module implements a core typechecker for pure and ghost F* terms.

It expects terms to be elaborated with all implicit arguments and annotated
bound variables, though it also accepts typechecking terms that contain unsolved
unification variables at their introduced types.

Abstractly, the main `check g e` computes
  
     g |- e : t | p

where a term `e` is typed at `t` in environment `g`,
provided the  guard `p` is provable in `g` (i.e., g |= p). 

We write `g |- e : t` for `g |- e : t | True`

A main nuance is in its use of caches, of two kinds:

1. A term typing cache

Each sub-call to check memoizes the result `g |- e : t` and returns the guard
`p` to be proven.

Subsequent calls to `check g' e'` looks up `e'` in the cache, and if it findds
`g |- e : t`, checks that `g'` is an extension of `g`, and if so, records a
cache hit and returns `g' |- e : t`.


2. A guard cache

When issuing a guard (e.g,. as the result of checking a subtyping relation 
`g |- t <: t' | p`), we also cache `g |= p`.

If a guard is issued later for `g' |= p`, we check if `g |= p` is cached and if
`g'` extensions `g`, we record a cache hit and do not emit the guard.

Guards are not proven immediately; instead they are accumulated and returned to
the caller to be proven later. To accomodate this API, we have two levels of
caches:

- A functional cache: cache_t.term_map and cache_t.guard_map
   
   These caches are initialized to empty at each call into the public API of the
   checker, e.g, check_term.

   The call to check_term populates the caches as it checks a term and returns
   guard to the caller. 

   The main invariant is the the provability of the returned guard implies the
   provability of all cached guards in the guard_map; and, consequently, the
   typing of all terms in the term_map.

   Once the returned guard is discharged by the caller (e.g, by calling SMT), a
   callback into this Core checker notifies it that the returned guard has been
   proven, and which point, the term_map and guard_map are promoted to the
   second level imperative cache, described next.

- The second level cache accumulates entries across multiple calls to this
  Core checker. Every entry in this cache contains guards that have already been
  proven, and contains terms whose typing has already been established.

  The second level cache is explicit cleared by called clear_memo_table, which 
  FStarC.TypeChecker.Tc does at each top-level declaration.

Dependencies:

  This checker does not depend on the elaborator (TcTerm, TcUtil) or on the
  unifier (Rel). The utilities it shares with them are in small modules:
  VCUtil (labels and simplification of VCs), UnivEq (universe equality),
  UniverseOf (the types of constants and syntactic universe computation),
  Termination (the refined types of recursive definitions) and CommonBase.
  Still, terms it is given may have been elaborated by TcTerm, and it
  re-checks them; and a few Env callbacks (e.g.
  [env.typeof_well_typed_tot_or_gtot_term], used by
  Termination) dispatch to TcTerm at runtime, only to compute terms that
  this checker then checks.

*)
open FStarC
open FStar.List.Tot
open FStarC.Effect
open FStarC.Syntax.Syntax
open FStarC.TypeChecker
open FStarC.Errors.Msg { fquotes }
module Env = FStarC.TypeChecker.Env
module S = FStarC.Syntax.Syntax
module R = FStarC.Range
module U = FStarC.Syntax.Util
module N = FStarC.TypeChecker.Normalize
module PC = FStarC.Parser.Const
module I = FStarC.Ident
module BU = FStarC.Util
module VCUtil = FStarC.TypeChecker.VCUtil
module UnivEq = FStarC.TypeChecker.UnivEq
module UniverseOf = FStarC.TypeChecker.UniverseOf
module Termination = FStarC.TypeChecker.Termination
module Err = FStarC.TypeChecker.Err
module Hash = FStarC.Syntax.Hash
module Subst = FStarC.Syntax.Subst
module TEQ = FStarC.TypeChecker.TermEqAndSimplify
module Visit = FStarC.Syntax.Visit

open FStarC.Class.Show
open FStarC.Class.Setlike
open FStarC.Class.Tagged
open FStarC.Class.PP
open FStarC.Syntax.Print {}

open FStarC.Pprint
open FStarC.Errors.Msg { text }

let dbg       = Debug.get_toggle "Core"
let dbg_facts = Debug.get_toggle "CoreFacts"
let dbg_Eq    = Debug.get_toggle "CoreEq"
let dbg_Top   = Debug.get_toggle "CoreTop"
let dbg_Exit  = Debug.get_toggle "CoreExit"
let dbg_DisableCoreCache = Debug.get_toggle "DisableCoreCache"

let goal_ctr = mk_ref 0
let get_goal_ctr () = !goal_ctr
let incr_goal_ctr () = let v = !goal_ctr in goal_ctr := v + 1; v + 1

(* The effect of a computation, as tracked internally. [Tot] and [GTot] are
   distinguished because the checker's rules for them (promotion of a ghost
   computation with a non-informative type, erasure) are special; every other
   effect is a *root* effect name (see doc/ref/simplified_effect_system.md),
   ordered by the effect lattice. *)
type eff =
  | ETot
  | EGhost
  | EEff of I.lident

let eff_of_tot_or_ghost (e:tot_or_ghost) : eff =
  match e with
  | E_Total -> ETot
  | E_Ghost -> EGhost

let eff_to_lid (e:eff) : I.lident =
  match e with
  | ETot -> PC.primitive_pure_lid
  | EGhost -> PC.primitive_ghost_lid
  | EEff m -> m

instance showable_eff : showable eff = {
  show = (function
          | ETot -> "Tot"
          | EGhost -> "GTot"
          | EEff m -> show m);
}

let eff_eq (e0 e1:eff) : ML bool =
  match e0, e1 with
  | ETot, ETot
  | EGhost, EGhost -> true
  | EEff m0, EEff m1 -> I.lid_equals m0 m1
  | _ -> false

type env = {
   tcenv : Env.env;
   allow_universe_instantiation : bool;
   should_read_cache: bool;
   max_binder_index: int;
   (* Checking a top-level function, and no binder has been pushed yet: the
      binders closed over here are those of the definition, which TcTerm has
      in its environment when it discharges its guard. *)
   at_top: bool
}


let debug g (f: unit -> ML unit) : ML unit =
  if !dbg
  then f ()

let max a b = if a > b then a else b
let push_binder g b = { g with max_binder_index=max g.max_binder_index b.binder_bv.index; 
                               tcenv = Env.push_binders g.tcenv [b];
                               at_top = false }

let push_binders = List.fold_left push_binder

let fresh_binder (g:env) (old:binder)
  : ML (env & binder)
  = let ctr = g.max_binder_index + 1 in
    let bv = { old.binder_bv with index = ctr } in
    let b = S.mk_binder_with_attrs bv old.binder_qual old.binder_positivity old.binder_attrs in
    push_binder g b, b

let wild_bv (t:typ) (r:Range.t) : bv =
  { ppname=Ident.mk_ident (Ident.reserved_prefix, r); index=0; sort=t }

let new_binder (g:env) (t:typ) (r:Range.t)
: ML (env & binder)
= let bv = wild_bv t r in
  let b = S.mk_binder bv in
  fresh_binder g b

let open_binders (g:env) (bs:binders)
  = let g, bs_rev, subst =
        List.fold_left
          (fun (g, bs, subst) b ->
            let bv = { b.binder_bv with sort = Subst.subst subst b.binder_bv.sort } in
            let b = { binder_bv = bv;
                      binder_qual = Subst.subst_bqual subst b.binder_qual;
                      binder_positivity = b.binder_positivity;
                      binder_attrs = List.map (Subst.subst subst) b.binder_attrs } in
            let g, b' = fresh_binder g b in
            g, b'::bs, DB(0, b'.binder_bv)::Subst.shift_subst 1 subst)
          (g, [], [])
          bs
    in
    g, List.rev bs_rev, subst

let open_pat (g:env) (p:pat)
  : ML (env & pat & subst_t)
  = let rec open_pat_aux g p sub : ML _ =
        match p.v with
        | Pat_constant _ -> g, p, sub

        | Pat_cons(fv, us_opt, pats) ->
          let g, pats, sub =
            List.fold_left
              (fun (g, pats, sub) (p, imp) ->
                let g, p, sub = open_pat_aux g p sub in
                (g, (p,imp)::pats, sub))
              (g, [], sub)
              pats
            in
            g, {p with v=Pat_cons(fv, us_opt, List.rev pats)}, sub

        | Pat_var x ->
          let bx = S.mk_binder {x with sort = Subst.subst sub x.sort} in
          let g, bx' = fresh_binder g bx in
          let sub = DB(0, bx'.binder_bv)::Subst.shift_subst 1 sub in
          g, {p with v=Pat_var bx'.binder_bv}, sub

        | Pat_dot_term eopt ->
          let eopt = Option.map (Subst.subst sub) eopt in
          g, {p with v=Pat_dot_term eopt}, sub
    in
    open_pat_aux g p []


let open_term (g:env) (b:binder) (t:term)
  : ML (env & binder & term)
  = let g, b' = fresh_binder g b in
    let t = FStarC.Syntax.Subst.subst [DB(0, b'.binder_bv)] t in
    g, b', t

let open_term_binders (g:env) (bs:binders) (t:term)
  : ML (env & binders & term)
  = let g, bs, subst = open_binders g bs in
    g, bs, Subst.subst subst t

let open_comp (g:env) (b:binder) (c:comp)
  : ML (env & binder & comp)
  = let g, bx = fresh_binder g b in
    let c = FStarC.Syntax.Subst.subst_comp [DB(0, bx.binder_bv)] c in
    g, bx, c

let open_comp_binders (g:env) (bs:binders) (c:comp)
  : ML (env & binders & comp)
  = let g, bs, s = open_binders g bs in
    let c = FStarC.Syntax.Subst.subst_comp s c in
    g, bs, c

let letrec_binders (lbs:list letbinding) : ML binders =
  lbs |> List.map (fun lb -> S.mk_binder { Inl?.v lb.lbname with sort = lb.lbtyp })

let arrow_formals_comp g c =
    let bs, c = U.arrow_formals_comp_ln c in
    let g, bs, subst = open_binders g bs in
    g, bs, Subst.subst_comp subst c

let open_branch (g:env) (br:S.branch)
  : ML (env & branch)
  = let (p, wopt, e) = br in
    let g, p, s = open_pat g p in
    g, (p, Option.map (Subst.subst s) wopt, Subst.subst s e)

//br0 and br1 are expected to have equal patterns
let open_branches_eq_pat (g:env) (br0 br1:S.branch)
  = let (p0, wopt0, e0) = br0 in
    let (_,  wopt1, e1) = br1 in
    let g, p0, s = open_pat g p0 in
    g,
    (p0, Option.map (Subst.subst s) wopt0, Subst.subst s e0),
    (p0, Option.map (Subst.subst s) wopt1, Subst.subst s e1)

(* What the typing of a term [e] says about [e] and its subterms, beyond
   [e]'s type: propositions assumed in the VCs that [e] is the witness of
   (see [witness_guard]), or that are in the scope of a [let] binding [e]
   (see [close_let_guard]). They are computed by [do_check] in the same pass
   as [e]'s type, from those of [e]'s subterms, and cached with it; lazily,
   since most are never needed. Only a pure [e] has any.
   * [f_sub]: about the subterms of [e]: the arguments of an application,
     the definitions of its [let]s, the branches of a [match] (under the
     condition that each is taken), ...
   * [f_term]: about [e] itself (what its type says about it, see
     [term_facts]), and [f_sub]; and [f_tail] if [e] was checked against an
     expected type pushed into it, whose type was then not synthesized
     (see [check_against_typ_synth]).
   * [f_tail]: [f_term] of the expression that the [let]s of [e] end with,
     under those [let]s, e.g. [p] for [let x = e1 in lemma x], where
     [lemma x : squash p]. *)
type facts = {
  f_sub : Thunk.t (list term);
  f_term: Thunk.t (list term);
  f_tail: Thunk.t (list term);
}

(* The witness of a subtyping, with the facts about its subterms. *)
type witness = term & Thunk.t (list term)

type relation =
  | EQUALITY
  | SUBTYPING : option witness -> relation

let relation_to_string = function
  | EQUALITY -> "=?="
  | SUBTYPING None -> "<:?"
  | SUBTYPING (Some (tm, _)) -> Format.fmt1 "( <:? %s)" (show tm)

type context_term =
  | CtxTerm : term -> context_term
  | CtxRel : term -> relation -> term -> context_term

let context_term_to_string (c:context_term) =
  match c with
  | CtxTerm term -> show term
  | CtxRel t0 r t1 ->
    Format.fmt3 "%s %s %s"
              (show t0)
              (relation_to_string r)
              (show t1)

type context = {
  no_guard : bool;
  unfolding_ok : bool;
  error_context: list (string & option context_term)
}

(* The instance prints some brief info on the error_context. `print_context`
below is a full printer. *)
instance showable_context : showable context = {
  show = (fun context -> Format.fmt3 "{no_guard=%s; unfolding_ok=%s; error_context=%s}"
                                    (show context.no_guard)
                                    (show context.unfolding_ok)
                                    (show (List.map fst context.error_context)));
}

let print_ctx_head (ctx:context) =
    match ctx.error_context with
    | [] -> "{Context: <empty>}\n"
    | (msg, ctx_term)::_ ->
      Format.fmt2 "{Context: %s (%s)}\n"
        msg
        (match ctx_term with None -> "" | Some ctx_term -> context_term_to_string ctx_term)


let print_context (ctx:context)
  : ML string =
  let rec aux (depth:string) (ctx:_) : ML _ =
    match ctx with
    | [] -> ""
    | (msg, ctx_term)::tl ->
      let hd =
        Format.fmt3
          "%s %s (%s)\n"
          depth
          msg
          (match ctx_term with None -> "" | Some ctx_term -> context_term_to_string ctx_term)
      in
      let tl = aux (depth ^ ">") tl in
      hd ^ tl
  in
  aux "" (List.rev ctx.error_context)

(* An error may carry the code with which TcTerm reports the same failure;
   it is then reported as TcTerm does (see [error_code]). *)
let error = context & Errors.error_message (* = list doc *) & option Errors.error_code

let print_error (err:error) =
  let ctx, msg, _ = err in
  Format.fmt2 "%s%s" (print_context ctx) (Errors.Msg.rendermsg msg)

instance showable_error : showable error = { show = print_error }

let print_error_short (err:error) =
  let _, msg, _ = err in
  Errors.Msg.rendermsg msg

let error_code (err:error) : ML (option Errors.error_code) =
  let _, _, c = err in c

let error_message (err:error) : ML Errors.error_message =
  let _, msg, _ = err in msg

(* The position of the innermost term of the error's context that has one. *)
let error_range (err:error) : ML (option R.t) =
  let ctx, _, _ = err in
  let ok (r:R.t) : ML bool = R.file_of_use_range r <> R.file_of_use_range R.dummyRange in
  let ctx_range (c:context_term) : ML (option R.t) =
    match c with
    | CtxRel _ (SUBTYPING (Some (tm, _))) _ -> if ok tm.pos then Some tm.pos else None
    | CtxTerm t -> if ok t.pos then Some t.pos else None
    | CtxRel t0 _ _ -> if ok t0.pos then Some t0.pos else None
  in
  List.tryPick (fun (_, c) -> match c with None -> None | Some c -> ctx_range c) ctx.error_context

let precondition = option typ

let success a = a & precondition

type hash_entry = {
   he_term:term;
   he_gamma:list binding;
   he_eff: eff;
   he_typ: typ;
   he_facts: facts
}

type guard_entry = {
  ge_gamma: list binding
}

type cache_t = {
  term_map : FStarC.Syntax.Hash.term_map hash_entry;
  guard_map : FStarC.Syntax.Hash.term_map guard_entry;
}

type __result a =
  | Success of a & cache_t
  | Error of error

module HashTable = FStarC.HashTable
type tc_table = {
  table:HashTable.t term hash_entry;
  guard_table:HashTable.t term guard_entry;
  counter:ref int //version counter
}

instance showable_result #a (_ : showable a) : Tot (showable (__result a)) = {
  show = (function
          | Success (a, _) -> "Success " ^ show a
          | Error e ->   "Error " ^ print_error_short e);
}


let result a = context -> cache_t -> ML (__result (success a))

let equal_term_for_hash t1 t2 =
  FStarC.Profiling.profile (fun _ -> Hash.equal_term t1 t2) None "FStarC.TypeChecker.Core.equal_term_for_hash"
(* A fast path for relating terms, so up to delayed substitutions and solved
   uvars: unlike the cache keys, these terms are not deeply compressed. *)
let equal_term t1 t2 =
  FStarC.Profiling.profile (fun _ -> Hash.equal_term_upto_compress t1 t2) None "FStarC.TypeChecker.Core.equal_term"
let table : tc_table = {
  table = HashTable.create 1048576; //2^20
  guard_table = HashTable.create 1048576; //2^20
  counter = mk_ref 0
} 
type cache_stats_t = { hits : int; misses : int }
let cache_stats = mk_ref { hits = 0; misses = 0 }
let record_cache_hit () =
   let cs = !cache_stats in
    cache_stats := { cs with hits = cs.hits + 1 }
let record_cache_miss () =
   let cs = !cache_stats in
    cache_stats := { cs with misses = cs.misses + 1 }
let reset_cache_stats () =
    cache_stats := { hits = 0; misses = 0 }
let report_cache_stats () = !cache_stats
let clear_memo_table () = 
  HashTable.clear table.table;
  HashTable.clear table.guard_table;
  table.counter := !table.counter + 1

type guard_commit_token = {
  guard_cache: ref (option cache_t);
  guard_counter: int
}

let my_guard_and_tok_t = typ & (unit -> unit)
let empty_token () = ()
let mk_token (cache:cache_t) : ML guard_commit_token =
  { guard_cache = mk_ref (Some cache);
    guard_counter = !table.counter }

let commit_guard_core (g:guard_commit_token) : ML unit =
  if g.guard_counter <> !table.counter
  then (//table has been cleared since the token was issued; drop the cache
      ()
  ) //no need to update the cache, nothing has been evicted
  else (
    let cache = !g.guard_cache in
    match cache with
    | None -> () //cache was already used
    | Some cache ->
      g.guard_cache := None; //invalidate the cache in the token
      FStarC.Syntax.Hash.term_map_fold
        (fun term hash_entry _ -> HashTable.add table.table term hash_entry)
        cache.term_map
        ();
      FStarC.Syntax.Hash.term_map_fold
        (fun term guard_entry _ -> HashTable.add table.guard_table term guard_entry)
        cache.guard_map
        ()
  )
let commit_cache_cb cache : guard_commit_token_cb = fun _ -> commit_guard_core (mk_token cache)
let commit_guard (cb:guard_commit_token_cb) : ML unit = cb()
let commit_guard_and_tok_opt (t:option guard_and_tok_t) =
  match t with
  | None -> ()
  | Some (_, tok) -> commit_guard tok
inline_for_extraction
let return (#a:Type) (x:a) : result a = fun _ cache -> Success ((x, None), cache)

inline_for_extraction
let return_with_guard (#a:Type) (x:a) (g:precondition) : result a = fun _ cache -> Success ((x, g), cache)

let and_pre (p1 p2:precondition) =
  match p1, p2 with
  | None, None -> None
  | Some p, None
    | None, Some p -> Some p
  | Some p1, Some p2 -> Some (U.mk_conj p1 p2)

inline_for_extraction
let (let!) (#a:Type) (#b:Type) (x:result a) (y:a -> ML (result b))
  : result b
  = fun ctx0 cache0 ->
      match x ctx0 cache0 with
      | Success ((x, g1), cache1) ->
        (match y x ctx0 cache1 with
         | Success ((y, g2), cache2) -> Success ((y, and_pre g1 g2), cache2)
         | err -> err)
      | Error err -> Error err

inline_for_extraction
let (and!) (#a:Type) (#b:Type) (x:result a) (y:result b)
  : result (a & b)
  = let! v = x in
    let! u = y in
    return (v, u)

inline_for_extraction
let with_guard (#a #b:Type) (x:result a) (f: either (success a) error -> ML (result b))
: result b
= fun ctx cache ->
    match x ctx cache with
    | Success (r, cache') -> f (Inl r) ctx cache'
    | Error err -> f (Inr err) ctx cache

[@@FStar.Attributes.custard_inline]
let (let?) (#a:Type) (#b:Type) (x:option a) (f: a -> option b)
  : option b
  = match x with
    | None -> None
    | Some x -> f x

let fail_str #a msg : result a = fun ctx cache -> Error (ctx, Errors.mkmsg msg, None)

let fail #a msg : result a = fun ctx cache -> Error (ctx, msg, None)

let fail_code #a (code:Errors.error_code) msg : result a = fun ctx cache -> Error (ctx, msg, Some code)

let fail_propagate #a (err:error) : result a = fun _ cache -> Error err

let dump_context
  : result unit
  = fun ctx cache ->
      Format.print_string (print_context ctx);
      return () ctx cache

inline_for_extraction
let handle_with (#a:Type) (x:result a) (h: unit -> ML (result a))
  : result a
  = fun ctx cache ->
      match x ctx cache with
      | Error _ -> h () ctx cache
      | res -> res

inline_for_extraction
let with_context (#a:Type) (msg:string) (t:option context_term) (x:unit -> ML (result a))
  : result a
  = fun ctx cache ->
     let ctx = { ctx with error_context=((msg,t)::ctx.error_context) } in
     x () ctx cache

let mk_type (u:universe) = S.mk (Tm_type u) R.dummyRange

let is_type (g:env) (t:term)
  : result universe
  = let aux t =
        match (Subst.compress t).n with
        | Tm_type u ->
          return u

        | _ ->
          fail [
            text "Expected a type, got" ^/^ fquotes (pp t)
          ]
    in
    (* Unfold until a [Type] appears, e.g. through [type p (x:t) =
       a:u0{...}] with [u0 = Type0]: the [Unrefine] step has the normalizer
       continue with the sort of every refinement it reaches in head
       position. An ascription it leaves (e.g. the [Type0 <: Type] of [kf 0]
       in tests/custard/KindAbbrev) is stripped and the rest unfolded in
       turn, until nothing changes. No bound is needed: [t] is the type of
       a well-typed term, so it normalizes. *)
    let rec go (t:term) : ML (result universe) =
      handle_with
        (aux t)
        (fun _ ->
          let t' = U.unascribe (N.unfold_whnf' [Env.Unrefine] g.tcenv t) in
          if U.term_eq t t' then aux t' else go t')
    in
    with_context "is_type" (Some (CtxTerm t)) (fun _ -> go t)

let comp_eff (c:comp) : ML eff =
  if U.is_total_comp c then ETot
  else if U.is_tot_or_gtot_comp c then EGhost
  else EEff (U.comp_effect_name c)

let rec is_arrow (g:env) (t:term)
  : result (binder & eff & typ)
  = let rec aux t : ML _ =
        match (Subst.compress t).n with
        | Tm_arrow {b=x; comp=c} ->
          (* A [Pure]/[Ghost] arrow carries no specification any more -- its
             precondition is an implicit binder and its postcondition is part
             of the result type -- and an effect name is always a root effect,
             so the comp's effect is all there is to read off. *)
          let g, x, c = open_comp g x c in
          return (x, comp_eff c, U.comp_result c)

        | Tm_refine {b=x} ->
          is_arrow g x.sort

        | Tm_meta {tm=t}
        | Tm_ascribed {tm=t} ->
          aux t

        | _ ->
          fail [
            text "Expected an arrow, got a" ^/^ doc_of_string (tag_of t) ^^ colon ^/^ fquotes (pp t);
          ]
    in
    with_context "is_arrow" None (fun _ ->
      handle_with
        (aux t)
        (fun _ -> aux (N.unfold_whnf g.tcenv t)))

let check_arg_qual (a:aqual) (b:bqual)
  : result unit
  = match b with
    | Some (Implicit _)
    | Some (Meta _) ->
      begin
      match a with
      | Some ({aqual_implicit=true}) ->
        return ()
      | _ ->
        fail_str "missing arg qualifier implicit"
      end

    | _ ->
      begin
      match a with
      | Some ({aqual_implicit=true}) ->
        fail_str "extra arg qualifier implicit"
      | _ -> return ()
      end

let check_bqual (b0 b1:bqual)
  : ML (result unit)
  = if U.bqual_compat b0 b1
    then return ()
    else fail_str (Format.fmt2 "Binder qualifier mismatch, %s vs %s" (show b0) (show b1))

let check_aqual (a0 a1:aqual)
  : ML (result unit)
  = match a0, a1 with
    | None, None -> return ()
    | Some ({aqual_implicit=b0}), Some ({aqual_implicit=b1}) ->
      if b0 = b1
      then return ()
      else
        fail [
          text "Unequal arg qualifiers: lhs implicit="
          ^^ pp b0 ^/^ text "and rhs implicit=" ^^ pp b1
        ]
    | None, Some { aqual_implicit=false }
    | Some { aqual_implicit=false }, None ->
      return ()
    | _ ->
      fail [
        text "Unequal arg qualifiers: lhs" ^/^ fquotes (pp a0)
        ^^ text "and rhs" ^/^ fquotes (pp a1)
      ]

let check_positivity_qual (rel:relation) (p0 p1:option positivity_qualifier)
  : result unit
  = if CommonBase.check_positivity_qual (SUBTYPING? rel) p0 p1
    then return ()
    else fail_str "Unequal positivity qualifiers"

let mk_forall_l_gen (keep_unit:bool) (us:universes) (xs:binders) (t:term)
  : ML term
  = (* As [Env.close_guard], a quantifier over a null binder of (unrefined)
       [unit], e.g. of a thunk [fun () -> ...], is dropped (unless
       [keep_unit], for the binders of the definition itself, e.g. of
       [let f () = ...], which TcTerm has in its environment when it
       discharges the guard), so that goals handed to tactics, and the
       context of a failed goal, are as with TcTerm. Named binders are kept, e.g. those
       of the thunks of a [calc]: the SMT encoding assumes a quantifier-free
       conjunct of a guard when proving the next ones
       ([ErrorReporting.split_goals]), and keeping the quantifier keeps a
       proof step out of the context of the next. (Other null binders, e.g.
       [_:squash p], are hypotheses and are kept too.) *)
    let vacuous (x:binder) (t:term) : ML bool =
      not keep_unit &&
      S.is_null_binder x &&
      (match (Subst.compress x.binder_bv.sort).n with
       | Tm_fvar fv -> S.fv_eq_lid fv PC.unit_lid
       | _ -> false) &&
      not (mem x.binder_bv (FStarC.Syntax.Free.names t))
    in
    FStarC.List.fold_right2
        (fun u x t -> if vacuous x t then t else U.mk_forall u x.binder_bv t)
        us
        xs
        t

let mk_forall_l us xs t : ML term = mk_forall_l_gen false us xs t

let close_guard (xs:binders) (us:universes) (g:precondition)
  : ML precondition
  = match g with
    | None -> None
    | Some t -> Some (mk_forall_l us xs t)

let close_with_definition (x:binder) (u:universe) (t:term) (g:typ)
: ML typ
= (* Oriented as TcTerm's [e == x] (see [TcUtil.mk_binder_eqn]), which
     is how the hypothesis is shown in the context of a failed goal. *)
  let g' = U.mk_imp (U.mk_eq2 u x.binder_bv.sort t (S.bv_to_name x.binder_bv)) g in
  U.mk_forall u x.binder_bv g'

let close_guard_with_definition (x:binder) (u:universe) (t:term) (g:precondition)
  : ML precondition
  = match g with
    | None -> None
    | Some t' ->
      Some (
       let t' = U.mk_imp (U.mk_eq2 u x.binder_bv.sort t (S.bv_to_name x.binder_bv)) t' in
       U.mk_forall u x.binder_bv t'
      )

(* [exists (x:t). body], with the refinement of [t], if any, stated as a
   conjunct of the body instead of in the sort of the binder. [l_Exists]
   repeats the sort (as its type argument and in the abstraction's binder),
   and the type of an effectful [let] is closed existentially over its
   definition's own type, which is itself such an existential for a chain
   of [let]s (e.g., [hide b && c1 && ... && cn]): keeping the refinement in
   the sort would double the type at every [let]. *)
let mk_exists_unrefined (u:universe) (x:bv) (body:term) : ML term =
  match (Subst.compress (U.flatten_refinement x.sort)).n with
  | Tm_refine {b=y; phi} ->
    let bs, phi = Subst.open_term [S.mk_binder y] phi in
    let phi = Subst.subst [NT((List.hd bs).binder_bv, S.bv_to_name x)] phi in
    U.mk_exists u { x with sort = y.sort } (U.mk_conj phi body)
  | _ -> U.mk_exists u x body

let abs (g:env) (a:typ) (f: binder -> term) : ML term =
  let g, xb = new_binder g a a.pos in
  U.abs [xb] (f xb) None

let weaken_subtyping (p:term) (g:term)
: ML term
= U.mk_imp p g

let push_hypothesis (g:env) (h:term) : ML env =
  let g, h = new_binder g h h.pos in
  g

(* Facts gathered from the types of subterms repeat themselves, e.g. the
   refinement of a variable used several times; stating each once keeps the
   VC small. *)
let dedup_facts (fs:list term) : ML (list term) =
  List.fold_left
    (fun (acc:list term) (f:term) ->
      if BU.for_some (fun (g:term) -> U.term_eq f g) acc then acc else acc @ [f])
    [] fs

(* Whether [d] occurs as a subterm of [t]. *)
let occurs_in (d:term) (t:term) : ML bool =
  let found = mk_ref false in
  let _ = FStarC.Syntax.Visit.visit_term false
            (fun (t:term) -> if not !found && U.term_eq t d then found := true; t) t in
  !found

let no_guard (g:result 'a)
  : result 'a
  = fun ctx cache ->
      match g ({ ctx with no_guard = true}) cache with
      | Success ((x, None), cache) -> Success ((x, None), cache)
      | Success ((x, Some g), cache) -> fail_str (Format.fmt1 "Unexpected guard: %s" (show g)) ctx cache
      | err -> err

let equatable g t = t |> U.leftmost_head |> VCUtil.may_relate_by_smt g.tcenv true

(* Whether an argument of an application, or of an application in an argument
   and so on, binds a variable, e.g. [p ** (exists* x. q x)], or [reveal #(a ->
   nat) f]. The SMT encoding of such a term names it after its free variables
   (e.g., as [Tm_abs_<hash> q] or [Tm_arrow_<hash> a]), so an equation between
   two of them that differ under the binder is beyond the SMT solver, unless
   they are related argument-wise, under the binder. *)
let rec args_contain_binders (t:term) : ML bool =
  let _, args = U.head_and_args_full t in
  BU.for_some (fun (a, _) ->
    match (Subst.compress a).n with
    | Tm_abs _ | Tm_arrow _ | Tm_refine _ -> true
    | Tm_app _ -> args_contain_binders a
    | _ -> false) args

(* Whether a formula is first-order: no quantifier, abstraction, arrow,
   refinement, match or let anywhere in it. *)
let rec quantifier_free (t:term) : ML bool =
  match (Subst.compress t).n with
  | Tm_abs _ | Tm_arrow _ | Tm_refine _ | Tm_match _ | Tm_let _ -> false
  | Tm_app {hd; arg=(a, _)} -> quantifier_free hd && quantifier_free a
  | Tm_meta {tm} | Tm_ascribed {tm} -> quantifier_free tm
  | _ -> true

(* Either of two checks suffices: if both have guards, their disjunction is
   the guard. The caches of both are then dropped, since their entries would
   claim that their own guards, rather than the disjunction, were emitted.
   But a quantifier-free guard of [f1] is taken on its own: a disjunction is
   a burden on the SMT solver, which case-splits on it wherever it is a
   hypothesis, i.e. in every later goal of a split query. *)
let either_guard (f1 f2: unit -> ML (result unit)) : result unit
  = fun ctx cache ->
      match f1 () ctx cache with
      | Success (((), None), cache1) -> Success (((), None), cache1)
      | Success (((), Some p1), cache1) when quantifier_free p1 ->
        Success (((), Some p1), cache1)
      | r1 ->
        match f2 () ctx cache with
        | Success (((), None), cache2) -> Success (((), None), cache2)
        | r2 ->
          match r1, r2 with
          | Success (((), Some p1), _), Success (((), Some p2), _) ->
            Success (((), Some (U.mk_disj p1 p2)), cache)
          | Success (((), Some p1), cache1), Error _ -> Success (((), Some p1), cache1)
          | Error _, Success (((), Some p2), cache2) -> Success (((), Some p2), cache2)
          | Error e, _ -> Error e

let apply_predicate x p = fun e -> Subst.subst [NT(x.binder_bv, e)] p

let is_gtot_comp c = U.is_tot_or_gtot_comp c && not (U.is_total_comp c)

let rec context_included (g0 g1: list binding) : ML bool =
  if BU.physical_equality g0 g1 then true else
  match g0, g1 with
  | [], _ -> true

  | b0::g0', b1::g1' ->
     begin
     match b0, b1 with
     | Binding_var x0, Binding_var x1 ->
       if x0.index = x1.index
       then equal_term x0.sort x1.sort
            && context_included g0' g1'
       else context_included g0 g1'

     | Binding_lid (l0, (us0, t0)), Binding_lid (l1, (us1, t1)) ->
       (* A local binding of a top-level name (e.g., a recursive function,
          at a type refined for termination checking) must agree. *)
       if I.lid_equals l0 l1
       then List.length us0 = List.length us1
            && equal_term t0 t1
            && context_included g0' g1'
       else context_included g0 g1'

     | Binding_univ u0, Binding_univ u1 ->
       if I.ident_equals u0 u1
       then context_included g0' g1'
       else context_included g0 g1'

     | _ ->
       false
     end

  | _ -> false

(* Replace all the *use* ranges in [t] by the use range in [r]. *)
let replace_all_use_ranges (r:Range.t) (t:term) : ML term =
  let ur = Range.use_range r in
  t |> Syntax.Visit.visit_term false (fun t ->
    { t with pos = Range.set_use_range t.pos ur })

let get_cache () : result cache_t = fun _ cache -> Success ((cache,None), cache)
let put_cache (cache:cache_t) : result unit = fun _ _ -> Success (((), None), cache)

let raw_lookup (e:term) : result (option hash_entry) =
  let! cache = get_cache() in
  match FStarC.Syntax.Hash.term_map_lookup e cache.term_map with
  | Some he ->
    return (Some he)
  | None ->
    return (HashTable.try_find table.table e)

let raw_lookup_guard (e:term) : result (option guard_entry) =
  let! cache = get_cache() in
  match FStarC.Syntax.Hash.term_map_lookup e cache.guard_map with
  | Some he ->
    return (Some he)
  | None ->
    return (HashTable.try_find table.guard_table e)

let insert_guard (g:env) (guard:typ)
  : result unit
  = let! cache = get_cache () in
    put_cache {cache with guard_map = FStarC.Syntax.Hash.term_map_add guard { ge_gamma = g.tcenv.gamma } cache.guard_map }

(* [compress_shared t] is [t] with its delayed substitutions pushed and its
   solved uvars replaced by their solutions throughout. Unlike
   [Compress.deep_compress], it returns [t] itself if [t] is already
   compressed, and otherwise shares every subterm of [t] that is; and it
   leaves lazy terms and quotations as they are, so the result means the
   same as [t] to Core and can be checked in its place. *)
let rec compress_shared (t:term) : ML term =
  let same (#a:Type) (x y:a) = BU.physical_equality x y in
  let t0 = Subst.compress t in
  let rebuild n = S.mk n t0.pos in
  match t0.n with
  | Tm_uinst (f, us) ->
    let f' = compress_shared f in
    let us' = map_shared compress_univ_shared us in
    if same f f' && same us us' then t0 else rebuild (Tm_uinst (f', us'))
  | Tm_type u ->
    let u' = compress_univ_shared u in
    if same u u' then t0 else rebuild (Tm_type u')
  | Tm_app {hd; arg=(a, q)} ->
    let hd' = compress_shared hd in
    let a' = compress_shared a in
    if same hd hd' && same a a' then t0 else rebuild (Tm_app {hd=hd'; arg=(a', q)})
  | Tm_abs {b; body; rc_opt} ->
    let b' = compress_binder_shared b in
    let body' = compress_shared body in
    if same b b' && same body body' then t0 else rebuild (Tm_abs {b=b'; body=body'; rc_opt})
  | Tm_arrow {b; comp} ->
    let b' = compress_binder_shared b in
    let comp' = compress_comp_shared comp in
    if same b b' && same comp comp' then t0 else rebuild (Tm_arrow {b=b'; comp=comp'})
  | Tm_refine {b; phi} ->
    let b' = compress_bv_shared b in
    let phi' = compress_shared phi in
    if same b b' && same phi phi' then t0 else rebuild (Tm_refine {b=b'; phi=phi'})
  | Tm_match {scrutinee; ret_opt; brs; rc_opt} ->
    let scrutinee' = compress_shared scrutinee in
    let brs' = map_shared compress_branch_shared brs in
    if same scrutinee scrutinee' && same brs brs' then t0
    else rebuild (Tm_match {scrutinee=scrutinee'; ret_opt; brs=brs'; rc_opt})
  | Tm_ascribed {tm; asc=(tc, tac, eq); eff_opt} ->
    let tm' = compress_shared tm in
    let tc' =
      match tc with
      | Inl t -> let t' = compress_shared t in if same t t' then tc else Inl t'
      | Inr c -> let c' = compress_comp_shared c in if same c c' then tc else Inr c'
    in
    if same tm tm' && same tc tc' then t0
    else rebuild (Tm_ascribed {tm=tm'; asc=(tc', tac, eq); eff_opt})
  | Tm_let {lbs=(is_rec, lbs); body} ->
    let lbs' = map_shared compress_letbinding_shared lbs in
    let body' = compress_shared body in
    if same lbs lbs' && same body body' then t0
    else rebuild (Tm_let {lbs=(is_rec, lbs'); body=body'})
  | Tm_meta {tm; meta} ->
    let tm' = compress_shared tm in
    let meta' =
      match meta with
      | Meta_monadic (m, ty) ->
        let ty' = compress_shared ty in if same ty ty' then meta else Meta_monadic (m, ty')
      | Meta_monadic_lift (m1, m2, ty) ->
        let ty' = compress_shared ty in if same ty ty' then meta else Meta_monadic_lift (m1, m2, ty')
      | _ -> meta
    in
    if same tm tm' && same meta meta' then t0 else rebuild (Tm_meta {tm=tm'; meta=meta'})
  | _ -> t0

and map_shared (#a:Type) (f:a -> ML a) (l:list a) : ML (list a) =
  match l with
  | [] -> l
  | x::xs ->
    let x' = f x in
    let xs' = map_shared f xs in
    if BU.physical_equality x x' && BU.physical_equality xs xs' then l else x'::xs'

and compress_univ_shared (u:universe) : ML universe =
  let u0 = Subst.compress_univ u in
  match u0 with
  | U_succ v ->
    let v' = compress_univ_shared v in
    if BU.physical_equality v v' then u0 else U_succ v'
  | U_max us ->
    let us' = map_shared compress_univ_shared us in
    if BU.physical_equality us us' then u0 else U_max us'
  | _ -> u0

and compress_bv_shared (x:bv) : ML bv =
  let sort' = compress_shared x.sort in
  if BU.physical_equality x.sort sort' then x else { x with sort = sort' }

and compress_binder_shared (b:binder) : ML binder =
  let bv' = compress_bv_shared b.binder_bv in
  if BU.physical_equality b.binder_bv bv' then b else { b with binder_bv = bv' }

and compress_comp_shared (c:comp) : ML comp =
  match c.n with
  | Comp ct ->
    let t' = compress_shared ct.result_typ in
    if BU.physical_equality ct.result_typ t' then c
    else S.mk_comp' (Comp { ct with result_typ = t' }) c.pos

and compress_branch_shared (br:branch) : ML branch =
  let (p, w, body) = br in
  let body' = compress_shared body in
  if BU.physical_equality body body' then br else (p, w, body')

and compress_letbinding_shared (lb:letbinding) : ML letbinding =
  let typ' = compress_shared lb.lbtyp in
  let def' = compress_shared lb.lbdef in
  if BU.physical_equality lb.lbtyp typ' && BU.physical_equality lb.lbdef def' then lb
  else { lb with lbtyp = typ'; lbdef = def' }

(* The cache is keyed by syntactic equality (FStarC.Syntax.Hash.equal_term),
   which does not look through delayed substitutions or solved uvars, so the
   keys are compressed. A key shares with the term it is the key of, and
   [memo_check] checks the key, whose subterms are then their own keys: a
   copy per cache entry would be quadratic in the depth of the term. Parts of
   a term that [compress_shared] does not compress (e.g., attributes) can
   only cause cache misses. *)
let cache_key (t:term) : ML term = compress_shared t

let guard (g:env) (guard:typ)
  : result unit
  = fun ctx cache ->
    let guard = cache_key guard in
    (match! raw_lookup_guard guard with
     | Some ge ->
       if ge.ge_gamma `context_included` g.tcenv.gamma
       then return () //cache hit 
       else (
         insert_guard g guard ;!
         return_with_guard () (Some guard)
       )
     | _ ->
       insert_guard g guard ;!
       return_with_guard () (Some guard)) ctx cache


(* Emit [guard], a transformation (closure, weakening) of a guard that a
   sub-computation emitted and whose guard the caller has consumed. It must
   not be dropped as a cache hit: when the transformation is trivial (e.g.,
   closing over no binders), the entry found is the one just inserted by the
   sub-computation, whose guard is not otherwise part of the result. *)
let reemit_guard (g:env) (guard:typ)
  : result unit
  = fun ctx cache ->
    let guard = cache_key guard in
    (insert_guard g guard ;!
     return_with_guard () (Some guard)) ctx cache

let with_binders (#a:Type) (initial_env:env) (xs:binders) (us:universes) (f:result a)
  : result a
  = with_guard f
    (function
      | Inr err -> fail_propagate err
      | Inl (res, None) -> return res
      | Inl (res, Some form) ->
        let form = mk_forall_l_gen initial_env.at_top us xs form in
        reemit_guard initial_env form ;!
        return res)
  
(* As [with_binders] for one binder; if its sort is a refinement
   [y:t{phi}], quantifies over [t] and assumes [phi], as TcTerm's guards
   for the domains of arrows do (see [Rel]): the refinement is then shown
   as a hypothesis in the context of a failed goal. *)
let with_binder_unrefined (#a:Type) (initial_env:env) (x:binder) (u:universe) (f:result a)
  : ML (result a)
  = match (Subst.compress (U.flatten_refinement x.binder_bv.sort)).n with
    | Tm_refine {b=y; phi} ->
      with_guard f
      (function
        | Inr err -> fail_propagate err
        | Inl (res, None) -> return res
        | Inl (res, Some form) ->
          let phi = Subst.subst [DB(0, x.binder_bv)] phi in
          let xb = { x with binder_bv = { x.binder_bv with sort = y.sort } } in
          (* Not twice, e.g. for [x:t{phi}] related to [t{psi}], whose guard
             is already [phi ==> psi]. *)
          let already =
            match FStarC.Syntax.Formula.destruct_typ_as_formula form with
            | Some (FStarC.Syntax.Formula.BaseConn (l, [(p, _); _])) -> I.lid_equals l PC.imp_lid && U.term_eq p phi
            | _ -> false
          in
          let form = mk_forall_l [u] [xb] (if already then form else U.mk_imp phi form) in
          reemit_guard initial_env form ;!
          return res)
    | _ -> with_binders initial_env [x] [u] f

let with_definition (#a:Type) (initial_env:env) (x:binder) (u:universe) (t:term) (f:result a)
  : result a
  = with_guard f
    (function
      | Inr err -> fail_propagate err
      | Inl (res, None) -> return res
      | Inl (res, Some form) ->
        let form = close_with_definition x u t form in
        reemit_guard initial_env form ;!
        return res)

let weaken #a (initial_env:env) (p:term) (f:result a)
: result a
= with_guard f
  (function
    | Inr err -> fail_propagate err
    | Inl (res, None) -> return res
    | Inl (res, Some form) ->
      let form = weaken_subtyping p form in
      reemit_guard initial_env form ;!
      return res)

(* Weaken the guard of [f] with a branch hypothesis (see
   [branch_conditions]), unless it is trivial. *)
let weaken_branch #a (initial_env:env) (hyp:typ) (f:result a)
: ML (result a)
= if U.is_t_true hyp then f else
  with_guard f
  (function
    | Inr err -> fail_propagate err
    | Inl (res, None) -> return res
    | Inl (res, Some form) ->
      reemit_guard initial_env (U.mk_imp hyp form) ;!
      return res)

(* Label the guard of [f] with [msg], at [r], for the SMT solver to report
   when it cannot prove it (see [ErrorReporting.split_goals], where the
   innermost label wins). The message is only computed if there is a guard. *)
let label_guard (#a:Type) (g:env) (r:R.t) (msg:unit -> ML Errors.error_message) (f:result a)
  : result a
  = with_guard f
    (function
      | Inr err -> fail_propagate err
      | Inl (res, None) -> return res
      | Inl (res, Some form) ->
        reemit_guard g (VCUtil.label (msg ()) r form) ;!
        return res)

(* Locate the goals of the guard of [f] at [r], unless they have a more
   precise position (within [r]): the message "Could not prove
   post-condition" is only a position for [ErrorReporting], which reports an
   inner label, if any, or the message of an outer one, instead. E.g. the
   guard of checking a function body against its annotated computation type
   is located at the body, as by TcTerm (see [TcTerm.check_expected_effect]). *)
let label_position (#a:Type) (g:env) (r:R.t) (f:result a)
  : result a
  = label_guard g r (fun () -> Errors.mkmsg "Could not prove post-condition") f

let label_postcondition (#a:Type) (g:env) (at:term) (f:result a)
  : result a
  = label_position g at.pos f

(* As TcTerm (see [TcTerm.value_check_expected_typ]), the guard of a subtyping
   [t0 <: t1] of a term [e] is labeled "Subtyping check failed" at [e], except
   for a value of type [unit] at [squash p], e.g. a [()] given for a
   precondition: reporting that as "expected squash p, got unit" would bury
   the obligation [p], which is only located at [e]. *)
let label_subtyping (#a:Type) (g:env) (e:term) (t0 t1:typ) (f:result a)
  : ML (result a)
  = let is_value =
      match (Subst.compress (U.unmeta e)).n with
      | Tm_constant _ | Tm_name _ -> true
      | _ -> false
    in
    if is_value && U.is_unit t0 && Some? (U.un_squash t1)
    then (* The obligation is still reported at [e], as by TcTerm. *)
      label_position g e.pos f
    else label_guard g e.pos (fun () -> Err.subtyping_failed g.tcenv t0 t1 ()) f

let weaken_with_guard_formula env (p:CommonBase.guard_formula) (g:result 'a)
  = match p with
    | CommonBase.Trivial -> g
    | CommonBase.NonTrivial p -> weaken env p g

let insert (g:env) (e:term) (res:success (eff & typ & facts))
: result unit
= let! cache = get_cache() in
  let (eff, typ, facts), _ = res in
  let entry = {
      he_term = e;
      he_gamma = g.tcenv.gamma;
      he_eff = eff;
      he_typ = typ;
      he_facts = facts
  }
  in
  debug g (fun _ ->
    Format.print3 "Inserting into cache\n %s : %s\nwith\n\tenv %s\n"
      (show e)
      (show typ)
      (show g.tcenv.gamma));
  let new_cache = { cache with term_map = FStarC.Syntax.Hash.term_map_add e entry cache.term_map } in
  put_cache new_cache

let lookup (g:env) (e:term) : result (eff & typ & facts) =
  match! raw_lookup e with
  | None ->
    record_cache_miss ();
    fail_str "not in cache"
  | Some he ->
     if he.he_gamma `context_included` g.tcenv.gamma
     && not !dbg_DisableCoreCache
     then (
       record_cache_hit();
       if !dbg then
         Format.print4 "cache hit\n %s : %s\nmatching\n\tenv0 %s\n\tenv1 %s\n"
           (show e)
           (show he.he_typ)
           (show g.tcenv.gamma)
           (show he.he_gamma);
      
      (* Important: replace all the use ranges in the cached type for the
        use range of the term being looked up. Otherwise, the cached ranges will
        refer to the original term we cached, and could be completely unrelated
        to [e] here. See https://github.com/FStarLang/pulse/issues/416. *)
       let ty = replace_all_use_ranges (pos e) he.he_typ in
       return (he.he_eff, ty, he.he_facts)
     )
     else (
       // record_cache_miss();
       fail_str "not in cache"
     )

let check_no_escape (bs:binders) t =
    let xs = FStarC.Syntax.Free.names t in
    if BU.for_all (fun b -> not (mem b.binder_bv xs)) bs
    then return ()
    else fail_str "Name escapes its scope"

let rec map (#a #b:Type) (f:a -> ML (result b)) (l:list a) : ML (result (list b)) =
  match l with
  | [] -> return []
  | hd::tl ->
    let! hd = f hd in
    let! tl = map f tl in
    return (hd::tl)

let mapi (#a #b:Type) (f:int -> a -> ML (result b)) (l:list a) : ML (result (list b)) =
  let rec aux i l : ML _ =
    match l with
    | [] -> return []
    | hd::tl ->
      let! hd = f i hd in
      let! tl = aux (i + 1) tl in
      return (hd::tl)
  in
  aux 0 l

let rec map2 (#a #b #c:Type) (f:a -> b -> ML (result c)) (l1:list a) (l2:list b) : ML (result (list c)) =
  match l1, l2 with
  | [], [] -> return []
  | hd1::tl1, hd2::tl2 ->
    let! hd = f hd1 hd2 in
    let! tl = map2 f tl1 tl2 in
    return (hd::tl)

let rec fold (#a #b:Type) (f:a -> b -> ML (result a)) (x:a) (l:list b) : ML (result a) =
  match l with
  | [] -> return x
  | hd::tl ->
    let! x = f x hd in
    fold f x tl

let rec fold2 (#a #b #c:Type) (f:a -> b -> c -> ML (result a)) (x:a) (l1:list b) (l2:list c) : ML (result a) =
  match l1, l2 with
  | [], [] -> return x
  | hd1::tl1, hd2::tl2 ->
    let! x = f x hd1 hd2 in
    fold2 f x tl1 tl2

let rec iter2 (xs ys:list 'a) (f: 'a -> 'a -> 'b -> ML (result 'b)) (b:'b)
  : ML (result 'b)
  = match xs, ys with
    | [], [] -> return b
    | x::xs, y::ys ->
      let! b = f x y b in
      iter2 xs ys f b
    | _ -> fail_str "Lists of differing length"

let is_non_informative g t = N.non_info_norm g t

let non_informative g t
  : ML bool
  = is_non_informative g.tcenv t

let mk_comp_of_eff (m:I.lident) (t:typ) : ML comp =
  S.mk_Comp { effect_name = m; result_typ = t; flags = []; source_effect_name = m }

let as_comp (g:env) (et: (eff & typ))
  : ML comp
  = match et with
    | ETot, t -> S.mk_Total t
    | EGhost, t ->
      if non_informative g t
      then S.mk_Total t
      else S.mk_GTotal t
    | EEff m, t -> mk_comp_of_eff m t

let comp_as_eff_and_type (c:comp)
  : ML (eff & typ)
  = comp_eff c, U.comp_result c

let lid_to_eff (l:I.lident) : ML eff =
  if PC.is_tot_lid l then ETot
  else if PC.is_gtot_lid l then EGhost
  else EEff l

let is_tot_or_ghost_eff (e:eff) : ML bool =
  match e with
  | ETot | EGhost -> true
  | _ -> false

(* Whether [t], the type of some term, syntactically says that the term is a
   type or a proposition. *)
let is_type_or_prop (t:typ) : ML bool =
  match (Subst.compress (U.unrefine t)).n with
  | Tm_type _ -> true
  | _ -> (
    match (U.un_uinst (Subst.compress (U.unrefine t))).n with
    | Tm_fvar fv -> S.fv_eq_lid fv PC.prop_lid || S.fv_eq_lid fv PC.eqtype_lid
    | _ -> false
  )

(** Facts (see [facts]) *)

let no_facts_l () : ML (Thunk.t (list term)) = Thunk.mkv []

let no_facts () : ML facts =
  let none = no_facts_l () in
  { f_sub = none; f_term = none; f_tail = none }

let facts_concat (fs:list (Thunk.t (list term))) : ML (Thunk.t (list term)) =
  Thunk.mk (fun () -> List.flatten (List.map Thunk.force fs))

let facts_subst (s:subst_t) (fs:Thunk.t (list term)) : ML (Thunk.t (list term)) =
  Thunk.map (List.map (Subst.subst s)) fs

(* The facts [fs] with the variables [xs], of universes [us], going out of
   scope, e.g. the variable of a [let] that cannot be substituted by its
   (effectful) definition. Rather than drop the facts that mention them,
   they are stated together under an existential over [xs], which the
   variables themselves witness: as in [TcUtil.close_escaping], what the
   facts say about other variables through [xs] then survives. *)
let facts_exists (xs:list bv) (us:list universe) (fs:Thunk.t (list term)) : ML (Thunk.t (list term)) =
  Thunk.map
    (fun (fs:list term) ->
      let mentions_xs (f:term) : ML bool =
        let fvs = FStarC.Syntax.Free.names f in
        BU.for_some (fun (x:bv) -> mem x fvs) xs
      in
      let bound, free = List.partition mentions_xs fs in
      match bound with
      | [] -> free
      | _ -> List.fold_right2 U.mk_exists us xs (U.mk_conj_l bound) :: free)
    fs

(* What the type [t_a] of the pure term [a] says about it. *)
let type_facts (g:env) (unfold_ok:bool) (a:term) (t_a:typ)
  : ML (list term)
  = let refinement (t:typ) : ML (option term) =
      match (Subst.compress (U.flatten_refinement t)).n with
      | Tm_refine {b=x; phi} ->
        let bs, phi = Subst.open_term [S.mk_binder x] phi in
        Some (Subst.subst [NT((List.hd bs).binder_bv, a)] phi)
      | _ -> None
    in
    match refinement t_a with
    | Some f -> [f]
    | None ->
      match U.un_squash t_a with
      | Some p -> [p]
      | None ->
        if not unfold_ok then [] else
        match refinement (N.normalize_refinement N.whnf_steps g.tcenv t_a) with
        | Some f -> [f]
        | None -> []

(* The [f_term] of [a], of effect [eff] and type [t_a], whose subterms have
   the facts [sub]. *)
let term_facts (g:env) (a:term) (eff:eff) (t_a:typ) (sub:Thunk.t (list term))
  : ML (Thunk.t (list term))
  = Thunk.mk (fun () ->
    (* What the type of a variable or a constant says about it is already
       in scope: the SMT encoding assumes it where the variable is bound, or
       with the constant's declaration. Restating it at every use only
       swells the VC. *)
    match (Subst.compress (U.unmeta a)).n with
    | Tm_name _ | Tm_constant _ -> []
    | Tm_fvar _ | Tm_uinst _ ->
      (* Except for a top-level proof, e.g. [let _ = lift_emp in e] where
         [lift_emp : squash p], as TcTerm's [bind] adds [p]. *)
      (match U.un_squash t_a with
       | Some p -> [p]
       | None -> [])
    | _ ->
    if not (is_tot_or_ghost_eff eff) then []
    (* [a] is a type or a proposition, e.g. the [p] of [assert p]: what the
       types of its subterms say is a specification-level fact that the SMT
       encoding already derives from their typing, and TcTerm never states
       it. Stating it anyway can derail the solver (everparse's
       [LowParse.BitFields.uint_set_bitfield_set_bitfield_same_gen]). *)
    else if is_type_or_prop t_a then []
    else
      (* The result type of a top-level function is stated as a fact only
         when it is a refinement, e.g. [c:U64.t{v a >= v b ==> v c = ...}]
         for [U64.gte_mask a b], not when it is a name that unfolds to one,
         e.g. [pos] for [pow2 n]. The SMT solver gets the latter through
         the function's typing axiom, as with TcTerm. Stating it at every
         use only adds hypotheses to the VC, which, being about nonlinear
         terms, can derail the solver
         ([FStar.Math.Lemmas.pow2_multiplication_modulo_lemma_1]). *)
      let top_level_head =
        match (U.un_uinst (U.head_of (U.unmeta a))).n with
        | Tm_fvar _ -> true
        | _ -> false
      in
      type_facts g (not top_level_head) a t_a @ Thunk.force sub)

(* The facts that [do_check] gathers from the subterms of a term, from
   which [mk_facts] makes the term's [facts]: [s_sub] is its [f_sub], and
   [s_tail] its [f_tail], if not its [f_term]. *)
type sub_facts = {
  s_sub : Thunk.t (list term);
  s_tail: option (Thunk.t (list term));
}

let no_sub_facts () : ML sub_facts = { s_sub = no_facts_l (); s_tail = None }

(* For a term with no [let]s to end with, e.g. a function or a [match]. *)
let no_tail_facts () : ML sub_facts =
  let none = no_facts_l () in
  { s_sub = none; s_tail = Some none }

(* Those of the term wrapped (e.g. ascribed) in another, of the same value. *)
let inner_facts (f:facts) : sub_facts = { s_sub = f.f_sub; s_tail = Some f.f_tail }

let mk_facts (g:env) (e:term) (eff:eff) (t:typ) (s:sub_facts) : ML facts =
  let tf = term_facts g e eff t s.s_sub in
  { f_sub = s.s_sub;
    f_term = tf;
    f_tail = (match s.s_tail with Some tl -> tl | None -> tf) }

(* Those of [let x = def in body], from those of [def] and [body]: a pure
   [def] is substituted for [x], whose facts are those of [def]; otherwise,
   those of [body] are closed over [x], of universe [u]. *)
let let_facts (pure_def:bool) (def:term) (x:bv) (u:universe) (fdef fbody:facts) : ML sub_facts =
  if pure_def
  then
    let s = [NT(x, def)] in
    { s_sub = facts_concat [fdef.f_term; facts_subst s fbody.f_sub];
      s_tail = Some (facts_subst s fbody.f_tail) }
  else
    { s_sub = facts_exists [x] [u] fbody.f_sub;
      s_tail = Some (facts_exists [x] [u] fbody.f_tail) }

(* Those of [let rec xs = ... in body], of universes [us]: the recursive
   names are not definitions that could be substituted, so the facts of the
   body are closed over them. *)
let letrec_facts (xs:binders) (us:list universe) (fbody:facts) : ML sub_facts =
  let xs = List.map (fun (b:binder) -> b.binder_bv) xs in
  { s_sub = facts_exists xs us fbody.f_sub;
    s_tail = Some (facts_exists xs us fbody.f_tail) }

(* [e], of type [t_e] and effect [eff], was expected to have effect
   [target_eff] (and type [target_t]): reported as TcTerm's
   [Err.computed_computation_type_does_not_match_annotation], whose computed
   type carries the equation TcTerm adds to the type of a pure term. *)
let fail_effect_mismatch (#a:Type) (g:env) (e:term) (t_e:typ) (e_eff:eff) (target_t:typ) (target_eff:eff)
  : ML (result a)
  = let name (x:eff) : ML string =
      match x with
      | ETot -> "Tot"
      | EGhost -> "GTot"
      | EEff m -> show m
    in
    let t_e =
      match e_eff with
      | ETot -> U.comp_result (VCUtil.maybe_assume_result_eq_pure_term g.tcenv e (S.mk_Total t_e))
      | EGhost -> U.comp_result (VCUtil.maybe_assume_result_eq_pure_term g.tcenv e (S.mk_GTotal t_e))
      | _ -> t_e
    in
    let ppt = N.term_to_doc g.tcenv in
    fail_code Errors.Fatal_ComputedTypeNotMatchAnnotation [
      prefix 2 1 (text "Computed type") (ppt t_e) ^/^
      prefix 2 1 (text "and effect") (text (name e_eff)) ^/^
      prefix 2 1 (text "is not compatible with the annotated type") (ppt target_t) ^/^
      prefix 2 1 (text "and effect") (text (name target_eff))
    ]

(* The least effect both [e0] and [e1] lift to, if any. *)
let join_eff (g:env) (e0 e1:eff)
  : ML (result eff)
  = match e0, e1 with
    | ETot, e
    | e, ETot -> return e
    | EGhost, EGhost -> return EGhost
    | _ ->
      (* As [N.ghost_to_pure2]: composed with an erasable effect, GHOST is
         promoted to PURE, its erasability being accounted for by the other
         effect. *)
      let promote e other =
        match e, other with
        | EGhost, EEff m when Env.is_erasable_effect g.tcenv m -> ETot
        | _ -> e
      in
      let e0, e1 = promote e0 e1, promote e1 e0 in
      if ETot? e0 then return e1 else
      if ETot? e1 then return e0 else
      match Env.join_opt g.tcenv (eff_to_lid e0) (eff_to_lid e1) with
      | Some m -> return (lid_to_eff m)
      | None ->
        fail [
          text "Computations with effects" ^/^ pp (eff_to_lid e0)
          ^/^ text "and" ^/^ pp (eff_to_lid e1) ^/^ text "cannot be composed"
        ]

let rec join_eff_l (g:env) (es:list eff)
  : ML (result eff)
  = match es with
    | [] -> return ETot
    | e::es ->
      let! e' = join_eff_l g es in
      join_eff g e e'

(* [e0] may be used where [e1] is expected. *)
let sub_eff (g:env) (e0 e1:eff) : ML bool =
  match e0, e1 with
  | ETot, _ -> true
  | EGhost, EGhost -> true
  | EGhost, ETot -> false
  | _, ETot -> false
  (* GHOST lifts to an erasable effect via PURE, as in [N.ghost_to_pure2] *)
  | EGhost, EEff m when Env.is_erasable_effect g.tcenv m ->
    Some? (Env.monad_leq g.tcenv PC.primitive_pure_lid m)
  | _ ->
    Some? (Env.monad_leq g.tcenv (eff_to_lid e0) (eff_to_lid e1))

let guard_not_allowed
  : result bool
  = fun ctx cache -> Success ((ctx.no_guard, None), cache)

let unfolding_ok
  : result bool
  = fun ctx cache -> Success ((ctx.unfolding_ok, None), cache)



instance showable_tot_or_ghost = {
    show = (function
            | E_Total -> "E_Total"
            | E_Ghost -> "E_Ghost");
}

instance showable_side = {
    show = (function
            | Left -> "Left"
            | Right -> "Right"
            | Both -> "Both"
            | Neither -> "Neither");
}



(* The conditions of a branch, as TcTerm has them (see
   [TcUtil.get_neg_branch_conds]). The path condition of a branch, a
   proposition, is the conjunction of the negations of the conditions of the
   branches before it; [False] after an irrefutable pattern. Given it, the
   branch condition [bc] of a branch (if its pattern is refutable) and the
   equation [eq] of the scrutinee with its pattern, returns:
   - the hypothesis under which the branch is taken, which does not mention
     the pattern variables: the path condition and [bc], as one hypothesis;
   - that, and [eq];
   - the path condition of the next branch.
   Of a branch, the guard is [hyp ==> forall xs. eq ==> G], where [xs] are
   the pattern variables: the equation is the last hypothesis (tactics look
   it up). *)
let branch_conditions (path_condition:typ) (branch_condition:option term) (eq:typ)
  : ML (typ & typ & typ)
  = let hyp =
      match branch_condition with
      | None -> path_condition
      | Some bc -> U.mk_conj_simp path_condition (U.b2t bc)
    in
    let next =
      match branch_condition with
      | None -> U.t_false
      | Some bc -> U.mk_conj_simp path_condition (U.mk_neg (U.b2t bc))
    in
    hyp, U.mk_conj_simp hyp eq, next

let push_branch_hypothesis (g:env) (hyp:typ) : ML env =
  if U.is_t_true hyp then g else push_hypothesis g hyp

(* The obligation that no branch is missing, given the path condition after
   the last branch, labeled as by TcTerm. *)
(* A match whose scrutinee has type bool (up to refinement) and whose
   branches include both constant patterns `true` and `false` (without
   when clauses) is exhaustive, so its residual path condition is false
   and needs no SMT query. Pulse's elaborated `if`s produce many of these. *)
let match_covers_bool (g:env) (t_sc:typ) (brs:list branch) : ML bool =
  let has b =
    List.existsb
      (fun (p, w, _) ->
        None? w &&
        (match p.v with
         | Pat_constant (FStarC.Const.Const_bool b') -> b = b'
         | _ -> false))
      brs
  in
  has true && has false &&
  U.is_fvar PC.bool_lid
    (t_sc |> N.normalize_refinement N.whnf_steps g.tcenv |> U.unrefine)

let exhaustiveness_obligation (r:R.t) (path_condition:typ) : ML (option typ) =
  if U.is_t_false path_condition then None
  else Some (VCUtil.label Err.exhaustiveness_check r (U.mk_imp path_condition U.t_false))

let maybe_relate_after_unfolding (g:Env.env) t0 t1 : ML side =
  let dd0 = Env.delta_depth_of_term g t0 in
  let dd1 = Env.delta_depth_of_term g t1 in

  if dd0 = dd1 then
    Both
  else if CommonBase.delta_depth_greater_than dd0 dd1 then
    Left
  else
    Right

instance showable_rel : showable relation = {
    show = fun rel ->
      match rel with
      | EQUALITY -> "=?="
      | SUBTYPING _ -> "<:?"
}

(*
     G |- e : t0 <: t1 | p

or   G |- t0 <: t1 | p

 *)

(* Failures of [check_relation] without a guard, remembered for the rest of
   the current top-level check. A failed relation is retried in several ways
   (argument-wise, then by unfolding either side, then by a fallback), and the
   retries meet the same subproblems again: relating two long chains of
   definitions that differ, e.g. EverCDDL's environments [env5] and [env4],
   each defined by extending the previous one, revisits each level of the
   chain from every level above it, which is exponential in its length. A
   failure is only reused under the same environment (physically), relation,
   flags and terms; returning a failure is always sound. *)
type relation_failure = {
  rf_tcenv : Env.env;
  rf_unfolding_ok : bool;
  rf_allow_univ : bool;
  rf_at_top : bool;
  rf_error : error;
}

let relation_failures : HashTable.t term (list relation_failure) = HashTable.create 1024

let clear_relation_failures () : ML unit = HashTable.clear relation_failures

let relation_failure_key (rel:relation) (t0 t1:typ) : ML (option term) =
  match rel with
  | EQUALITY -> Some (S.mk_Tm_app U.tand [S.as_arg t0; S.as_arg t1] R.dummyRange)
  | SUBTYPING None -> Some (S.mk_Tm_app U.timp [S.as_arg t0; S.as_arg t1] R.dummyRange)
  | SUBTYPING (Some _) -> None

let with_relation_failure_memo (g:env) (rel:relation) (t0 t1:typ) (f:result unit)
  : result unit
  = fun ctx cache ->
      if not ctx.no_guard then f ctx cache else
      match relation_failure_key rel t0 t1 with
      | None -> f ctx cache
      | Some key ->
        let same (e:relation_failure) : ML bool =
          BU.physical_equality e.rf_tcenv g.tcenv
          && e.rf_unfolding_ok = ctx.unfolding_ok
          && e.rf_allow_univ = g.allow_universe_instantiation
          && e.rf_at_top = g.at_top
        in
        let entries =
          match HashTable.try_find relation_failures key with
          | None -> []
          | Some l -> l
        in
        match List.tryFind same entries with
        | Some e -> Error e.rf_error
        | None ->
          match f ctx cache with
          | Error err ->
            let e = { rf_tcenv = g.tcenv; rf_unfolding_ok = ctx.unfolding_ok;
                      rf_allow_univ = g.allow_universe_instantiation; rf_at_top = g.at_top;
                      rf_error = err } in
            HashTable.add relation_failures key (e :: entries);
            Error err
          | r -> r

let rec check_relation' (g:env) (rel:relation) (t0 t1:typ)
  : ML (result unit)
  = let err (lbl:string) =
        match rel with
        | EQUALITY ->
          fail [
            parens (text lbl) ^/^ text "not equal terms:"
            ^/^ fquotes (pp t0)
            ^/^ text "<>"
            ^/^ fquotes (pp t1)
          ]
        | _ ->
          fail [
            parens (text lbl)
            ^/^ fquotes (pp t0)
            ^/^ text "is not a subtype of"
            ^/^ fquotes (pp t1)
          ]
    in

    let! guard_not_ok = guard_not_allowed in
    let guard_ok = not guard_not_ok in
    let head_matches t0 t1
      : ML bool
      = let head0 = U.leftmost_head t0 in
        let head1 = U.leftmost_head t1 in
        match (U.un_uinst head0).n, (U.un_uinst head1).n with
        | Tm_fvar fv0, Tm_fvar fv1 -> fv_eq fv0 fv1
        | Tm_name x0, Tm_name x1 -> bv_eq x0 x1
        | Tm_constant c0, Tm_constant c1 -> equal_term head0 head1
        | Tm_type _, Tm_type _
        | Tm_arrow _, Tm_arrow _
        | Tm_match _, Tm_match _ -> true
        | _ -> false
    in
    let which_side_to_unfold t0 t1 =
      maybe_relate_after_unfolding g.tcenv t0 t1 in
    (* As [Rel] when SMT is allowed: a recursive definition (e.g.
       [let rec type_of_nat (n:nat) = bool]) may be unfolded too. *)
    (* An unfolding stuck on a match (e.g. of a recursive definition applied
       to a variable) is only taken when [allow_stuck] and the other side is
       a match already: relating two such unfoldings would relate their
       branches, i.e. the definition applied to the pattern variables, which
       unfold again, without end. *)
    let is_match (t:term) : ML bool =
      Tm_match? (Subst.compress (U.unascribe (U.unmeta t))).n
    in
    let unfold_rec_head (allow_stuck:bool) (other:term) (t:term) : ML (option term) =
      match (U.un_uinst (U.leftmost_head t)).n with
      | Tm_fvar fv
          when None? (Env.lookup_nonrec_definition [Env.Unfold delta_constant] g.tcenv fv.fv_name)
            && Some? (Env.lookup_definition [Env.Unfold delta_constant] g.tcenv fv.fv_name) ->
        let t' = N.normalize [Env.UnfoldUntil delta_constant; Env.Weak; Env.HNF; Env.Primops;
                              Env.Beta; Env.Iota; Env.Zeta] g.tcenv t in
        if TEQ.eq_tm g.tcenv t t' = TEQ.Equal then None
        else if is_match (U.leftmost_head t') && not (allow_stuck && is_match other) then None
        else Some t'
      | _ -> None
    in
    (* As [Rel] ([head_matches_delta]), which unfolds with [UnfoldUntil
       delta_constant]: a [match] whose scrutinee only reduces after
       unfolding definitions in it, e.g. [parse_array_kind k 8 2] unfolded
       to [match fldata_array_precond k 8 2 && .. with | true -> .. | _ ->
       ..], is reduced by computing that scrutinee. [Zeta] is left out, as
       in [Rel]. The reduction is kept only if a branch is taken. Reducing
       to head normal form leaves the arguments of constructors as they are,
       e.g. [Some k.lo], on which a primitive equality is stuck, in the
       scrutinee or in that of a nested [match] in the branch taken; if no
       branch is taken then, the [match] is normalized fully. *)
    let reduce_match (t:term) : ML (option term) =
      let reduced t' = if is_match (U.leftmost_head t') then None else Some t' in
      if not (is_match t) then None
      else
        let t' = N.normalize [Env.UnfoldUntil delta_constant; Env.Weak; Env.HNF; Env.Primops;
                              Env.Beta; Env.Iota] g.tcenv t in
        match reduced t' with
        | Some t' -> Some t'
        | None ->
          reduced (N.normalize [Env.UnfoldUntil delta_constant; Env.Weak; Env.Primops;
                                Env.Beta; Env.Iota] g.tcenv t)
    in
    let unfold_head_with (allow_rec:bool) (allow_stuck:bool) (other:term) (t:term) : ML (option term) =
      match N.maybe_unfold_head g.tcenv t with
      | Some t' -> (
        match reduce_match t' with
        | Some t'' -> Some t''
        | None -> Some t')
      | None ->
        match reduce_match t with
        | Some t' -> Some t'
        | None -> if allow_rec then unfold_rec_head allow_stuck other t else None
    in
    let maybe_unfold_side'' (allow_rec:bool) (allow_stuck:bool) side t0 t1
      : ML (option (term & term))
      = let unfold_head other t = unfold_head_with allow_rec allow_stuck other t in
        Profiling.profile (fun _ ->
        match side with
        | Neither -> None
        | Both -> (
          match unfold_head t1 t0,
                unfold_head t0 t1
          with
          | Some t0, Some t1 -> Some (t0, t1)
          | Some t0, None -> Some (t0, t1)
          | None, Some t1 -> Some (t0, t1)
          | _ -> None
        )
        | Left -> (
          match unfold_head t1 t0 with
          | Some t0 -> Some (t0, t1)
          | _ -> None
        )
        | Right -> (
          match unfold_head t0 t1 with
          | Some t1 -> Some (t0, t1)
          | _ -> None
        ))
        None
        "FStarC.TypeChecker.Core.maybe_unfold_side"
    in
    let maybe_unfold_side' (allow_rec:bool) side t0 t1 = maybe_unfold_side'' allow_rec true side t0 t1 in
    let maybe_unfold_side side t0 t1 = maybe_unfold_side' guard_ok side t0 t1
    in
    let maybe_unfold t0 t1
      : result (option (term & term))
      = if! unfolding_ok
        then return (maybe_unfold_side (which_side_to_unfold t0 t1) t0 t1)
        else return None
    in
    let emit_guard t0 t1 =
       match rel with
       | SUBTYPING wit ->
         (* [t0] and [t1] are types, and it suffices
            that the term at hand (or any term of type [t0]) has type [t1]. *)
         let! u0 = universe_of_well_typed_term g t0 in
         let! u1 = universe_of_well_typed_term g t1 in
         begin match wit with
         | Some (tm, fs) -> witness_guard g fs (U.mk_has_type [u0; u1] t0 tm t1)
         | None ->
           let x = S.new_bv None t0 in
           guard g (U.mk_forall u0 x (U.mk_has_type [u0; u1] t0 (S.bv_to_name x) t1))
         end
       | EQUALITY ->
         let! _, t_typ, _ = with_context "checking lhs while emitting guard" None (fun _ -> do_check g t0) in
         let! u = universe_of_well_typed_term g t_typ in
         guard g (U.mk_eq2 u t_typ t0 t1)
    in
    let fallback t0 t1 =
      if guard_ok
      then if equatable g t0
            || equatable g t1
            (* e.g. [x:(match sw with ...){p} <: int] *)
            || equatable g (U.unrefine t0)
            || equatable g (U.unrefine t1)
           then emit_guard t0 t1
           else err "not equatable"
      else err "guards not allowed"
    in
    let maybe_unfold_side_and_retry side t0 t1 =
      let is_app (t:term) : ML bool =
        match (Subst.compress (U.unascribe (U.unmeta t))).n with
        | Tm_app _ | Tm_fvar _ | Tm_uinst _ -> true
        | _ -> false
      in
      let is_match_or_abs (t:term) : ML bool =
        match (Subst.compress (U.unascribe (U.unmeta t))).n with
        | Tm_match _ | Tm_abs _ -> true
        | _ -> false
      in
      let is_refine (t:term) : ML bool =
        match (Subst.compress (U.unascribe (U.unmeta t))).n with
        | Tm_refine _ -> true
        | _ -> false
      in
      let has_definition (t:term) : ML bool =
        match (U.un_uinst (U.leftmost_head t)).n with
        | Tm_fvar fv -> Some? (Env.lookup_definition [Env.Unfold delta_constant] g.tcenv fv.fv_name)
        | Tm_name _ | Tm_bvar _ -> false
        | _ -> true
      in
      let rec bases_match (n:int) (t0:term) (t1:term) : ML bool =
        (* Whether the base types of two refinements come to have the same
           head by unfolding applications, e.g. [nat] and [int], but not
           [sum_type s] (which unfolds to a [match] on [s]) and [t']. *)
        let t0 = U.unascribe (U.unmeta (U.unrefine t0)) in
        let t1 = U.unascribe (U.unmeta (U.unrefine t1)) in
        if head_matches t0 t1 then true
        else if n = 0 || not (is_app t0 && is_app t1) then false
        else match maybe_unfold_side' false (which_side_to_unfold t0 t1) t0 t1 with
             | None -> false
             | Some (t0, t1) -> bases_match (n - 1) t0 t1
      in
      let rec unfold_to_match (n:int) (t0:term) (t1:term) : ML bool =
        if head_matches t0 t1 then true
        else if (is_match t0 && is_app t1) || (is_app t0 && is_match t1) then
          (* One side unfolded to a [match], the other is still an
             application: unfold that further. If it has no definition
             (e.g. [p ** q] against [match c with | true -> p ** q | ...],
             the unfolding of a [let side .. = if c then p ** q else ..]), the
             equation between it and the [match] is what the SMT solver can
             prove, by cases, while one between it and the folded side would
             need the solver to unfold that, and then to relate the
             abstractions in its body (e.g., [exists* x. ..]) to those of
             the other side, which are encoded apart. *)
          let side = if is_app t0 then Left else Right in
          match (if n = 0 then None else maybe_unfold_side' false side t0 t1) with
          | Some (t0, t1) -> unfold_to_match (n - 1) (U.unascribe (U.unmeta t0)) (U.unascribe (U.unmeta t1))
          | None -> not (has_definition (if is_app t0 then t0 else t1))
        else if is_refine t0 || is_refine t1 then
          (* One side unfolded to a refinement, e.g. [pfr f] to [x:int{f x
             == true}] against [ct k] for a recursive [ct]: unfolding only
             helps if the base type of the refinement comes to match the
             other side, e.g. [nat] against [int]. Otherwise the guard is
             better stated on the terms as they are, [pfr f == ct k], which
             the SMT solver can prove from the equations of [ct]: the
             encoding of the refinement in it would be a fresh term,
             unrelated to that of the body of [pfr]. *)
          bases_match n t0 t1
        else if not (is_app t0 && is_app t1) then
          (* Unfolding reached a [match] or a [fun], e.g. [maybe_close
             a c] against [close a]: relating that to the other side
             can only produce a guard about the unfoldings, an equation
             between a [fun] and a [match] which the SMT solver can
             seldom prove. Treat it as a mismatch, so that the guard is
             stated on the terms as they are. *)
          not (is_match_or_abs t0 || is_match_or_abs t1)
        else if n = 0 then false
        else match maybe_unfold_side' false (which_side_to_unfold t0 t1) t0 t1 with
             | None -> false
             | Some (t0, t1) -> unfold_to_match (n - 1) (U.unascribe (U.unmeta t0)) (U.unascribe (U.unmeta t1))
      in
      (* As [Rel] ([head_matches_delta]): when the unfoldings of two
         applications never come to have the same head, the guard is stated
         on the terms as they are, not on their unfoldings, which the SMT
         patterns of lemmas about them would not match, e.g. [denote_term
         (elab_exp (open_exp e x)) == open_term (denote_term (elab_exp e)) x]
         where [open_term] unfolds to an application of another recursive
         function. *)
      let is_name (t:term) : ML bool =
        match (Subst.compress (U.unascribe (U.unmeta t))).n with
        | Tm_name _ -> true
        | _ -> false
      in
      (* Likewise when one side is a variable, e.g. the index [g] of a
         pattern-bound [h:typing g e t] against [extend_gen x t_x g']: the
         unfolding of the other side can only help if it closes the relation
         outright; otherwise [g == extend_gen x t_x g'] is what the SMT
         solver can prove, from the inversion of [h]'s type. *)
      (* Whether unfolding the other side of a variable, recursive
         definitions included, closes the relation outright, e.g. [l] and
         [[] @ l] under [--no_smt]: [op_At] unfolds to [append [] l], which
         only reduces to [l] by unfolding [append]. [Zeta] is used only
         here, in a single normalization to head normal form of the
         non-variable side, and not in the general unfolding of the heads
         of applications: there, [match]es of recursive definitions could
         unfold forever, e.g. relating [f l] and [g l] for two recursive
         functions that are equal by a lemma. *)
      let closes_with_zeta () =
        let zeta t =
          if is_name t then t
          else N.normalize [Env.UnfoldUntil delta_constant; Env.Weak; Env.HNF; Env.Primops;
                            Env.Beta; Env.Iota; Env.Zeta] g.tcenv t
        in
        let t0'' = zeta t0 in
        let t1'' = zeta t1 in
        if U.term_eq t0 t0'' && U.term_eq t1 t1''
        then err "no unfolding"
        else no_guard (check_relation g rel t0'' t1'')
      in
      (* Neither side unfolds, e.g. [k0.parser_kind_low + k1.parser_kind_low]
         (a primitive operation on projections of definitions) against the
         literal [25]. As [Rel], whose guard [k0.parser_kind_low +
         k1.parser_kind_low == 25] is normalized away when discharged, the
         relation is closed by evaluating both sides, if one of them is a
         literal. [Zeta] is left out. *)
      let closes_by_evaluation () =
        let is_const (t:term) : ML bool =
          match (Subst.compress (U.unascribe (U.unmeta t))).n with
          | Tm_constant _ -> true
          | _ -> false
        in
        if not (is_const t0 || is_const t1) then err "no evaluation"
        else
          let ev t =
            N.normalize [Env.UnfoldUntil delta_constant; Env.Weak; Env.Primops;
                         Env.Beta; Env.Iota] g.tcenv t
          in
          let t0'' = ev t0 in
          let t1'' = ev t1 in
          if U.term_eq t0 t0'' && U.term_eq t1 t1''
          then err "no evaluation"
          else no_guard (check_relation g rel t0'' t1'')
      in
      let retry_unfolded t0' t1' =
        if is_name t0 || is_name t1
        then handle_with (no_guard (check_relation g rel t0' t1'))
               (fun _ -> handle_with (closes_with_zeta ())
               (fun _ -> handle_with (fallback t0 t1) (fun _ -> check_relation g rel t0' t1')))
        else if is_app t0 && is_app t1
            && not (unfold_to_match 16 (U.unascribe (U.unmeta t0')) (U.unascribe (U.unmeta t1')))
        then handle_with (no_guard (check_relation g rel t0' t1'))
               (fun _ -> handle_with (fallback t0 t1) (fun _ -> check_relation g rel t0' t1'))
        else check_relation g rel t0' t1'
      in
      if! unfolding_ok then
        match maybe_unfold_side' false side t0 t1 with
        | Some (t0', t1') when not guard_ok -> check_relation g rel t0' t1'
        | Some (t0', t1') -> retry_unfolded t0' t1'
        | None ->
          (* Unfolding a recursive definition (which needs a guard, for the
             SMT solver may then prove the relation from its equations) is
             only worth it if it closes the relation outright, e.g. when the
             unfolding reduces by iota. Otherwise the guard is stated on the
             terms as they are. This is tried even when guards are not
             allowed, e.g. relating [natlt n & unit] to [abs (ICons n INil)]
             for a recursive [abs] while trying to relate the arguments of
             two applications without a guard. *)
          match maybe_unfold_side'' true guard_ok side t0 t1 with
          | Some (t0', t1') ->
            handle_with (no_guard (check_relation g rel t0' t1')) (fun _ -> fallback t0 t1)
          | None -> handle_with (closes_by_evaluation ()) (fun _ -> fallback t0 t1)
      else
        fallback t0 t1
    in
    let maybe_unfold_and_retry t0 t1 =
      maybe_unfold_side_and_retry (which_side_to_unfold t0 t1) t0 t1
    in
    let unfoldable_head (t:term) : bool =
      match t.n with
      | Tm_app _ | Tm_fvar _ | Tm_uinst _ -> true
      | _ -> false
    in
    let abs_vs_unfoldable side t0 t1 =
      if! unfolding_ok then
        match maybe_unfold_side' false side t0 t1 with
        | Some (t0', t1') -> check_relation g rel t0' t1'
        | None -> fallback t0 t1
      else fallback t0 t1
    in
    let beta_iota_reduce t =
        let t = Subst.compress t in
        let t = N.normalize [Env.HNF; Env.Weak; Env.Beta; Env.Iota; Env.Primops] g.tcenv t in
        match t.n with
        | Tm_refine _ ->
          U.flatten_refinement t
        | _ -> t
    in
    let beta_iota_reduce t =
        Profiling.profile
          (fun () -> beta_iota_reduce t)
          None
          "FStarC.TypeChecker.Core.beta_iota_reduce"
    in
    let t0 = Subst.compress (beta_iota_reduce t0) |> U.unlazy_emb in
    let t1 = Subst.compress (beta_iota_reduce t1) |> U.unlazy_emb in
    let check_relation g rel t0 t1 =
      with_context "check_relation" (Some (CtxRel t0 rel t1))
        (fun _ -> check_relation g rel t0 t1)
    in
    if equal_term t0 t1 then return ()
    else
      match t0.n, t1.n with
      | Tm_type u0, Tm_type u1 ->
        // when g.allow_universe_instantiation ->
        // See above remark regarding universe instantiations
        if UnivEq.teq_univs g.tcenv [u0] [u1]
        then return ()
        else err "Unequal universes"

      | Tm_meta {tm=t0; meta=Meta_pattern _}, _
      | Tm_meta {tm=t0; meta=Meta_named _}, _
      | Tm_meta {tm=t0; meta=Meta_labeled _}, _
      | Tm_meta {tm=t0; meta=Meta_desugared _}, _
      | Tm_ascribed {tm=t0}, _ ->
        check_relation g rel t0 t1

      | _, Tm_meta {tm=t1; meta=Meta_pattern _}
      | _, Tm_meta {tm=t1; meta=Meta_named _}
      | _, Tm_meta {tm=t1; meta=Meta_labeled _}
      | _, Tm_meta {tm=t1; meta=Meta_desugared _}
      | _, Tm_ascribed {tm=t1} ->
        check_relation g rel t0 t1

      | Tm_uinst (f0, us0), Tm_uinst(f1, us1) ->
        if equal_term f0 f1
        then ( //heads are equal, equate universes
             if UnivEq.teq_univs g.tcenv us0 us1
             then return ()
             else err "Unequal universe instantiations"
        )
        else maybe_unfold_and_retry t0 t1

      | Tm_fvar _, Tm_fvar _ ->
        maybe_unfold_and_retry t0 t1


      (* [squash p] is definitionally [_:unit{p}], so relating two squashed
         propositions by subtyping is an implication between them. Without this
         rule, the congruence rule for applications below would instead demand
         that the two propositions be *equal*, which is much too strong: it is
         what a caller runs into whenever the postcondition of a lemma is not
         syntactically the goal it is used to justify. *)
      | _, _ when SUBTYPING? rel
               && guard_ok
               && Some? (U.is_squash t0)
               && Some? (U.is_squash t1) ->
        let p0 = Some?.v (U.is_squash t0) in
        let p1 = Some?.v (U.is_squash t1) in
        if equal_term p0 p1
        then return ()
        else (
          match rel with
          | SUBTYPING (Some (_, fs)) -> witness_guard g fs (U.mk_imp p0 p1)
          | _ -> guard g (U.mk_imp p0 p1)
        )

      | Tm_refine {b=x0; phi=f0}, Tm_refine {b=x1; phi=f1} ->
        if head_matches x0.sort x1.sort
        then (
          (* Subtyping suffices for the sorts, e.g. arrows: refinements are
             covariant. *)
          check_relation g rel x0.sort x1.sort ;!
          let! u = universe_of_well_typed_term g x0.sort in
          let g0 = g in
          let g, b, f0 = open_term g (S.mk_binder x0) f0 in
          let f1 = Subst.subst [DB(0, b.binder_bv)] f1 in
            (match! guard_not_allowed with
             | true ->
               with_binders g0 [b] [u]
                 (check_relation g EQUALITY f0 f1)

             | _ ->
               match rel with
               | EQUALITY ->
                 (* As [Rel]: the refinements are equal if they are
                    syntactically so, or else if they are equivalent;
                    decomposing them further with guards would demand more,
                    e.g. [xs == f xs] for [x < length xs <==> x < length (f xs)]. *)
                 with_binders g0 [b] [u]
                   (handle_with
                      (no_guard (check_relation g EQUALITY f0 f1))
                      (fun _ -> guard g (U.mk_iff f0 f1)))

               | SUBTYPING (Some (tm, fs)) ->
                 witness_guard g0 fs (Subst.subst [NT(b.binder_bv, tm)] (U.mk_imp f0 f1))

               | SUBTYPING None ->
                 guard g0 (U.mk_forall u b.binder_bv (U.mk_imp f0 f1)))
        )
        else (
          match! maybe_unfold x0.sort x1.sort with
          | None ->
            if !dbg then
              Format.print2 "Cannot match ref heads %s and %s\n" (show x0.sort) (show x1.sort);
            fallback t0 t1
          | Some (t0, t1) ->
            let lhs = S.mk (Tm_refine {b={x0 with sort = t0}; phi=f0}) t0.pos in
            let rhs = S.mk (Tm_refine {b={x1 with sort = t1}; phi=f1}) t1.pos in
            check_relation g rel (U.flatten_refinement lhs) (U.flatten_refinement rhs)
        )

      | Tm_refine {b=x0; phi=f0}, _ ->
        if head_matches x0.sort t1
        then (
          (* For subtyping, we just check that x0.sort <: t1. But for equality,
          we must show that the refinement on the LHS is constantly true. *)
          if EQUALITY? rel then (
            let! u0 = universe_of_well_typed_term g x0.sort in
            let g0 = g in
            let g, b0, f0 = open_term g (S.mk_binder x0) f0 in
            if! guard_not_allowed then
              with_binders g0 [b0] [u0]
                (check_relation g EQUALITY U.t_true f0)
            else (
              with_binders g0 [b0] [u0]
                (handle_with
                    (no_guard (check_relation g EQUALITY U.t_true f0))
                    (fun _ -> guard g f0))
            )
          ) else return ();!
          check_relation g rel x0.sort t1
        )
        else (
          match! maybe_unfold x0.sort t1 with
          | None -> fallback t0 t1
          | Some (t0, t1) ->
            let lhs = S.mk (Tm_refine {b={x0 with sort = t0}; phi=f0}) t0.pos in
            check_relation g rel (U.flatten_refinement lhs) t1
        )

      | _, Tm_refine {b=x1; phi=f1} ->
        if head_matches t0 x1.sort
        then (
          let! u1 = universe_of_well_typed_term g x1.sort in
          check_relation g rel t0 x1.sort ;!
          let g0 = g in
          let g, b1, f1 = open_term g (S.mk_binder x1) f1 in
          if! guard_not_allowed then
            with_binders g0 [b1] [u1]
              (check_relation g EQUALITY U.t_true f1)
          else (
            match rel with
            | EQUALITY ->
              with_binders g0 [b1] [u1]
                (handle_with
                    (no_guard (check_relation g EQUALITY U.t_true f1))
                    (fun _ -> guard g f1))

            | SUBTYPING (Some (tm, fs)) ->
                 let f1 = Subst.subst [NT(b1.binder_bv, tm)] f1 in
                 (* A precondition ([unit <: squash p]): TcTerm simplifies its
                    guard on its own, as it creates it
                    ([value_check_expected_typ]), which unfolds an [unfold]
                    abbreviation at its head, e.g. [normal p] into the
                    [norm] request it stands for. A tactic processing the
                    VC may depend on it. *)
                 let f1 = if U.is_unit x1.sort then VCUtil.simplify_vc false g0.tcenv f1 else f1 in
                 witness_guard g0 fs f1

            | SUBTYPING None ->
                 (* Over a fresh (unnamed) variable. *)
                 let x = S.new_bv (Some (S.range_of_bv b1.binder_bv)) b1.binder_bv.sort in
                 let f1 = Subst.subst [NT(b1.binder_bv, S.bv_to_name x)] f1 in
                 guard g0 (U.mk_forall u1 x f1)
          )
        )
        else (
          match! maybe_unfold t0 x1.sort with
          | None -> fallback t0 t1
          | Some (t0, t1) ->
            let rhs = S.mk (Tm_refine {b={x1 with sort = t1}; phi=f1}) t1.pos in
            check_relation g rel t0 (U.flatten_refinement rhs)
        )

      (* An abstraction and a term that is not one: as in [Rel]
         ([head_matches_delta]), the latter is unfolded, e.g. [non_neg_inv r]
         to [fun m -> exists v. r == v] (tests/bug-reports/closed/Bug2002).
         There is no eta rule: [fun (x:a) -> f x] is not equal to [f], whose
         domain may be larger than [a] (see FStar.FunctionalExtensionality
         and tests/micro-benchmarks/Test.FunctionalExtensionality). *)
      | Tm_abs _, _ when unfoldable_head t1 ->
        abs_vs_unfoldable Right t0 t1
      | _, Tm_abs _ when unfoldable_head t0 ->
        abs_vs_unfoldable Left t0 t1

      | Tm_uinst _, _
      | Tm_fvar _, _
      | Tm_app _, _
      | _, Tm_uinst _
      | _, Tm_fvar _
      | _, Tm_app _ ->
        let head_matches = head_matches t0 t1 in
        let head0, args0 = U.leftmost_head_and_args t0 in
        let head1, args1 = U.leftmost_head_and_args t1 in
        if not (head_matches && List.length args0 = List.length args1)
        then maybe_unfold_and_retry t0 t1
        else (
          (* If we're proving equality, SMT queries are ok, and either head
             is equatable:
              - first try proving equality structurally, without a guard.
              - if that fails, then emit an SMT query
             This is designed to be able to prove things like `v.v1 == u.v1`
             first by trying to unify `v` and `u` and if it fails
             then prove `v.v1 == u.v1` *)
          let compare_head_and_args () =
            handle_with
              (check_relation g EQUALITY head0 head1 ;!
               check_relation_args g EQUALITY args0 args1)
              (fun _ -> maybe_unfold_side_and_retry Both t0 t1)
          in
          let abs_args =
            List.length args0 = List.length args1 &&
            BU.for_some (fun ((a0, _), (a1, _)) ->
              Tm_abs? (Subst.compress a0).n && Tm_abs? (Subst.compress a1).n)
              (List.zip args0 args1)
          in
          if guard_ok &&
            (EQUALITY? rel) && 
            (equatable g t0 || equatable g t1)
          then (
            (* An equation between two applications with abstractions as
               corresponding arguments (or terms with binders, as arguments
               of their arguments: see [args_contain_binders]), e.g.
               [on_domain a f == on_domain a g],
               is beyond the SMT solver without extensionality. As [Rel]
               does, the arguments, and so the bodies of the abstractions,
               may be related under their binder; but that is sufficient
               rather than necessary (e.g., [False == p x] needs
               propositional extensionality, while [on_domain a (fun _ ->
               False) == on_domain a p] may be a hypothesis), so either may
               be proven. *)
            let args_or_eq () : result unit =
              with_guard (compare_head_and_args ()) (function
                | Inr err -> fail_propagate err
                | Inl ((), None) -> return ()
                | Inl ((), Some phi) ->
                  let! _, t_typ, _ = do_check g t0 in
                  let! u = universe_of_well_typed_term g t_typ in
                  reemit_guard g (U.mk_disj phi (U.mk_eq2 u t_typ t0 t1)))
            in
            handle_with 
              (no_guard (compare_head_and_args ()))
              (fun _ ->
                if abs_args || args_contain_binders t0 || args_contain_binders t1
                then handle_with (args_or_eq ()) (fun _ -> emit_guard t0 t1)
                else emit_guard t0 t1)
          )
          else if guard_ok
          then (
            (* E.g. [fin n <: fin (n + m)], or [swap_for xs == swap_for (f xs)]
               where [swap_for xs] unfolds to a refinement mentioning only
               [length xs]: rather than demanding that the arguments be equal,
               which may well be false, try relating the unfoldings, as [Rel]
               does, before settling for that. But the arguments may also be
               provably equal where the unfoldings are not (e.g. equal
               sequences given by a lemma, where the unfoldings quantify
               over their indices), so if both need a guard, either suffices,
               unless that of the unfoldings is quantifier-free, e.g. [i < n
               ==> i < n + m], in which case it is the only guard. *)
            handle_with
              (no_guard (check_relation g EQUALITY head0 head1 ;!
                         check_relation_args g EQUALITY args0 args1))
              (fun _ ->
                match! maybe_unfold t0 t1 with
                | Some (t0', t1') ->
                  let unfolded () = check_relation g rel t0' t1' in
                  let argwise () =
                    check_relation g EQUALITY head0 head1 ;!
                    check_relation_args g EQUALITY args0 args1
                  in
                  (* In an equation with abstractions as corresponding
                     arguments, e.g. [forevery (fun i -> p i) == forevery
                     (fun i -> q i)], the unfoldings only relate the same
                     abstractions again, deeper down: offering both would
                     duplicate the argument-wise guard at each level of
                     nesting. (Not so for subtyping, e.g. [st pre post <: st
                     pre' post'], where the unfoldings may be related by
                     implications, but the arguments only by equations.) *)
                  (* A head with the [unifier_hint_injective] attribute,
                     e.g. [parser k t], is related argument-wise, as by
                     [Rel], which does not unfold it: its unfoldings may only
                     be related by equations between its arguments that are
                     beyond the SMT solver, e.g. [parser_kind_prop #t k p ==>
                     parser_kind_prop #t' k' p], for types [t], [t'] equal by
                     unfolding. *)
                  let injective =
                    match (U.un_uinst head0).n with
                    | Tm_fvar fv -> Env.fv_has_attr g.tcenv fv PC.unifier_hint_injective_lid
                    | _ -> false
                  in
                  if (abs_args && rel = EQUALITY) || injective
                  then handle_with (argwise ()) (fun _ -> unfolded ())
                  else either_guard unfolded argwise
                | None -> compare_head_and_args ())
          )
          else compare_head_and_args ()
        )

      | Tm_abs {b=b0; body=body0}, Tm_abs {b=b1; body=body1} ->
        check_relation g EQUALITY b0.binder_bv.sort b1.binder_bv.sort;!
        check_bqual b0.binder_qual b1.binder_qual;!
        check_positivity_qual EQUALITY b0.binder_positivity b1.binder_positivity;!
        let! u = universe_of_well_typed_term g b0.binder_bv.sort in
        let g0 = g in
        let g, b0, body0 = open_term g b0 body0 in
        let body1 = Subst.subst [DB(0, b0.binder_bv)] body1 in
        with_binders g0 [b0] [u]
          (check_relation g EQUALITY body0 body1)

      | Tm_arrow {b=x0; comp=c0}, Tm_arrow {b=x1; comp=c1} ->
        with_context "subtype arrow" None (fun _ ->
          let! _ = check_bqual x0.binder_qual x1.binder_qual in
          check_positivity_qual rel x0.binder_positivity x1.binder_positivity;!
          let! u1 = universe_of_well_typed_term g x1.binder_bv.sort in
          let g_x1, x1, c1 = open_comp g x1 c1 in
          let c0 = Subst.subst_comp [DB(0, x1.binder_bv)] c0 in
          with_binder_unrefined g x1 u1 (
            let rel_arg =
              match rel with
              | EQUALITY -> EQUALITY
              | _ -> SUBTYPING (Some (S.bv_to_name x1.binder_bv, no_facts_l ()))
            in
            let rel_comp =
              match rel with
              | EQUALITY -> EQUALITY
              | SUBTYPING e ->
                SUBTYPING
                  (if U.is_pure_or_ghost_comp c0
                   then match e with
                        | None -> None
                        | Some (e, _) ->
                          (* Beta-reduced; the facts about [e]'s subterms
                             are not about the result's. *)
                          match (Subst.compress e).n with
                          | Tm_abs {body} ->
                            Some (Subst.subst [DB(0, x1.binder_bv)] body, no_facts_l ())
                          | _ ->
                            Some (S.mk_Tm_app e (snd (U.args_of_binders [x1])) R.dummyRange, no_facts_l ())
                   else None)
            in
            (* In [g_x1]: [x1] is free in the guard, as the witness, and
               binders opened while relating the domains (e.g. those of
               the branches of a [match]) must not reuse its index. *)
            check_relation g_x1 rel_arg x1.binder_bv.sort x0.binder_bv.sort ;!
            with_context "check_subcomp" None (fun _ ->
              check_relation_comp g_x1 rel_comp c0 c1
            )
          )
        )

      | Tm_match {scrutinee=e0;brs=brs0}, Tm_match {scrutinee=e1;brs=brs1} ->
        let relate_branch br0 br1 (_:unit)
          : ML (result unit)
          = match br0, br1 with
            | (p0, None, body0), (p1, None, body1) ->
              if not (S.eq_pat p0 p1)
              then fail_str "patterns not equal"
              else begin
                let g', (p0, _, body0), (p1, _, body1) = open_branches_eq_pat g (p0, None, body0) (p1, None, body1) in
                match PatternUtils.raw_pat_as_exp g.tcenv p0 with
                | Some (pe, bvs0) ->
                  let bs0 = List.map S.mk_binder bvs0 in
                  // We need universes for the binders
                  let! us = check_binders g bs0 in
                  (* The bodies are related knowing which branch is taken,
                     e.g. [y:t{x == Unknown u}] when relating
                     [dsum_type_of_unknown_tag s] to [t]. *)
                  let! sc_eq =
                    match! type_of_checked g e0 with
                    | None -> return None
                    | Some (_, t_sc) ->
                      let! u_sc = quietly (universe_of_well_typed_term g t_sc) in
                      return (Some (U.mk_eq2 u_sc t_sc e0 pe))
                  in
                  let g'', hyp =
                    match sc_eq with
                    | None -> g', U.t_true
                    | Some h -> push_hypothesis g' h, h
                  in
                  with_context "relate_branch" None (fun _ ->
                    with_binders g bs0 us
                      (weaken_branch g' hyp (check_relation g'' rel body0 body1)))
             | _ -> fail_str "raw_pat_as_exp failed in check_equality match rule"
             end
            | _ -> fail_str "Core does not support branches with when"
        in
        handle_with
          (check_relation g EQUALITY e0 e1 ;!
           iter2 brs0 brs1 relate_branch ())
          (fun _ -> fallback t0 t1)

      | _ -> fallback t0 t1

and check_relation (g:env) (rel:relation) (t0 t1:typ)
  : ML (result unit)
  = (* With [use_eq_strict] (the [no_subtyping] attribute), there is no
       subtyping: the types must be equal. *)
    let rel = if g.tcenv.use_eq_strict then EQUALITY else rel in
    if !dbg
    then (
      fun ctx cache ->
        Format.print3 "check_relation (%s, %s, %s) {\n"
                    (show t0)
                    (show rel)
                    (show t1);
        let res = with_relation_failure_memo g rel t0 t1 (check_relation' g rel t0 t1) ctx cache in
        match res with
        | Error err ->
          Format.print4 "} check_relation (%s, %s, %s) failed with %s\n"
            (show t0) (show rel) (show t1) (show err);
          Error err
        | Success ((_, g), cache) ->
          Format.print4 "} check_relation  (%s, %s, %s) succeeded with guard %s\n"
            (show t0) (show rel) (show t1) (show g);
          res
    )
    else (
      with_relation_failure_memo g rel t0 t1 (check_relation' g rel t0 t1)
    )

and check_relation_args (g:env) rel (a0 a1:args)
  : ML (result unit)
  = if List.length a0 = List.length a1
    then iter2 a0 a1
         (fun (t0, q0) (t1, q1) _ ->
            check_aqual q0 q1;!
            check_relation g rel t0 t1)
         ()
    else fail_str "Unequal number of arguments"

and check_relation_comp (g:env) rel (c0 c1:comp)
  : ML (result unit)
  = let e0, t0 = comp_as_eff_and_type c0 in
    let e1, t1 = comp_as_eff_and_type c1 in
    match e0, e1 with
    | ETot, _
    | EGhost, EGhost ->
      (* A total computation may be used at any effect. For EQUALITY this is
         not quite right when [e1] is not [ETot], but relating two arrows whose
         comps differ only by an admissible sub-effect is what every caller of
         EQUALITY on comps has always relied on. *)
      check_relation g rel t0 t1

    | EGhost, ETot ->
      if non_informative g t1
      then check_relation g rel t0 t1
      else fail_str "Expected a Total computation, but got Ghost"

    | _ ->
      let ok =
        match rel with
        | EQUALITY -> eff_eq e0 e1
        | SUBTYPING _ -> sub_eff g e0 e1
      in
      if ok
      then (
        (* The result of an effectful computation is not a term we may put in
           a formula, so relate the result types without a witness. *)
        let rel =
          match rel with
          | EQUALITY -> EQUALITY
          | SUBTYPING _ -> SUBTYPING None
        in
        check_relation g rel t0 t1
      )
      else
        fail [
          text "Subcomp failed: computation with effect" ^/^ fquotes (pp (eff_to_lid e0))
          ^/^ text "cannot be used at effect" ^/^ fquotes (pp (eff_to_lid e1))
        ]


and check_subtype (g:env) (e:option witness) (t0 t1:typ)
: ML (result _)
  = let chk : result unit = fun ctx cache ->
      Profiling.profile
        (fun () ->
          let rel = SUBTYPING e in
          with_context (if ctx.no_guard then "check_subtype(no_guard)" else "check_subtype")
                       (Some (CtxRel t0 rel t1))
            (fun _ -> check_relation g rel t0 t1)
            ctx cache)
        None
        "FStarC.TypeChecker.Core.check_subtype"
    in
    match e with
    | Some (tm, _) -> label_subtyping g tm t0 t1 chk
    | None -> chk

(* The guard [phi] about the witness of a refinement subtyping, whose
   subterms have the facts [fs]. The type synthesized for an application is
   its head's result type, which says nothing about its arguments; so also
   assume what the types of its arguments say about them. TcTerm makes those
   facts available by binding every argument to a name of its type. *)
and witness_guard (g:env) (fs:Thunk.t (list term)) (phi:typ)
  : ML (result unit)
  = let facts = dedup_facts (Thunk.force fs) in
    if !dbg_facts then Format.print2 "witness_guard %s: %s facts\n" (show phi) (show (List.length facts));
    match facts with
    | [] -> guard g phi
    | _ -> guard g (U.mk_imp (U.mk_conj_l facts) phi)

(* Run [f], dropping its guard: for computations whose guards have already
   been emitted. The cache is kept only when there was no guard: its entries
   claim their guards have been emitted. *)
and quietly (#a:Type) (f:result a)
  : result a
  = fun ctx cache ->
      match f ctx cache with
      | Success ((x, None), cache') -> Success ((x, None), cache')
      | Success ((x, Some _), _) -> Success ((x, None), cache)
      | Error e -> Error e

(* The type of a term that has already been checked, whose typing guard has
   hence already been emitted and may be dropped. The cache is kept only when
   there was no guard: its entries claim their guards have been emitted. *)
and type_of_checked (g:env) (e:term)
  : ML (result (option (eff & typ)))
  = fun ctx cache ->
      match check "checked term" g e ctx cache with
      | Success ((et, None), cache') -> Success ((Some et, None), cache')
      | Success ((et, Some _), _) -> Success ((Some et, None), cache)
      | Error _ -> Success ((None, None), cache)

and is_prop (g:env) (t:term) : ML (result unit) =
  with_context "is_prop" (Some (CtxTerm t)) fun _ ->
    check_subtype g None t t_prop

and memo_check (g:env) (e:term)
  : ML (result (eff & typ & facts))
  = let key = cache_key e in
    let e = key in
    let check_then_memo g e =
      with_guard (do_check_and_promote g e)
      (function
      | Inl (res, guard) ->
        insert g key (res, guard);!
        return_with_guard res guard

      | Inr err ->
        fail_propagate err)
    in
    if not g.should_read_cache
    then check_then_memo g e
    else (
      with_guard (lookup g key)
      (function
      | Inr _ ->
        check_then_memo g e
      | Inl (et, None) -> //cache hit; great, just return
        return et
      | Inl (et, pre) -> ( //cache hit with a guard
        failwith "Impossible"
      )
    ))

and check' (msg:string) (g:env) (e:term)
  : ML (result (eff & typ & facts))
  = with_context msg (Some (CtxTerm e)) (fun _ -> memo_check g e)

(* The effect and type of [e]. *)
and check (msg:string) (g:env) (e:term)
  : ML (result (eff & typ))
  = let! eff, t, _ = check_f msg g e in
    return (eff, t)

(* Also returning the facts about [e]. *)
and check_f (msg:string) (g:env) (e:term)
  : ML (result (eff & typ & facts))
  = if !dbg
    then (
      fun ctx cache -> 
        Format.print2 "{About to check %s %s\n" msg (show e);
        let res = check' msg g e ctx cache in
        match res with
        | Error err -> Error err
        | Success (((eff, typ, _), guard), cache) ->
          Format.print3 "Checked %s at type %s with guard %s}\n"
            (show e)
            (show typ)
            (show guard);
          res
    )
    else check' msg g e

and do_check_and_promote (g:env) (e:term)
  : ML (result (eff & typ & facts))
  = let! (eff, t, sf) = do_check g e in
    let eff =
      match eff with
      | EGhost -> if non_informative g t then ETot else EGhost
      | _ -> eff in
    return (eff, t, mk_facts g e eff t sf)

(* For a term none of whose subterms has facts. *)
and no_sub (r:result (eff & typ))
  : ML (result (eff & typ & sub_facts))
  = let! eff, t = r in
    return (eff, t, no_sub_facts ())

(*  G |- e : Tot t | pre, also returning the facts about the subterms of [e] *)
and do_check (g:env) (e:term)
  : ML (result (eff & typ & sub_facts)) =
  let e = Subst.compress e in
  match e.n with
  | Tm_lazy ({lkind=Lazy_embedding _}) ->
    do_check g (U.unlazy e)

  | Tm_lazy i ->
    no_sub (return (ETot, i.ltyp))

  | Tm_meta {tm=t; meta=Meta_monadic (m, a)}
      when (match (fst (U.head_and_args_full t)).n with
            | Tm_constant (FStarC.Const.Const_reflect _) -> true
            | _ -> false) ->
    (* [reflect e], as elaborated by TcTerm: [e] is the representation of
       a computation in [m] returning an [a]. *)
    let _, args = U.head_and_args_full t in
    (match args with
     | [(e, _)] ->
       let! _, t_a = check "reflect result type" g a in
       let! u_a = is_type g t_a in
       let! eff_e, t_e, fe = check_f "reflect argument" g e in
       if not (ETot? eff_e) then fail_str "Expected a total argument to reflect" else (
       let repr = Env.reify_comp g.tcenv (mk_comp_of_eff m a) u_a in
       check_subtype g (Some (e, fe.f_sub)) t_e repr ;!
       return (EEff m, a, { no_sub_facts () with s_sub = fe.f_term }))
     | _ -> fail_str "Ill-applied reflect")

  | Tm_meta {tm=t} ->
    let! eff, t, f = memo_check g t in
    return (eff, t, inner_facts f)

  | Tm_quoted (_, qi) ->
    no_sub (match qi.qkind with
     | Quote_static ->
       (* A static quotation is a [term], as long as its antiquotations are *)
       let rec aux (aqs:list term) : ML (result unit) =
         match aqs with
         | [] -> return ()
         | aq::aqs ->
           let! eff_aq, t_aq, faq = check_f "antiquotation" g aq in
           if not (ETot? eff_aq) then fail_str "Expected a total antiquotation" else (
           check_subtype g (Some (aq, faq.f_sub)) t_aq S.t_term ;!
           aux aqs)
       in
       aux (snd qi.antiquotations) ;!
       return (ETot, S.t_term)
     | Quote_dynamic ->
       (* The quoted term is only elaborated (laxly), not checked, by TcTerm *)
       return (EEff PC.effect_TAC_lid, S.t_term))

  | Tm_uvar (uv, s) ->
    no_sub (return (ETot, Subst.subst' s (U.ctx_uvar_typ uv)))

  | Tm_name x ->
    no_sub begin
    match Env.try_lookup_bv g.tcenv x with
    | None ->
      fail_str (Format.fmt1 "Variable not found: %s" (show x))
    | Some (t, _) ->
      (* As [Env.lookup_bv]: the type of an occurrence is used at the
         occurrence, e.g. the refinement of a recursive function's argument
         that proves termination is reported at the recursive call. *)
      return (ETot, Subst.set_use_range (S.range_of_bv x) t)
    end

  | Tm_fvar f ->
    no_sub begin
    match Env.try_lookup_lid g.tcenv f.fv_name with
    | Some (([], t), _) ->
      return (ETot, t)

    | _ -> //no implicit universe instantiation allowed
      fail_str "Missing universes instantiation"
    end

  | Tm_uinst ({n=Tm_fvar f}, us) ->
    no_sub begin
    match Env.try_lookup_and_inst_lid g.tcenv us f.fv_name with
    | None ->
      fail_str (Format.fmt1 "Top-level name not found: %s" (Ident.string_of_lid f.fv_name))

    | Some (t, _) ->
      return (ETot, t)
    end

  | Tm_constant c ->
    no_sub begin
    let open FStarC.Const in
    match c with
    | Const_range_of
    | Const_set_range_of
    | Const_reify _
    | Const_reflect _ ->
      fail_str "Unhandled constant"

    | _ ->
      let t = UniverseOf.tc_constant g.tcenv e.pos c in
      return (ETot, t)
    end

  | Tm_type u ->
    no_sub (return (ETot, mk_type (U_succ u)))

  | Tm_refine {b=x; phi} ->
    no_sub begin
    let! _, t = check "refinement head" g x.sort in
    let! u = is_type g t in
    let g', x, phi = open_term g (S.mk_binder x) phi in
    with_binders g [x] [u] (
      let! _, t' = check "refinement formula" g' phi in
      is_prop g' t';!
      (* As in [TcTerm]: a refinement is typed [Type u], even when its sort
         is, say, an [eqtype]. *)
      return (ETot, mk_type u)
    )
    end

  | Tm_abs _ ->
    (* One n-ary node at a time, as [TcTerm] does: [abs_formals_ln] would also
       look through ascriptions on the body, and so give the function a type
       with a longer arrow spine than the one the user wrote. The SMT encoding
       of a top-level definition depends on that spine. *)
    let xs, body, _ = U.abs_one_group_ln e in
    let g', xs, body = open_term_binders g xs body in
    let! us = with_context "abs binders" None (fun _ -> check_binders g xs) in
    (* A body ascribed with a computation type, e.g. [Lemma ... [SMTPat ...]],
       gives the function that computation type as written, flags,
       decreases clause and all: they are part of the function's type (the
       SMT encoding of a lemma depends on them), not just its effect. *)
    let rec ascribed_comp (t:term) : ML (option comp) =
      match (Subst.compress t).n with
      | Tm_ascribed {asc=(Inr c, _, _)} -> Some c
      | Tm_meta {tm; meta=Meta_pattern _}
      | Tm_meta {tm; meta=Meta_named _}
      | Tm_meta {tm; meta=Meta_labeled _}
      | Tm_meta {tm; meta=Meta_desugared _} -> ascribed_comp tm
      | _ -> None
    in
    with_binders g xs us (
      let! t = check "abs body" g' body in
      let c =
        match ascribed_comp body with
        | Some c -> c
        | None -> as_comp g t
      in
      return (ETot, U.arrow xs c, no_tail_facts ())
    )

  | Tm_arrow _ ->
    no_sub begin
    let xs, c = U.arrow_formals_comp_ln_strict e in
    let g', xs, c = open_comp_binders g xs c in
    let! us = with_context "arrow binders" None (fun _ -> check_binders g xs) in
    with_binders g xs us (
      let! u = with_context "arrow comp" None (fun _ -> check_comp g' c) in
      return (ETot, mk_type (S.U_max (u::us)))
    )
    end

  | Tm_app _ -> (
    (* [deps] are the (pure) arguments so far that the rest of the arrow
       depends on: the formal type of a later argument mentions them, and
       relating it to the actual type may need what their types say about
       them (e.g. [length (f xs) == length xs] to relate
       [list (swap (length xs))] and [list (swap (length (f xs)))]). TcTerm
       makes those facts available by binding every argument to a name of its
       type. *)
    (* [fs] are the facts about the arguments so far. *)
    let rec check_app_arg (st:(eff & typ & list (term & Thunk.t (list term)) & list (Thunk.t (list term)))) (a:arg)
      : ML (result (eff & typ & list (term & Thunk.t (list term)) & list (Thunk.t (list term)))) =
      let eff_hd, t_hd, deps, fs = st in
      let arg, arg_qual = a in
      let! x, eff_arr, t' = is_arrow g t_hd in
      let with_deps (#a:Type) (f:unit -> ML (result a)) : ML (result a) =
        match deps with
        | [] -> f ()
        | _ ->
          with_guard (f ()) (function
            | Inr err -> fail_propagate err
            | Inl (res, None) -> return res
            | Inl (res, Some form) ->
              match List.filter (fun (d, _) -> occurs_in d form) deps with
              | [] -> return_with_guard res (Some form)
              | deps ->
                match dedup_facts (List.collect (fun (_, f) -> Thunk.force f) deps) with
                | [] -> return_with_guard res (Some form)
                | facts ->
                  reemit_guard g (U.mk_imp (U.mk_conj_l facts) form) ;!
                  return res)
      in
      (* A function argument is checked against its formal arrow type, as
         TcTerm does, rather than having its type synthesized and then
         related to the formal: what the body proves (e.g. the typing of
         [join w1 w3] in [introduce p ==> exists w3. q w3 with (let w3 =
         ... in lemma (join w1 w3))]) then scopes over the goal it is
         proven for. *)
      (* Likewise a match with neither a return annotation nor a residual
         type, as built by tactics (e.g. Pulse's join of the postconditions
         of a conditional, [pts_to r (match b with true -> 0ul | false ->
         f x)]): synthesized, its type would be its first branch's, e.g.
         [x:U32.t{v x = 0}], which the other branches need not have. *)
      let unannotated_match =
        match (Subst.compress arg).n with
        | Tm_match {ret_opt=None; brs; rc_opt} ->
          List.for_all (fun (_, w, _) -> None? w) brs
          && (match rc_opt with
              | Some ({ residual_typ = Some _ }) -> false
              | _ -> true)
        | _ -> false
      in
      let abs_checked =
        unannotated_match
        || (Tm_abs? (Subst.compress arg).n
            && Some? (abs_against_arrow g arg x.binder_bv.sort))
      in
      let! eff_arg, t_arg, f_arg =
        if abs_checked
        then (
          let! eff, f_arg = with_context "app arg" (Some (CtxTerm arg)) (fun _ ->
                              with_deps (fun _ -> check_against_typ g arg x.binder_bv.sort)) in
          return (eff, x.binder_bv.sort, f_arg)
        )
        else check_f "app arg" g arg
      in
      (* A ghost argument for a non-informative formal, e.g. a total
         function for an [a -> GTot b], is total, as by TcTerm, which checks
         it against the formal. *)
      let eff_arg =
        match eff_arg with
        | EGhost when non_informative g x.binder_bv.sort -> ETot
        | _ -> eff_arg
      in
      let pure_arg = is_tot_or_ghost_eff eff_arg in
      let subtyping () =
        (* The obligations of the formal, e.g. a termination refinement,
           are about this argument: locate them at it, as TcTerm does. *)
        check_subtype g (if pure_arg then Some (arg, f_arg.f_sub) else None) t_arg
          (Subst.set_use_range arg.pos x.binder_bv.sort) in
      (if abs_checked then return ()
       else with_context "app subtyping" (Some (CtxTerm arg)) (fun _ -> with_deps subtyping)) ;!
      with_context "app arg qual" None (fun _ -> check_arg_qual arg_qual x.binder_qual) ;!
      let! eff = join_eff_l g [eff_hd; eff_arr; eff_arg] in
      let dependent = mem x.binder_bv (FStarC.Syntax.Free.names t') in
      (* An effectful argument is not a term we may substitute into a type. *)
      if not pure_arg && dependent
      then fail [
             text "The type of this application depends on its argument"
             ^/^ fquotes (pp arg) ^/^ text "which has effect" ^/^ pp (eff_to_lid eff_arg)
           ]
      else
        (* What the type of a variable (or constant) says about it is
           already in scope, where the variable is bound. *)
        let atomic =
          match (Subst.compress (U.unmeta arg)).n with
          | Tm_name _ | Tm_fvar _ | Tm_uinst _ | Tm_constant _ -> true
          | _ -> false
        in
        return (eff, Subst.subst [NT(x.binder_bv, arg)] t',
                (if dependent && not atomic then deps @ [(arg, f_arg.f_term)] else deps),
                f_arg.f_term :: fs)
    in
    (* The facts about an application are those about its arguments. *)
    let check_app hd args =
       let! eff_hd, t = check "app head" g hd in
       let! eff, t, _, fs = fold check_app_arg (eff_hd, t, [], []) args in
       return (eff, t, { no_sub_facts () with s_sub = facts_concat (List.rev fs) })
    in
    let hd, args = U.head_and_args_full e in
    match (Subst.compress hd).n, args with
    | Tm_constant FStarC.Const.Const_range_of, [(e, None)] ->
      let! eff, _, fe = check_f "range_of argument" g e in
      return (eff, S.t_range, { no_sub_facts () with s_sub = fe.f_term })

    | Tm_constant FStarC.Const.Const_set_range_of, [(e, None); (r, None)] ->
      let! eff_r, t_r, fr = check_f "set_range_of range" g r in
      check_subtype g (if is_tot_or_ghost_eff eff_r then Some (r, fr.f_sub) else None) t_r S.t_range ;!
      let! eff_e, t_e, fe = check_f "set_range_of argument" g e in
      let! eff = join_eff g eff_r eff_e in
      return (eff, t_e, { no_sub_facts () with s_sub = facts_concat [fe.f_term; fr.f_term] })

    | Tm_constant (FStarC.Const.Const_reify _), [(e, _)] ->
      no_sub begin
      let! eff_e, t_e = check "reify argument" g e in
      (match eff_e with
       | EEff m when Env.is_user_reifiable_effect g.tcenv m ->
         let! u = universe_of_well_typed_term g t_e in
         let repr = Env.reify_comp g.tcenv (mk_comp_of_eff m t_e) u in
         let eff =
           if U.has_attribute (Env.get_effect_decl g.tcenv m).eff_attrs PC.primitive_extraction_attr then EGhost
           else if Env.is_total_effect g.tcenv m then ETot
           else EEff PC.primitive_div_lid
         in
         return (eff, repr)
       | _ -> fail_str "Expected a reifiable computation")
      end

    | Tm_constant FStarC.Const.Const_range_of, _
    | Tm_constant FStarC.Const.Const_set_range_of, _
    | Tm_constant (FStarC.Const.Const_reify _), _
    | Tm_constant (FStarC.Const.Const_reflect _), _ ->
      fail_str "Ill-applied or unexpected constant"

    | _, [(t1, _); (t2, _)] when VCUtil.short_circuit_head hd ->
      let! eff_hd, t_hd = check "app head" g hd in
      let! x, eff_arr1, s1 = is_arrow g t_hd in
      let! eff_arg1, t_t1, f1 = check_f "app arg" g t1 in
      with_context "operator arg1" None (fun _ -> check_subtype g (Some (t1, f1.f_sub)) t_t1 x.binder_bv.sort) ;!
      let s1 = Subst.subst [NT(x.binder_bv, t1)] s1 in
      let! y, eff_arr2, s2 = is_arrow g s1 in
      let guard_formula = VCUtil.short_circuit hd [(t1, None)] in
      let g' =
        match guard_formula with
        | CommonBase.Trivial -> g
        | CommonBase.NonTrivial gf -> push_hypothesis g gf
      in
      let! eff_arg2, t_t2, f2 = weaken_with_guard_formula g guard_formula (check_f "app arg" g' t2) in
      with_context "operator arg2" None (fun _ -> check_subtype g' (Some (t2, f2.f_sub)) t_t2 y.binder_bv.sort) ;!
      let! eff = join_eff_l g [eff_hd; eff_arr1; eff_arr2; eff_arg1; eff_arg2] in
      (* The facts about [t2] hold when it is evaluated. *)
      let f2 =
        match guard_formula with
        | CommonBase.Trivial -> f2.f_term
        | CommonBase.NonTrivial gf ->
          Thunk.map (fun (fs:list term) ->
            match fs with
            | [] -> []
            | _ -> [U.mk_imp gf (U.mk_conj_l fs)]) f2.f_term
      in
      return (eff, Subst.subst [NT(y.binder_bv, t2)] s2,
              { no_sub_facts () with s_sub = facts_concat [f1.f_term; f2] })

    | Tm_fvar fv, [(a, Some ({ aqual_implicit = true })); (_, None)]
        when S.fv_eq_lid fv PC.forall_lid || S.fv_eq_lid fv PC.exists_lid ->
      (* [TcUtil] closes variables escaping the type of a [let] with
         quantifiers that it leaves without universes; their universe is
         that of the domain. *)
      let! _, t_a = check "quantifier domain" g a in
      let! u = is_type g t_a in
      check_app (S.mk_Tm_uinst hd [u]) args

    | _, [(t, Some ({ aqual_implicit = true })); (tau, None)]
        when U.is_synth_by_tactic hd ->
      (* [synth_by_tactic #t tau] is left for Core by [TcTerm.tc_synth]
         when [t] is a proof goal: its tactic is to prove that goal, here,
         in the context in which Core checks it, as for [assert p by tau].
         A synthesis at any other type must have been run by the
         elaborator, and replaced by the tactic's result; the declaration
         of [synth_by_tactic] in the library gives no obligation for it. *)
      let! eff, ty, sf = check_app hd args in
      (match VCUtil.synth_proof_goal g.tcenv t with
       | Some p ->
         reemit_guard g (CommonBase.mk_by_tactic tau p) ;!
         return (eff, ty, sf)
       | None ->
         fail [
           text "This synthesis by a tactic was not run, and its type"
           ^/^ fquotes (pp t) ^/^ text "is not a proposition."
           ^/^ text "Synthesis is supported only in the definitions of top-level let-bindings."
         ])

    | _ -> check_app hd args
  )

  | Tm_ascribed {tm=e; asc=(Inl t, tac, eq)} ->
    let! _, t' = check "ascription type" g t in
    is_type g t';!
    let! eff, fe =
      with_ascription_tactic g tac (fun _ ->
        if eq
        then (
          (* [e $: t]: the type of [e] must be [t], not merely a subtype of it *)
          let! eff, te, fe = check_f "ascribed term" g e in
          with_context "ascription equality" None (fun _ -> check_relation g EQUALITY te t) ;!
          return (eff, fe)
        )
        else with_context "ascription subtyping" None (fun _ -> check_against_typ g e t)) in
    return (eff, t, inner_facts fe)

  | Tm_ascribed {tm=e; asc=(Inr c, tac, _)} ->
    let! _ = with_context "ascription comp" None (fun _ -> check_comp g c) in
    let! fe =
      with_ascription_tactic g tac (fun _ ->
        with_context "ascription subtyping (comp)" None (fun _ -> check_against_comp_f g e c)) in
    let eff, t = comp_as_eff_and_type c in
    return (eff, t, inner_facts fe)

  | Tm_let {lbs=(false, [lb]); body} ->
    check_let g lb body None

  | Tm_match {brs}
      when BU.for_some (fun (_, w, _) -> Some? w) brs ->
    (* As in [TcTerm.tc_eqn], which rejects them when verifying *)
    let w = List.tryPick (fun (_, w, _) -> w) brs |> Option.must in
    with_context "when clause" (Some (CtxTerm w)) (fun _ ->
      fail_code Errors.Fatal_WhenClauseNotSupported
        (Errors.mkmsg "When clauses are not yet supported in --verify mode; they will be some day"))

  | Tm_match {scrutinee=sc; ret_opt=None; brs=branches; rc_opt} ->
    check_match g e.pos sc branches rc_opt None

  | Tm_match {scrutinee=sc; ret_opt=Some (as_x, (Inl returns_ty, None, eq)); brs=branches; rc_opt} ->
    let! eff_sc, t_sc = check "scrutinee" g sc in
    let all_branches = branches in
    let! u_sc = universe_of_well_typed_term g t_sc in
    let as_x = {as_x with binder_bv = { as_x.binder_bv with sort = t_sc } } in
    let g_as_x, as_x, returns_ty = open_term g as_x returns_ty in
    let! _eff_t, returns_ty_t =
      with_binders g [as_x] [u_sc] (check "return type" g_as_x returns_ty) in
    let! _u_ty = is_type g_as_x returns_ty_t in
    let rec check_branches (path_condition: typ)
                           (branches: list S.branch)
                           (acc_eff: eff)
      : ML (result eff)
      = match branches with
        | [] ->
          if match_covers_bool g t_sc all_branches then return acc_eff else
          (match exhaustiveness_obligation e.pos path_condition with
           | None -> return acc_eff
           | Some phi -> guard g phi ;! return acc_eff)

        | (p, None, b) :: rest ->
          let _, (p, _, b) = open_branch g (p, None, b) in
          let! (bs, us) = with_context "check_pat" None (fun _ -> check_pat g p t_sc) in
          let! branch_condition = pattern_branch_condition g sc p in
          let pat_exp = PatternUtils.raw_pat_as_exp g.tcenv p |> Option.must |> fst in
          let pat_sc_eq = U.mk_eq2 u_sc t_sc sc pat_exp in
          let hyp, _, next_path_condition =
              branch_conditions path_condition branch_condition pat_sc_eq
          in
          let g_h = push_branch_hypothesis g hyp in
          let g'0 = push_binders g_h bs in
          let g' = push_hypothesis g'0 pat_sc_eq in
          let! eff_br, tbr =
            weaken_branch g hyp
            (with_binders g_h bs us
              (weaken_branch g'0 pat_sc_eq
                 (let! eff_br, tbr, fb = check_f "branch" g' b in
                  (* As in [TcTerm.tc_eqn], the branch is expected to have the
                     annotation at the pattern, rather than at the scrutinee:
                     e.g., a recursive function in it applied to the
                     pattern reduces. *)
                  let expect_tbr = Subst.subst [NT(as_x.binder_bv, pat_exp)] returns_ty in
                  let rel =
                    if eq
                    then EQUALITY
                    else SUBTYPING (if is_tot_or_ghost_eff eff_br then Some (b, fb.f_sub) else None)
                  in
                  with_context "branch check relation" None (fun _ -> check_relation g' rel tbr expect_tbr);!
                  let! eff = join_eff g eff_br acc_eff in
                  return (eff, expect_tbr)))) in
          (* Branches after a wildcard are dead code, checked, as by TcTerm,
             under the (false) path condition. *)
          check_branches next_path_condition rest eff_br in

    let! eff = check_branches U.t_true branches ETot in
    let ty = Subst.subst [NT(as_x.binder_bv, sc)] returns_ty in
    return (eff, ty, no_tail_facts ())

  | Tm_match {scrutinee=sc; ret_opt=Some (as_x, (Inr c, None, eq)); brs; rc_opt} ->
    (* [returns C] is [returns t], where [t] is [C]'s result type, with an
       effect: computation types carry no specification beyond their effect
       and result type. *)
    let e' = { e with n = Tm_match {scrutinee=sc; ret_opt=Some (as_x, (Inl (U.comp_result c), None, eq)); brs; rc_opt} } in
    let! eff, t, sf = do_check g e' in
    let target = comp_eff c in
    let eff = match eff, target with
              | EGhost, ETot when non_informative g t -> ETot
              | _ -> eff in
    if not (sub_eff g eff target)
    then fail_effect_mismatch g e t eff (U.comp_result c) target
    else return (target, t, sf)

  | Tm_match _ ->
    fail_str "Match with a tactic handler on its returns annotation"

  | Tm_let {lbs=(true, lbs); body} ->
    let lbs, body = Subst.open_let_rec lbs body in
    let! us = check_letrec_types g lbs in
    let xs = letrec_binders lbs in
    let g' = push_binders g xs in
    with_binders g xs us (
      check_letrec_defs g None lbs us ;!
      let! eff, t, fb = check_f "let rec body" g' body in
      let fvs = FStarC.Syntax.Free.names t in
      if xs |> BU.for_some (fun x -> mem x.binder_bv fvs)
      then fail_str "Recursive name escapes its scope"
      else return (eff, t, letrec_facts xs us fb)
    )

  | _ ->
    fail_str (Format.fmt1 "Unexpected term: %s" (tag_of e))

(* The SMT lemma type [t] as a quantified formula with its patterns, as
   [U.smt_lemma_as_forall], with the universes of its binders computed here. *)
and smt_lemma_as_forall (g:env) (t:typ)
  : ML (result term)
  = match U.destruct_lemma_with_smt_patterns t with
    | None -> fail_str "not an SMT lemma"
    | Some (bs0, pre, post, patterns) ->
      let rec univs (g:env) (bs:binders) : ML (result (list universe)) =
        match bs with
        | [] -> return []
        | b::bs ->
          let! u = quietly (universe_of g b.binder_bv.sort) in
          let! us = univs (push_binders g [b]) bs in
          return (u::us)
      in
      let! us = univs g bs0 in
      let body = S.mk (Tm_meta {tm=U.mk_imp pre post;
                                meta=Meta_pattern (S.binders_to_names bs0, patterns)}) t.pos in
      return (List.fold_right2 (fun (b:binder) u out -> U.mk_forall u b.binder_bv out) bs0 us body)

(* A non-recursive [let x = e in body], with [body] checked against [expected]
   if given. In three steps: the definition ([check_let_def]); the body, with
   [x] bound at [let_binder_sort]; and the closing of the body's guard over
   [x] ([close_let_guard]) and, with no expected type, of its type
   ([let_result_typ]). *)
and check_let (g:env) (lb:letbinding) (body:term) (expected:option typ)
  : ML (result (eff & typ & sub_facts))
  = let Inl x0 = lb.lbname in
    let! eff_def, lbtyp, u, tdef, fdef = check_let_def g lb in
    let x0 = { x0 with sort = let_binder_sort g lbtyp tdef } in
    let g', x, body = open_term g (S.mk_binder x0) body in
    let! eff, t, fbody =
      close_let_guard g lb eff_def lbtyp tdef fdef x u (
        match expected with
        | Some t ->
          let! eff_body, fbody = check_against_typ g' body t in
          let! eff = join_eff g eff_def eff_body in
          return (eff, t, fbody)
        | None ->
          let! eff_body, t, fbody = check_f "let body" g' body in
          let! t = let_result_typ g g' lb.lbdef eff_def x u body eff_body t in
          let! eff = join_eff g eff_def eff_body in
          return (eff, t, fbody)) in
    return (eff, t, let_facts (is_tot_or_ghost_eff eff_def) lb.lbdef x.binder_bv u fdef fbody)

(* The definition [e] of a non-recursive [let]. Returns the effect of [e],
   the type [lbtyp] at which it is bound (its annotation, or else its own
   type), the universe of [lbtyp], the type synthesized for [e], if any, and
   the facts about [e].

   Without an annotation, the type of [e] is synthesized. With one, [e] is
   checked as follows, and then the annotation is checked to be a type:
   * A pure or ghost [e] is checked against it (see [check_against_typ]):
     the obligations of [e] meeting it are then where [e]'s own hypotheses
     are in scope, e.g. in [let f : t = (lemma (); f0) in body], [f0] meets
     [t] under the lemma. What [e] establishes beyond its annotation is
     stated in the VC of the body (see [close_let_guard]).
   * The result of an effectful [e] is described by its type only, which
     carries its postcondition, e.g. that [n >= 0] after
     [if n < 0 then fail ""]: that type is synthesized, and then related to
     the annotation.
   The effect the elaborator recorded in [lb.lbeff], that of the whole
   [let], bounds that of [e]: when it is pure or ghost, so is [e]. It only
   chooses between the two strategies, both of which are sound. *)
and check_let_def (g:env) (lb:letbinding)
  : ML (result (eff & typ & universe & option typ & facts))
  = if Tm_unknown? (Subst.compress lb.lbtyp).n
    then (
      (* A [let] appearing inside a *type* may still carry the annotation the
         desugarer left, i.e. none at all: not every producer of a term runs
         it through the elaborator first. *)
      let! eff, tdef, fdef = check_f "let definition" g lb.lbdef in
      (* The definition's type, which Core computed, is well-formed: only
         its universe is needed. *)
      let! u = quietly (universe_of_well_typed_term g tdef) in
      return (eff, tdef, u, Some tdef, fdef)
    )
    else (
      let pure =
        U.is_pure_or_ghost_effect lb.lbeff
        || Ident.lid_equals lb.lbeff PC.effect_Lemma_lid in
      let! eff, tdef, fdef =
        with_context "let definition" (Some (CtxTerm lb.lbdef)) (fun _ ->
          if pure
          then check_against_typ_synth g lb.lbdef lb.lbtyp
          else check_against_typ_by_subtyping g lb.lbdef lb.lbtyp) in
      (* The annotation is checked after the definition, whose guard then
         carries the well-formedness conditions the annotations inside it
         share with this one, e.g. [j < length a] for a local lemma
         [aux (j:nat{j < 16}) : Lemma (index a j == index b j)] whose body
         binds another such lemma: they are in scope of the goals of the
         body. Checked first, the annotation would emit them closed over its
         own binders, as a separate conjunct, and the identical guards of the
         body would then be dropped as cache hits (see [guard]). *)
      let! u = with_context "let type" (Some (CtxTerm lb.lbtyp)) (fun _ -> universe_of g lb.lbtyp) in
      return (eff, lb.lbtyp, u, tdef, fdef)
    )

(* The type at which a [let]'s body sees its variable: its annotation
   [lbtyp], as the user wrote it (it may well be the only form of it that
   exposes, say, an arrow), further refined by what the type [tdef]
   synthesized for the definition says about it. The annotation may be one
   that elaboration inferred, which lacks the refinements that carry the
   definition's postcondition (a lemma's, say). The definition has both
   types, so the variable may be assumed to have both. *)
and let_binder_sort (g:env) (lbtyp:typ) (tdef:option typ)
  : ML typ
  = match tdef with
    | None -> lbtyp
    | Some tdef ->
      if U.term_eq lbtyp tdef then tdef
      else
        let refinement (t:typ) : ML (option (bv & term)) =
          match (Subst.compress (U.flatten_refinement t)).n with
          | Tm_refine {b=y; phi} ->
            let bs, phi = Subst.open_term [S.mk_binder y] phi in
            Some ((List.hd bs).binder_bv, phi)
          | _ -> None
        in
        let r =
          match refinement tdef with
          | Some r -> Some r
          | None ->
            match U.un_squash tdef with
            | Some p -> Some (S.new_bv None lbtyp, p)
            | None -> refinement (N.normalize_refinement N.whnf_steps g.tcenv tdef)
        in
        match r with
        | Some (y, phi) -> U.refine { y with sort = lbtyp } phi
        | None -> lbtyp

(* Close the guard of [f], the body of a [let] binding [x] (of universe [u])
   to the definition [lb.lbdef], of effect [eff_def]. The variable of an
   effectful definition is merely a binder of its type. A pure or ghost
   definition is a term: the guard may assume its defining equation, or have
   it substituted for [x], and the facts [fdef] about it. *)
and close_let_guard (#a:Type) (g:env) (lb:letbinding) (eff_def:eff) (lbtyp:typ) (tdef:option typ)
                    (fdef:facts) (x:binder) (u:universe) (f:result a)
  : ML (result a)
  = if not (is_tot_or_ghost_eff eff_def) then with_binders g [x] [u] f else
    let annotated = not (Tm_unknown? (Subst.compress lb.lbtyp).n) in
    let smt_lemma_typ =
      if U.is_smt_lemma lbtyp then Some lbtyp
      else match tdef with
           | Some t when U.is_smt_lemma t -> Some t
           | _ -> None
    in
    (* As in [TcUtil.should_return], the defining equation of [x] is only
       worth stating if [x] may have more than one value, i.e. its type (or,
       for a function, its result type) is not [unit]-like, e.g. a local
       lemma; and if its definition is not irreducible. Such equations would
       only drag the definition, a lambda say, into the context of every
       later obligation. *)
    let def_eq_useful =
      let c = lbtyp |> U.arrow_formals_comp |> snd in
      U.is_pure_or_ghost_comp c
      && not (VCUtil.is_unit_like (N.unfold_whnf g.tcenv (U.comp_result c)))
      && (let head, _ = U.head_and_args_full lb.lbdef in
          match (U.un_uinst head).n with
          | Tm_fvar fv -> not (Env.is_irreducible g.tcenv (S.lid_of_fv fv))
          | _ -> true)
    in
    with_guard f (function
      | Inr err -> fail_propagate err
      | Inl (res, None) -> return res
      | Inl (res, Some form) ->
        (* A local lemma with SMT patterns, e.g.
           [let fwd x : Lemma (p x) [SMTPat (f x)] = ... in e], is available
           to the SMT solver in [e], as [TcTerm] does. *)
        let! form =
          match smt_lemma_typ with
          | None -> return form
          | Some lem_typ ->
            let! quant = handle_with (smt_lemma_as_forall g lem_typ) (fun _ -> return U.t_true) in
            return (U.mk_imp quant form)
        in
        (* [let unfold x = e] asks for [e] to be substituted into the VC, as
           [TcTerm] does. Without SMT, the guard must simplify to [True] as it
           stands: substituting the definition (which is equivalent to
           quantifying over [x] with its defining equation) lets it do so
           when it relates [x] to the definition itself. *)
        let inline_vc = U.has_attribute lb.lbattrs PC.inline_let_vc_attr || Options.no_smt () in
        (* Even when [x] does not occur in the guard, its defining equation
           is kept if it is useful, as TcTerm does: the definition may be
           there only to put a term into the VC, as a trigger, e.g.
           [introduce forall x y. q x y with let p = (x, y) in ()]. *)
        let x_free = def_eq_useful || mem x.binder_bv (FStarC.Syntax.Free.names form) in
        let quantified = x_free && not inline_vc in
        (* When [x] is quantified, what the definition's own type says about
           it is already said by [x]'s type: only the facts about its
           subterms remain. Otherwise they are stated about the definition
           itself, and, preferably, what its annotation says about it, as
           TcTerm assumes it: it may be stated differently than the
           definition's own type, even when the two are [term_eq], e.g. in
           the residual types of abstractions, which the SMT encoding of the
           abstractions depends on, as in
           [let _ : squash (p (fun x -> f x)) = lemma f in e]. *)
        let facts = Thunk.force (if quantified then fdef.f_sub else fdef.f_term) in
        let facts =
          if quantified || not annotated then facts
          else type_facts g true lb.lbdef lbtyp @ facts
        in
        (* When the annotation was pushed into the definition, its type was
           not synthesized: what it would have said about the definition
           beyond the annotation is stated here instead (see
           [let_binder_sort]), e.g. the [squash p] of
           [let _ : unit = (let x = e1 in lemma x) in body]. *)
        let facts =
          match tdef with
          | None -> facts @ Thunk.force fdef.f_tail
          | Some _ -> facts
        in
        let facts = dedup_facts facts in
        if !dbg_facts then Format.print2 "let facts for %s: %s\n" (show lb.lbdef) (show facts);
        let form =
          if inline_vc then Subst.subst [NT(x.binder_bv, lb.lbdef)] form
          else if not x_free then form
          else if def_eq_useful then close_with_definition x u lb.lbdef form
          else U.mk_forall u x.binder_bv form in
        let form = if Nil? facts then form else U.mk_imp (U.mk_conj_l facts) form in
        reemit_guard g form ;!
        return res)

(* The type of [let x = e in body], from the type [t] of [body], in which
   [x] may not escape. *)
and let_result_typ (g g':env) (e:term) (eff_def:eff) (x:binder) (u:universe)
                   (body:term) (eff_body:eff) (t:typ)
  : ML (result typ)
  = let x_in_t = mem x.binder_bv (FStarC.Syntax.Free.names t) in
    if is_tot_or_ghost_eff eff_def then (
      if x_in_t
      then return (Subst.subst [NT(x.binder_bv, e)] t)
      (* The definition's refinement is a fact about the rest of the
         computation; for a pure body, it is kept in the VC (see
         [close_let_guard]), but the result of an effectful body is only
         described by its type, so it is kept there, e.g.
         [let Some x = admit (); f () in ...] where [admit () : _:unit{False}]
         and [f] is effectful: the exhaustiveness check of the pattern relies
         on [False]. *)
      else if is_tot_or_ghost_eff eff_body then return t
      else
        let phi_x = U.refinement_hypothesis
                      (N.normalize_refinement N.whnf_steps g.tcenv x.binder_bv.sort)
                      (S.bv_to_name x.binder_bv) in
        if U.is_t_true phi_x then return t
        else
          let r = S.new_bv None t in
          return (U.refine r (U.mk_exists u x.binder_bv phi_x))
    )
    else (
      (* The result of an effectful definition cannot be substituted into
         the body's type. As in [TcUtil], [x] is instead closed
         existentially, over what the body's type says about it and, for a
         pure body, over the body itself (the value of the [let]), e.g.
         [let s = f x in C s y] has type [r:t{exists s. r == C s y}]. *)
      let x_in_body = mem x.binder_bv (FStarC.Syntax.Free.names body) in
      let eq_body = is_tot_or_ghost_eff eff_body in
      if not x_in_t && not eq_body then return t
      else if not x_in_t && not x_in_body then
        (* [body] is pure here ([eq_body], by the test above) and does not
           mention [x]: it is the value of the [let], if it returns at all,
           e.g. [let tok = f () in v] has value [v]. *)
        if U.is_unit (U.unrefine (N.unfold_whnf g'.tcenv t)) then return t
        else
          let r = S.new_bv None t in
          let! u_b = universe_of_well_typed_term g' t in
          return (U.refine r (U.mk_eq2 u_b t (S.bv_to_name r) body))
      else
        let tn = if x_in_t then N.normalize_refinement N.whnf_steps g'.tcenv t else t in
        let base = if x_in_t then U.unrefine tn else t in
        if mem x.binder_bv (FStarC.Syntax.Free.names base)
        then fail_str "Name escapes its scope"
        else
          let r = S.new_bv None base in
          let phi_t = if x_in_t then [U.refinement_hypothesis tn (S.bv_to_name r)] else [] in
          let! eq =
            if eq_body then
              let! u_b = universe_of_well_typed_term g' base in
              return [U.mk_eq2 u_b base (S.bv_to_name r) body]
            else return []
          in
          return (U.refine r (mk_exists_unrefined u x.binder_bv (U.mk_conj_l (phi_t @ eq))))
    )

(* A [match] without a return annotation, whose branches are checked against
   [expected] if given, or else against the type of the first one (or the
   residual type recorded by the elaborator, if any). *)
and check_match (g:env) (r:R.t) (sc:term) (branches:list branch) (rc_opt:option residual_comp) (expected:option typ)
  : ML (result (eff & typ & sub_facts))
  = let! eff_sc, t_sc = check "scrutinee" g sc in
    let branches0 = branches in
    let! u_sc = universe_of_well_typed_term g t_sc in
    (* With no expected type, the match's type is the residual type the
       elaborator recorded, which is typically unrefined. As in [TcUtil.bind_cases], it is
       refined with what each branch's own type says under the condition that
       the branch is taken (otherwise, e.g., [if b then fail "" else (); e]
       forgets [not b] when checking [e]). [res_x] names the match's result. *)
    let res_x : option bv =
      match expected, rc_opt with
      | None, Some ({ residual_typ = Some t }) when is_tot_or_ghost_eff eff_sc ->
        Some (S.new_bv None t)
      | _ -> None
    in
    let! u_res : universe =
      match res_x with
      | None -> return U_zero
      | Some x -> universe_of g x.sort
    in
    (* [w] is the branch itself, when it is pure: the match's result is then
       equal to it. Facts that mention the pattern variables [bs] are
       quantified existentially, together with the equation relating the
       scrutinee to the pattern, e.g., [PH? h ==> exists p. h == PH p /\ x == p]. *)
    let branch_fact (bs:binders) (us:list universe) (pat_sc_eq:term)
                    (cond:term) (tbr:typ) (w:option term) : ML (list term) =
      match res_x with
      | None -> []
      | Some x ->
        let rec conjuncts (t:term) : ML (list term) =
          let hd, args = U.head_and_args_full t in
          match (U.un_uinst hd).n, args with
          | Tm_fvar fv, [(a, _); (b, _)] when S.fv_eq_lid fv PC.and_lid ->
            conjuncts a @ conjuncts b
          | _ -> [t] in
        let mentions_bs (f:term) : ML bool =
          let fvs = FStarC.Syntax.Free.names f in
          BU.for_some (fun (b:binder) -> mem b.binder_bv fvs) bs
        in
        let phi =
          U.refinement_hypothesis (N.normalize_refinement N.whnf_steps g.tcenv tbr) (S.bv_to_name x)
          |> conjuncts
          |> List.filter (fun (f:term) -> not (U.is_t_true f))
        in
        let phi =
          match w with
          | None -> phi
          | Some b -> phi @ [U.mk_eq2 u_res x.sort (S.bv_to_name x) b]
        in
        let phi_free, phi_bound = List.partition (fun f -> not (mentions_bs f)) phi in
        let phi_bound =
          match phi_bound with
          | [] -> []
          | _ ->
            if List.length bs <> List.length us then [] else
            [List.fold_right2
              (fun (b:binder) (u:universe) (body:term) -> U.mk_exists u b.binder_bv body)
              bs us
              (U.mk_conj_l (pat_sc_eq :: phi_bound))]
        in
        match phi_free @ phi_bound with
        | [] -> []
        | phi -> [U.mk_imp cond (U.mk_conj_l phi)]
    in
    (* The facts [fb] about the branch [b] taken under [cond], or else
       [this], the equation [pat_sc_eq] relating the scrutinee to the
       pattern binding [bs] (see [branch_conditions]). *)
    let branch_facts (bs:binders) (us:list universe) (cond this:term) (fb:facts)
      : ML (Thunk.t (list term)) =
      Thunk.mk (fun () ->
        (* Facts that do not mention the pattern variables hold whenever the
           branch is taken: stating them under [forall bs. sc == p ==> ...]
           would leave it to the SMT solver to find the [bs], e.g. for
           [eliminate exists]. *)
        let mentions_bs (f:term) : ML bool =
          let fvs = FStarC.Syntax.Free.names f in
          BU.for_some (fun (b:binder) -> mem b.binder_bv fvs) bs
        in
        let fb_free, fb_bound = List.partition (fun f -> not (mentions_bs f)) (Thunk.force fb.f_term) in
        (match fb_free with
         | [] -> []
         | _ -> [U.mk_imp cond (U.mk_conj_l fb_free)]) @
        (match fb_bound with
         | [] -> []
         | _ -> [mk_forall_l us bs (U.mk_imp this (U.mk_conj_l fb_bound))]))
    in
    (* Returns the effect and type of the match, the facts for its type (see
       [branch_fact]), and the facts about its branches. *)
    let rec check_branches path_condition
                           branch_typ_opt
                           branches
      : ML (result (eff & typ & list term & list (Thunk.t (list term))))
      = match branches with
        | [] ->
          (match branch_typ_opt with
           | None ->
             fail_str "could not compute a type for the match"

           | Some (eff, t) ->
             if match_covers_bool g t_sc branches0 then return (eff, t, [], []) else
             match exhaustiveness_obligation r path_condition with
             | None -> return (eff, t, [], [])
             | Some phi -> guard g phi ;! return (eff, t, [], []))

        | (p, None, b) :: rest ->
          let _, (p, _, b) = open_branch g (p, None, b) in
          let! (bs, us) = with_context "check_pat" None (fun _ -> check_pat g p t_sc) in
          let! branch_condition = pattern_branch_condition g sc p in
          let pat_sc_eq =
            U.mk_eq2 u_sc t_sc sc
            (PatternUtils.raw_pat_as_exp g.tcenv p |> Option.must |> fst) in
          let hyp, this, next_path_condition =
              branch_conditions path_condition branch_condition pat_sc_eq
          in
          let g_h = push_branch_hypothesis g hyp in
          let g'0 = push_binders g_h bs in
          let g' = push_hypothesis g'0 pat_sc_eq in
          let! eff_br, tbr, facts, fb =
            weaken_branch g hyp
            (with_binders g_h bs us
              (weaken_branch g'0 pat_sc_eq
                 (match branch_typ_opt with
                  | None ->
                    let! eff_br, tbr, fb = with_context "branch" (Some (CtxTerm b)) (fun _ -> check_f "branch" g' b) in
                    check_no_escape bs tbr;!
                    return (eff_br, tbr, [], fb)

                  | Some (acc_eff, expect_tbr) ->
                    let against () : ML (result (eff & typ & list term & facts)) =
                      let! eff_br, fb =
                        with_context "branch" (Some (CtxTerm b)) (fun _ ->
                          check_against_typ g' b expect_tbr) in
                      let! eff = join_eff g eff_br acc_eff in
                      return (eff, expect_tbr, [], fb)
                    in
                    if None? res_x then against () else
                    handle_with
                      (let! eff_br, tbr, fb = check_f "branch" g' b in
                       check_no_escape bs tbr;!
                       let w = if is_tot_or_ghost_eff eff_br then Some b else None in
                       check_subtype g' (Option.map (fun b -> (b, fb.f_sub)) w) tbr expect_tbr;!
                       let! eff = join_eff g eff_br acc_eff in
                       (* The branch is taken under [hyp], which does not
                          mention the pattern variables. *)
                       return (eff, expect_tbr, branch_fact bs us pat_sc_eq hyp tbr w, fb))
                      against))) in
          let fb = branch_facts bs us hyp this fb in
          (* Branches after a wildcard are dead code, checked, as by TcTerm,
             under the (false) path condition: their facts are not needed. *)
          let! eff, t, more, more_fb = check_branches next_path_condition (Some (eff_br, tbr)) rest in
          let more_fb = match p.v with | Pat_var _ -> [] | _ -> more_fb in
          return (eff, t, facts @ more, fb :: more_fb)
    in

    let! branch_typ_opt =
        match expected, rc_opt with
        | Some t, _ -> return (Some (ETot, t))
        | None, Some ({ residual_typ = Some t }) ->
          universe_of g t ;!
          return (Some (ETot, t))

        | _, _ ->
          return None
    in
    let! eff_br, t_br, facts, fbs =
      let ctx =
        match branch_typ_opt with
        | None -> None
        | Some (_, t) -> Some (CtxTerm t)
      in
      with_context "check_branches" ctx
        (fun _ -> check_branches U.t_true branch_typ_opt branches)
    in
    let! eff = join_eff g eff_sc eff_br in
    let t_br =
      match res_x, facts with
      | Some x, _::_ when not (is_tot_or_ghost_eff eff) -> U.refine x (U.mk_conj_l facts)
      | _ -> t_br
    in
    return (eff, t_br, { s_sub = facts_concat fbs; s_tail = Some (no_facts_l ()) })

(* Check [e] against the type [t], returning the effect of [e]. The expected
   type is pushed into [let]s and [match]es, as [TcTerm] does: a guard is then
   emitted where the relevant binders and path conditions are in scope, and
   with the pure result of an effectful computation as the witness. *)
and check_against_typ (g:env) (e:term) (t:typ)
  : ML (result (eff & facts))
  = let! eff, _, f = check_against_typ_synth g e t in
    return (eff, f)

(* As [check_against_typ], also returning the type synthesized for [e] when
   [e] is not one that the expected type is pushed into: that type is then
   related to [t] by subtyping, and may say more about [e] than [t] does. *)
and check_against_typ_synth (g:env) (e:term) (t:typ)
  : ML (result (eff & option typ & facts))
  = (* As in [do_check_and_promote]: e.g. [let z = ghost_f y in ()] is
       total, and may be composed with [Div]. *)
    let promote (ef:eff) : ML eff =
      match ef with
      | EGhost -> if non_informative g t then ETot else EGhost
      | _ -> ef
    in
    (* [e], checked against [t], is known to have type [t]. As [t] was
       pushed into [e], its type was not synthesized: what that type would
       have said about [e] beyond [t] is what the expression its [let]s end
       with establishes, e.g. the [squash p] of [lemma ()] in a branch
       [(lemma0 (); lemma ())] checked against [unit]. (Not so for an
       effectful [e], whose tail is not necessarily reached.) *)
    let checked (ef:eff) (sf:sub_facts) : ML (result (eff & option typ & facts)) =
      let ef = promote ef in
      let f = mk_facts g e ef t sf in
      let f =
        match sf.s_tail with
        | Some tl when is_tot_or_ghost_eff ef ->
          { f with f_term = Thunk.mk (fun () -> dedup_facts (Thunk.force f.f_term @ Thunk.force tl)) }
        | _ -> f
      in
      return (ef, None, f)
    in
    match (Subst.compress e).n with
    | Tm_let {lbs=(false, [lb]); body} ->
      let! eff, _, sf = check_let g lb body (Some t) in
      checked eff sf
    | Tm_match {scrutinee=sc; ret_opt=None; brs; rc_opt}
        when List.for_all (fun (_, w, _) -> None? w) brs ->
      let! eff, _, sf = check_match g e.pos sc brs rc_opt (Some t) in
      checked eff sf
    | Tm_let {lbs=(true, lbs); body} ->
      (* The SMT encoding knows nothing of a local recursive function, so the
         expected type is related to the body's, rather than to the whole
         [let rec]. *)
      let lbs, body = Subst.open_let_rec lbs body in
      let! us = check_letrec_types g lbs in
      let xs = letrec_binders lbs in
      let! eff, topt, fb =
        with_binders g xs us (
          check_letrec_defs g None lbs us ;!
          check_against_typ_synth (push_binders g xs) body t) in
      let sf = letrec_facts xs us fb in
      (* What the body's own type says about it, which [letrec_facts] only
         states under an existential over the recursive names (e.g. the
         [nat] of [g n] in [let rec g (m:nat) : nat = ... in g n]), is said
         about the whole [let rec] instead, when that type does not mention
         them. *)
      (match topt with
       | Some te
           when (let fvs = FStarC.Syntax.Free.names te in
                 not (BU.for_some (fun (x:binder) -> mem x.binder_bv fvs) xs)) ->
         return (eff, topt, mk_facts g e eff te sf)
       | _ -> checked eff sf)
    | Tm_meta {tm}
        when (match (Subst.compress (U.unmeta tm)).n with
              | Tm_let _ | Tm_match _ -> true
              | _ -> false) ->
      let! eff, topt, f = check_against_typ_synth g tm t in
      (match topt with
       | None -> checked eff (inner_facts f)
       | Some te -> return (eff, topt, mk_facts g e eff te (inner_facts f)))
    | Tm_abs _ ->
      begin match abs_against_arrow g e t with
      | None -> check_against_typ_by_subtyping g e t
      | Some (xs, body, formals, c) ->
      (* A function checked against an arrow type has its body checked
         against the arrow's computation type, rather than having its type
         synthesized and then related to the arrow: the body, e.g. a [let]
         binding a local SMT lemma, may then scope over the goal. *)
      let _, xs, body = open_term_binders g xs body in
      let! us = with_context "abs binders" None (fun _ -> check_binders g xs) in
      let sub = List.map2 (fun (f:binder) (x:binder) -> NT(f.binder_bv, S.bv_to_name x.binder_bv)) formals xs in
      (* As by TcTerm (see [TcTerm.tc_abs_check_binders]), the annotation of
         each binder is related to its expected type in the scope of the
         binders before it only. [gi.at_top] is kept for closing the guard
         over the binders of the spine (see [with_binders]), not for
         checking anything else. *)
      let rec check_formals (gi:env) (formals:binders) (xs:binders) (us:universes) : ML (result unit) =
        let gi_ = { gi with at_top = false } in
        match formals, xs, us with
        | f::formals, x::xs, u::us ->
          label_guard gi_ x.binder_bv.sort.pos
            (fun () -> Errors.mkmsg "Type annotation on parameter incompatible with the expected type")
            (with_context "abs binder subtyping" None (fun _ ->
              check_subtype gi_ None (Subst.subst sub f.binder_bv.sort) x.binder_bv.sort)) ;!
          with_binders gi [x] [u]
            (check_formals { push_binder gi x with at_top = gi.at_top } formals xs us)
        | _ ->
          with_context "abs body" (Some (CtxTerm body)) (fun _ ->
            (* At the range of the abstraction, as TcTerm's
               [check_expected_effect], called by [tc_abs] in the
               abstraction's environment. *)
            label_postcondition gi_ e (check_against_comp gi_ body (Subst.subst_comp sub c)))
      in
      check_formals g formals xs us ;!
      return (ETot, None, no_facts ())
      end
    | _ -> check_against_typ_by_subtyping g e t

(* [e <: t by tac]: as in [TcTerm], the guard of checking [e] against [t] is
   left to [tac], even when trivial (so that [e <: t by fail ""] fails). *)
and with_ascription_tactic (#a:Type) (g:env) (tac:option term) (f:unit -> ML (result a))
  : ML (result a)
  = match tac with
    | None -> f ()
    | Some tac ->
      with_guard (f ()) (function
        | Inr err -> fail_propagate err
        | Inl (res, phi) ->
          let phi = match phi with | None -> U.t_true | Some phi -> phi in
          reemit_guard g (CommonBase.mk_by_tactic tac (U.mk_squash phi)) ;!
          return res)

and check_against_typ_by_subtyping (g:env) (e:term) (t:typ)
  : ML (result (eff & option typ & facts))
  = let! eff, te, f = check_f "checked term" g e in
    let w = if is_tot_or_ghost_eff eff then Some (e, f.f_sub) else None in
    let chk () = check_subtype g w te t in
    with_context "subtyping" (Some (CtxRel te (SUBTYPING w) t)) (fun _ ->
      (* [check_subtype] labels its guard when it has a witness. *)
      if Some? w then chk () else label_subtyping g e te t (chk ())) ;!
    return (eff, Some te, f)

(* For [e = fun xs -> body] (one group of binders) and [t] an arrow with at
   least as many binders, looking through abbreviations but not through
   refinements (which would drop their predicates): [xs], [body], the first
   [|xs|] binders of [t] and the computation type they abstract. *)
and abs_against_arrow (g:env) (e:term) (t:typ)
  : ML (option (binders & term & binders & comp))
  = let xs, body, _ = U.abs_one_group_ln e in
    let n = List.length xs in
    let t =
      let t = Subst.compress t in
      if Tm_arrow? t.n then t else U.unascribe (N.unfold_whnf g.tcenv t)
    in
    let formals, c = U.arrow_formals_comp_strict t in
    let len = List.length formals in
    if len = 0 then None
    else if len < n then
      (* E.g. [fun frame s0 -> e] against [frame:slprop -> act frame], where
         [act frame] is an abbreviation for an arrow: the first [len]
         binders are checked against [t], and the function of the rest (a
         spine of unary abstractions, so still locally nameless) against
         [c]. *)
      let rec peel (k:int) (e:term) : ML term =
        if k = 0 then e
        else match (Subst.compress e).n with
             | Tm_abs {body} -> peel (k - 1) body
             | _ -> failwith "impossible: abs_against_arrow"
      in
      Some (fst (List.splitAt len xs), peel len e, formals, c)
    else if len = n then Some (xs, body, formals, c)
    else
      let formals, rest = List.splitAt n formals in
      Some (xs, body, formals, S.mk_Total (U.arrow rest c))

(* Check [e] against [c], a
   computation type of any effect. *)
and check_against_comp (g:env) (e:term) (c:comp)
  : ML (result unit)
  = let! _ = check_against_comp_f g e c in
    return ()

(* Also returning the facts about [e]. *)
and check_against_comp_f (g:env) (e:term) (c:comp)
  : ML (result facts)
  = let reflected =
      let hd, args = U.head_and_args_full (U.unmeta e) in
      match (Subst.compress hd).n, args with
      | Tm_constant (FStarC.Const.Const_reflect l), [(e', _)]
          when I.lid_equals l (U.comp_effect_name c) ->
        Some e'
      | _ -> None
    in
    match reflected with
    | Some e' ->
      (* [M?.reflect e <: C], as elaborated by TcTerm for a reflection with
         an expected computation type [C] in [M]: [e] is a representation of
         [C]. *)
      let! u = universe_of_well_typed_term g (U.comp_result c) in
      let repr = Env.reify_comp g.tcenv c u in
      let! eff_e, fe' = check_against_typ g e' repr in
      if not (ETot? eff_e) then fail_str "Expected a total argument to reflect"
      else
        let eff, t = comp_as_eff_and_type c in
        return (mk_facts g e eff t { no_sub_facts () with s_sub = fe'.f_term })
    | None ->
    let target_eff, target_t = comp_as_eff_and_type c in
    let! eff, fe = check_against_typ g e target_t in
    let eff =
      match eff, target_eff with
      | EGhost, ETot when non_informative g target_t -> ETot
      | _ -> eff
    in
    if not (sub_eff g eff target_eff)
    then (
      let! _, t_e = handle_with (check "computed type" g e) (fun _ -> return (eff, target_t)) in
      fail_effect_mismatch g e t_e eff target_t target_eff
    )
    else return fe

and check_letrec_types (g:env) (lbs:list letbinding)
  : ML (result (list universe))
  = match lbs with
    | [] -> return []
    | lb::lbs ->
      let! u = with_context "let rec type" (Some (CtxTerm lb.lbtyp)) (fun _ -> universe_of g lb.lbtyp) in
      let! us = check_letrec_types g lbs in
      return (u::us)

(* Check the definitions of a nest of mutually recursive definitions, whose
   names (bound variables) and universes are already opened, and whose types
   are well-formed, at universes [us]. The guard may mention the names in the
   nest, at their declared types (the caller closes over them).

   A definition whose type is a total arrow must terminate. As in
   [TcTerm.tc_abs], its first [arity] binders are opened as the binders of its
   type, and every terminating name in the nest is then in scope at a type
   refined to only accept arguments that precede those binders (see
   [Termination.guard_letrecs]); the guard of the body is closed over those refined
   names right away, as it would be unsound to assume them at their declared
   types. Other definitions (and other names in the nest) are checked
   assuming the names at their declared types, as is sound for partial
   correctness. *)
and check_letrec_defs (g:env) (top:option (list subst_elt)) (lbs:list letbinding) (us:list universe)
  : ML (result unit)
  = (* [top]: for a top-level nest, maps its local names back to the
       top-level names; the guard of each body is stated with those,
       rather than quantified over the local names (see
       [check_top_level_letrec']).

        A total definition with [@@admit_termination] is not itself known to
       terminate, but, as in [TcTerm], its body must still respect the
       termination arguments of the other names in the nest. *)
    let lb_info (lb:letbinding) : ML (option (int & binders & comp)) =
      let bs, _, _ = U.abs_formals lb.lbdef in
      match bs with
      | [] -> None
      | _ ->
        let formals, c = N.get_n_binders_no_unrefine g.tcenv (List.length bs) lb.lbtyp in
        let arity = List.length formals in
        if arity = 0 then None
        else if U.comp_effect_name c |> Env.lookup_effect_quals g.tcenv |> List.contains TotalEffect
        then Some (arity, formals, c)
        else None
    in
    let admitted (lb:letbinding) = U.has_attribute lb.lbattrs PC.admit_termination_lid in
    let infos = List.map2 (fun lb u -> lb, u, lb_info lb) lbs us in
    let letrecs =
      infos |> List.collect (fun (lb, _, info) ->
        match info with
        | Some (arity, _, _) when not (admitted lb) -> [(lb.lbname, arity, lb.lbtyp, lb.lbunivs)]
        | _ -> [])
    in
    let g_plain = push_binders g (letrec_binders lbs) in
    let nonterminating =
      infos |> List.collect (fun (lb, u, info) ->
        if None? info || admitted lb then [S.mk_binder { Inl?.v lb.lbname with sort = lb.lbtyp }, u] else [])
    in
    let universe_of_name (l:lbname) : ML universe =
      match List.tryFind (fun (lb, _, _) -> S.bv_eq (Inl?.v lb.lbname) (Inl?.v l)) infos with
      | Some (_, u, _) -> u
      | None -> failwith "impossible: universe_of_name"
    in
    let check_one (lbi : letbinding & universe & option (int & binders & comp)) : ML (result unit) =
      let lb, _, info = lbi in
      match (Subst.compress lb.lbdef).n, info with
      | Tm_abs _, None ->
        with_context "let rec definition" (Some (CtxTerm lb.lbdef)) (fun _ ->
          check_against_comp g_plain lb.lbdef (S.mk_Total lb.lbtyp))

      | Tm_abs _, Some (arity, formals, c) ->
        let bs, body, rc = U.abs_formals lb.lbdef in
        let bs0, bs1 = List.splitAt arity bs in
        let body = if Nil? bs1 then body else U.abs bs1 body rc in
        let c = Subst.close_comp formals c in
        let formals = Subst.close_binders formals in
        (* As TcTerm, which checks the definition's own binders, name the
           formals as in the definition, not as in its type: they appear
           in the termination goals. *)
        let formals =
          List.map2 (fun (b:binder) (f:binder) ->
            if S.is_null_bv b.binder_bv then f
            else { f with binder_bv = { f.binder_bv with ppname = b.binder_bv.ppname } })
            bs0 formals
        in
        let g', formals, opening = open_binders g formals in
        let c = Subst.subst_comp opening c in
        let! ufs = with_context "let rec formals" None (fun _ -> check_binders g formals) in
        let sub = List.map2 (fun (b:binder) (f:binder) -> NT(b.binder_bv, S.bv_to_name f.binder_bv)) bs0 formals in
        (* Rename the definition's binders to the formals by closing and
           reopening, not by [sub], which would locate every occurrence at
           the binder. *)
        let body = Subst.subst opening (Subst.close bs0 body) in
        with_binders g formals ufs (
          let rec check_actuals (bs0:binders) (formals:binders) : ML (result unit) =
            match bs0, formals with
            | b::bs0, f::formals ->
              let sort = Subst.subst sub b.binder_bv.sort in
              let! _ = with_context "let rec binder" (Some (CtxTerm sort)) (fun _ -> universe_of g' sort) in
              with_context "let rec binder subtyping" None (fun _ ->
                check_subtype g' None f.binder_bv.sort sort) ;!
              check_actuals bs0 formals
            | _ -> return ()
          in
          check_actuals bs0 formals ;!
          (* The termination goals are labelled at the range of the
             environment: as in TcTerm, that of the definition, which
             includes the recursive calls. *)
          let refined =
            Termination.guard_letrecs true
              (Env.set_range { g'.tcenv with letrecs = letrecs } lb.lbdef.pos)
              formals c
          in
          (* The refined types are the formal types, already checked, with a
             [<<] refinement, whose universe instantiations [guard_letrecs]
             leaves as fresh unification variables. Check the refined types
             here, in context, which solves them. E.g., the decreases clause
             of a polymorphically recursive function may not be well-typed
             at the types of the recursive calls. *)
          let rec check_refined (ts:list typ) : ML (result unit) =
            match ts with
            | [] -> return ()
            | t::ts ->
              let! _ = with_context "let rec refined type" (Some (CtxTerm t))
                         (fun _ -> universe_of g' t) in
              check_refined ts
          in
          check_refined (List.map (fun (_, t, _) -> t) refined) ;!
          let refined =
            refined |> List.map (fun (l, t, _) ->
              let t = N.reduce_uvar_solutions g'.tcenv t in
              S.mk_binder { Inl?.v l with sort = t }, universe_of_name l)
          in
          let bs = List.map fst refined @ List.map fst nonterminating in
          let bus = List.map snd refined @ List.map snd nonterminating in
          let g'' = push_binders g' bs in
          let check_body () =
            with_context "let rec body" (Some (CtxTerm body)) (fun _ ->
              check_against_comp g'' body c)
          in
          match top with
          | None -> with_binders g' bs bus (check_body ())
          | Some back ->
            with_guard (check_body ()) (function
              | Inr err -> fail_propagate err
              | Inl (res, None) -> return res
              | Inl (res, Some form) ->
                reemit_guard g' (Subst.subst back form) ;!
                return res))

      | _ ->
        fail_str (Format.fmt1 "Only function literals may be defined recursively; got %s"
                    (show lb.lbdef))
    in
    let rec check_all infos : ML (result unit) =
      match infos with
      | [] -> return ()
      | i::is -> check_one i ;! check_all is
    in
    check_all infos

and check_binders (g_initial:env) (xs:binders)
  : ML (result (list universe))
  = let rec aux g xs : ML _ =
      match xs with
      | [] ->
        return []

      | x ::xs ->
        let! _, t = check "binder sort" g x.binder_bv.sort in
        let! u = is_type g t in
        with_binders g [x] [u] (
          let g' = push_binder g x in
          let! us = aux g' xs in
          return (u::us)
        )
    in
    aux g_initial xs

//
// May be called with an effectful comp type, e.g. from within an arrow
// Caller should enforce Tot/GTot if needed
//
and check_comp (g:env) (c:comp)
  : ML (result universe)
  = match c.n with
    (* [Tot] and [GTot] are primitive: they have no signature to apply and no
       representation, so all there is to check is that the result is a type. *)
    | Comp ct when PC.is_tot_or_gtot_lid ct.effect_name ->
      let! _, t = check "(G)Tot comp result" g (U.comp_result c) in
      is_type g t
    | Comp ct ->
      (* A comp is its effect name applied to the result type. *)
      let u = g.tcenv.universe_of g.tcenv ct.result_typ in
      let effect_app_tm =
        let head = S.mk_Tm_uinst (S.fvar ct.effect_name None) [u] in
        S.mk_Tm_app head [as_arg ct.result_typ] ct.result_typ.pos in
      let! _, t = check "effectful comp" g effect_app_tm in
      with_context "comp fully applied" None (fun _ -> check_subtype g None t S.teff);!
      return (Env.effect_universe g.tcenv ct.effect_name u)

and universe_of (g:env) (t:typ)
  : ML (result universe)
  = let! _, t = check "universe of" g t in
    is_type g t

and universe_of_well_typed_term (g:env) (t:typ)
  : ML (result universe)
  = (* Computed mostly syntactically (see [UniverseOf]); otherwise, by
       checking [t]. *)
    try
      let u = UniverseOf.universe_of UniverseOf.no_hooks g.tcenv t in
      return u
    with
    | _ -> universe_of g t

and check_pat (g:env) (p:pat) (t_sc:typ) : ML (result (binders & universes)) =
  let rec unrefine_tsc (t_sc:typ) : ML typ =
    let t = N.normalize_refinement N.whnf_steps g.tcenv (U.unmeta t_sc) |> U.unmeta in
    match (Subst.compress t).n with
    | Tm_refine {b} -> unrefine_tsc b.sort
    | _ -> t in

  match p.v with
  | Pat_constant c ->
    let e =
      match c with
      | FStarC.Const.Const_machine_int(repr, base, sw, w) ->
        FStarC.ToSyntax.ToSyntax.desugar_machine_integer g.tcenv.dsenv repr base (sw, w) p.p
      | _ ->
        mk (Tm_constant c) p.p in
    let! _, t_const = check "pat_const" g e in
    let! _ = with_context "check_pat constant" None (fun () -> check_subtype g (Some (e, no_facts_l ())) t_const (unrefine_tsc t_sc)) in
    return ([], [])

  | Pat_var bv ->
    let b = S.mk_binder {bv with sort=t_sc} in
    let! [u] = with_context "check_pat_binder" None (fun _ -> check_binders g [b]) in
    return ([b], [u])

  | Pat_cons (fv, usopt, pats) ->
    let us = if None? usopt then [] else usopt |> Option.must in

    let formals, t_pat =
      Env.lookup_and_inst_datacon g.tcenv us (S.lid_of_fv fv)
      |> U.arrow_formals in

    let dot_pats, rest_pats =
      let pats = pats |> List.map fst in
      pats |> BU.prefix_until (fun p -> match p.v with
                                    | Pat_dot_term _ -> false
                                    | _ -> true)
           |> Option.map (fun (dot_pats, pat, rest_pats) ->
                            dot_pats, (pat::rest_pats))
           |> Option.dflt (pats, []) in

    let dot_formals, rest_formals = List.splitAt (List.length dot_pats) formals in

    let! ss = fold2 (fun ss {binder_bv=f} p ->
      let expected_t = Subst.subst ss f.sort in
      let! pat_dot_t =
        match p.v with
        | Pat_dot_term (Some t) -> return t
        | _ -> fail_str "check_pat in core has unset dot pattern" in

      let! _, p_t = check "pat dot term" g pat_dot_t in
      let!_ = with_context "check_pat cons" None (fun _ -> check_subtype g (Some (pat_dot_t, no_facts_l ())) p_t expected_t) in

      return (ss@[NT (f, pat_dot_t)])) [] dot_formals dot_pats in

    let! _, ss, bs, us = fold2 (fun (g, ss, bs, us) {binder_bv=f} p ->
      let expected_t = Subst.subst ss f.sort in
      let! (bs_p, us_p) = with_binders g bs us (check_pat g p expected_t) in
      let p_e = PatternUtils.raw_pat_as_exp g.tcenv p |> Option.must |> fst in
      return (push_binders g bs_p,
              ss@[NT (f, p_e)],
              bs@bs_p,
              us@us_p)) (g, ss, [], []) rest_formals rest_pats in

    let t_pat = Subst.subst ss t_pat in

    let!_ = no_guard (check_scrutinee_pattern_type_compatible g (unrefine_tsc t_sc) t_pat) in

    return (bs, us)

  | _ -> fail_str "check_pat called with a dot pattern"

and check_scrutinee_pattern_type_compatible (g:env) (t_sc t_pat:typ)
  : ML (result precondition)
  = let open Env in
    let err (s:string) =
      fail [
        flow (break_ 1) [
          text "Scrutinee type";
          fquotes (pp t_sc);
          text "and pattern type";
          fquotes (pp t_pat);
          text "are not compatible because";
          text s;
        ]
      ]
    in

    let head_sc, args_sc = U.head_and_args_full t_sc in
    let head_pat, args_pat = U.head_and_args_full t_pat in

    let! (t_fv:fv) =
      match (Subst.compress head_sc).n, (Subst.compress head_pat).n with
      | Tm_fvar (fv_head), Tm_fvar (fv_pat)
        when Ident.lid_equals (lid_of_fv fv_head) (lid_of_fv fv_pat) -> return fv_head
      | Tm_uinst ({n=Tm_fvar (fv_head)}, us_head), Tm_uinst ({n=Tm_fvar (fv_pat)}, us_pat)
        when Ident.lid_equals (lid_of_fv fv_head) (lid_of_fv fv_pat) ->
        if UnivEq.teq_univs g.tcenv us_head us_pat
        then return fv_head
        else err "Incompatible universe instantiations"
      | _, _ -> err (Format.fmt2 "Head constructors(%s and %s) not fvar"
                      (tag_of head_sc)
                      (tag_of head_pat)) in

    (if Env.is_type_constructor g.tcenv (lid_of_fv t_fv)
     then return t_fv
     else err (Format.fmt1 "%s is not a type constructor" (show t_fv)));!

    (if List.length args_sc = List.length args_pat then return t_fv
     else err (Format.fmt2 "Number of arguments don't match (%s and %s)"
                          (show (List.length args_sc))
                          (show (List.length args_pat))));!

   let params_sc, params_pat =
     match Env.num_inductive_ty_params g.tcenv (S.lid_of_fv t_fv) with
     | None -> args_sc, args_pat
     | Some n -> fst (BU.first_N n args_sc), fst (BU.first_N n args_pat) in

  iter2 params_sc params_pat (fun (t_sc, _) (t_pat, _) _ ->
     check_relation g EQUALITY t_sc t_pat) () ;!

   // TODO: return equality of indices for the caller to weaken the guard with?

   return None

(* The condition under which [scrutinee] matches [pat]. It does not mention
   the variables of the pattern: those that the pattern's dot terms (e.g. the
   parameters of a constructor) mention are replaced by the corresponding
   projections of the scrutinee. *)
and pattern_branch_condition (g:env) (scrutinee:term) (pat:pat)
  : ML (result (option term))
  = let! bc = pattern_branch_condition' g scrutinee pat in
    match bc with
    | None -> return None
    | Some bc ->
      let! projs = pattern_var_projections g scrutinee pat in
      let sub =
        List.fold_left
          (fun (sub:list subst_elt) (x, t) -> sub @ [NT(x, Subst.subst sub t)])
          [] projs in
      return (Some (Subst.subst sub bc))

(* Each variable of [pat], as a projection of [scrutinee], in the order
   they are bound. *)
and pattern_var_projections (g:env) (scrutinee:term) (pat:pat)
  : ML (result (list (bv & term)))
  = match pat.v with
    | Pat_var x -> return [(x, scrutinee)]
    | Pat_cons (fv, us_opt, sub_pats) ->
      let! type_args = inductive_type_args g scrutinee fv in
      let! projs =
        mapi (fun i (pi, _) ->
          match pi.v with
          | Pat_var _ | Pat_cons _ ->
            pattern_var_projections g (pat_field_projection g scrutinee pat.p fv us_opt type_args sub_pats i) pi
          | _ -> return []) sub_pats
      in
      return (List.flatten projs)
    | _ -> return []

(* The universes and arguments (parameters and indices) of the inductive
   type of the constructor [fv] of which [scrutinee] is an instance, as the
   implicit arguments of its discriminators and projectors. *)
and inductive_type_args (g:env) (scrutinee:term) (fv:fv)
  : ML (result (option (option universes & list term)))
  = let tc_lid = Env.typ_of_datacon g.tcenv fv.fv_name in
    (* Only an indexed type needs its arguments looked up in the scrutinee's
       type: the parameters are the pattern's dot terms (see
       [pat_field_projection]). Looking them up is not free, e.g. for nested
       dependent tuples, the type of each nested projection contains the one
       above it, twice. *)
    let has_indices =
      match Env.lookup_qname g.tcenv tc_lid with
      | Some (Inr ({ sigel = Sig_inductive_typ {t} }, _), _) ->
        not (Nil? (fst (U.arrow_formals t)))
      | _ -> true
    in
    if not has_indices then return None else
    let! t_sc = type_of_checked g scrutinee in
    match t_sc with
    | None -> return None
    | Some (_, t_sc) ->
      let rec aux (n:int) (t:typ) : ML (option (option universes & list term)) =
        let t = U.unrefine (N.unfold_whnf g.tcenv t) in
        let head, args = U.head_and_args_full t in
        match (Subst.compress head).n with
        | Tm_uinst ({n=Tm_fvar hfv}, us) when S.fv_eq_lid hfv tc_lid -> Some (Some us, List.map fst args)
        | Tm_fvar hfv when S.fv_eq_lid hfv tc_lid -> Some (None, List.map fst args)
        | _ when n > 0 ->
          let t' = N.normalize_refinement N.whnf_steps g.tcenv t in
          if U.term_eq t t' then None else aux (n - 1) t'
        | _ -> None
      in
      return (aux 4 t_sc)

and pat_field_projection (g:env) (scrutinee:term) (pat_p:Range.t) (fv:fv) (us_opt:option universes)
                         (type_args:option (option universes & list term))
                         (sub_pats:list (pat & bool)) (i:int)
  : ML term
  = let wild_pat pos = S.withinfo (Pat_var (wild_bv S.tun pos)) pos in
      (* The [i]th field of the scrutinee, as an application of its
         projector, as [TcTerm] builds branch conditions: unlike a [match],
         the SMT encoding of a projector carries the field's type. The
         projector's type arguments are the constructor's parameters, which
         the elaborated pattern records as dot patterns. *)
      let ith_projector_app (i:int) : ML (option term) =
        (* The projector's implicit arguments are the parameters and the
           indices of the scrutinee's type; failing to find the latter,
           e.g. for a type with no indices, the parameters are those the
           elaborated pattern records as dot patterns. *)
        let us_opt, params =
          match type_args with
          | Some (us, args) -> (match us with | Some _ -> us | None -> us_opt), Some args
          | None ->
          (us_opt, (match Env.num_inductive_ty_params g.tcenv (Env.typ_of_datacon g.tcenv fv.fv_name) with
          | None -> None
          | Some n ->
            if n > List.length sub_pats then None else
            let ps, _ = List.splitAt n sub_pats in
            let rec aux (ps:list (S.pat & bool)) : option (list term) =
              match ps with
              | [] -> Some []
              | ({v=Pat_dot_term (Some t)}, _) :: ps ->
                (match aux ps with None -> None | Some ts -> Some (t :: ts))
              | _ -> None
            in
            aux ps))
        in
        match params with
        | None -> None
        | Some params ->
          let proj = Env.lookup_projector g.tcenv fv.fv_name i in
          match Env.try_lookup_lid g.tcenv proj with
          | None -> None //e.g., we are typechecking the projector itself
          | Some _ ->
            let head = S.fvar (I.set_lid_range proj scrutinee.pos) None in
            let head = match us_opt with | Some us -> S.mk_Tm_uinst head us | None -> head in
            Some (S.mk_Tm_app head (List.map S.iarg params @ [S.as_arg scrutinee]) scrutinee.pos)
      in
      let mk_ith_projector i =
        match ith_projector_app i with
        | Some t -> t
        | None ->
        let ith_pat_var, ith_pat =
            // NOTE: This variable must have an ID distinct from all the other
            // wildcards below (constantly 0). Otherwise, the close_branch call
            // below will wrongly turn this bv in the branch expression to @0,
            // the 0th DB index.
            let bv = { wild_bv S.tun scrutinee.pos with index = 1 } in
            bv, S.withinfo (Pat_var bv) scrutinee.pos
        in
        let sub_pats = List.mapi (fun j (s,b) -> if i <> j then wild_pat s.p,b else ith_pat,b) sub_pats in
        let pat = S.withinfo (Pat_cons(fv, us_opt, sub_pats)) pat_p in
        let branch = S.bv_to_name ith_pat_var in
        let eqn = Subst.close_branch (pat, None, branch) in
        S.mk (Tm_match {scrutinee; ret_opt=None; brs=[eqn]; rc_opt=None}) scrutinee.pos
      in
      mk_ith_projector i

and pattern_branch_condition' (g:env)
                             (scrutinee:term)
                             (pat:pat)
  : ML (result (option term))
  = match pat.v with
    | Pat_var _ ->
      return None
    | Pat_constant FStarC.Const.Const_unit ->
      (* [()] always matches *)
      return None
    | Pat_constant c ->
      let const_exp =
        match PatternUtils.raw_pat_as_exp g.tcenv pat with
        | None -> failwith "Impossible"
        | Some (e, _) -> e
      in
      let! _, t_const = check "constant pattern" g const_exp in
      return (Some (U.mk_decidable_eq t_const scrutinee const_exp))

    | Pat_cons(fv, us_opt, sub_pats) ->
      let wild_pat pos = S.withinfo (Pat_var (wild_bv S.tun pos)) pos in
      let mk_head_discriminator () =
        (* Dot patterns (the constructor's parameters) are kept, so that the
           discriminator is well-typed if it ends up in a type Core checks. *)
        let wild_sub_pat (s, b) =
          match s.v with
          | Pat_dot_term (Some _) -> (s, b)
          | _ -> (wild_pat s.p, b) in
        let pat = S.withinfo (Pat_cons(fv, us_opt, List.map wild_sub_pat sub_pats)) pat.p in
        let branch1 = (pat, None, U.exp_true_bool) in
        let branch2 = (S.withinfo (Pat_var (wild_bv S.tun pat.p)) pat.p, None, U.exp_false_bool) in
        S.mk (Tm_match {scrutinee; ret_opt=None; brs=[branch1; branch2]; rc_opt=None}) scrutinee.pos
      in
      let! type_args = inductive_type_args g scrutinee fv in
      let mk_ith_projector i = pat_field_projection g scrutinee pat.p fv us_opt type_args sub_pats i in
      let discrimination =
        let is_induc, datacons = Env.datacons_of_typ g.tcenv (Env.typ_of_datacon g.tcenv fv.fv_name) in
        (* Why the `not is_induc`? We may be checking an exception pattern. See issue #1535. *)
        if not is_induc || List.length datacons > 1
        then let discriminator = U.mk_discriminator fv.fv_name in
             match Env.try_lookup_lid g.tcenv discriminator with
             | None ->
               // We don't use the discriminator if we are typechecking it
               None
             | _ ->
               Some discriminator
        else None //single constructor inductives do not need a discriminator
      in
      (* The discriminator is applied to the scrutinee, as [TcTerm] builds
         branch conditions: the SMT encoding of a [match] on the scrutinee
         is a term of its own, about which the solver knows less, e.g. when
         the scrutinee is itself a projection, [TEq? b && Nat? b.t]. Its
         implicit arguments are the scrutinee type's parameters and indices;
         failing to find them, a [match] is used. *)
      let! discrimination =
        match discrimination with
        | None -> return None
        | Some discriminator ->
          let type_args =
            match type_args with
            | Some _ -> type_args
            | None ->
              match Env.num_inductive_ty_params g.tcenv (Env.typ_of_datacon g.tcenv fv.fv_name) with
              | Some n when n <= List.length sub_pats ->
                let ps, _ = List.splitAt n sub_pats in
                let rec aux (ps:list (S.pat & bool)) : option (list term) =
                  match ps with
                  | [] -> Some []
                  | ({v=Pat_dot_term (Some t)}, _) :: ps ->
                    (match aux ps with None -> None | Some ts -> Some (t :: ts))
                  | _ -> None
                in
                (match aux ps with
                 | Some ts -> Some (us_opt, ts)
                 | None -> None)
              | _ -> None
          in
          let app =
            match type_args with
            | None -> None
            | Some (us, args) ->
              let d = S.fvar (I.set_lid_range discriminator scrutinee.pos) None in
              let d = match us with | Some us -> S.mk_Tm_uinst d us | None -> d in
              Some (S.mk_Tm_app d (List.map S.iarg args @ [S.as_arg scrutinee]) scrutinee.pos)
          in
          match app with
          | Some app -> return (Some app)
          | None -> return (Some (mk_head_discriminator ()))
      in
      let! sub_term_guards =
          mapi
          (fun i (pi, _) ->
            match pi.v with
            | Pat_dot_term _
            | Pat_var _ ->
              return None
            | _ ->
              let scrutinee_sub_term = mk_ith_projector i in
              pattern_branch_condition' g scrutinee_sub_term pi)
          sub_pats
      in
      let guards = List.collect (function None -> [] | Some t -> [t]) (discrimination :: sub_term_guards) in
      match guards with
      | [] -> return None
      | guards -> return (Some (U.mk_and_l guards))

(* Core names the binders it opens deterministically, above the largest
   index in its context (see [fresh_binder]), so that the same term opened in
   the same context is the same term, and its checks can be memoized. These
   indices must not be those of names generated by [GenSym], as when Core
   opens a term with [Subst] (e.g. [U.arrow_formals_comp]): a binder of the
   context may be the last name [GenSym] generated, and its next ones would
   then be Core's. So Core's indices start far above any [GenSym] index. *)
let core_index_base : int = 1099511627776 (* 2^40 *)

let initial_env g : ML env =
  let max_index =
      List.fold_left
         (fun index b ->
           match b with
           | Binding_var x -> max x.index index
           | _ -> index)
         core_index_base g.Env.gamma
  in
  { tcenv = g;
    allow_universe_instantiation = false;
    should_read_cache = true;
    max_binder_index = max_index;
    at_top = false
  }

//
// In case the expected type and effect are set,
//   they are returned as is
//
let check_term_top' g e topt (must_tot:bool)
  : ML (result (eff & typ))
  = let g = { initial_env g with at_top = Tm_abs? (Subst.compress (U.unascribe e)).n } in
    let! eff_te =
      match topt with
      | None -> check "top" g e
      | Some t ->
        let! eff, _ =
          with_context "top-level subtyping" None (fun _ ->
            check_against_typ ({ g with allow_universe_instantiation = true}) e t) in
        return (eff, t)
    in
    let eff_te =
      match eff_te with
      | EGhost, t when must_tot && non_informative g t -> ETot, t
      | _ -> eff_te
    in
    if must_tot && not (eff_eq (fst eff_te) ETot)
    then fail_effect_mismatch g e (snd eff_te) (fst eff_te) (snd eff_te) ETot
    else return eff_te

(* Check [e] against the computation type [c] (of any effect). *)
let check_term_at_comp' g e (c:comp)
  : ML (result (eff & typ))
  = let g = initial_env g in
    let target = comp_as_eff_and_type c in
    check_against_comp ({ g with allow_universe_instantiation = true}) e c ;!
    return target

(* Check a nest of top-level recursive definitions, with their universes
   opened and pushed in [g]. The top-level names are replaced by fresh
   variables, so that the nest is checked (and its guard closed) just as an
   inner let rec. *)
let check_top_level_letrec' g (lbs:list letbinding)
  : ML (result (eff & typ))
  = let g = initial_env g in
    let names =
      lbs |> List.map (fun lb ->
        let fv = Inr?.v lb.lbname in
        fv, S.gen_bv (Ident.string_of_id (Ident.ident_of_lid fv.fv_name)) (Some (S.range_of_fv fv)) lb.lbtyp)
    in
    let name_of (fv:fv) : ML (option bv) =
      match List.tryFind (fun (fv', _) -> S.fv_eq fv fv') names with
      | Some (_, x) -> Some x
      | None -> None
    in
    let replace (t:term) : ML term =
      t |> Syntax.Visit.visit_term false (fun t ->
        match t.n with
        (* Occurrences keep their ranges: the type of a name is used at
           its occurrence (see [lookup]). *)
        | Tm_fvar fv ->
          (match name_of fv with
           | Some x -> { t with n = Tm_name (S.set_range_of_bv x t.pos) }
           | None -> t)
        | Tm_uinst ({n=Tm_name x}, _) -> { t with n = Tm_name (S.set_range_of_bv x t.pos) }
        | _ -> t)
    in
    let lbs =
      List.map2 (fun lb (_, x) -> { lb with lbname = Inl x; lbdef = replace lb.lbdef }) lbs names
    in
    let! us = check_letrec_types g lbs in
    (* The guard mentions the names at their declared types: substitute the
       top-level names back, rather than quantifying over them, as they are
       in TcTerm's environment when it discharges the guard. *)
    let back : list subst_elt =
      List.map2 (fun (lb:letbinding) (fv, x) ->
        let t = S.fv_to_tm fv in
        let t = match lb.lbunivs with
                | [] -> t
                | us -> S.mk_Tm_uinst t (List.map U_name us) in
        NT (x, t)) lbs names
    in
    with_guard (check_letrec_defs g (Some back) lbs us) (function
      | Inr err -> fail_propagate err
      | Inl (_, None) -> return (ETot, S.t_unit)
      | Inl (_, Some form) ->
        reemit_guard g (Subst.subst back form) ;!
        return (ETot, S.t_unit))

(* The SMT encoding names a function literal after its body and its type,
   including the residual type of its body (see Bug1595). TcTerm gives a
   literal checked against an expected arrow the residual type of that arrow,
   e.g. [_:bool{_ == true <==> o x y}] for [fun x y -> f x y] passed as a
   [x:_ -> y:_ -> Pure bool True (fun z -> z == true <==> o x y)], and its
   unifier copies the literal as is into implicit arguments, e.g. the [p] of
   [Classical.forall_intro], where the same literal elsewhere has residual
   type [bool]: the two copies would be distinct terms to the SMT solver.
   (Core checks the elaboration as is, so nothing recomputes their residual
   types from their position.) In a guard, the residual types of
   function literals are only used for the typing axioms of their encodings,
   so they are weakened to their unrefined types: copies of a literal are
   then encoded alike. When the body, or the tail of its [let]s, is ascribed
   a refinement type (e.g., [fun y -> let _ = lem y in (y <: y:t{p y})]), the
   residual type is that of the literal itself, rather than of its position,
   and is kept: it is the same in all copies, including those in definitions,
   which are encoded as they are. *)
let unrefine_abs_residuals (t:term) : ML term =
  let rec ascribed_a_refinement (body:term) : ML bool =
    match (Subst.compress body).n with
    | Tm_ascribed {asc=(Inl t', _, _)} -> Tm_refine? (Subst.compress t').n
    | Tm_meta {tm} -> ascribed_a_refinement tm
    | Tm_let {lbs=(false, _); body} -> ascribed_a_refinement body
    | _ -> false
  in
  Visit.visit_term false (fun t ->
    match t.n with
    | Tm_abs ab when Some? ab.rc_opt && Some? (Some?.v ab.rc_opt).residual_typ ->
      let rc = Some?.v ab.rc_opt in
      let rt = Some?.v rc.residual_typ in
      if not (Tm_refine? (Subst.compress rt).n) || ascribed_a_refinement ab.body then t
      else { t with n = Tm_abs { ab with rc_opt = Some { rc with residual_typ = Some (U.unrefine rt) } } }
    | _ -> t) t

let simplify_steps =
    [Env.Beta;
     Env.UnfoldUntil delta_constant;
     Env.UnfoldQual ["unfold"];
     Env.UnfoldOnly [PC.pure_wp_monotonic_lid; PC.pure_wp_monotonic0_lid];
     Env.Simplify;
     Env.Primops;
     Env.NoFullNorm]

let initial_cache : cache_t = { 
  term_map = FStarC.Syntax.Hash.term_map_empty #hash_entry;
  guard_map = FStarC.Syntax.Hash.term_map_empty #guard_entry 
}

let check_term_top_gen (g:Env.env) (e:term) (topt:option typ) (simplify:bool) (f:result (eff & typ))
  : ML (__result ((eff & S.typ) & precondition))
  = if !dbg_Eq
    then Format.print1 "(%s) Entering core ... \n"
                   (show (get_goal_ctr()));

    if !dbg || !dbg_Top
    then (Format.print3 "(%s) Entering core with %s <: %s\n"
                   (show (get_goal_ctr()))
                   (show e) 
                   (show topt));
    reset_cache_stats();
    clear_relation_failures ();
    let ctx = { unfolding_ok = true; no_guard = false; error_context = [("Top", None)] } in
    let res =
      Profiling.profile
        (fun () -> f ctx initial_cache)
        None
        "FStarC.TypeChecker.Core.check_term_top"
    in
    if !dbg || !dbg_Top
    then Format.print2 "(%s) Core result = %s\n"
                   (show (get_goal_ctr()))
                   (show res);
    (
    let res =
      match res with
      | Success ((et, Some guard0), cache) ->
        // Options.push();
        // Options.set_option "debug" (Options.List [Options.String "Unfolding"]);
        let guard = unrefine_abs_residuals guard0 in
        let guard = if simplify then N.normalize simplify_steps g guard else guard in
        // Options.pop();
        if !dbg || !dbg_Top || !dbg_Exit
        then begin
          Format.print3 "(%s) Exiting core: Simplified guard from {{%s}} to {{%s}}\n"
            (show (get_goal_ctr()))
            (show guard0)
            (show guard);
          let guard_names = Syntax.Free.names guard |> elems in
          match List.tryFind (fun bv -> List.for_all (fun binding_env ->
            match binding_env with
            | Binding_var bv_env -> not (S.bv_eq bv_env bv)
            | _ -> true) g.gamma) guard_names with
          | Some bv ->
            Format.print1 "WARNING: %s is free in the core generated guard\n" (show (S.bv_to_name bv))
          | _ -> ()
        end;
        Success ((et, Some guard), cache)

      | Success _ ->
        if !dbg || !dbg_Top
        then Format.print1 "(%s) Exiting core (ok)\n"
                    (show (get_goal_ctr()));
        res

      | Error _ ->
        if !dbg || !dbg_Top
        then Format.print1 "(%s) Exiting core (failed)\n"
                       (show (get_goal_ctr()));
        res
    in
    if !dbg_Eq
    then (
      Format.print1 "THT Statistics { num_bindings = %s }\n" (show (HashTable.size table.table));
      let cs = report_cache_stats() in
      Format.print2 "Cache_stats { hits = %s; misses = %s }\n"
                     (show cs.hits)
                     (show cs.misses)
    );
    res
    )

let return_my_guard_and_tok_t (g:precondition) (cache:cache_t) : ML (option (typ & (unit -> ML unit))) =
    let tok = mk_token cache in
    match g with
    | None -> 
      commit_guard_core tok;
      None
    | Some guard ->
      Some (guard, (fun _ -> commit_guard_core tok))

let check_term_top g e topt (must_tot:bool)
  : ML (__result ((tot_or_ghost & S.typ) & precondition))
  = match check_term_top_gen g e topt true (check_term_top' g e topt must_tot) with
    | Success (((ETot, t), guard), cache) -> Success (((E_Total, t), guard), cache)
    | Success (((EGhost, t), guard), cache) -> Success (((E_Ghost, t), guard), cache)
    | Success (((EEff m, _), _), _) ->
      Error ({ unfolding_ok = true; no_guard = false; error_context = [("Top", None)] },
             [text "Expected a total or ghost term, but it has effect" ^/^ pp m], None)
    | Error err -> Error err

let check_term g e t must_tot =
  match check_term_top g e (Some t) must_tot with
  | Success ((_, g), cache) -> Inl <| return_my_guard_and_tok_t g cache
  | Error err -> Inr err

let check_term_at_type g e t =
  let must_tot = false in
  match check_term_top g e (Some t) must_tot with
  | Success (((eff, _), g), cache) -> Inl (eff, return_my_guard_and_tok_t g cache)
  | Error err -> Inr err

let compute_term_type g e =
  let must_tot = false in
  match check_term_top g e None must_tot with
  | Success (((eff, ty), g), cache) -> Inl (eff, ty, return_my_guard_and_tok_t g cache)
  | Error err -> Inr err

let check_term_at_comp g e c =
  match check_term_top_gen g e (Some (U.comp_result c)) false (check_term_at_comp' g e c) with
  | Success ((_, g), cache) -> Inl (return_my_guard_and_tok_t g cache)
  | Error err -> Inr err

let check_top_level_letrec g lbs =
  match check_term_top_gen g S.unit_const None false (check_top_level_letrec' g lbs) with
  | Success ((_, g), cache) -> Inl (return_my_guard_and_tok_t g cache)
  | Error err -> Inr err

let compute_term_comp g e topt check_t =
  let f : result (eff & typ) =
    match topt with
    | None -> check_term_top' g e None false
    | Some _ when not check_t -> check_term_top' g e topt false
    | Some t ->
      fun ctx cache ->
        let g0 = initial_env g in
        (let! _ = with_context "expected type" (Some (CtxTerm t)) (fun _ -> universe_of g0 t) in
         check_term_top' g e topt false) ctx cache
  in
  match check_term_top_gen g e topt false f with
  | Success ((et, g), cache) ->
    let c =
      match et with
      | ETot, t -> S.mk_Total t
      | EGhost, t -> S.mk_GTotal t
      | EEff m, t -> mk_comp_of_eff m t
    in
    Inl (c, return_my_guard_and_tok_t g cache)
  | Error err -> Inr err

let open_binders_in_term (env:Env.env) (bs:binders) (t:term) =
  let g = initial_env env in
  let g', bs, t = open_term_binders g bs t in
  g'.tcenv, bs, t

let open_binders_in_comp (env:Env.env) (bs:binders) (c:comp) =
  let g = initial_env env in
  let g', bs, c = open_comp_binders g bs c in
  g'.tcenv, bs, c

let check_term_equality guard_ok unfolding_ok g t0 t1
  = let g = initial_env g in
    if !dbg_Top then
       Format.print4 "Entering check_term_equality with %s and %s (guard_ok=%s; unfolding_ok=%s) {\n"
         (show t0) (show t1) (show guard_ok) (show unfolding_ok);
    clear_relation_failures ();
    let ctx = { unfolding_ok = unfolding_ok; no_guard = not guard_ok; error_context = [("Eq", None)] } in
    let r = check_relation g EQUALITY t0 t1 ctx initial_cache in
    if !dbg_Top then
       Format.print3 "} Exiting check_term_equality (%s, %s). Result = %s.\n" (show t0) (show t1) (show r);
    let r =
      match r with
      | Success ((_, g), cache) -> Inl (return_my_guard_and_tok_t g cache)
      | Error err -> Inr err
    in
    r

let check_term_subtyping guard_ok unfolding_ok g t0 t1
  = let g = initial_env g in
    clear_relation_failures ();
    let ctx = { unfolding_ok = unfolding_ok; no_guard = not guard_ok; error_context = [("Subtyping", None)] } in
    match check_relation g (SUBTYPING None) t0 t1 ctx initial_cache with
    | Success ((_, g), cache) -> Inl (return_my_guard_and_tok_t g cache)
    | Error err -> Inr err