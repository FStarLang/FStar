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
module FStarC.TypeChecker.Core.Cache

(* See the interface. *)

open FStarC.TypeChecker.CommonBase
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
open FStarC.TypeChecker.Core.Base
open FStarC.TypeChecker.Core.Monad
open FStarC.TypeChecker.Core.Util
module HashTable = FStarC.HashTable

let table : tc_table = {
  table = HashTable.create 1048576; //2^20
  guard_table = HashTable.create 1048576; //2^20
  counter = mk_ref 0
} 

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

let initial_cache : cache_t = { 
  term_map = FStarC.Syntax.Hash.term_map_empty #hash_entry;
  guard_map = FStarC.Syntax.Hash.term_map_empty #guard_entry 
}

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
