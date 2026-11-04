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
module FStarC.TypeChecker.UniverseOf

open FStarC
open FStarC.Effect
open FStarC.List
open FStarC.Errors
open FStarC.Defensive
open FStarC.Const
open FStarC.Syntax.Syntax
open FStarC.Syntax.Print {}
open FStarC.TypeChecker.Env
open FStarC.Class.Show
module S = FStarC.Syntax.Syntax
module SS = FStarC.Syntax.Subst
module U = FStarC.Syntax.Util
module N = FStarC.TypeChecker.Normalize
module UF = FStarC.Syntax.Unionfind
module BU = FStarC.Util
module Const = FStarC.Parser.Const
module Env = FStarC.TypeChecker.Env

let tc_constant (env:env) r (c:sconst) : ML typ =
  let res =
     match c with
      | Const_unit -> t_unit
      | Const_bool _ -> t_bool
      | Const_int _ -> t_int
      | Const_machine_int (v, base, sw, w) ->
        let lid =
          match sw, w with
          | Signed, Int8 -> Const.int8_lid
          | Signed, Int16 -> Const.int16_lid
          | Signed, Int32 -> Const.int32_lid
          | Signed, Int64 -> Const.int64_lid
          | Signed, Sizet ->
            raise_error r Errors.Fatal_UnsupportedConstant
              "Ill-typed machine integer constant: there are no signed size_t literals"
          | Unsigned, Int8 -> Const.uint8_lid
          | Unsigned, Int16 -> Const.uint16_lid
          | Unsigned, Int32 -> Const.uint32_lid
          | Unsigned, Int64 -> Const.uint64_lid
          | Unsigned, Sizet -> Const.sizet_lid
        in
        (* This is the authoritative range check for machine integer
           literals: the syntax type does not enforce it, so constants built
           by reflection (pack_const) are checked here too. *)
        if not (within_bounds v sw w)
        then raise_error r Errors.Error_OutOfRange
               (Format.fmt2 "%s is not in the expected range for %s"
                  (string_of_int_literal v base) (show lid));
        tconst lid
      | Const_string _ -> t_string
      | Const_real _ -> t_real
      | Const_char _ ->
        FStarC.Syntax.DsEnv.try_lookup_lid env.dsenv FStarC.Parser.Const.char_lid
        |> Some?.v

      (* TODO (KM) : Try to change this to U.ktype1 *)
      (* (because that's the minimal universe level of the WP) *)
      (* and see how much code breaks *)
      | Const_effect -> U.ktype0 //NS: really?
      | Const_range _ -> t_range
      | Const_range_of
      | Const_set_range_of
      | Const_reify _
      | Const_reflect _ ->
        raise_error r Errors.Fatal_IllTyped
          (Format.fmt1 "Ill-typed %s: this constant must be fully applied" (show c))

      | _ -> raise_error r Errors.Fatal_UnsupportedConstant ("Unsupported constant: " ^ show c)
  in
  SS.set_use_range r res

let level_of_type_fail (env:Env.env) (e:term) (t:string) : ML _ =
    raise_error env Errors.Fatal_UnexpectedTermType [
      Errors.text (Format.fmt2 "Expected a type; got %s of type %s" (show e) t)
    ]

let level_of_type (h:hooks) env e t : ML _ =
    let rec aux retry t : ML _ =
        match (U.unrefine t).n with
        | Tm_type u -> u
        | _ ->
          if retry
          then let t = N.normalize [Env.UnfoldUntil delta_constant] env t in
               aux false t
          else h.level_of_non_type env e t
    in aux true t

(*
 * This helper routine computes the result type of applying args to
 *   a term of type t_hd
 *
 * It assumes that the terms are ghost/pure and well-typed in env
 *   -- to be called from fastpath type checking routines ONLY
 *)

(* private *)
let rec apply_well_typed env (t_hd:typ) (args:args) : ML (option typ) =
  if Nil? args
  then Some t_hd
  else
    let thd = N.unfold_whnf env t_hd in
    match thd.n with
       | Tm_arrow _ ->
         let bs, c = U.arrow_formals_comp_ln_strict thd in
         let n_args = List.length args in
         let n_bs = List.length bs in
         let bs, args, t, remaining_args =  (* bs (opened), args (length args = length bs), comp result type, remaining args *)
           if n_args < n_bs
           then let bs, rest = BU.first_N n_args bs in
                let t = S.mk_Tm_arrow rest c t_hd.pos in
                let bs, c = SS.open_comp bs (S.mk_Total t) in
                bs, args, U.comp_result c, []
           else let bs, c = SS.open_comp bs c in
                let args, remaining_args = List.splitAt n_bs args in
                bs, args, U.comp_result c, remaining_args in
         let subst = List.map2 (fun b a -> NT (b.binder_bv, fst a)) bs args in
         let t = SS.subst subst t in
         apply_well_typed env t remaining_args
       | Tm_refine {b=x} -> apply_well_typed env x.sort args
       | Tm_ascribed {tm=t} -> apply_well_typed env t args
       | _ -> None


(* universe_of_aux h env e:
      During type-inference, we build terms like WPs for which we need to compute
      explicit universe instantiations.

      This is generally called from within TypeChecker.Util
      when building WPs. For example, in building (return_value<u> t e),
      u=universe_of env t.

      We don't aim to compute a precise type for e.
      Rather, we look to compute the universe level of e's type,
      presuming that e must have type Type

      For instance, if e is an application (f _), we compute the type of f to be bs -> C,
      and we take the universe level of e to be (level_of (comp_result C)),
      disregarding the arguments of f.

      This a returns a term of shape Tm_type at the wanted universe.
 *)
let rec universe_of_aux (h:hooks) env e : ML term =
   match (SS.compress e).n with
   | Tm_bvar _
   | Tm_unknown
   | Tm_delayed _ ->
     failwith ("TcTerm.universe_of:Impossible (bvar/unknown/lazy) " ^
               (show e))
   //normalize let bindings away and then compute the universe
   | Tm_let _ ->
     let e = N.normalize [] env e in
     universe_of_aux h env e
   //we expect to compute (Type u); so an abstraction always fails
   | Tm_abs _ ->
     level_of_type_fail env e "arrow type"
   //these next few cases are easy; we just use the type stored at the node
   | Tm_uvar (u, s) -> SS.subst' s (U.ctx_uvar_typ u)
   | Tm_meta {tm=t} -> universe_of_aux h env t
   | Tm_name n ->
     let (t, _rng) = Env.lookup_bv env n in
     t
   | Tm_fvar fv ->
     let (_, t), _ = Env.lookup_lid env fv.fv_name in
     t
   | Tm_lazy i -> universe_of_aux h env (U.unfold_lazy i)
   | Tm_ascribed {asc=(Inl t, _, _)} -> t
   | Tm_ascribed {asc=(Inr c, _, _)} -> U.comp_result c
   //also easy, since we can quickly recompute the type
   | Tm_type u -> S.mk (Tm_type (U_succ u)) e.pos
   | Tm_quoted _ -> U.ktype0
   | Tm_constant sc -> tc_constant env e.pos sc
   //slightly subtle, since fv is a type-scheme; instantiate it with us
   | Tm_uinst({n=Tm_fvar fv}, us) ->
     let (us', t), _ = Env.lookup_lid env fv.fv_name in
     if List.length us <> List.length us' then
       raise_error env Errors.Fatal_UnexpectedNumberOfUniverse
          "Unexpected number of universe instantiations";
     (* FIXME: this logic is repeated from the Tm_uinst case of tc_value *)
     List.iter2
       (fun ul ur -> match ul, ur with
        | U_unif u'', _ -> UF.univ_change u'' ur
        // TODO: more cases? we cannot get U_succ or U_max here I believe...
        | U_name n1, U_name n2 when Ident.ident_equals n1 n2 -> ()
        | _ ->
          raise_error env Errors.Fatal_IncompatibleUniverse
            (Format.fmt3 "Incompatible universe application for %s, expected %s got %s\n"
                       (show fv) (show ul) (show ur)))
       us' us;
     t

   | Tm_uinst _ ->
     failwith "Impossible: Tm_uinst's head must be an fvar"
   //the refinement formula plays no role in the universe computation; so skip it
   | Tm_refine {b=x} -> universe_of_aux h env x.sort
   //U_max(univ_of bs, univ_of c)
   | Tm_arrow _ ->
     let bs, c = U.arrow_formals_comp_strict e in
     let env = Env.push_binders env bs in
     let us = List.map (fun ({binder_bv=b}) -> level_of_type h env b.sort (universe_of_aux h env b.sort)) bs in
     let u_res =
        let res = U.comp_result c in
        level_of_type h env res (universe_of_aux h env res) in
     let u_c = Env.effect_universe env (U.comp_effect_name c) u_res in
     let u = N.normalize_universe env (S.U_max (u_c::us)) in
     S.mk (Tm_type u) e.pos
   //See the comment at the top of this function; we just compute the universe of hd's result type
   | Tm_app _ ->
     let hd, args = U.head_and_args_full e in
     let rec type_of_head retry env hd args : ML _ =
        let hd = SS.compress hd in
        match hd.n with
        | Tm_unknown
        | Tm_bvar _
        | Tm_delayed _ ->
          failwith "Impossible: universe_of_aux: Tm_app: unexpected head type"
        | Tm_fvar _
        | Tm_name _
        | Tm_uvar _
        | Tm_uinst _
        | Tm_ascribed _
        | Tm_refine _
        | Tm_constant _
        | Tm_arrow _
        | Tm_meta _
        | Tm_type _ ->
          universe_of_aux h env hd, args
        | Tm_match {brs=b::_} ->  //AR: TODO: use return annotation? Or the residual_comp?
          let (pat, _, tm) = SS.open_branch b in
          let bvs = S.pat_bvs pat in
          let hd, args' = U.head_and_args_full tm in
          type_of_head retry (Env.push_bvs env bvs) hd (args'@args)
        | _ when retry ->
          //head is either an abs, so we have a beta-redex
          //      or a let,
          // GM: NOTE: not using hd and args here,
          //     this is calling itself with the `e` from
          //     universe_of_aux and splitting it again.
          let e = N.normalize [Env.Beta; Env.DoNotUnfoldPureLets] env e in
          let hd, args = U.head_and_args_full e in
          type_of_head false env hd args
        | _ ->
          h.type_of_head env hd, args
     in
     let t, args = type_of_head true env hd args in
     (match apply_well_typed env t args with
      | Some t -> t
      | None -> level_of_type_fail env e (show t))
   | Tm_match {brs=b::_} ->  //AR: TODO: use return annotation?
     let (pat, _, tm) = SS.open_branch b in
     let bvs = S.pat_bvs pat in
     universe_of_aux h (Env.push_bvs env bvs) tm

   | Tm_match {brs=[]} ->  //AR: TODO: use return annotation?
     level_of_type_fail env e "empty match cases"


let universe_of (h:hooks) env e : ML _ = Errors.with_ctx "While attempting to compute a universe level" (fun () ->
    if Debug.high () then
      Format.print1 "Calling universe_of_aux with %s {\n" (show e);
    def_check_scoped e.pos "universe_of entry" env e;

    let r = universe_of_aux h env e in
    if Debug.high () then
      Format.print1 "Got result from universe_of_aux = %s }\n" (show r);
    level_of_type h env e r
)

let no_hooks : hooks = {
  type_of_head = (fun env hd ->
    raise_error env Errors.Fatal_UnexpectedTermType [
      Errors.text (Format.fmt1 "Cannot compute the type of %s syntactically" (show hd))
    ]);
  level_of_non_type = (fun env e t -> level_of_type_fail env e (show t));
}
