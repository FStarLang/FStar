(*
   Copyright 2008-2014 Nikhil Swamy and Microsoft Research

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
module FStarC.TypeChecker.Common

open FStarC.Class.Show
open FStarC.Class.Monoid
open FStarC.CList
open FStarC.Range.Type
open FStarC.Effect
open FStarC.List

open FStarC
open FStarC.Syntax
open FStarC.Syntax.Syntax
open FStarC.Ident
module S = FStarC.Syntax.Syntax
module U = FStarC.Syntax.Util
open FStarC.Syntax.Print {}

module BU = FStarC.Util
module PC = FStarC.Parser.Const
module C = FStarC.Parser.Const
module SS = FStarC.Syntax.Subst
module Free = FStarC.Syntax.Free
open FStarC.Class.Setlike


let as_tprob (p:prob) : ML (problem typ) = match p with
   | TProb p -> p
   | _ -> failwith "Expected a TProb"

instance showable_guard_formula : showable guard_formula = {
  show = (function
          | Trivial      -> "Trivial"
          | NonTrivial f -> "NonTrivial " ^ show f)
}

instance showable_deferred_reason : showable deferred_reason = {
  show = (function
          | Deferred_univ_constraint -> "Deferred_univ_constraint"
          | Deferred_occur_check_failed -> "Deferred_occur_check_failed"
          | Deferred_first_order_heuristic_failed -> "Deferred_first_order_heuristic_failed"
          | Deferred_flex -> "Deferred_flex"
          | Deferred_free_names_check_failed -> "Deferred_free_names_check_failed"
          | Deferred_not_a_pattern -> "Deferred_not_a_pattern"
          | Deferred_flex_flex_nonpattern -> "Deferred_flex_flex_nonpattern"
          | Deferred_delay_match_heuristic -> "Deferred_delay_match_heuristic"
          | Deferred_to_user_tac -> "Deferred_to_user_tac"
          );
}

let check_uvar_ctx_invariant (reason:string) (r:range) (should_check:bool) (g:gamma) (bs:binders)
  : ML unit =
     let fail () =
         failwith (Format.fmt5
                   "Invariant violation: gamma and binders are out of sync\n\t\
                               reason=%s, range=%s, should_check=%s\n\t
                               gamma=%s\n\t\
                               binders=%s\n"
                               reason
                               (Range.string_of_range r)
                               (if should_check then "true" else "false")
                               (show g)
                               (show bs))
     in
     if not should_check then ()
     else match BU.prefix_until (function Binding_var _ -> true | _ -> false) g, bs with
     | None, [] -> ()
     | Some (_, hd, gamma_tail), _::_ ->
       let _, x = BU.prefix bs in
       begin
       match hd with
       | Binding_var x' when S.bv_eq x.binder_bv x' ->
         ()
       | _ -> fail()
        end
     | _ -> fail()

let mk_by_tactic tac f
  : ML term =
    let t_by_tactic = S.mk_Tm_uinst (tabbrev C.by_tactic_lid) [U_zero] in
    S.mk_Tm_app t_by_tactic [S.as_arg tac; S.as_arg f] Range.dummyRange

let rec delta_depth_greater_than l m = match l, m with
    | Delta_equational_at_level i, Delta_equational_at_level j -> i > j
    | Delta_constant_at_level i,   Delta_constant_at_level j   -> i > j
    | Delta_abstract d, _                                      -> delta_depth_greater_than d m
    | _, Delta_abstract d                                      -> delta_depth_greater_than l d
    | Delta_equational_at_level _, _                           -> true
    | _, Delta_equational_at_level _                           -> false

let rec decr_delta_depth = function
    | Delta_constant_at_level 0
    | Delta_equational_at_level 0 -> None
    | Delta_constant_at_level i   -> Some (Delta_constant_at_level (i - 1))
    | Delta_equational_at_level i -> Some (Delta_equational_at_level (i - 1))
    | Delta_abstract d            -> decr_delta_depth d

(***********************************************************************************)
(* A table of file -> starting row -> starting col -> identifier info              *)
(* Used to support querying information about an identifier in interactive mode    *)
(*    The table provides:                                                          *)
(*          -- the full name of the identifier                                     *)
(*          -- the source range of its use                                         *)
(*          -- the source range of its defining occurrence                         *)
(*          -- its type                                                            *)
(***********************************************************************************)

let insert_col_info (col:int) (info:identifier_info) (col_infos:list (int & identifier_info))
  : ML (list (int & identifier_info)) =
    // Tail recursive helper
    let rec __insert aux rest =
        match rest with
        | [] -> (aux, [col, info])
        | (c,i)::rest' ->
          if col < c
          then (aux, (col, info)::rest)
          else __insert ((c,i)::aux) rest'
     in
     let l, r = __insert [] col_infos
     in (List.rev l) @ r

let find_nearest_preceding_col_info (col:int) (col_infos:list (int & identifier_info)) =
    let rec aux out = function
        | [] -> out
        | (c, i)::rest ->
          if c > col then out
          else aux (Some i) rest
    in
    aux None col_infos

let id_info_table_empty =
    { id_info_enabled = false;
      id_info_db = PSMap.empty ();
      id_info_buffer = [] }

open FStarC.Range

let print_identifier_info info =
  Format.fmt3 "id info { %s, %s : %s}"
    (Range.string_of_range info.identifier_range)
    (match info.identifier with
     | Inl x -> show x
     | Inr fv -> show fv)
    (show info.identifier_ty)

let id_info__insert (ty_map: typ -> ML (option typ)) db info =
    let range = info.identifier_range in
    let use_range = Range.set_def_range range (Range.use_range range) in
    let id_ty =
      match info.identifier with
      | Inr _ ->
        ty_map info.identifier_ty
      | Inl x ->
        ty_map info.identifier_ty
    in
    match id_ty with
    | None -> db
    | Some id_ty ->
      let info = { info with identifier_range = use_range;
                             identifier_ty = id_ty } in

      let fn = file_of_range use_range in
      let start = start_of_range use_range in
      let row, col = line_of_pos start, col_of_pos start in

      let rows = PSMap.find_default db fn (PIMap.empty ()) in
      let cols = PIMap.find_default rows row [] in

      insert_col_info col info cols
      |> PIMap.add rows row
      |> PSMap.add db fn

let id_info_insert table id ty range =
    let info = { identifier = id; identifier_ty = ty; identifier_range = range} in
    { table with id_info_buffer = info :: table.id_info_buffer }

let id_info_insert_bv table bv ty : ML id_info_table =
    if table.id_info_enabled then id_info_insert table (Inl bv) ty (range_of_bv bv)
    else table

let id_info_insert_fv table fv ty : ML id_info_table =
    if table.id_info_enabled then id_info_insert table (Inr fv) ty (range_of_fv fv)
    else table

let id_info_toggle table enabled =
    { table with id_info_enabled = enabled }

let id_info_promote table ty_map
  : ML id_info_table =
    { table with
      id_info_buffer = [];
      id_info_db = List.fold_left (id_info__insert ty_map)
                     table.id_info_db table.id_info_buffer }

let id_info_at_pos (table: id_info_table) (fn:string) (row:int) (col:int) : option identifier_info =
    let rows = PSMap.find_default table.id_info_db fn (PIMap.empty ()) in
    let cols = PIMap.find_default rows row [] in

    match find_nearest_preceding_col_info col cols with
    | None -> None
    | Some info ->
      let last_col = col_of_pos (end_of_range info.identifier_range) in
      if col <= last_col then Some info else None

instance showable_implicit : showable implicit = {
  show = (fun i -> show (i.imp_uvar.ctx_uvar_head, i.imp_uvar.ctx_uvar_reason));
}

let trivial_guard =
  let open FStarC.Class.Listlike in
  {
    guard_f=Trivial;
    deferred_to_tac=empty;
    deferred=empty;
    univ_ineqs=(empty, empty);
    implicits=empty;
  }

let conj_guard_f g1 g2 : ML guard_formula = match g1, g2 with
  | Trivial, g
  | g, Trivial -> g
  | NonTrivial f1, NonTrivial f2 -> NonTrivial (U.mk_conj f1 f2)

let binop_guard (f: guard_formula -> guard_formula -> ML guard_formula) g1 g2 : ML guard_t = {
  guard_f=f g1.guard_f g2.guard_f;
  deferred_to_tac=g1.deferred_to_tac ++ g2.deferred_to_tac;
  deferred=g1.deferred ++ g2.deferred;
  univ_ineqs=(fst g1.univ_ineqs ++ fst g2.univ_ineqs,
              snd g1.univ_ineqs ++ snd g2.univ_ineqs);
  implicits=g1.implicits ++ g2.implicits;
}
let conj_guard g1 g2 : ML guard_t = binop_guard conj_guard_f g1 g2

instance monoid_guard_t : monoid guard_t = {
  mzero = trivial_guard;
  mplus = conj_guard;
}

let rec check_trivial (t:term) : ML guard_formula =
    let hd, args = U.head_and_args_full (U.unmeta t) in
    match (U.un_uinst (U.unmeta hd)).n, args with
    | Tm_fvar tc, [] 
      when S.fv_eq_lid tc PC.true_lid ->
      Trivial
      
    | Tm_fvar sq, [v, _]
      when S.fv_eq_lid sq PC.squash_lid ->         
      (match check_trivial v with
       | Trivial -> Trivial
       | _ -> NonTrivial t)

    | _ -> NonTrivial t

let imp_guard_f g1 g2 : ML guard_formula = match g1, g2 with
  | Trivial, g -> g
  | g, Trivial -> Trivial
  | NonTrivial f1, NonTrivial f2 ->
    let imp = U.mk_imp f1 f2 in check_trivial imp

let imp_guard g1 g2 : ML guard_t = binop_guard imp_guard_f g1 g2

let conj_guards gs : ML guard_t = List.fold_left conj_guard trivial_guard gs
let split_guard g =
 {g with guard_f = Trivial},
 {trivial_guard with guard_f = g.guard_f}

let weaken_guard_formula g fml : ML guard_t =
  if U.is_t_true fml then g else
  match g.guard_f with
  | Trivial -> g
  | NonTrivial f ->
    { g with guard_f = check_trivial (U.mk_imp fml f) }


let check_positivity_qual subtyping p0 p1
  = if p0 = p1 then true
    else if subtyping
    then match p0, p1 with
         | Some _, None -> true
         | Some BinderUnused, Some BinderStrictlyPositive -> true
         | _ -> false
    else false

let one_point_defn (x:bv) (hyp:term) : ML (option (term & term)) =
  let is_x (t:term) =
    match (SS.compress t).n with
    | Tm_name y -> S.bv_eq x y
    | _ -> false in
  let as_defn (t:term) : ML (option term) =
    let hd, args = U.head_and_args_full t in
    match (U.un_uinst hd).n, args with
    | Tm_fvar fv, [_; (lhs, _); (rhs, _)] when S.fv_eq_lid fv C.eq2_lid ->
      if is_x lhs && not (mem x (Free.names rhs)) then Some rhs
      else if is_x rhs && not (mem x (Free.names lhs)) then Some lhs
      else None
    | _ -> None in
  let rec find (t:term) : ML (option (term & term)) =
    let hd, args = U.head_and_args_full t in
    match (U.un_uinst hd).n, args with
    | Tm_fvar fv, [(a, _); (b, _)] when S.fv_eq_lid fv C.and_lid ->
      (match find a with
       | Some (v, rest) -> Some (v, U.mk_conj_simp rest b)
       | None ->
         match find b with
         | Some (v, rest) -> Some (v, U.mk_conj_simp a rest)
         | None -> None)
    | _ ->
      match as_defn t with
      | Some v -> Some (v, U.t_true)
      | None -> None in
  find hyp

let post_obligation (x:bv) (hyp:term) (concl:term) : ML term =
  match one_point_defn x hyp with
  | Some (v, rest) -> SS.subst [NT (x, v)] (U.mk_imp_simp rest concl)
  | None -> U.mk_forall_no_univ x (U.mk_imp hyp concl)
