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
module FStarC.Syntax.Formula

open FStarC.Effect
open FStarC.List

open FStarC
open FStarC.Ident
open FStarC.Syntax
open FStarC.Syntax.Syntax
open FStarC.Syntax.Print

module BU = FStarC.Util
module PC = FStarC.Parser.Const
module U = FStarC.Syntax.Util
module SS = FStarC.Syntax.Subst

open FStarC.Class.Show
open FStarC.Class.Monad

let connective_to_string c =
    match c with
    | QAll p -> "QAll " ^ show p
    | QEx p -> "QEx " ^ show p
    | BaseConn p -> "BaseConn" ^ show p

instance showable_connective = {
  show = connective_to_string;
}

(* destruct_typ_as_formula can be hot; these tables are defined
   here to ensure they are constructed only once in the executing
   binary

   the tables encode arity -> match_lid -> output_lid
   *)
let destruct_base_table = let f x = (x,x) in [
  (0, [f PC.true_lid; f PC.false_lid]);
  (1, [f PC.not_lid]);
  (2, [f PC.and_lid; f PC.or_lid; f PC.imp_lid; f PC.iff_lid; f PC.eq2_lid]);
  (3, [f PC.ite_lid; f PC.eq2_lid]);
]

let destruct_sq_base_table = [
  (0, [(PC.c_true_lid, PC.true_lid); (PC.empty_type_lid, PC.false_lid)]);
  (2, [(PC.c_and_lid, PC.and_lid);
       (PC.c_or_lid, PC.or_lid);
       (PC.c_eq2_lid, PC.eq2_lid)]);
  (3, [(PC.c_eq2_lid, PC.eq2_lid)]);
]

let rec unmeta_monadic f =
  let f = Subst.compress f in
  match f.n with
  | Tm_meta {tm=t; meta=Meta_monadic _}
  | Tm_meta {tm=t; meta=Meta_monadic_lift _} -> unmeta_monadic t
  | _ -> f

let lookup_arity_lid table target_lid args =
    let arg_len : int = List.length args in
    let aux (arity, lids) =
        if arg_len = arity
        then BU.find_map lids
            (fun (lid, out_lid) ->
              if lid_equals target_lid lid
              then Some (BaseConn (out_lid, args))
              else None)
        else None
    in
    BU.find_map table aux

let destruct_base_conn t =
    let hd, args = U.head_and_args t in
    match (U.un_uinst hd).n with
    | Tm_fvar fv -> lookup_arity_lid destruct_base_table fv.fv_name args
    | _ -> None

let destruct_sq_base_conn t =
    let! t = U.un_squash t in
    let t = U.unmeta t in
    let hd, args = U.head_and_args_full t in
    match (U.un_uinst hd).n with
    | Tm_fvar fv -> lookup_arity_lid destruct_sq_base_table fv.fv_name args
    | _ -> None

let patterns t =
    let t = SS.compress t in
    match t.n with
        | Tm_meta {tm=t; meta=Meta_pattern (_, pats)} -> pats, SS.compress t
        | _ -> [], t

let destruct_q_conn t =
    let is_q (fa:bool) (fv:fv) : bool =
        if fa
        then U.is_forall fv.fv_name
        else U.is_exists fv.fv_name
    in
    let flat t =
        let t, args = U.head_and_args t in
        U.un_uinst t, args |> List.map (fun (t, imp) -> U.unascribe t, imp)
    in
    let rec aux qopt out t = match qopt, flat t with
        | Some fa, ({n=Tm_fvar tc}, [({n=Tm_abs {bs=[b]; body=t2}}, _)])
        | Some fa, ({n=Tm_fvar tc}, [_; ({n=Tm_abs {bs=[b]; body=t2}}, _)])
            when (is_q fa tc) ->
          aux qopt (b::out) t2

        | None, ({n=Tm_fvar tc}, [({n=Tm_abs {bs=[b]; body=t2}}, _)])
        | None, ({n=Tm_fvar tc}, [_; ({n=Tm_abs {bs=[b]; body=t2}}, _)])
            when (U.is_qlid tc.fv_name) ->
          aux (Some (U.is_forall tc.fv_name)) (b::out) t2

        | Some b, _ ->
          let bs = List.rev out in
          let bs, t = Subst.open_term bs t in
          let pats, body = patterns t in
          if b
          then Some (QAll(bs, pats, body))
          else Some  (QEx(bs, pats, body))

        | _ -> None in
    aux None [] t

let rec destruct_sq_forall t =
    let! t = U.un_squash t in
    let t = U.unmeta t in
    match U.arrow_one t with
    | Some (b, c) ->
        if not (U.is_tot_or_gtot_comp c)
        then None
        else
            let q = U.comp_result c in
            if U.is_free_in b.binder_bv q
            then (
                let pats, q = patterns q in
                maybe_collect <| Some (QAll([b], pats, q))
            ) else (
                // Since we know it's not free, we can just open and discard the binder
                Some (BaseConn (PC.imp_lid, [as_arg b.binder_bv.sort; as_arg q]))
            )
    | _ -> None
and destruct_sq_exists t =
    let! t = U.un_squash t in
    let t = U.unmeta t in
    let hd, args = U.head_and_args_full t in
    match (U.un_uinst hd).n, args with
    | Tm_fvar fv, [(a1, _); (a2, _)]
        when fv_eq_lid fv PC.lid_dtuple2 ->
            begin match (SS.compress a2).n with
            | Tm_abs {bs=[b]; body=q} ->
                let bs, q = SS.open_term [b] q in
                let b = match bs with // coverage...
                        | [b] -> b
                        | _ -> failwith "impossible"
                in
                let pats, q = patterns q in
                maybe_collect <| Some (QEx ([b], pats, q))
            | _ -> None
            end
    | _ -> None
and maybe_collect f =
    match f with
    | Some (QAll (bs, pats, phi)) ->
        begin match destruct_sq_forall phi with
        | Some (QAll (bs', pats', psi)) -> Some <| QAll(bs@bs', pats@pats', psi)
        | _ -> f
        end
    | Some (QEx (bs, pats, phi)) ->
        begin match destruct_sq_exists phi with
        | Some (QEx (bs', pats', psi)) -> Some <| QEx(bs@bs', pats@pats', psi)
        | _ -> f
        end
    | _ -> f

let destruct_typ_as_formula f : option connective =
  let phi = unmeta_monadic f in
  let r = 
    // Try all possibilities, stopping at the first
    Option.catch (destruct_base_conn phi) (fun () ->
    Option.catch (destruct_q_conn phi) (fun () ->
    Option.catch (destruct_sq_base_conn phi) (fun () ->
    Option.catch (destruct_sq_forall phi) (fun () ->
    Option.catch (destruct_sq_exists phi) (fun () ->
              None)))))
  in
  r
