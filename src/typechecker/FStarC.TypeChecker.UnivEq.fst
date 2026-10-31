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
module FStarC.TypeChecker.UnivEq

open FStarC
open FStarC.Effect
open FStarC.List
open FStarC.Syntax.Syntax
open FStarC.Syntax.Print {}
open FStarC.Class.Show
module Env = FStarC.TypeChecker.Env
module N = FStarC.TypeChecker.Normalize
module SS = FStarC.Syntax.Subst
module U = FStarC.Syntax.Util
module UF = FStarC.Syntax.Unionfind
module BU = FStarC.Util

(* Make a thunk for a string, but keep the UF state
 * so it can be set before calling the function. This is
 * used since most error messages call term_to_string,
 * which will resolve uvars and explode if the version is
 * wrong. *)
let mklstr (f : unit -> ML string) : ML _
  =
    let uf = UF.get () in
    Thunk.mk (fun () ->
        let tx = UF.new_transaction () in
        UF.set uf;
        let r = f () in
        UF.rollback tx;
        r)

let norm_univ env u : ML _
  =
    let rec aux u : ML _ =
        let u = SS.compress_univ u in
        match u with
            | U_succ u ->
              U_succ (aux u)

            | U_max us ->
              U_max (List.map aux us)

            | _ -> u in
    N.normalize_universe env (aux u)

let commit_univ v u =
  match u with
  | U_unif u' -> UF.univ_union v u'
  | _ -> UF.univ_change v u

let ufailed_simple (#w:Type) (s:string) : ML (univ_eq_sol w) =
  UFailed (Thunk.mkv s)

let ufailed_thunk (#w:Type) (s: unit -> ML string) : ML (univ_eq_sol w) =
  UFailed (mklstr s)

let rec solve_universe_eq #w env umax_heuristic_ok defer_ok solve (st:w) u1 u2 : ML (univ_eq_sol w)
  =
    let u1 = N.normalize_universe env u1 in
    let u2 = N.normalize_universe env u2 in
    let rec occurs_univ v1 u : ML _ = match u with
        | U_max us ->
          us |> BU.for_some (fun u ->
            let k, _ = U.univ_kernel u in
            match k with
                | U_unif v2 -> UF.univ_equiv v1 v2
                | _ -> false)
        | _ -> occurs_univ v1 (U_max [u]) in

    let rec filter_out_common_univs (u1:list universe) (u2:list universe) : ML (list universe & list universe) =
      let common_elts = u1 |> List.fold_left (fun uvs uv1 -> if u2 |> List.existsML (fun uv2 -> U.eq_univs uv1 uv2) then uv1::uvs else uvs) [] in
      let filter = List.filter (fun u -> not (common_elts |> List.existsML (fun u' -> U.eq_univs u u'))) in
      filter u1, filter u2
    in

    let try_umax_components u1 u2 msg : ML (univ_eq_sol w) =
        if not umax_heuristic_ok
        then ufailed_simple "Unable to unify universe terms with umax"
        else
        match u1, u2 with
            | U_max us1, U_max us2 ->
              begin
              //filter out common universes in us1 and us2
              //this allows more cases to unify, e.g. us1 = [uvar; un] and us2=[un; un']
              //with just structural comparison, this would fail to unify, but after filtering away un, we can unify uvar with un'
              let us1, us2 = filter_out_common_univs us1 us2 in
              if List.length us1 = List.length us2 //go for a structural match
              then let rec aux st us1 us2 : ML _ = match us1, us2 with
                        | u1::us1, u2::us2 ->
                          begin match solve_universe_eq env umax_heuristic_ok defer_ok solve st u1 u2 with
                            | USolved st ->
                                aux st us1 us2
                            | failed -> failed
                          end
                        | _ -> USolved st in
                    aux st us1 us2
              else ufailed_thunk
                             (fun () -> Format.fmt2 "Unable to unify universes: %s and %s"
                                                   (show u1)
                                                   (show u2))
              end
            | U_max us, u'
            | u', U_max us ->
                let rec aux st us : ML _ = match us with
                | [] -> USolved st
                | u::us ->
                    begin match solve_universe_eq env umax_heuristic_ok defer_ok solve st u u' with
                    | USolved st ->
                      aux st us
                    | failed -> failed
                    end
                in aux st us

            | _ ->
              ufailed_thunk (fun () ->
                            Format.fmt3 "Unable to unify universes: %s and %s (%s)"
                                       (show u1)
                                       (show u2) msg) in

    match u1, u2 with
        | U_bvar _, _
        | U_unknown, _
        | _, U_bvar _
        | _, U_unknown -> failwith (Format.fmt2 "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                                        (show u1)
                                        (show u2))

        | U_name x, U_name y ->
          if (Ident.string_of_id x) = (Ident.string_of_id y)
          then USolved st
          else ufailed_simple "Incompatible universes"

        | U_zero, U_zero ->
          USolved st

        | U_succ u1, U_succ u2 ->
          solve_universe_eq env umax_heuristic_ok defer_ok solve st u1 u2

        | U_unif v1, U_unif v2 ->
          if UF.univ_equiv v1 v2
          then USolved st
          else USolved (solve st v1 u2)

        | U_unif v1, u
        | u, U_unif v1 ->
          let u = norm_univ env u in
          if occurs_univ v1 u
          then try_umax_components u1 u2
                (Format.fmt2 "Failed occurs check: %s occurs in %s" (show (U_unif v1)) (show u))
          else USolved (solve st v1 u)

        | U_max _, _
        | _, U_max _ ->
          if defer_ok
          then UDeferred st
          else let u1 = norm_univ env u1 in
               let u2 = norm_univ env u2 in
               if U.eq_univs u1 u2
               then USolved st
               else try_umax_components u1 u2 ""

        | U_succ _, U_zero
        | U_succ _, U_name _
        | U_zero,   U_succ _
        | U_zero,   U_name _
        | U_name _, U_succ _
        | U_name _, U_zero ->
          ufailed_simple "Incompatible universes"

let teq_univs env us1 us2 =
  let solve1 (defer_ok:bool) (eq:universe & universe) : ML (univ_eq_sol unit) =
    let u1, u2 = eq in
    solve_universe_eq env true defer_ok (fun () v u -> commit_univ v u) () u1 u2
  in
  let rec solve_now (eqs:list (universe & universe)) : ML bool =
    match eqs with
    | [] -> true
    | eq::eqs -> USolved? (solve1 false eq) && solve_now eqs
  in
  let rec solve_or_defer (deferred:list (universe & universe)) (eqs:list (universe & universe))
    : ML (option (list (universe & universe))) =
    match eqs with
    | [] -> Some (List.rev deferred)
    | eq::eqs ->
      match solve1 true eq with
      | USolved () -> solve_or_defer deferred eqs
      | UDeferred () -> solve_or_defer (eq::deferred) eqs
      | UFailed _ -> None
  in
  List.length us1 = List.length us2 &&
  (let tx = UF.new_transaction () in
   let ok =
     match solve_or_defer [] (List.zip us1 us2) with
     | None -> false
     | Some deferred -> solve_now deferred
   in
   if ok then UF.commit tx else UF.rollback tx;
   ok)
