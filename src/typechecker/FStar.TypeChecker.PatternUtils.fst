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

module FStar.TypeChecker.PatternUtils
open FStar.Compiler.Effect
open FStar
open FStar.Compiler
open FStar.Compiler.Util
open FStar.Errors
open FStar.TypeChecker
open FStar.Syntax
open FStar.TypeChecker.Env
open FStar.Syntax.Syntax
open FStar.Ident
open FStar.Syntax.Subst
open FStar.TypeChecker.Common

type lcomp_with_binder = option bv * lcomp

module SS = FStar.Syntax.Subst
module S = FStar.Syntax.Syntax
module BU = FStar.Compiler.Util
module U = FStar.Syntax.Util
module P = FStar.Syntax.Print
module C = FStar.Parser.Const

(************************************************************************)
(* Utilities on patterns  *)
(************************************************************************)

let rec elaborate_pat env p = //Adds missing implicit patterns to constructor patterns
    let maybe_dot inaccessible a r =
        if inaccessible
        then withinfo (Pat_dot_term(a, tun)) r
        else withinfo (Pat_var a) r
    in
    match p.v with
    | Pat_cons({fv_qual=Some (Unresolved_constructor _)}, _, _) ->
      (* Unresolved constructors cannot be elaborated yet.
         tc_pat has to resolve it first. *)
      p

    | Pat_cons(fv, us_opt, pats) ->
        let pats = List.map (fun (p, imp) -> elaborate_pat env p, imp) pats in
        let _, t = Env.lookup_datacon env fv.fv_name.v in
        let f, _ = U.arrow_formals t in
        let rec aux formals pats =
            match formals, pats with
            | [], [] -> []
            | [], _::_ ->
                raise_error (Errors.Fatal_TooManyPatternArguments,
                            "Too many pattern arguments")
                            (range_of_lid fv.fv_name.v)
            | _::_, [] -> //fill the rest with dot patterns, if all the remaining formals are implicit
            formals |>
            List.map
                (fun fml ->
                    let t, imp = fml.binder_bv, fml.binder_qual in
                    match imp with
                    | Some (Implicit inaccessible) ->
                    let a = Syntax.new_bv (Some (Syntax.range_of_bv t)) tun in
                    let r = range_of_lid fv.fv_name.v in
                    maybe_dot inaccessible a r, true

                    | _ ->
                    raise_error (Errors.Fatal_InsufficientPatternArguments,
                                BU.format1 "Insufficient pattern arguments (%s)"
                                            (Print.pat_to_string p))
                                (range_of_lid fv.fv_name.v))

            | f::formals', (p, p_imp)::pats' ->
            begin
            match f.binder_bv, f.binder_qual with
            | (_, Some (Implicit inaccessible))
                when inaccessible && p_imp -> //we have an inaccessible pattern but the user wrote a pattern there explicitly
              begin
              match p.v with
              | Pat_dot_term _ ->
                (p, true)::aux formals' pats'

              | Pat_wild _ -> //it's ok; it's not going to be bound anyway
                let a = Syntax.new_bv (Some p.p) tun in
                let p = maybe_dot inaccessible a (range_of_lid fv.fv_name.v) in
                (p, true)::aux formals' pats'

              | _ ->
                raise_error (Errors.Fatal_InsufficientPatternArguments,
                             BU.format1 "This pattern (%s) binds an inaccesible argument; use a wildcard ('_') pattern"
                                         (Print.pat_to_string p))
                             p.p
              end

            | (_, Some (Implicit _)) when p_imp ->
                (p, true)::aux formals' pats'

            | (_, Some (Implicit inaccessible)) ->
                let a = Syntax.new_bv (Some p.p) tun in
                let p = maybe_dot inaccessible a (range_of_lid fv.fv_name.v) in
                (p, true)::aux formals' pats

            | (_, imp) ->
                (p, S.is_bqual_implicit imp)::aux formals' pats'
            end
        in
        {p with v=Pat_cons(fv, us_opt, aux f pats)}
    | _ -> p

exception Raw_pat_cannot_be_translated
let raw_pat_as_exp (env:Env.env) (p:pat)
  : option (term * list bv)
  = let rec aux bs p = 
        match p.v with
        | Pat_constant c ->
          let e =
              match c with
              | FStar.Const.Const_int(repr, Some sw) ->
                FStar.ToSyntax.ToSyntax.desugar_machine_integer env.dsenv repr sw p.p
              | _ ->
                mk (Tm_constant c) p.p
          in
          e, bs

        | Pat_dot_term(_, t) ->
          begin
          let t = SS.compress t in
          match t.n with
          | Tm_unknown -> raise Raw_pat_cannot_be_translated
          | _ -> t, bs
          end

        | Pat_wild x
        | Pat_var x ->
          mk (Tm_name x) p.p, x::bs

        | Pat_cons(fv, us_opt, pats) ->
          let args, bs = 
            List.fold_right
              (fun (p, i) (args, bs) ->
                let ep, bs = aux bs p in
                ((ep, as_aqual_implicit i) :: args), bs)
              pats
              ([], bs)
          in
          let hd = Syntax.fv_to_tm fv in
          let hd = 
            match us_opt with
            | None -> hd
            | Some us -> S.mk_Tm_uinst hd us 
          in
          let e = mk_Tm_app hd args p.p in
          e, bs
    in
    try Some (aux [] p)
    with Raw_pat_cannot_be_translated -> None

(*
  pat_as_exps allow_implicits env p:
    Turns a pattern p into a triple:
*)
let pat_as_exp (introduce_bv_uvars:bool)
               (inst_pat_cons_univs:bool)
               (env:Env.env)
               (p:pat)
    : (list bv          (* pattern-bound variables (which may appear in the branch of match) *)
     * term              (* expressions corresponding to the pattern *)
     * guard_t           (* guard with just the implicit variables introduced in the pattern *)
     * pat)   =          (* decorated pattern, with all the missing implicit args in p filled in *)
    let intro_bv (env:Env.env) (x:bv) :(bv * guard_t * Env.env) =
        if not introduce_bv_uvars
        then {x with sort=S.tun}, Env.trivial_guard, env
        else let t, _ = U.type_u() in
             let t_x, _, guard = new_implicit_var_aux "pattern bv type" (S.range_of_bv x) env t Allow_untyped None in
             let x = {x with sort=t_x} in
             x, guard, Env.push_bv env x
    in
    let rec pat_as_arg_with_env env (p:pat) :
                                    (list bv    //all pattern-bound vars including wild-cards, in proper order
                                    * list bv   //just the accessible vars, for the disjunctive pattern test
                                    * list bv   //just the wildcards
                                    * Env.env    //env extending with the pattern-bound variables
                                    * term       //the pattern as a term/typ
                                    * guard_t    //guard with all new implicits
                                    * pat) =     //the elaborated pattern itself
        match p.v with
           | Pat_constant c ->
             let e =
                match c with
                | FStar.Const.Const_int(repr, Some sw) ->
                  FStar.ToSyntax.ToSyntax.desugar_machine_integer env.dsenv repr sw p.p
                | _ ->
                  mk (Tm_constant c) p.p
             in
             ([], [], [], env, e, trivial_guard, p)

           | Pat_dot_term(x, _) ->
             let k, _ = U.type_u () in
             let t, _, g = new_implicit_var_aux "pat_dot_term type" (S.range_of_bv x) env k Allow_ghost None in
             let x = {x with sort=t} in
             let e, _,  g' = new_implicit_var_aux "pat_dot_term" (S.range_of_bv x) env t Allow_ghost None in
             let p = {p with v=Pat_dot_term(x, e)} in
             ([], [], [], env, e, conj_guard g g', p)

           | Pat_wild x ->
             let x, g, env = intro_bv env x in
             let e = mk (Tm_name x) p.p in
             ([x], [], [x], env, e, g, p)

           | Pat_var x ->
             let x, g, env = intro_bv env x in
             let e = mk (Tm_name x) p.p in
             ([x], [x], [], env, e, g, p)

           | Pat_cons(fv, us_opt, pats) -> 
             let (b, a, w, env, args, guard, pats) =
               pats |>
               List.fold_left
                 (fun (b, a, w, env, args, guard, pats) (p, imp) ->
                    let (b', a', w', env, te, guard', pat) = pat_as_arg_with_env env p in
                    let arg = if imp then iarg te else as_arg te in
                    (b'::b, a'::a, w'::w, env, arg::args, conj_guard guard guard', (pat, imp)::pats))
               ([], [], [], env, [], trivial_guard, [])
             in
             let inst_head hd us_opt = 
               match us_opt with
               | None -> hd
               | Some us -> Syntax.mk_Tm_uinst hd us
             in
             let hd, us_opt =
               let hd = Syntax.fv_to_tm fv in
               if not inst_pat_cons_univs
               || Some? us_opt
               then inst_head hd us_opt, us_opt
               else let us, _ = Env.lookup_datacon env (Syntax.lid_of_fv fv) in
                    if List.length us = 0 then hd, Some []
                    else Syntax.mk_Tm_uinst hd us, Some us
             in
             let e = mk_Tm_app hd (args |> List.rev) p.p in
             (List.rev b |> List.flatten,
              List.rev a |> List.flatten,
              List.rev w |> List.flatten,
              env,
              e,
              guard,
              {p with v=Pat_cons(fv, us_opt, List.rev pats)})
    in
    let one_pat env p =
        let p = elaborate_pat env p in
        let b, a, w, env, arg, guard, p = pat_as_arg_with_env env p in
        match b |> BU.find_dup bv_eq with
            | Some x ->
              let m = Print.bv_to_string x in
              let err = (Errors.Fatal_NonLinearPatternVars, (format1 "The pattern variable \"%s\" was used more than once" m)) in
              raise_error err p.p
            | _ -> b, a, w, arg, guard, p
    in
    let b, _, _, tm, guard, p = one_pat env p in
    b, tm, guard, p
