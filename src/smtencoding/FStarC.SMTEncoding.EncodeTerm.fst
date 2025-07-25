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

module FStarC.SMTEncoding.EncodeTerm
open FStarC.Effect
open FStarC.List
open FStarC
open FStarC.Defensive
open FStarC.TypeChecker.Env
open FStarC.Syntax
open FStarC.Syntax.Syntax
open FStarC.TypeChecker
open FStarC.SMTEncoding.Term
open FStarC.Ident
open FStarC.Const
open FStarC.SMTEncoding
open FStarC.SMTEncoding.Util
open FStarC.SMTEncoding.Env

module BU     = FStarC.Util
module Const  = FStarC.Parser.Const
module EMB    = FStarC.Syntax.Embeddings
module Env    = FStarC.TypeChecker.Env
module N      = FStarC.TypeChecker.Normalize
module RC     = FStarC.Reflection.V2.Constants
module R      = FStarC.Reflection.V2.Builtins
module SE     = FStarC.Syntax.Embeddings
module S      = FStarC.Syntax.Syntax
module SS     = FStarC.Syntax.Subst
module TcUtil = FStarC.TypeChecker.Util
module U      = FStarC.Syntax.Util

open FStarC.Class.Show
open FStarC.Class.Tagged
open FStarC.Class.Setlike
open FStarC.Syntax.Print {}
open FStarC.Reflection.V2.Embeddings {}

let dbg_PartialApp       = Debug.get_toggle "PartialApp"
let dbg_SMTEncoding      = Debug.get_toggle "SMTEncoding"
let dbg_SMTEncodingReify = Debug.get_toggle "SMTEncodingReify"

(*---------------------------------------------------------------------------------*)
(*  <Utilities> *)

let mkForall_fuel' mname r n (pats, vars, body) =
    let fallback () = mkForall r (pats, vars, body) in
    if (Options.unthrottle_inductives())
    then fallback ()
    else let fsym, fterm = fresh_fvar mname "f" Fuel_sort in
         let add_fuel tms =
            tms |> List.map (fun p -> match p.tm with
            | Term.App(Var "HasType", args) -> mkApp("HasTypeFuel", fterm::args)
            | _ -> p) in
         let pats = List.map add_fuel pats in
         let body = match body.tm with
            | Term.App(Imp, [guard; body']) ->
              let guard = match guard.tm with
                | App(And, guards) -> mk_and_l (add_fuel guards)
                | _ -> add_fuel [guard] |> List.hd in
              mkImp(guard,body')
            | _ -> body in
         let vars = mk_fv (fsym, Fuel_sort)::vars in
         mkForall r (pats, vars, body)

let mkForall_fuel mname r = mkForall_fuel' mname r 1

let head_normal env t =
   let t = U.unmeta t in
   match t.n with
    | Tm_arrow _
    | Tm_refine _
    | Tm_bvar _
    | Tm_uvar _
    | Tm_abs _
    | Tm_constant _ -> true
    | Tm_fvar fv
    | Tm_app {hd={n=Tm_fvar fv}} -> Env.lookup_definition [Env.Eager_unfolding_only] env.tcenv fv.fv_name.v |> None?
    | _ -> false

let head_redex env t =
    match (U.un_uinst t).n with
    | Tm_abs {rc_opt=Some rc} ->
      Ident.lid_equals rc.residual_effect Const.effect_Tot_lid
      || Ident.lid_equals rc.residual_effect Const.effect_GTot_lid
      || List.existsb (function TOTAL -> true | _ -> false) rc.residual_flags

    | Tm_fvar fv ->
      Env.lookup_definition [Env.Eager_unfolding_only] env.tcenv fv.fv_name.v |> Some?

    | _ -> false

let norm_with_steps steps env t =
  Profiling.profile
    (fun () -> N.normalize steps env t)
    (Some (Ident.string_of_lid (Env.current_module env)))
    "FStarC.SMTEncoding.EncodeTerm.norm_with_steps"

let normalize_refinement steps env t =
  Profiling.profile
    (fun () -> N.normalize_refinement steps env t)
    (Some (Ident.string_of_lid (Env.current_module env)))
    "FStarC.SMTEncoding.EncodeTerm.normalize_refinement"

let whnf env t =
    if head_normal env t then t
    else norm_with_steps [Env.Beta; Env.Weak; Env.HNF; Env.Exclude Env.Zeta;  //we don't know if it will terminate, so no recursion
                          Env.Eager_unfolding; Env.EraseUniverses] env.tcenv t
let norm env t = norm_with_steps [Env.Beta; Env.Exclude Env.Zeta;  //we don't know if it will terminate, so no recursion
                                  Env.Eager_unfolding; Env.EraseUniverses] env.tcenv t

(* `maybe_whnf env t` attempts to reduce t to weak-head normal form.
 *  It is called when `t` is a head redex, e.g., if its head symbol is marked for unfolding.
 *  However, if its head symbol is also marked as `strict_on_arguments`, then if it is applied
 *  to non-constant arguments, then it may actually not be unfolded.
 *  In those cases `maybe_whnf env t` may not reduce `t` at all.
 *  In callers of this code, we need to be careful to check that if `t` was not reduced, then
 *  we do not enter into infinite loops by recursing on `t` itself.
 *)

let maybe_whnf env t =
  let t' = whnf env t in
  let head', _ = U.head_and_args t' in
  if head_redex env head' //this wasn't reducible for some reason, e.g., not applied to strict arguments
  then None
  else Some t'

let trivial_post t : Syntax.term =
    U.abs [null_binder t]
             (Syntax.fvar Const.true_lid None)
             None

let mk_Apply e (vars:fvs) =
    vars |> List.fold_left (fun out var ->
            match fv_sort var with
            | Fuel_sort -> mk_ApplyTF out (mkFreeV var)
            | s ->
              // let _ = if s <> Term_sort then (printfn "Expected Term_sort; got %A" s; failwith "DIE!") in
              mk_ApplyTT out (mkFreeV var)) e
let mk_Apply_args e args = args |> List.fold_left mk_ApplyTT e
let raise_arity_mismatch head arity n_args rng =
    Errors.raise_error rng Errors.Fatal_SMTEncodingArityMismatch
      (Format.fmt3 "Head symbol %s expects at least %s arguments; got only %s"
              head
              (show arity)
              (show n_args))

//See issue #1750 and tests/bug-reports/Bug1750.fst
let isTotFun_axioms pos head vars guards is_pure =
    let maybe_mkForall pat vars body =
        match vars with
        | [] -> body
        | _ -> mkForall pos (pat, vars, body)
    in
    let rec is_tot_fun_axioms ctx ctx_guard head vars guards =
        match vars, guards with
        | [], [] ->
          mkTrue

        | [_], _ ->
          //last arrow, the effect label tells us if its pure or not
          if is_pure
          then maybe_mkForall [[head]] ctx (mkImp (ctx_guard, mk_IsTotFun head))
          else mkTrue

        | x::vars, g_x::guards ->
          //curried arrow with more than 1 argument
          //head is definitely Tot
          let is_tot_fun_head =
              maybe_mkForall [[head]] ctx (mkImp (ctx_guard, mk_IsTotFun head))
          in
          let app = mk_Apply head [x] in
          let ctx = ctx @ [x] in
          let ctx_guard = mkAnd (ctx_guard, g_x) in
          let rest = is_tot_fun_axioms ctx ctx_guard app vars guards in
          mkAnd (is_tot_fun_head, rest)

        | _ ->
            failwith "impossible: isTotFun_axioms"
    in
    is_tot_fun_axioms [] mkTrue head vars guards

let maybe_curry_app rng (head:either op term) (arity:int) (args:list term) : term =
    let n_args = List.length args in
    match head with
    | Inr head -> //must curry
      mk_Apply_args head args

    | Inl head ->
        if n_args = arity
        then Util.mkApp'(head, args)
        else if n_args > arity
        then let args, rest = BU.first_N arity args in
             let head = Util.mkApp'(head, args) in
             mk_Apply_args head rest
        else raise_arity_mismatch (Term.op_to_string head) arity n_args rng

let maybe_curry_fvb rng fvb args =
    if fvb.fvb_thunked
    then mk_Apply_args (force_thunk fvb) args
    else maybe_curry_app rng (Inl (Var fvb.smt_id)) fvb.smt_arity args

let is_app = function
    | Var "ApplyTT"
    | Var "ApplyTF" -> true
    | _ -> false

let check_pattern_vars env vars pats =
    let pats =
        pats |> List.map (fun (x, _) ->
        norm_with_steps [Env.Beta;Env.AllowUnboundUniverses;Env.EraseUniverses] env.tcenv x)
    in
    match pats with
    | [] -> ()
    | hd::tl ->
        let pat_vars = List.fold_left (fun out x -> union out (Free.names x)) (Free.names hd) tl in
        match vars |> Option.find (fun ({binder_bv=b}) -> not (mem b pat_vars)) with
        | None -> ()
        | Some ({binder_bv=x}) ->
        let pos = List.fold_left (fun out t -> Range.union_ranges out t.pos) hd.pos tl in
        Errors.log_issue pos Errors.Warning_SMTPatternIllFormed
          (Format.fmt1 "SMT pattern misses at least one bound variable: %s" (show x))

(*  </Utilities> *)

(**********************************************************************************)
(* The main encoding of terms and formulae: mutually recursive                    *)
(* see fstar-priv/papers/mm/encoding.txt for a semi-formal sketch of the encoding *)
(**********************************************************************************)

(* Abstractly:

      ctx = (bvvdef -> term(Term_sort))
       ex = set (var x term(Bool))        existentially bound variables
    [[e]] : ctx -> term(Term_sort) * ex
    [[f]] : ctx -> term(Bool)
   [[bs]] : ctx -> (vars
                    * term(Bool)  <-- guard on bound vars
                    * ctx)   <-- context extended with bound vars

    Concretely, [[*]] are the encode_* functions, for exp, formula, binders
    ctx is implemented using env_t
    and term( * ) is just term
 *)

type label = (fv & string & Range.t)
type labels = list label
type pattern = {
  pat_vars: list (bv & fv);
  pat_term: unit -> (term & decls_t);                   (* the pattern as a term(exp) *)
  guard: term -> term;                                  (* the guard condition of the pattern, as applied to a particular scrutinee term(exp) *)
  projections: term -> list (bv & term)                (* bound variables of the pattern, and the corresponding projected components of the scrutinee *)
 }

let as_function_typ env t0 =
    let rec aux norm t =
        let t = SS.compress t in
        match t.n with
            | Tm_arrow _ -> t
            | Tm_refine _ -> aux true (U.unrefine t)
            | _ -> if norm
                   then aux false (whnf env t)
                   else failwith (Format.fmt2 "(%s) Expected a function typ; got %s" (Range.string_of_range t0.pos) (show t0))
    in aux true t0

let rec curried_arrow_formals_comp k =
  let k = Subst.compress k in
  match k.n with
  | Tm_arrow {bs; comp=c}  -> Subst.open_comp bs c
  | Tm_refine {b=bv} ->
    let args, res = curried_arrow_formals_comp bv.sort in
    begin
    match args with
    | [] -> [], Syntax.mk_Total k
    | _ -> args, res
    end
  | _                -> [], Syntax.mk_Total k

let is_arithmetic_primitive head args =
    match head.n, args with
    | Tm_fvar fv, [_;_]->
      S.fv_eq_lid fv Const.op_Addition
      || S.fv_eq_lid fv Const.op_Subtraction
      || S.fv_eq_lid fv Const.op_Multiply
      || S.fv_eq_lid fv Const.op_Division
      || S.fv_eq_lid fv Const.op_Modulus
      || S.fv_eq_lid fv Const.real_op_LT
      || S.fv_eq_lid fv Const.real_op_LTE
      || S.fv_eq_lid fv Const.real_op_GT
      || S.fv_eq_lid fv Const.real_op_GTE
      || S.fv_eq_lid fv Const.real_op_Addition
      || S.fv_eq_lid fv Const.real_op_Subtraction
      || S.fv_eq_lid fv Const.real_op_Multiply
      || S.fv_eq_lid fv Const.real_op_Division

    | Tm_fvar fv, [_] ->
      S.fv_eq_lid fv Const.op_Minus

    | _ -> false

let isInteger (tm: Syntax.term') : bool =
    match tm with
    | Tm_constant (Const_int (n,None)) -> true
    | _ -> false

let getInteger (tm : Syntax.term') =
    match tm with
    | Tm_constant (Const_int (n,None)) -> FStarC.Util.int_of_string n
    | _ -> failwith "Expected an Integer term"

(* We only want to encode a term as a bitvector term (not an uninterpreted function)
   if there is a concrete/constant size argument given*)
let is_BitVector_primitive head args =
    match head.n, args with
    | Tm_fvar fv, [(sz_arg, _);_;_] ->
      (S.fv_eq_lid fv Const.bv_and_lid
      || S.fv_eq_lid fv Const.bv_xor_lid
      || S.fv_eq_lid fv Const.bv_or_lid
      || S.fv_eq_lid fv Const.bv_add_lid
      || S.fv_eq_lid fv Const.bv_sub_lid
      || S.fv_eq_lid fv Const.bv_shift_left_lid
      || S.fv_eq_lid fv Const.bv_shift_right_lid
      || S.fv_eq_lid fv Const.bv_udiv_lid
      || S.fv_eq_lid fv Const.bv_mod_lid
      || S.fv_eq_lid fv Const.bv_mul_lid
      || S.fv_eq_lid fv Const.bv_shift_left'_lid
      || S.fv_eq_lid fv Const.bv_shift_right'_lid
      || S.fv_eq_lid fv Const.bv_udiv_unsafe_lid
      || S.fv_eq_lid fv Const.bv_mod_unsafe_lid
      || S.fv_eq_lid fv Const.bv_mul'_lid
      || S.fv_eq_lid fv Const.bv_ult_lid
      || S.fv_eq_lid fv Const.bv_uext_lid) &&
      (isInteger sz_arg.n)
    | Tm_fvar fv, [(sz_arg, _); _] ->
        (S.fv_eq_lid fv Const.nat_to_bv_lid
         || S.fv_eq_lid fv Const.bv_to_nat_lid) &&
        (isInteger sz_arg.n)

    | _ -> false

let rec encode_const c env =
  Errors.with_ctx "While encoding a constant to SMT" (fun () ->
    match c with
    | Const_unit -> mk_Term_unit, []
    | Const_bool true -> boxBool mkTrue, []
    | Const_bool false -> boxBool mkFalse, []
    | Const_char c -> mkApp("FStar.Char.__char_of_int", [boxInt (mkInteger' (BU.int_of_char c))]), []
    | Const_int (i, None)  -> boxInt (mkInteger i), []
    | Const_int (repr, Some sw) ->
      let syntax_term = FStarC.ToSyntax.ToSyntax.desugar_machine_integer env.tcenv.dsenv repr sw Range.dummyRange in
      encode_term syntax_term env
    | Const_string(s, _) -> Term.boxString <| mk_String_const s, []
    | Const_range _ -> mk_Range_const (), []
    | Const_effect -> mk_Term_type, []
    | Const_real r -> boxReal (mkReal r), []
    | c -> failwith (Format.fmt1 "Unhandled constant: %s" (show c))
  )
and encode_binders (fuel_opt:option term) (bs:Syntax.binders) (env:env_t) :
                            (list fv                       (* translated bound variables *)
                            & list term                    (* guards *)
                            & env_t                         (* extended context *)
                            & decls_t                       (* top-level decls to be emitted *)
                            & list bv)                     (* names *) =

    if Debug.medium () then Format.print1 "Encoding binders %s\n" (show bs);

    let vars, guards, env, decls, names =
      bs |> List.fold_left
      (fun (vars, guards, env, decls, names) b ->
        let v, g, env, decls', n =
            let x = b.binder_bv in
            let xxsym, xx, env' = gen_term_var env x in
            let guard_x_t, decls' =
              encode_term_pred fuel_opt (norm env x.sort) env xx
            in //if we had polarities, we could generate a mkHasTypeZ here in the negative case
            mk_fv (xxsym, Term_sort),
            guard_x_t,
            env',
            decls',
            x
        in
        v::vars, g::guards, env, decls@decls', n::names)
       ([], [], env, [], [])
    in
    List.rev vars,
    List.rev guards,
    env,
    decls,
    List.rev names

and encode_term_pred (fuel_opt:option term) (t:typ) (env:env_t) (e:term) : term & decls_t =
    let t, decls = encode_term t env in
    mk_HasTypeWithFuel fuel_opt e t, decls

and encode_arith_term env head args_e =
    let arg_tms, decls = encode_args args_e env in
    let head_fv =
        match head.n with
        | Tm_fvar fv -> fv
        | _ -> failwith "Impossible"
    in
    let unary unbox arg_tms =
        unbox (List.hd arg_tms)
    in
    let binary unbox arg_tms =
        unbox (List.hd arg_tms),
        unbox (List.hd (List.tl arg_tms))
    in
    let mk_default () =
        let fname, fuel_args, arity = lookup_free_var_sym env head_fv.fv_name in
        let args = fuel_args@arg_tms in
        maybe_curry_app head.pos fname arity args
    in
    let mk_l : (term -> term) -> ('a -> term) -> (list term -> 'a) -> list term -> term =
      fun box op mk_args ts ->
          if Options.smtencoding_l_arith_native () then
             op (mk_args ts) |> box
          else mk_default ()
    in
    let mk_nl box unbox nm op ts =
      if Options.smtencoding_nl_arith_wrapped () then
          let t1, t2 = binary unbox ts in
          Util.mkApp(nm, [t1;t2]) |> box
      else if Options.smtencoding_nl_arith_native () then
          op (binary unbox ts) |> box
      else mk_default ()
    in
    let add box unbox = mk_l box Util.mkAdd (binary unbox)  in
    let sub box unbox = mk_l box Util.mkSub (binary unbox) in
    let minus box unbox = mk_l box Util.mkMinus (unary unbox) in
    let mul box unbox nm = mk_nl box unbox nm Util.mkMul in
    let div box unbox nm = mk_nl box unbox nm Util.mkDiv in
    let modulus box unbox = mk_nl box unbox "_mod" Util.mkMod in
    let ops =
        [(Const.op_Addition,    add Term.boxInt Term.unboxInt);
         (Const.op_Subtraction, sub Term.boxInt Term.unboxInt);
         (Const.op_Multiply,    mul Term.boxInt Term.unboxInt "_mul");
         (Const.op_Division,    div Term.boxInt Term.unboxInt "_div");
         (Const.op_Modulus,     modulus Term.boxInt Term.unboxInt);
         (Const.op_Minus,       minus Term.boxInt Term.unboxInt);
         (Const.real_op_Addition,    add Term.boxReal Term.unboxReal);
         (Const.real_op_Subtraction, sub Term.boxReal Term.unboxReal);
         (Const.real_op_Multiply,    mul Term.boxReal Term.unboxReal "_rmul");
         (Const.real_op_Division,    mk_nl Term.boxReal Term.unboxReal "_rdiv" Util.mkRealDiv);
         (Const.real_op_LT,          mk_l Term.boxBool Util.mkLT  (binary Term.unboxReal));
         (Const.real_op_LTE,         mk_l Term.boxBool Util.mkLTE (binary Term.unboxReal));
         (Const.real_op_GT,          mk_l Term.boxBool Util.mkGT  (binary Term.unboxReal));
         (Const.real_op_GTE,         mk_l Term.boxBool Util.mkGTE (binary Term.unboxReal))]
    in
    let _, op =
        List.tryFind (fun (l, _) -> S.fv_eq_lid head_fv l) ops |>
        Some?.v
    in
    op arg_tms, decls

 and encode_BitVector_term env head args_e =
    (*first argument should be the implicit vector size
      we do not want to encode this*)
    let (tm_sz, _) : arg = List.hd args_e in
    let sz = getInteger tm_sz.n in
    let sz_key = FStarC.Format.fmt1 "BitVector_%s" (show sz) in
    let sz_decls =
      let t_decls, constr_name, discriminator_name = mkBvConstructor sz in
      //Typing inversion for bv_t n
      let decls, typing_inversion =
        (* forall (x:Term). HasType x (bv_t n) ==> is-BoxVec#n x *)
        let bv_t_n, decls =
          let head = S.lid_as_fv FStarC.Parser.Const.bv_t_lid None in
          let t = U.mk_app (S.fv_to_tm head) [tm_sz, None] in
          encode_term t env
        in
        let xsym = mk_fv (varops.fresh env.current_module_name "x", Term_sort) in
        let x = mkFreeV xsym in
        let x_has_type_bv_t_n = mk_HasType x bv_t_n in
        let ax = mkForall head.pos ([[x_has_type_bv_t_n]],
                                    [xsym],
                                    mkImp(x_has_type_bv_t_n, mkApp (discriminator_name, [x]))) in
        let name = "typing_inversion_for_" ^constr_name in
        decls, mkAssume(ax, Some name, name)
      in
      decls@mk_decls "" sz_key (t_decls@[typing_inversion]) []
    in
    (* we need to treat the size argument for zero_extend specially*)
    let arg_tms, ext_sz =
        match head.n, args_e with
        | Tm_fvar fv, [_;(sz_arg, _);_] when
            (S.fv_eq_lid fv Const.bv_uext_lid &&
                (isInteger sz_arg.n)) ->
                (List.tail (List.tail args_e), Some (getInteger sz_arg.n))
        | Tm_fvar fv, [_;(sz_arg, _);_] when
            (S.fv_eq_lid fv Const.bv_uext_lid) ->
            (*fail if extension size is not a constant*)
            failwith (FStarC.Format.fmt1 "Not a constant bitvector extend size: %s"
                            (show sz_arg))
        | _  -> (List.tail args_e, None)
    in

    let arg_tms, decls = encode_args arg_tms env in
    let head_fv =
        match head.n with
        | Tm_fvar fv -> fv
        | _ -> failwith "Impossible"
    in
    let unary arg_tms =
        Term.unboxBitVec sz (List.hd arg_tms)
    in
    let unary_arith arg_tms =
        Term.unboxInt (List.hd arg_tms)
    in
    let binary arg_tms =
        Term.unboxBitVec sz (List.hd arg_tms),
        Term.unboxBitVec sz (List.hd (List.tl arg_tms))
    in
    let binary_arith arg_tms =
        Term.unboxBitVec sz (List.hd arg_tms),
        Term.unboxInt (List.hd (List.tl arg_tms))
    in
    let mk_bv : ('a -> term) -> (list term -> 'a) -> (term -> term) -> list term -> term =
      fun op mk_args resBox ts ->
             op (mk_args ts) |> resBox
    in
    let bv_and  = mk_bv Util.mkBvAnd binary (Term.boxBitVec sz) in
    let bv_xor  = mk_bv Util.mkBvXor binary (Term.boxBitVec sz) in
    let bv_or   = mk_bv Util.mkBvOr binary (Term.boxBitVec sz) in
    let bv_add  = mk_bv Util.mkBvAdd binary (Term.boxBitVec sz) in
    let bv_sub  = mk_bv Util.mkBvSub binary (Term.boxBitVec sz) in
    let bv_shl  = mk_bv (Util.mkBvShl sz) binary_arith (Term.boxBitVec sz) in
    let bv_shr  = mk_bv (Util.mkBvShr sz) binary_arith (Term.boxBitVec sz) in
    let bv_udiv = mk_bv (Util.mkBvUdiv sz) binary_arith (Term.boxBitVec sz) in
    let bv_mod  = mk_bv (Util.mkBvMod sz) binary_arith (Term.boxBitVec sz) in
    let bv_mul  = mk_bv (Util.mkBvMul sz) binary_arith (Term.boxBitVec sz) in

    // Binary bv_t -> bv_t -> bv_t variants
    let bv_shl' = mk_bv (Util.mkBvShl' sz) binary (Term.boxBitVec sz) in
    let bv_shr' = mk_bv (Util.mkBvShr' sz) binary (Term.boxBitVec sz) in
    let bv_udiv_unsafe = mk_bv (Util.mkBvUdivUnsafe sz) binary (Term.boxBitVec sz) in
    let bv_mod_unsafe  = mk_bv (Util.mkBvModUnsafe sz) binary (Term.boxBitVec sz) in
    let bv_mul' = mk_bv (Util.mkBvMul' sz) binary (Term.boxBitVec sz) in

    let bv_ult  = mk_bv Util.mkBvUlt binary Term.boxBool in
    let bv_uext arg_tms =
           mk_bv (Util.mkBvUext (match ext_sz with | Some x -> x | None -> failwith "impossible")) unary
                         (Term.boxBitVec (sz +  (match ext_sz with | Some x -> x | None -> failwith "impossible"))) arg_tms in
    let to_int  = mk_bv Util.mkBvToNat unary Term.boxInt in
    let bv_to   = mk_bv (Util.mkNatToBv sz) unary_arith (Term.boxBitVec sz) in
    let ops =
        [(Const.bv_and_lid, bv_and);
         (Const.bv_xor_lid, bv_xor);
         (Const.bv_or_lid, bv_or);
         (Const.bv_add_lid, bv_add);
         (Const.bv_sub_lid, bv_sub);
         (Const.bv_shift_left_lid, bv_shl);
         (Const.bv_shift_right_lid, bv_shr);
         (Const.bv_udiv_lid, bv_udiv);
         (Const.bv_mod_lid, bv_mod);
         (Const.bv_mul_lid, bv_mul);
         (Const.bv_shift_left'_lid, bv_shl');
         (Const.bv_shift_right'_lid, bv_shr');
         (Const.bv_udiv_unsafe_lid, bv_udiv_unsafe);
         (Const.bv_mod_unsafe_lid, bv_mod_unsafe);
         (Const.bv_mul'_lid, bv_mul');
         (Const.bv_ult_lid, bv_ult);
         (Const.bv_uext_lid, bv_uext);
         (Const.bv_to_nat_lid, to_int);
         (Const.nat_to_bv_lid, bv_to)]
    in
    let _, op =
        List.tryFind (fun (l, _) -> S.fv_eq_lid head_fv l) ops |>
        Some?.v
    in
    op arg_tms, sz_decls @ decls

and encode_deeply_embedded_quantifier (t:S.term) (env:env_t) : term & decls_t =
    let env = {env with encoding_quantifier=true} in
    let tm, decls = encode_term t env in
    let vars = Term.free_variables tm in
    let valid_tm = mk_Valid tm in
    let key = mkForall t.pos ([], vars, valid_tm) in
    let tkey_hash = hash_of_term key in
    match tm.tm with
    | App(_, [{tm=FreeV _}; {tm=FreeV _}]) ->
      FStarC.Errors.log_issue t Errors.Warning_QuantifierWithoutPattern
        "Not encoding deeply embedded, unguarded quantifier to SMT";
      tm, decls

    | _ ->
      let phi, decls' = encode_formula t env in
      let interp =
              match vars with
              | [] -> mkIff(mk_Valid tm, phi)
              | _ -> mkForall t.pos ([[valid_tm]], vars, mkIff(mk_Valid tm, phi))
      in
      let ax = mkAssume(interp,
                              Some "Interpretation of deeply embedded quantifier",
                              "l_quant_interp_" ^ (BU.digest_of_string tkey_hash)) in
      tm, decls@decls'@(mk_decls "" tkey_hash [ax] (decls@decls'))

(*
 * AR: no hashconsing in this function now
 *     it returns a list of decls blocks that may be duplicate
 *       for example, for two occurrences of x:int{x > 2}
 *     deduplication of these happens in Encode.fs
 *       just before giving the decls to Z3 (see Encode.fs.recover_caching_and_update_env)
 *)
and encode_term (t:typ) (env:env_t) : (term         (* encoding of t, expects t to be in normal form already *)
                                     & decls_t)     (* top-level declarations to be emitted (for shared representations of existentially bound terms *) =

    def_check_scoped t.pos "encode_term" env.tcenv t;
    let t = SS.compress t in
    let t0 = t in
    if !dbg_SMTEncoding
    then Format.print2 "(%s)   %s\n" (tag_of t) (show t);
    match t.n with
      | Tm_delayed  _
      | Tm_unknown    ->
        failwith (Format.fmt3 "(%s) Impossible: %s\n%s\n"
                             (Range.string_of_range <| t.pos)
                             (tag_of t)
                             (show t))

      | Tm_lazy i ->
        let e = U.unfold_lazy i in
        if !dbg_SMTEncoding then
            Format.print2 ">> Unfolded (%s) ~> (%s)\n" (show t)
                                                   (show e);
        encode_term e env

      | Tm_bvar x ->
        failwith (Format.fmt1 "Impossible: locally nameless; got %s" (show x))

      | Tm_ascribed {tm=t; asc=(k,_,_)} ->
        if (match k with Inl t -> U.is_unit t | _ -> false)
        then Term.mk_Term_unit, []
        else encode_term t env

      | Tm_quoted (qt, _) ->
        // Inspect the term and encode its view, recursively.
        // Quoted terms are, in a way, simply an optimization.
        // They should be equivalent to a fully spelled out view.
        //
        // Actual encoding: `q ~> pack qv where qv is the view of q
        let tv = EMB.embed (R.inspect_ln qt) t.pos None EMB.id_norm_cb in
        if !dbg_SMTEncoding then
            Format.print2 ">> Inspected (%s) ~> (%s)\n" (show t0)
                                                    (show tv);
        let t = U.mk_app (RC.refl_constant_term RC.fstar_refl_pack_ln) [S.as_arg tv] in
        encode_term t env

      | Tm_meta {tm=t; meta=Meta_pattern _} ->
        encode_term t ({env with encoding_quantifier=false})

      | Tm_meta {tm=t} ->
        encode_term t env

      | Tm_name x ->
        let t = lookup_term_var env x in
        t, []

      | Tm_fvar v ->
        let encode_freev () =
          let fvb = lookup_free_var_name env v.fv_name in
          let tok = lookup_free_var env v.fv_name in
          let tkey_hash = Term.hash_of_term tok in
          let aux_decls, sym_name =
               if fvb.smt_arity > 0
               then //kick partial application axioms if arity > 0; see #613
                    //and if the head symbol is just a variable
                    //rather than maybe a fuel-instrumented name (cf. #1433)
                   match tok.tm with
                   | FreeV _
                   | App(_, []) ->
                     let sym_name = "@kick_partial_app_" ^ (BU.digest_of_string tkey_hash) in  //the '@' retains this for hints
                     [Util.mkAssume(kick_partial_app tok,
                                    Some "kick_partial_app",
                                    sym_name)], sym_name
                   | _ -> [], ""
               else [], "" in
          tok, (if aux_decls = []
                then ([] |> mk_decls_trivial)
                else mk_decls sym_name tkey_hash aux_decls [])
        in
        if head_redex env t
        then match maybe_whnf env t with
             | None -> encode_freev()
             | Some t -> encode_term t env
        else encode_freev ()

      | Tm_type _ ->
        mk_Term_type, []

      | Tm_uinst(t, _) ->
        encode_term t env

      | Tm_constant c ->
        encode_const c env

      | Tm_arrow {bs=binders; comp=c} ->
        let module_name = env.current_module_name in
        let binders, res = SS.open_comp binders c in
        if  (env.encode_non_total_function_typ
             && U.is_pure_or_ghost_comp res)
             || U.is_tot_or_gtot_comp res
        then let vars, guards_l, env', decls, _ = encode_binders None binders env in
             let fsym = mk_fv (varops.fresh module_name "f", Term_sort) in
             let f = mkFreeV  fsym in
             let app = mk_Apply f vars in
             let tcenv_bs = { env'.tcenv with admit=true } in
             let pre_opt, res_t = TcUtil.pure_or_ghost_pre_and_post tcenv_bs res in
             let res_pred, decls' = encode_term_pred None res_t env' app in
             let guards, guard_decls = match pre_opt with
                | None -> mk_and_l guards_l, []
                | Some pre ->
                  let guard, decls0 = encode_formula pre env' in
                  mk_and_l (guard::guards_l), decls0  in
             //AR: promote ghost to pure for non-informative types
             let is_pure = res |> N.maybe_ghost_to_pure env.tcenv |> U.is_pure_comp in
             //cf. Bug #1750
             //We need to distinguish pure and ghost functions in the encoding
             //both in hash consing, producing different type constructors for them.
             //Tot functions get an additional predicate IsTotFun in their interpretation
             let t_interp =
                 mkForall t.pos
                          ([[app]],
                            vars,
                              mkImp(guards, res_pred))
             in

             (*
              * AR/NS: For an arrow like int -> int -> int -> GTot int, t_interp is of the form:
              *     forall x0.
              *           HasType x0 (int -> int -> int -> GTot int)
              *          <==>
              *           (forall (x1:int) (x2:int) (x3:int).
              *             HasType (ApplyTT (ApplyTT (ApplyTT (x0 x1)) x2) x3) int)
              *          /\ IsTotFun x0
              *          /\ (forall x1. IsTotFun (ApplyTT x0 x1)
              *
              *   I.e, we add IsTotFun axioms for every total partial application.
              *   Importantly, in the example above, the axiom is omitted for
              *   (x0 x1 x2 : int -> GTot int), since this function is not total
              *)


             //finally add the IsTotFun for the function term itself
             let t_interp =
                 let tot_fun_axioms = isTotFun_axioms t.pos f vars guards_l is_pure in
                 mkAnd (t_interp, tot_fun_axioms)
             in
             let cvars =
               Term.free_variables t_interp
               |> List.filter (fun x -> fv_name x <> fv_name fsym)
             in
             let tkey =
               mkForall t.pos ([], fsym::cvars, t_interp)
             in
             let prefix =
               if is_pure
               then "Tm_arrow_"
               else "Tm_ghost_arrow_"
             in
             let tkey_hash =
               prefix ^ hash_of_term tkey in
             let tsym =
               prefix ^ BU.digest_of_string tkey_hash
             in
             let cvar_sorts = List.map fv_sort cvars in
             let caption =
                 if Options.log_queries()
                 then Some (BU.replace_char (N.term_to_string env.tcenv t0) '\n' ' ')
                 else None in

             let tdecl = Term.DeclFun(tsym, cvar_sorts, Term_sort, caption) in

             let t = mkApp(tsym, List.map mkFreeV cvars) in //arity ok
             let t_has_kind = mk_HasType t mk_Term_type in

             let k_assumption =
             let a_name = "kinding_"^tsym in
             Util.mkAssume (mkForall t0.pos ([[t_has_kind]], cvars, t_has_kind), Some a_name, a_name) in

             let f_has_t = mk_HasType f t in
             let f_has_t_z = mk_HasTypeZ f t in
             let pre_typing =
             let a_name = "pre_typing_"^tsym in
             Util.mkAssume(mkForall_fuel module_name t0.pos ([[f_has_t]], fsym::cvars,
                           mkImp(f_has_t, mk_tester "Tm_arrow" (mk_PreType f))),
                           Some "pre-typing for functions",
                           module_name ^ "_" ^ a_name) in
             let t_interp =
                 let a_name = "interpretation_"^tsym in
                 Util.mkAssume(mkForall t0.pos ([[f_has_t_z]],
                                                fsym::cvars,
                                                 mkIff (f_has_t_z, t_interp)),
                               Some a_name,
                               module_name ^ "_" ^ a_name)
             in
             let t_decls = [tdecl; k_assumption; pre_typing; t_interp] in
             t, decls@decls'@guard_decls@(mk_decls tsym tkey_hash t_decls (decls@decls'@guard_decls))

        else
             (*
              * AR: compute a hash for the Non total arrow,
              *       that we will use in the name of the arrow
              *       so that we can get some hashconsing
              *)
             let tkey_hash =
               (*
                * AR: any decls computed here are ignored
                *     we encode terms in this let-scope just to compute a hash
                *)
               let vars, guards_l, env_bs, _, _ = encode_binders None binders env in
               let c = Env.unfold_effect_abbrev (Env.push_binders env.tcenv binders) res |> S.mk_Comp in
               let ct, _ = encode_term (c |> U.comp_result) env_bs in
               let effect_args, _ = encode_args (c |> U.comp_effect_args) env_bs in
               let tkey = mkForall t.pos
                 ([], vars, mk_and_l (guards_l@[ct]@effect_args)) in
               let tkey_hash = "Non_total_Tm_arrow" ^ (hash_of_term tkey) ^ "@Effect=" ^
                 (c |> U.comp_effect_name |> string_of_lid) in
               BU.digest_of_string tkey_hash
             in

             let tsym = "Non_total_Tm_arrow_" ^ tkey_hash in
             (* We need to compute all free variables of this arrow
             expression and parametrize the encoding wrt to them. See
             issue #3028 *)
             let env0 = env in
             let fstar_fvs, (env, fv_decls, fv_vars, fv_tms, fv_guards) =
               let fvs = Free.names t0 |> elems in

               let getfreeV (t:term) : fv =
                 match t.tm with
                 | FreeV fv -> fv
                 | _ -> failwith "Impossible: getfreeV: gen_term_var should always returns a FreeV"
               in

               fvs,
               List.fold_left (fun (env, decls, vars, tms, guards) bv ->
                   (* Get the sort from the environment, do not trust .sort field *)
                   let (sort, _) = Env.lookup_bv env.tcenv bv in
                   (* Generate a fresh SMT variable for this bv *)
                   let sym, smt_tm, env = gen_term_var env bv in
                   let fv = getfreeV smt_tm in
                   (* Generate typing predicate for it at the sort type *)
                   let guard, decls' = encode_term_pred None (norm env sort) env smt_tm in
                   (env, decls'@decls, fv::vars, smt_tm::tms, guard::guards)
               ) (env, [], [], [], []) fvs
             in
             (* Putting in "correct" order... but does it matter? *)
             let fv_decls = List.rev fv_decls in
             let fv_vars = List.rev fv_vars in
             let fv_tms = List.rev fv_tms in
             let fv_guards = List.rev fv_guards in

             let arg_sorts = List.map (fun _ -> Term_sort) fv_tms in
             let tdecl = Term.DeclFun(tsym, arg_sorts, Term_sort, None) in
             let tapp = mkApp(tsym, fv_tms) in
             let t_kinding =
                let a_name = "non_total_function_typing_" ^tsym in
                let axiom =
                  (* We generate:
                     forall v1 .. vn, (v1 hasType t1 /\ ... vn hasType tn) ==> tapp hasType Type *)
                  (* NB: we use the conlusion (HasType tapp Type) as the pattern. Though Z3
                  will probably pick the same one if left empty. *)
                  mkForall t0.pos ([[mk_HasType tapp mk_Term_type]], fv_vars,
                    mkImp (mk_and_l fv_guards, mk_HasType tapp mk_Term_type))
                in
                (* We furthermore must close over any variable that is
                still free in the axiom. This can happen since the types
                of the fvs we are closing over above may not be closed
                in the current env. *)
                let svars = Term.free_variables axiom in
                let axiom = mkForall t0.pos ([], svars, axiom) in
                Util.mkAssume (axiom, Some "Typing for non-total arrows", a_name)
             in

             (* The axiom above is generated over a universal quantification of
             the free variables, but the actual encoding of this instance of the
             arrow is applied to (the encoding of) the actual free variables at
             this point. *)

             let tapp_concrete = mkApp(tsym, List.map (lookup_term_var env0) fstar_fvs) in
             tapp_concrete, fv_decls @ mk_decls tsym tkey_hash [tdecl ; t_kinding ] []

      | Tm_refine _ ->
        let x, f =
          let steps = [
            Env.Weak;
            Env.HNF;
            Env.EraseUniverses
          ] in
          match normalize_refinement steps env.tcenv t0 with
          | {n=Tm_refine {b=x; phi=f}} ->
            let b, f = SS.open_term [S.mk_binder x] f in
            (List.hd b).binder_bv, f
          | _ -> failwith "impossible"
        in

        let base_t, decls = encode_term x.sort env in
        let x, xtm, env' = gen_term_var env x in
        let refinement, decls' = encode_formula f env' in

        let fsym, fterm = fresh_fvar env.current_module_name "f" Fuel_sort in

        let tm_has_type_with_fuel = mk_HasTypeWithFuel (Some fterm) xtm base_t in

        (* `encoding` includes `x.sort` via `tm_has_type_with_fuel` *)
        let encoding = mkAnd(tm_has_type_with_fuel, refinement) in

        //earlier we used to get cvars from encoding
        //but mkAnd is optimized and when refinement is False, it returns False
        //in that case, cvars was turning out to be empty, resulting in non well-formed encoding (e.g. of hasEq, since free variables of base_t are not captured in cvars)
        //to get around that, computing cvars separately from the components of the encoding variable
        let cvars = BU.remove_dups fv_eq (Term.free_variables refinement @ Term.free_variables tm_has_type_with_fuel) in
        let cvars = cvars |> List.filter (fun y -> fv_name y <> x && fv_name y <> fsym) in

        let xfv = mk_fv (x, Term_sort) in
        let ffv = mk_fv (fsym, Fuel_sort) in
        let tkey = mkForall t0.pos ([], ffv::xfv::cvars, encoding) in
        let tkey_hash = Term.hash_of_term tkey in

        if !dbg_SMTEncoding
        then Format.print3 "Encoding Tm_refine %s with tkey_hash %s and digest %s\n"
               (show f) tkey_hash (BU.digest_of_string tkey_hash)
        else ();

        let tsym = "Tm_refine_" ^ (BU.digest_of_string tkey_hash) in
        let cvar_sorts = List.map fv_sort cvars in
        let tdecl = Term.DeclFun(tsym, cvar_sorts, Term_sort, None) in
        let t = mkApp(tsym, List.map mkFreeV cvars) in

        let x_has_base_t = mk_HasType xtm base_t in
        let x_has_t = mk_HasTypeWithFuel (Some fterm) xtm t in
        let t_has_kind = mk_HasType t mk_Term_type in

        //add hasEq axiom for this refinement type
        let t_haseq_base = mk_haseq base_t in
        let t_haseq_ref = mk_haseq t in

        let t_haseq =
        Util.mkAssume(mkForall t0.pos ([[t_haseq_ref]], cvars, (mkIff (t_haseq_ref, t_haseq_base))),
                        Some ("haseq for " ^ tsym),
                        "haseq" ^ tsym) in
        // let t_valid =
        //   let xx = (x, Term_sort) in
        //   let valid_t = mkApp ("Valid", [t]) in
        //   Util.mkAssume(mkForall ([[valid_t]], cvars,
        //       mkIff (mkExists ([], [xx], mkAnd (x_has_base_t, refinement)), valid_t)),
        //                 Some ("validity axiom for refinement"),
        //                 "ref_valid_" ^ tsym)
        // in

        let t_kinding =
        //TODO: guard by typing of cvars?; not necessary since we have pattern-guarded
        Util.mkAssume(mkForall t0.pos ([[t_has_kind]], cvars, t_has_kind),
                        Some "refinement kinding",
                        "refinement_kinding_" ^tsym)
        in
        let t_interp =
        Util.mkAssume(mkForall t0.pos ([[x_has_t]], ffv::xfv::cvars, mkIff(x_has_t, encoding)),
                        Some "refinement_interpretation",
                        "refinement_interpretation_"^tsym) in

        let t_decls = [tdecl;
                       t_kinding; //t_valid;
                       t_interp; t_haseq] in
        t, decls@decls'@mk_decls tsym tkey_hash t_decls (decls@decls')

      | Tm_uvar (uv, _) ->
        let ttm = mk_Term_uvar (Unionfind.uvar_id uv.ctx_uvar_head) Range.dummyRange in
        let t_has_k, decls = encode_term_pred None (U.ctx_uvar_typ uv) env ttm in //TODO: skip encoding this if it has already been encoded before
        let d =
            Util.mkAssume(t_has_k,
                          Some "Uvar typing",
                          varops.mk_unique
                            (Format.fmt1 "uvar_typing_%s"
                                        (show
                                            (Unionfind.uvar_id uv.ctx_uvar_head))))
        in
        ttm, decls@([d] |> mk_decls_trivial)

      | Tm_app _ ->
        let head, args_e = U.head_and_args t0 in
        let head, args_e =
          if head_redex env head
          then match maybe_whnf env t0 with
               | None -> head, args_e
               | Some t -> U.head_and_args t
          else head, args_e
        in
        begin
        match (SS.compress head).n, args_e with
        | _ when is_arithmetic_primitive head args_e ->
            encode_arith_term env head args_e

        | _ when is_BitVector_primitive head args_e ->
            encode_BitVector_term env head args_e

        | Tm_fvar fv, [(arg, _)]
        | Tm_uinst({n=Tm_fvar fv}, _), [(arg, _)]
            when
             (S.fv_eq_lid fv Const.squash_lid
              || S.fv_eq_lid fv Const.auto_squash_lid)
              && Some? (Syntax.Formula.destruct_typ_as_formula arg) ->
          let dummy = S.new_bv None t_unit in
          let t = U.refine dummy arg in (* so that `squash f`, when f is a formula, benefits from shallow embedding *)
          encode_term t env

        | Tm_fvar fv, _
        | Tm_uinst({n=Tm_fvar fv}, _), _
            when (not env.encoding_quantifier)
              && (S.fv_eq_lid fv Const.forall_lid
              ||  S.fv_eq_lid fv Const.exists_lid) ->
          encode_deeply_embedded_quantifier t0 env

        | Tm_constant Const_range_of, [(arg, _)] ->
            encode_const (Const_range arg.pos) env

        | Tm_constant Const_set_range_of, [(arg, _); (rng, _)] ->
            encode_term arg env

        | Tm_constant (Const_reify lopt), _ ->
          let fallback () =
            let f = varops.fresh env.current_module_name "Tm_reify" in
            let decl =
              Term.DeclFun (f, [], Term_sort, Some "Imprecise reify") in
            mkFreeV <| mk_fv (f, Term_sort), [decl] |> mk_decls_trivial in

          (match lopt with
           | None -> fallback ()
           | Some l
             when l |> Env.norm_eff_name env.tcenv
                    |> Env.is_layered_effect env.tcenv -> fallback ()
           | _ ->             
            let e0 = TcUtil.norm_reify env.tcenv []
              (U.mk_reify (args_e |> List.hd |> fst) lopt) in
            if !dbg_SMTEncodingReify
            then Format.print1 "Result of normalization %s\n" (show e0);
            let e = S.mk_Tm_app (TcUtil.remove_reify e0) (List.tl args_e) t0.pos in
            encode_term e env)

        | Tm_constant (Const_reflect _), [(arg, _)] ->
            encode_term arg env

        | Tm_fvar fv, [_; (phi, _)]
        | Tm_uinst ({n=Tm_fvar fv}, _), [_; (phi, _)]
          when S.fv_eq_lid fv Const.by_tactic_lid ->
          encode_term phi env

        | Tm_fvar fv, [_; _; (phi, _)]
        | Tm_uinst ({n=Tm_fvar fv}, _), [_; _; (phi, _)]
          when S.fv_eq_lid fv Const.rewrite_by_tactic_lid ->
          encode_term phi env

        | _ ->
            let args, decls = encode_args args_e env in

            let encode_partial_app (ht_opt:option (S.typ & S.binders & S.comp)) =
                let smt_head, decls' = encode_term head env in
                let app_tm = mk_Apply_args smt_head args in
                match ht_opt with
                | _ when 1=1 -> app_tm, decls@decls' //NS: Intentionally using a default case here to disable the axiom below
                | Some (head_type, formals, c) ->
                    if !dbg_PartialApp
                    then Format.print5 "Encoding partial application:\n\thead=%s\n\thead_type=%s\n\tformals=%s\n\tcomp=%s\n\tactual args=%s\n"
                             (show head)
                             (show head_type)
                             (show formals)
                             (show c)
                             (show args_e);
                    let formals, rest = BU.first_N (List.length args_e) formals in
                    let subst = List.map2 (fun ({binder_bv=bv}) (a, _) -> Syntax.NT(bv, a)) formals args_e in
                    let ty = U.arrow rest c |> SS.subst subst in
                    if !dbg_PartialApp
                    then Format.print1 "Encoding partial application, after subst:\n\tty=%s\n"
                            (show ty);
                    let vars, pattern, has_type, decls'' =
                      let t_hyps, decls =
                        List.fold_left2 (fun (t_hyps, decls) ({binder_bv=bv}) e ->
                          let t = SS.subst subst bv.sort in
                          let t_hyp, decls' = encode_term_pred None t env e in
                          if !dbg_PartialApp
                          then Format.print2 "Encoded typing hypothesis for %s ... got %s\n"
                                         (show t)
                                         (Term.print_smt_term t_hyp);
                          t_hyp::t_hyps, decls@decls')
                        ([], [])
                        formals
                        args
                      in
                      let t_head_hyp, decls' =
                        match smt_head.tm with
                        | FreeV _ ->
                          encode_term_pred None head_type env smt_head
                        | _ ->
                          mkTrue, []
                      in
                      let hyp = Term.mk_and_l (t_head_hyp::t_hyps) Range.dummyRange in
                      let has_type_conclusion, decls'' =
                          encode_term_pred None ty env app_tm
                      in
                      let has_type = mkImp (hyp, has_type_conclusion) in
                      let cvars = Term.free_variables has_type in
                      let app_tm_vars = Term.free_variables app_tm in
                      let pattern, vars =
                        if Term.fvs_subset_of cvars app_tm_vars
                        then [app_tm], app_tm_vars
                        else if Term.fvs_subset_of cvars (Term.free_variables has_type_conclusion)
                        then [has_type_conclusion], cvars
                        else begin
                          Errors.log_issue t0 Errors.Warning_SMTPatternIllFormed
                             (Format.fmt1 "No SMT pattern for partial application %s" (show t0));
                          [], cvars //no pattern!
                        end
                      in
                      vars,
                      pattern,
                      has_type,
                      decls@decls'@decls''
                    in
                    if !dbg_PartialApp
                    then Format.print1 "Encoding partial application, after SMT encoded predicate:\n\t=%s\n"
                            (Term.print_smt_term has_type);
                    let tkey_hash = Term.hash_of_term app_tm in
                    let e_typing = Util.mkAssume(mkForall t0.pos ([pattern], vars, has_type),
                                                Some "Partial app typing",
                                                ("partial_app_typing_" ^
                                                 (BU.digest_of_string (Term.hash_of_term app_tm)))) in
                    app_tm, decls@decls'@decls''@(mk_decls "" tkey_hash [e_typing] (decls@decls'@decls''))
                | None -> failwith "impossible"
            in

            let encode_full_app fv =
                let fname, fuel_args, arity = lookup_free_var_sym env fv in
                let tm = maybe_curry_app t0.pos fname arity (fuel_args@args) in
                tm, decls
            in

            let head = SS.compress head in

            let head_type =
                match head.n with
                | Tm_uinst({n=Tm_name x}, _)
                | Tm_name x -> Some x.sort
                | Tm_uinst({n=Tm_fvar fv}, _)
                | Tm_fvar fv -> Some (Env.lookup_lid env.tcenv fv.fv_name.v |> fst |> snd)
                | Tm_ascribed {asc=(Inl t, _, _)} -> Some t
                | Tm_ascribed {asc=(Inr c, _, _)} -> Some (U.comp_result c)
                | _ -> None
            in

            match head_type with
            | None -> encode_partial_app None
            | Some head_type ->
                let head_type, formals, c =
                  let head_type = U.unrefine <| normalize_refinement [Env.Weak; Env.HNF; Env.EraseUniverses] env.tcenv head_type in
                  let formals, c = curried_arrow_formals_comp head_type in
                  if List.length formals < List.length args
                  then let head_type =
                           U.unrefine
                           <| normalize_refinement
                                    [Env.Weak; Env.HNF; Env.EraseUniverses; Env.UnfoldUntil delta_constant]
                                    env.tcenv
                                    head_type
                       in
                       let formals, c = curried_arrow_formals_comp head_type in
                       head_type, formals, c
                  else head_type, formals, c
                in
                if !dbg_PartialApp
                then Format.print3 "Encoding partial application, head_type = %s, formals = %s, args = %s\n"
                            (show head_type)
                            (show formals)
                            (show args_e);

                begin
                match head.n with
                | Tm_uinst({n=Tm_fvar fv}, _)
                | Tm_fvar fv when (List.length formals = List.length args) -> encode_full_app fv.fv_name
                | _ ->
                    if List.length formals > List.length args
                    then encode_partial_app (Some (head_type, formals, c))
                    else encode_partial_app None
                end

        end

      | Tm_abs {bs; body; rc_opt=lopt} ->
          let bs, body, opening = SS.open_term' bs body in
          let fallback () =
            let arg_sorts, arg_terms =
              (* We need to compute all free variables of this lambda
              expression and parametrize the encoding wrt to them. See
              issue #3028 *)
              let fvs = Free.names t0 |> elems in
              let tms = List.map (lookup_term_var env) fvs in
              (List.map (fun _ -> Term_sort) fvs <: list sort),
              tms
            in
            let f = varops.fresh env.current_module_name "Tm_abs" in
            let decl = Term.DeclFun(f, arg_sorts, Term_sort, Some "Imprecise function encoding") in
            let fv : term = mkFreeV <| mk_fv (f, Term_sort) in
            let fapp = mkApp (f, arg_terms) in
            fapp, [decl] |> mk_decls_trivial
          in

          let is_impure (rc:S.residual_comp) =
            TypeChecker.Util.is_pure_or_ghost_effect env.tcenv rc.residual_effect |> not
          in

//          let reify_comp_and_body env body =
//            let reified_body = TcUtil.reify_body env.tcenv body in
//            let c = match c with
//              | Inl lc ->
//                let typ = reify_comp ({env.tcenv with admit=true}) (lc.comp ()) U_unknown in
//                Inl (U.lcomp_of_comp (S.mk_Total typ))
//
//              (* In this case we don't have enough information to reconstruct the *)
//              (* whole computation type and reify it *)
//              | Inr (eff_name, _) -> c
//            in
//            c, reified_body
//          in

          let codomain_eff rc =
              let res_typ =
                match rc.residual_typ with
                | None ->
                  let t, _, _ =
                      FStarC.TypeChecker.Util.new_implicit_var
                                              "SMTEncoding codomain"
                                              (Env.get_range env.tcenv)
                                              env.tcenv
                                              U.ktype0
                                              false
                                              in
                  t
                | Some t -> t
              in
              if Ident.lid_equals rc.residual_effect Const.effect_Tot_lid
              then Some (S.mk_Total res_typ)
              else if Ident.lid_equals rc.residual_effect Const.effect_GTot_lid
              then Some (S.mk_GTotal res_typ)
              (* TODO (KM) : shouldn't we do something when flags contains TOTAL ? *)
              else None
          in

          begin match lopt with
            | None ->
              let open FStarC.Class.PP in
              let open FStarC.Pprint in
              let open FStarC.Errors.Msg in
              //we don't even know if this is a pure function, so give up
              Errors.log_issue t0 Errors.Warning_FunctionLiteralPrecisionLoss [
                prefix 2 1 (text "Losing precision when encoding a function literal:")
                  (pp t0);
                text "Unannotated abstraction in the compiler?"
              ];
              fallback ()

            | Some rc ->
              if is_impure rc && not (is_smt_reifiable_rc env.tcenv rc)
              then fallback() //we know it's not pure; so don't encode it precisely
              else
                let vars, guards, envbody, decls, _ = encode_binders None bs env in
                let body = if is_smt_reifiable_rc env.tcenv rc
                           then TcUtil.norm_reify env.tcenv []
                                  (U.mk_reify body (Some rc.residual_effect))
                           else body
                in
                let body, decls' = encode_term body envbody in
                let is_pure = U.is_pure_effect rc.residual_effect in
                let arrow_t_opt, decls'' =
                  match codomain_eff rc with
                  | None   -> None, []
                  | Some c ->
                    let tfun = U.arrow bs c in
                    let t, decls = encode_term tfun env in
                    Some t, decls
                in
                let key_body = mkForall t0.pos ([], vars, mkImp(mk_and_l guards, body)) in
                let cvars = Term.free_variables key_body in
                //adding free variables of the return type also to cvars
                let cvars, key_body =
                  match arrow_t_opt with
                  | None   -> cvars, key_body
                  | Some t ->
                    BU.remove_dups fv_eq (Term.free_variables t @ cvars),
                    mkAnd (key_body, t) (* we make the encoding depend on the type of the abstraction, see #1595 *)
                in
                let tkey = mkForall t0.pos ([], cvars, key_body) in
                let tkey_hash = Term.hash_of_term tkey in
                if !dbg_PartialApp
                then Format.print2 "Checking eta expansion of\n\tvars={%s}\n\tbody=%s\n"
                       (List.map fv_name vars |> String.concat ", ")
                       (print_smt_term body);
                let cvar_sorts = List.map fv_sort cvars in
                let fsym = "Tm_abs_" ^ (BU.digest_of_string tkey_hash) in
                let fdecl = Term.DeclFun(fsym, cvar_sorts, Term_sort, None) in
                let f = mkApp(fsym, List.map mkFreeV cvars) in //arity ok, since introduced at cvar_sorts (#1383)
                let app = mk_Apply f vars in
                let typing_f =
                  match arrow_t_opt with
                  | None ->
                    let tot_fun_ax =
                      let ax = (isTotFun_axioms t0.pos f vars (vars |> List.map (fun _ -> mkTrue)) is_pure) in
                      match cvars with
                      | [] -> ax
                      | _ -> mkForall t0.pos ([[f]], cvars, ax)
                    in
                    let a_name = "tot_fun_"^fsym in
                    [Util.mkAssume(tot_fun_ax, Some a_name, a_name)]
                    //no typing axiom for this lambda, because we don't have enough info
                    //but we at least mark its partial applications as total (cf. #1750)
                  | Some t ->
                    let f_has_t = mk_HasTypeWithFuel None f t in
                    let a_name = "typing_"^fsym in
                    [Util.mkAssume(mkForall t0.pos ([[f]], cvars, f_has_t), Some a_name, a_name)]
                in
                let interp_f =
                  let a_name = "interpretation_" ^fsym in
                  Util.mkAssume(mkForall t0.pos ([[app]], vars@cvars, mkEq(app, body)), Some a_name, a_name)
                in
                let f_decls = (fdecl::typing_f)@[interp_f] in
                f, decls@decls'@decls''@(mk_decls fsym tkey_hash f_decls (decls@decls'@decls''))
          end

      | Tm_let {lbs=(_, {lbname=Inr _}::_)} ->
        failwith "Impossible: already handled by encoding of Sig_let"

      | Tm_let {lbs=(false, [{lbname=Inl x; lbtyp=t1; lbdef=e1}]); body=e2} ->
        encode_let x t1 e1 e2 env encode_term

      | Tm_let {lbs=(false, _::_)} ->
        failwith "Impossible: non-recursive let with multiple bindings"

      | Tm_let {lbs=(_, lbs)} ->
        let names = lbs |> List.map (fun lb ->
                                        let {lbname = lbname} = lb in
                                        let x = Inl?.v lbname in (* has to be Inl *)
                                        (Ident.string_of_id x.ppname, S.range_of_bv x)) in
        raise (Inner_let_rec names)

      | Tm_match {scrutinee=e; brs=pats} ->
        encode_match e pats mk_Term_unit env encode_term

and encode_let
    : bv -> typ -> S.term -> S.term -> env_t -> (S.term -> env_t -> term & decls_t)
    -> term & decls_t
    =
    fun x t1 e1 e2 env encode_body ->
        //setting the use_eq ascription flag to false,
        //  doesn't matter since the flag is irrelevant outside the typechecker
        let ee1, decls1 = encode_term (U.ascribe e1 (Inl t1, None, false)) env in
        let xs, e2 = SS.open_term [S.mk_binder x] e2 in
        let x = (List.hd xs).binder_bv in
        let env' = push_term_var env x ee1 in
        let ee2, decls2 = encode_body e2 env' in
        ee2, decls1@decls2

and encode_match (e:S.term) (pats:list S.branch) (default_case:term) (env:env_t)
                 (encode_br:S.term -> env_t -> (term & decls_t)) : term & decls_t =
    let scrsym, scr', env = gen_term_var env (S.null_bv (S.mk S.Tm_unknown Range.dummyRange)) in
    let scr, decls = encode_term e env in
    let match_tm, decls =
      let encode_branch b (else_case, decls) =
        let p, w, br = SS.open_branch b in
        let env0, pattern = encode_pat env p in
        let guard = pattern.guard scr' in
        let projections = pattern.projections scr' in
        let env = projections |> List.fold_left (fun env (x, t) -> push_term_var env x t) env in
        let guard, decls2 =
            match w with
            | None -> guard, []
            | Some w ->
              let w, decls2 = encode_term w env in
              mkAnd(guard, mkEq(w, Term.boxBool mkTrue)), decls2
       in
       let br, decls3 = encode_br br env in
       mkITE(guard, br, else_case), decls@decls2@decls3
      in
      List.fold_right encode_branch pats (default_case (* default; should be unreachable *), decls)
    in
    mkLet' ([mk_fv (scrsym,Term_sort), scr], match_tm) Range.dummyRange, decls

and encode_pat (env:env_t) (pat:S.pat) : (env_t & pattern) =
    if Debug.medium () then Format.print1 "Encoding pattern %s\n" (show pat);
    let vars, pat_term = FStarC.TypeChecker.Util.decorated_pattern_as_term pat in

    let env, vars = vars |> List.fold_left (fun (env, vars) v ->
            let xx, _, env = gen_term_var env v in
            env, (v, mk_fv (xx, Term_sort))::vars) (env, []) in

    let rec mk_guard pat (scrutinee:term) : term =
        match pat.v with
        | Pat_var _
        | Pat_dot_term _ -> mkTrue
        | Pat_constant c ->
            let tm, decls = encode_const c env in
            let _ = match decls with _::_ -> failwith "Unexpected encoding of constant pattern" | _ -> () in
            mkEq(scrutinee, tm)
        | Pat_cons(f, _, args) ->
            let is_f =
                let tc_name = Env.typ_of_datacon env.tcenv f.fv_name.v in
                match Env.datacons_of_typ env.tcenv tc_name with
                | _, [_] -> mkTrue //single constructor type; no need for a test
                | _ -> mk_data_tester env f.fv_name.v scrutinee
            in
            let sub_term_guards = args |> List.mapi (fun i (arg, _) ->
                let proj = primitive_projector_by_pos env.tcenv f.fv_name.v i in
                mk_guard arg (mkApp(proj, [scrutinee]))) in //arity ok, primitive projector (#1383)
            mk_and_l (is_f::sub_term_guards)
    in

    let rec mk_projections pat (scrutinee:term) =
        match pat.v with
        | Pat_dot_term _ -> []
        | Pat_var x -> [x, scrutinee]

        | Pat_constant _ -> []

        | Pat_cons(f, _, args) ->
            args
            |> List.mapi (fun i (arg, _) ->
                let proj = primitive_projector_by_pos env.tcenv f.fv_name.v i in
                mk_projections arg (mkApp(proj, [scrutinee]))) //arity ok, primitive projector (#1383)
            |> List.flatten
    in

    let pat_term () = encode_term pat_term env in

    let pattern = {
            pat_vars=vars;
            pat_term=pat_term;
            guard=mk_guard pat;
            projections=mk_projections pat;
        }  in

    env, pattern

and encode_args (l:args) (env:env_t) : (list term & decls_t)  =
    let l, decls = l |> List.fold_left
        (fun (tms, decls) (t, _) -> let t, decls' = encode_term t env in t::tms, decls@decls')
        ([], []) in
    List.rev l, decls

and encode_smt_patterns (pats_l:list (list S.arg)) env : list (list term) & decls_t =
    let env = {env with use_zfuel_name=true} in
    let encode_smt_pattern t =
        let head, args = U.head_and_args t in
        let head = U.un_uinst head in
        match head.n, args with
        | Tm_fvar fv, [_; (x, _); (t, _)]
            when S.fv_eq_lid fv Const.has_type_lid -> //interpret Prims.has_type as HasType
          let x, decls = encode_term x env in
          let t, decls' = encode_term t env in
          mk_HasType x t, decls@decls'

        | _ ->
          encode_term t env
    in
    List.fold_right (fun pats (pats_l, decls) ->
        let pats, decls =
            List.fold_right
                (fun (p, _) (pats, decls) ->
                    let t, d = encode_smt_pattern p in
                    match check_pattern_ok t with
                    | None ->
                      t::pats, d@decls
                    | Some illegal_subterm ->
                      Errors.log_issue p Errors.Warning_SMTPatternIllFormed
                        (Format.fmt2 "Pattern %s contains illegal sub-term (%s); dropping it"
                                        (show p)
                                        (show illegal_subterm));
                         pats, d@decls)
                pats ([], decls)
        in
        pats::pats_l, decls)
    pats_l ([], [])

and encode_formula (phi:typ) (env:env_t) : (term & decls_t)  = (* expects phi to be normalized; the existential variables are all labels *)
    let debug phi =
       if !dbg_SMTEncoding
       then Format.print2 "Formula (%s)  %s\n"
                     (tag_of phi)
                     (show phi) in
    let enc (f:list term -> term) : Range.t -> args -> (term & decls_t) = fun r l ->
        let decls, args = BU.fold_map (fun decls x -> let t, decls' = encode_term (fst x) env in decls@decls', t) [] l in
        ({f args with rng=r}, decls) in

    let const_op f r _ = (f r, []) in
    let un_op f l = f <| List.hd l in
    let bin_op : ((term & term) -> term) -> list term -> term = fun f -> function
        | [t1;t2] -> f(t1,t2)
        | _ -> failwith "Impossible" in

    let enc_prop_c f : Range.t -> args -> (term & decls_t) = fun r l ->
        let decls, phis =
            BU.fold_map (fun decls (t, _) ->
                let phi, decls' = encode_formula t env in
                decls@decls', phi)
            [] l in
        ({f phis with rng=r}, decls) in

    // This gets called for
    // eq2 : #a:Type -> a -> a -> Type
    // equals: #a:Type -> a -> a -> Type
    let eq_op r args : (term & decls_t) =
        let rf = List.filter (fun (a,q) -> match q with | Some ({ aqual_implicit = true }) -> false | _ -> true) args in
        if List.length rf <> 2
        then failwith (Format.fmt1 "eq_op: got %s non-implicit arguments instead of 2?" (show (List.length rf)))
        else enc (bin_op mkEq) r rf
    in

    let mk_imp r : Tot (args -> (term & decls_t)) = function
        | [(lhs, _); (rhs, _)] ->
          let l1, decls1 = encode_formula rhs env in
          begin match l1.tm with
            | App(TrueOp, _) -> (l1, decls1) (* Optimization: don't bother encoding the LHS of a trivial implication *)
            | _ ->
             let l2, decls2 = encode_formula lhs env in
             (Term.mkImp(l2, l1) r, decls1@decls2)
          end
         | _ -> failwith "impossible" in

    let mk_ite r: Tot (args -> (term & decls_t)) = function
        | [(guard, _); (_then, _); (_else, _)] ->
          let (g, decls1) = encode_formula guard env in
          let (t, decls2) = encode_formula _then env in
          let (e, decls3) = encode_formula _else env in

          let res = Term.mkITE(g, t, e) r in
          res, decls1@decls2@decls3
        | _ -> failwith "impossible" in


    let unboxInt_l : (list term -> term) -> list term -> term = fun f l -> f (List.map Term.unboxInt l) in
    let connectives = [
        (Const.and_lid,   enc_prop_c (bin_op mkAnd));
        (Const.or_lid,    enc_prop_c (bin_op mkOr));
        (Const.imp_lid,   mk_imp);
        (Const.iff_lid,   enc_prop_c (bin_op mkIff));
        (Const.ite_lid,   mk_ite);
        (Const.not_lid,   enc_prop_c (un_op mkNot));
        (Const.eq2_lid,   eq_op);
        (Const.c_eq2_lid, eq_op);
        (Const.true_lid,  const_op Term.mkTrue);
        (Const.false_lid, const_op Term.mkFalse);
    ] in

    let rec fallback phi =  match phi.n with
        | Tm_meta {tm=phi'; meta=Meta_labeled(msg, r, b)} ->
          let phi, decls = encode_formula phi' env in
          mk (Term.Labeled(phi, msg, r)) r, decls

        | Tm_meta _ ->
          encode_formula (U.unmeta phi) env

        | Tm_match {scrutinee=e;brs=pats} ->
           let t, decls = encode_match e pats mkUnreachable env encode_formula in
           t, decls

        | Tm_let {lbs=(false, [{lbname=Inl x; lbtyp=t1; lbdef=e1}]); body=e2} ->
           let t, decls = encode_let x t1 e1 e2 env encode_formula in
           t, decls

        | Tm_app {hd=head; args} ->
          let head = U.un_uinst head in
          begin match head.n, args with
            | Tm_fvar fv, [_; (x, _); (t, _)] when S.fv_eq_lid fv Const.has_type_lid -> //interpret Prims.has_type as HasType
              let x, decls = encode_term x env in
              let t, decls' = encode_term t env in
              mk_HasType x t, decls@decls'

            | Tm_fvar fv, [_; (phi, _)]
            | Tm_uinst ({n=Tm_fvar fv}, _), [_; (phi, _)]
              when S.fv_eq_lid fv Const.by_tactic_lid ->
              encode_formula phi env

            | Tm_fvar fv, [_; _; (phi, _)]
            | Tm_uinst ({n=Tm_fvar fv}, _), [_; _; (phi, _)]
              when S.fv_eq_lid fv Const.rewrite_by_tactic_lid ->
              encode_formula phi env

            | Tm_fvar fv, [(r, _); (msg, _); (phi, _)] when S.fv_eq_lid fv Const.labeled_lid -> //interpret (labeled r msg t) as Tm_meta(t, Meta_labeled(msg, r, false)
              (* NB: below we use Errors.mkmsg since FStar.Range.labeled takes a string, but
                 the Meta_labeled node needs a list of docs (Errors.error_message). *)
              begin match SE.try_unembed r SE.id_norm_cb,
                          SE.try_unembed msg SE.id_norm_cb with
              | Some r, Some s ->
                let phi = S.mk (Tm_meta {tm=phi; meta=Meta_labeled(Errors.mkmsg s, r, false)}) r in
                fallback phi

              (* If we could not unembed the position, still use the string *)
              | None, Some s ->
                let phi = S.mk (Tm_meta {tm=phi; meta=Meta_labeled(Errors.mkmsg s, phi.pos, false)}) phi.pos in
                fallback phi

              | _ ->
                fallback phi
              end

            | Tm_fvar fv, [(t, _)]
              when S.fv_eq_lid fv Const.squash_lid
                 || S.fv_eq_lid fv Const.auto_squash_lid ->
              encode_formula t env

            | _ ->
              let encode_valid () =
                let tt, decls = encode_term phi env in
                let tt =
                    if Range.rng_included (Range.use_range tt.rng) (Range.use_range phi.pos)
                    then tt
                    else {tt with rng=phi.pos} in
                mk_Valid tt, decls
              in
              if head_redex env head
              then match maybe_whnf env head with
                   | None -> encode_valid()
                   | Some phi -> encode_formula phi env
              else encode_valid()
          end

        | _ ->
            let tt, decls = encode_term phi env in
            let tt =
                  if Range.rng_included (Range.use_range tt.rng) (Range.use_range phi.pos)
                  then tt
                  else {tt with rng=phi.pos} in
            mk_Valid tt, decls in

    let encode_q_body env (bs:Syntax.binders) (ps:list args) body =
        let vars, guards, env, decls, _ = encode_binders None bs env in
        let pats, decls' = encode_smt_patterns ps env in
        let body, decls'' = encode_formula body env in
        let guards = match pats with
          | [[{tm=App(Var gf, [p])}]] when Ident.string_of_lid Const.guard_free = gf -> []
          | _ -> guards in
        vars, pats, mk_and_l guards, body, decls@decls'@decls'' in

    debug phi;

    let phi = U.unascribe phi in
    let open FStarC.Syntax.Formula in
    match destruct_typ_as_formula phi with
        | None -> fallback phi

        | Some (BaseConn(op, arms)) ->
          (match connectives |> List.tryFind (fun (l, _) -> lid_equals op l) with
             | None -> fallback phi
             | Some (_, f) -> f phi.pos arms)

        | Some (QAll(vars, pats, body)) ->
          pats |> List.iter (check_pattern_vars env vars);
          let vars, pats, guard, body, decls = encode_q_body env vars pats body in
          let tm = mkForall phi.pos (pats, vars, mkImp(guard, body)) in
          tm, decls

        | Some (QEx(vars, pats, body)) ->
          pats |> List.iter (check_pattern_vars env vars);
          let vars, pats, guard, body, decls = encode_q_body env vars pats body in
          mkExists phi.pos (pats, vars, mkAnd(guard, body)), decls

(* this assumes t is a Lemma *)
let encode_function_type_as_formula (t:typ) (env:env_t) : term & decls_t =
    let universe_of_binders binders = List.map (fun _ -> U_zero) binders in
    let quant = U.smt_lemma_as_forall t universe_of_binders in
    let env = {env with use_zfuel_name=true} in //see #1028; SMT lemmas should not violate the fuel instrumentation
    encode_formula quant env

(***************************************************************************************************)
(* end main encoding of kinds/types/exps/formulae *)
(***************************************************************************************************)
