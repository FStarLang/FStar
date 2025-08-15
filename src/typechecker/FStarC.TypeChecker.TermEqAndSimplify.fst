module FStarC.TypeChecker.TermEqAndSimplify

open FStarC
open FStarC.Effect
open FStarC.Syntax
open FStarC.Const
open FStarC.Ident
open FStarC.TypeChecker.Env
open FStarC.Syntax.Syntax
open FStarC.Syntax.Util
open FStarC.Syntax.Print {}

module SS = FStarC.Syntax.Subst
module U = FStarC.Syntax.Util
module PC = FStarC.Parser.Const
module S = FStarC.Syntax.Syntax

open FStarC.Class.Tagged
open FStarC.Class.Show

// Functions that we specially treat as injective, to make normalization
// (particularly of decidable equality) better. We should make sure they
// are actually proved to be injective.
let injectives =
    ["FStar.Int8.int_to_t";
     "FStar.Int16.int_to_t";
     "FStar.Int32.int_to_t";
     "FStar.Int64.int_to_t";
     "FStar.Int128.int_to_t";
     "FStar.UInt8.uint_to_t";
     "FStar.UInt16.uint_to_t";
     "FStar.UInt32.uint_to_t";
     "FStar.UInt64.uint_to_t";
     "FStar.UInt128.uint_to_t";
     "FStar.SizeT.uint_to_t";
     "FStar.Int8.__int_to_t";
     "FStar.Int16.__int_to_t";
     "FStar.Int32.__int_to_t";
     "FStar.Int64.__int_to_t";
     "FStar.Int128.__int_to_t";
     "FStar.UInt8.__uint_to_t";
     "FStar.UInt16.__uint_to_t";
     "FStar.UInt32.__uint_to_t";
     "FStar.UInt64.__uint_to_t";
     "FStar.UInt128.__uint_to_t";
     "FStar.SizeT.__uint_to_t";
     ]

// Compose two eq_result injectively, as in a pair
let eq_inj r s =
     match r, s with
     | Equal, Equal -> Equal
     | NotEqual, _
     | _, NotEqual -> NotEqual
     | _, _ -> Unknown

// Promote a bool to eq_result, conservatively.
let equal_if = function
    | true -> Equal
    | _ -> Unknown

// Promote a bool to an eq_result, taking a false to bet NotEqual.
// This is only useful for fully decidable equalities.
// Use with care, see note about Const_real below and #2806.
let equal_iff = function
    | true -> Equal
    | _ -> NotEqual

// Compose two equality results, NOT assuming a NotEqual implies anything.
// This is useful, e.g., for checking the equality of applications. Consider
//  f x ~ g y
// if f=g and x=y then we know these two expressions are equal, but cannot say
// anything when either result is NotEqual or Unknown, hence this returns Unknown
// in most cases.
// The second comparison is thunked for efficiency.
let eq_and r s =
    if r = Equal && s () = Equal
    then Equal
    else Unknown

(* Precondition: terms are well-typed in a common environment, or this can return false positives *)
let rec eq_tm (env:env_t) (t1:term) (t2:term) : eq_result =
    let t1 = canon_app t1 in
    let t2 = canon_app t2 in
    let equal_data (f1:S.fv) (args1:Syntax.args) (f2:fv) (args2:Syntax.args) (n_parms:int) =
        // we got constructors! we know they are injective and disjoint, so we can do some
        // good analysis on them
        if fv_eq f1 f2
        then (
          let n1 = List.length args1 in
          let n2 = List.length args2 in
          if n1 = n2 && n_parms <= n1
          then (
            let parms1, args1 = List.splitAt n_parms args1 in
            let parms2, args2 = List.splitAt n_parms args2 in
            let eq_arg_list as1 as2 =
                List.fold_left2
                  (fun acc (a1, q1) (a2, q2) ->
                        //if q1 <> q2
                        //then failwith (Format.fmt1 "Arguments of %s mismatch on implicit qualifier\n"
                        //                (Ident.string_of_lid f1.fv_name));
                        //NS: 05/06/2018 ...this does not always hold
                        //    it's been succeeding because the assert is disabled in the non-debug builds
                        //assert (q1 = q2);
                        eq_inj acc (eq_tm env a1 a2))
                    Equal
                    as1
                    as2
            in
            eq_arg_list args1 args2
          )
          else Unknown
        )
        else NotEqual
    in
    let qual_is_inj = function
      | Some Data_ctor
      | Some (Record_ctor _) -> true
      | _ -> false
    in
    let heads_and_args_in_case_both_data : option (S.fv & args & S.fv & args & int) =
      let head1, args1 = t1 |> unmeta |> head_and_args in
      let head2, args2 = t2 |> unmeta |> head_and_args in
      match (un_uinst head1).n, (un_uinst head2).n with
      | Tm_fvar f, Tm_fvar g 
        when qual_is_inj f.fv_qual &&
             qual_is_inj g.fv_qual -> (
        match Env.num_datacon_non_injective_ty_params env (lid_of_fv f) with
        | Some n -> Some (f, args1, g, args2, n)
        | _ -> None
      )
      | _ -> None
    in
    let t1 = unmeta t1 in
    let t2 = unmeta t2 in
    match t1.n, t2.n with
    // We sometimes compare open terms, as we get alpha-equivalence
    // for free.
    | Tm_bvar bv1, Tm_bvar bv2 ->
      equal_if (bv1.index = bv2.index)

    | Tm_lazy _, _ -> eq_tm env (unlazy t1) t2
    | _, Tm_lazy _ -> eq_tm env t1 (unlazy t2)

    | Tm_name a, Tm_name b ->
      equal_if (bv_eq a b)

    | _ when heads_and_args_in_case_both_data |> Some? ->  //matches only when both are data constructors
      heads_and_args_in_case_both_data |> Option.must |> (fun (f, args1, g, args2, n) ->
        equal_data f args1 g args2 n
      )

    | Tm_fvar f, Tm_fvar g -> equal_if (fv_eq f g)

    | Tm_uinst(f, us), Tm_uinst(g, vs) ->
      // If the fvars and universe instantiations match, then Equal,
      // otherwise Unknown.
      eq_and (eq_tm env f g) (fun () -> equal_if (eq_univs_list us vs))

    | Tm_constant (Const_range _), Tm_constant (Const_range _) ->
      // Ranges should be opaque, even to the normalizer. c.f. #1312
      Unknown

    | Tm_constant (Const_real r1), Tm_constant (Const_real r2) ->
      // We cannot simply compare strings (they are not canonicalized, e.g.
      // "01.R" and "1.0R"). Call the proper comparison in FStarC.Real, which
      // returns None for unknown.
      begin match Real.cmp (Real.Real r1) (Real.Real r2) with
        | Some Order.Eq -> Equal
        | Some Order.Lt
        | Some Order.Gt -> NotEqual
        | None ->
          // We don't know.
          Unknown
      end

    | Tm_constant c, Tm_constant d ->
      // NOTE: this relies on the fact that eq_const *correctly decides*
      // semantic equality of constants. This needs some care. For instance,
      // since integers are represented by a string, eq_const needs to take care
      // of ignoring leading zeroes, and match 0 with -0. An exception to this
      // are real number literals (handled above). See #2806.
      //
      // Currently (24/Jan/23) this seems to be correctly implemented, but
      // updates should be done with care.
      equal_iff (eq_const c d)

    | Tm_uvar (u1, ([], _)), Tm_uvar (u2, ([], _)) ->
      equal_if (Unionfind.equiv u1.ctx_uvar_head u2.ctx_uvar_head)

    | Tm_app {hd=h1; args=args1}, Tm_app {hd=h2; args=args2} ->
      begin match (un_uinst h1).n, (un_uinst h2).n with
      | Tm_fvar f1, Tm_fvar f2 when fv_eq f1 f2 && List.mem (string_of_lid (lid_of_fv f1)) injectives ->
        equal_data f1 args1 f2 args2 0

      | _ -> // can only assert they're equal if they syntactically match, nothing else
        eq_and (eq_tm env h1 h2) (fun () -> eq_args env args1 args2)
      end

    | Tm_match {scrutinee=t1; brs=bs1}, Tm_match {scrutinee=t2; brs=bs2} ->  //AR: note: no return annotations
        if List.length bs1 = List.length bs2
        then List.fold_right (fun (b1, b2) a -> eq_and a (fun () -> branch_matches env b1 b2))
                             (List.zip bs1 bs2)
                             (eq_tm env t1 t2)
        else Unknown

    | Tm_type u, Tm_type v ->
      equal_if (eq_univs u v)

    | Tm_quoted (t1, q1), Tm_quoted (t2, q2) ->
      // NOTE: we do NOT ever provide a meaningful result for quoted terms. Even
      // if term_eq (the syntactic equality) returns true, that does not mean we
      // can present the equality to userspace since term_eq ignores the names
      // of binders, but the view exposes them. Hence, we simply always return
      // Unknown. We do not seem to rely anywhere on simplifying equalities of
      // quoted literals. See also #2806.
      Unknown

    | Tm_refine {b=t1; phi=phi1}, Tm_refine {b=t2; phi=phi2} ->
      eq_and (eq_tm env t1.sort t2.sort) (fun () -> eq_tm env phi1 phi2)

      (*
       * AR: ignoring residual comp here, that's an ascription added by the typechecker
       *     do we care if that's different?
       *)
    | Tm_abs {bs=bs1; body=body1}, Tm_abs {bs=bs2; body=body2}
      when List.length bs1 = List.length bs2 ->

      eq_and (List.fold_left2 (fun r b1 b2 -> eq_and r (fun () -> eq_tm env b1.binder_bv.sort b2.binder_bv.sort))
                Equal bs1 bs2)
             (fun () -> eq_tm env body1 body2)

    | Tm_arrow {bs=bs1; comp=c1}, Tm_arrow {bs=bs2; comp=c2}
          when List.length bs1 = List.length bs2 ->
      eq_and (List.fold_left2 (fun r b1 b2 -> eq_and r (fun () -> eq_tm env b1.binder_bv.sort b2.binder_bv.sort))
                Equal bs1 bs2)
             (fun () -> eq_comp env c1 c2)

    | _ -> Unknown

and eq_antiquotations (env:env_t) a1 a2 =
  // Basically this;
  //  List.fold_left2 (fun acc t1 t2 -> eq_inj acc (eq_tm t1 t2)) Equal a1 a2
  // but lazy and handling lists of different size
  match a1, a2 with
  | [], [] -> Equal
  | [], _
  | _, [] -> NotEqual
  | t1::a1, t2::a2 ->
    match eq_tm env t1 t2 with
    | NotEqual -> NotEqual
    | Unknown ->
      (match eq_antiquotations env a1 a2 with
       | NotEqual -> NotEqual
       | _ -> Unknown)
    | Equal -> eq_antiquotations env a1 a2

and branch_matches env b1 b2 =
    let related_by f o1 o2 =
        match o1, o2 with
        | None, None -> true
        | Some x, Some y -> f x y
        | _, _ -> false
    in
    let (p1, w1, t1) = b1 in
    let (p2, w2, t2) = b2 in
    if eq_pat p1 p2
    then begin
         // We check the `when` branches too, even if unsupported for now
         if eq_tm env t1 t2 = Equal && related_by (fun t1 t2 -> eq_tm env t1 t2 = Equal) w1 w2
         then Equal
         else Unknown
         end
    else Unknown

and eq_args env (a1:args) (a2:args) : eq_result =
    match a1, a2 with
    | [], [] -> Equal
    | (a, _)::a1, (b, _)::b1 ->
      (match eq_tm env a b with
       | Equal -> eq_args env a1 b1
       | _ -> Unknown)
    | _ -> Unknown

and eq_comp env (c1 c2:comp) : eq_result =
  match c1.n, c2.n with
  | Total t1, Total t2
  | GTotal t1, GTotal t2 ->
    eq_tm env t1 t2
  | Comp ct1, Comp ct2 ->
    eq_and (equal_if (eq_univs_list ct1.comp_univs ct2.comp_univs))
           (fun _ ->
             eq_and (equal_if (Ident.lid_equals ct1.effect_name ct2.effect_name))
                    (fun _ ->
                      eq_and (eq_tm env ct1.result_typ ct2.result_typ)
                             (fun _ -> eq_args env ct1.effect_args ct2.effect_args)))
                             //ignoring cflags
  | _ -> NotEqual

let eq_tm_bool e t1 t2 = eq_tm e t1 t2 = Equal

let simplify (debug:bool) (env:env_t) (tm:term) : term =
    let w t = {t with pos=tm.pos} in
    let simp_t t =
        // catch annotated subformulae too
        match (U.unmeta t).n with
        | Tm_fvar fv when S.fv_eq_lid fv PC.true_lid ->  Some true
        | Tm_fvar fv when S.fv_eq_lid fv PC.false_lid -> Some false
        | _ -> None
    in
    let rec args_are_binders args bs =
        match args, bs with
        | (t, _)::args, b::bs ->
            begin match (SS.compress t).n with
            | Tm_name bv' -> S.bv_eq b.binder_bv bv' && args_are_binders args bs
            | _ -> false
            end
        | [], [] -> true
        | _, _ -> false
    in
    let is_applied (bs:binders) (t : term) : option bv =
        if debug then
            Format.print2 "WPE> is_applied %s -- %s\n"  (show t) (tag_of t);
        let hd, args = U.head_and_args_full t in
        match (SS.compress hd).n with
        | Tm_name bv when args_are_binders args bs ->
            if debug then
                Format.print3 "WPE> got it\n>>>>top = %s\n>>>>b = %s\n>>>>hd = %s\n"
                            (show t)
                            (show bv)
                            (show hd);
            Some bv
        | _ -> None
    in
    let is_applied_maybe_squashed (bs : binders) (t : term) : option bv =
        if debug then
            Format.print2 "WPE> is_applied_maybe_squashed %s -- %s\n"  (show t) (tag_of t);
        match is_squash t with

        | Some (_, t') -> is_applied bs t'
        | _ -> begin match is_auto_squash t with
               | Some (_, t') -> is_applied bs t'
               | _ -> is_applied bs t
               end
    in
    let is_const_match (phi : term) : option bool =
        match (SS.compress phi).n with
        (* Trying to be efficient, but just checking if they all agree *)
        (* Note, if we wanted to do this for any term instead of just True/False
         * we need to open the terms *)
        | Tm_match {brs=br::brs} ->
            let (_, _, e) = br in
            let r = begin match simp_t e with
            | None -> None
            | Some b -> if List.for_all (fun (_, _, e') -> simp_t e' = Some b) brs
                        then Some b
                        else None
            end
            in
            r
        | _ -> None
    in
    let maybe_auto_squash t =
        if U.is_sub_singleton t
        then t
        else U.mk_auto_squash U_zero t
    in
    let squashed_head_un_auto_squash_args t =
        //The head of t is already a squashed operator, e.g. /\ etc.
        //no point also squashing its arguments if they're already in U_zero
        let maybe_un_auto_squash_arg (t,q) =
            match U.is_auto_squash t with
            | Some (U_zero, t) ->
             //if we're squashing from U_zero to U_zero
             // then just remove it
              t, q
            | _ ->
              t,q
        in
        let head, args = U.head_and_args t in
        let args = List.map maybe_un_auto_squash_arg args in
        S.mk_Tm_app head args t.pos
    in
    let rec clearly_inhabited (ty : typ) : bool =
        match (U.unmeta ty).n with
        | Tm_uinst (t, _) -> clearly_inhabited t
        | Tm_arrow {comp=c} -> clearly_inhabited (U.comp_result c)
        | Tm_fvar fv ->
            let l = S.lid_of_fv fv in
               (Ident.lid_equals l PC.int_lid)
            || (Ident.lid_equals l PC.bool_lid)
            || (Ident.lid_equals l PC.string_lid)
            || (Ident.lid_equals l PC.exn_lid)
        | _ -> false
    in
    let simplify arg = (simp_t (fst arg), arg) in
    match (SS.compress tm).n with
    | Tm_app {hd={n=Tm_uinst({n=Tm_fvar fv}, _)}; args}
    | Tm_app {hd={n=Tm_fvar fv}; args} ->
      if S.fv_eq_lid fv PC.squash_lid
      then squashed_head_un_auto_squash_args tm
      else if S.fv_eq_lid fv PC.and_lid
      then match args |> List.map simplify with
           | [(Some true, _); (_, (arg, _))]
           | [(_, (arg, _)); (Some true, _)] -> maybe_auto_squash arg
           | [(Some false, _); _]
           | [_; (Some false, _)] -> w U.t_false
           | _ -> squashed_head_un_auto_squash_args tm
      else if S.fv_eq_lid fv PC.or_lid
      then match args |> List.map simplify with
           | [(Some true, _); _]
           | [_; (Some true, _)] -> w U.t_true
           | [(Some false, _); (_, (arg, _))]
           | [(_, (arg, _)); (Some false, _)] -> maybe_auto_squash arg
           | _ -> squashed_head_un_auto_squash_args tm
      else if S.fv_eq_lid fv PC.imp_lid
      then match args |> List.map simplify with
           | [_; (Some true, _)]
           | [(Some false, _); _] -> w U.t_true
           | [(Some true, _); (_, (arg, _))] -> maybe_auto_squash arg
           | [(_, (p, _)); (_, (q, _))] ->
             if U.term_eq p q
             then w U.t_true
             else squashed_head_un_auto_squash_args tm
           | _ -> squashed_head_un_auto_squash_args tm
      else if S.fv_eq_lid fv PC.iff_lid
      then match args |> List.map simplify with
           | [(Some true, _)  ; (Some true, _)]
           | [(Some false, _) ; (Some false, _)] -> w U.t_true
           | [(Some true, _)  ; (Some false, _)]
           | [(Some false, _) ; (Some true, _)]  -> w U.t_false
           | [(_, (arg, _))   ; (Some true, _)]
           | [(Some true, _)  ; (_, (arg, _))]   -> maybe_auto_squash arg
           | [(_, (arg, _))   ; (Some false, _)]
           | [(Some false, _) ; (_, (arg, _))]   -> maybe_auto_squash (U.mk_neg arg)
           | [(_, (p, _)); (_, (q, _))] ->
             if U.term_eq p q
             then w U.t_true
             else squashed_head_un_auto_squash_args tm
           | _ -> squashed_head_un_auto_squash_args tm
      else if S.fv_eq_lid fv PC.not_lid
      then match args |> List.map simplify with
           | [(Some true, _)] ->  w U.t_false
           | [(Some false, _)] -> w U.t_true
           | _ -> squashed_head_un_auto_squash_args tm
      else if S.fv_eq_lid fv PC.forall_lid
      then match args with
           (* Simplify ∀x. True to True *)
           | [(t, _)] ->
             begin match (SS.compress t).n with
                   | Tm_abs {bs=[_]; body} ->
                     (match simp_t body with
                     | Some true -> w U.t_true
                     | _ -> tm)
                   | _ -> tm
             end
           (* Simplify ∀x. True to True, and ∀x. False to False, if the domain is not empty *)
           | [(ty, Some ({ aqual_implicit = true })); (t, _)] ->
             begin match (SS.compress t).n with
                   | Tm_abs {bs=[_]; body} ->
                     (match simp_t body with
                     | Some true -> w U.t_true
                     | Some false when clearly_inhabited ty -> w U.t_false
                     | _ -> tm)
                   | _ -> tm
             end
           | _ -> tm
      else if S.fv_eq_lid fv PC.exists_lid
      then match args with
           (* Simplify ∃x. False to False *)
           | [(t, _)] ->
             begin match (SS.compress t).n with
                   | Tm_abs {bs=[_]; body} ->
                     (match simp_t body with
                     | Some false -> w U.t_false
                     | _ -> tm)
                   | _ -> tm
             end
           (* Simplify ∃x. False to False and ∃x. True to True, if the domain is not empty *)
           | [(ty, Some ({ aqual_implicit = true })); (t, _)] ->
             begin match (SS.compress t).n with
                   | Tm_abs {bs=[_]; body} ->
                     (match simp_t body with
                     | Some false -> w U.t_false
                     | Some true when clearly_inhabited ty -> w U.t_true
                     | _ -> tm)
                   | _ -> tm
             end
           | _ -> tm
      else if S.fv_eq_lid fv PC.b2t_lid
      then match args with
           | [{n=Tm_constant (Const_bool true)}, _] -> w U.t_true
           | [{n=Tm_constant (Const_bool false)}, _] -> w U.t_false
           | _ -> tm //its arg is a bool, can't unsquash
      else if S.fv_eq_lid fv PC.haseq_lid
      then begin
        (*
         * AR: We try to mimic the hasEq related axioms in Prims
         *       and the axiom related to refinements
         *     For other types, such as lists, whose hasEq is derived by the typechecker,
         *       we leave them as is
         *)
        let t_has_eq_for_sure (t:S.term) :bool =
          //Axioms from prims
          let haseq_lids = [PC.int_lid; PC.bool_lid; PC.unit_lid; PC.string_lid] in
          match (SS.compress t).n with
          | Tm_fvar fv when haseq_lids |> List.existsb (fun l -> S.fv_eq_lid fv l) -> true
          | _ -> false
        in
        if List.length args = 1 then
          let t = args |> List.hd |> fst in
          if t |> t_has_eq_for_sure then w U.t_true
          else
            match (SS.compress t).n with
            | Tm_refine _ ->
              let t = U.unrefine t in
              if t |> t_has_eq_for_sure then w U.t_true
              else
                //get the hasEq term itself
                let haseq_tm =
                  match (SS.compress tm).n with
                  | Tm_app {hd} -> hd
                  | _ -> failwith "Impossible! We have already checked that this is a Tm_app"
                in
                //and apply it to the unrefined type
                mk_app (haseq_tm) [t |> as_arg]
            | _ -> tm
        else tm
      end
      else if S.fv_eq_lid fv PC.eq2_lid
      then match args with
           | [(_typ, _); (a1, _); (a2, _)]  ->         //eq2
             (match eq_tm env a1 a2 with
              | Equal -> w U.t_true
              | NotEqual -> w U.t_false
              | _ -> tm)
           | _ -> tm
      else
      begin
        match U.is_auto_squash tm with
        | Some (U_zero, t)
             when U.is_sub_singleton t ->
             //remove redundant auto_squashes
             t
        | _ ->
             tm
      end
    | Tm_refine {b=bv; phi=t} ->
        begin match simp_t t with
        | Some true -> bv.sort
        | Some false -> tm
        | None -> tm
        end
    | Tm_match _ ->
        begin match is_const_match tm with
        | Some true -> w U.t_true
        | Some false -> w U.t_false
        | None -> tm
        end
    | _ -> tm
