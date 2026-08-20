open Prims
type base_typ =
  | Base_rigid of FStarC_Syntax_Syntax.fv 
  | Base_type 
  | Base_unknown 
let uu___is_Base_rigid (projectee : base_typ) : Prims.bool=
  match projectee with | Base_rigid _0 -> true | uu___ -> false
let __proj__Base_rigid__item___0 (projectee : base_typ) :
  FStarC_Syntax_Syntax.fv= match projectee with | Base_rigid _0 -> _0
let uu___is_Base_type (projectee : base_typ) : Prims.bool=
  match projectee with | Base_type -> true | uu___ -> false
let uu___is_Base_unknown (projectee : base_typ) : Prims.bool=
  match projectee with | Base_unknown -> true | uu___ -> false
let dbg : Prims.bool FStarC_Effect.ref= FStarC_Debug.get_toggle "Overload"
let showable_base_typ : base_typ FStarC_Class_Show.showable=
  {
    FStarC_Class_Show.show =
      (fun uu___ ->
         match uu___ with
         | Base_rigid fv ->
             let uu___1 =
               FStarC_Class_Show.show FStarC_Syntax_Syntax.showable_fv fv in
             Prims.strcat "Base_rigid " uu___1
         | Base_type -> "Base_type"
         | Base_unknown -> "Base_unknown")
  }
let base_steps : FStarC_TypeChecker_Env.step Prims.list=
  [FStarC_TypeChecker_Env.Unascribe;
  FStarC_TypeChecker_Env.Unmeta;
  FStarC_TypeChecker_Env.Unrefine]
let base_of_typ (env : FStarC_TypeChecker_Env.env)
  (t : FStarC_Syntax_Syntax.typ) : base_typ=
  let t1 = FStarC_TypeChecker_Normalize.unfold_whnf' base_steps env t in
  let uu___ = FStarC_Syntax_Util.head_and_args_full t1 in
  match uu___ with
  | (hd, uu___1) ->
      let r =
        let uu___2 =
          let uu___3 =
            let uu___4 = FStarC_Syntax_Util.un_uinst hd in
            FStarC_Syntax_Subst.compress uu___4 in
          uu___3.FStarC_Syntax_Syntax.n in
        match uu___2 with
        | FStarC_Syntax_Syntax.Tm_fvar fv -> Base_rigid fv
        | FStarC_Syntax_Syntax.Tm_type uu___3 -> Base_type
        | uu___3 -> Base_unknown in
      ((let uu___3 = FStarC_Effect.op_Bang dbg in
        if uu___3
        then
          let uu___4 =
            FStarC_Class_Show.show FStarC_Syntax_Print.showable_term t1 in
          let uu___5 = FStarC_Class_Show.show showable_base_typ r in
          FStarC_Format.print2 "(Overload) base_of_typ %s = %s\n" uu___4
            uu___5
        else ());
       r)
let base_head_fv (env : FStarC_TypeChecker_Env.env)
  (t : FStarC_Syntax_Syntax.typ) :
  FStarC_Syntax_Syntax.fv FStar_Pervasives_Native.option=
  let uu___ = base_of_typ env t in
  match uu___ with
  | Base_rigid fv -> FStar_Pervasives_Native.Some fv
  | uu___1 -> FStar_Pervasives_Native.None
let is_base_lid (l : FStarC_Ident.lident) (b : base_typ) : Prims.bool=
  match b with
  | Base_rigid fv -> FStarC_Syntax_Syntax.fv_eq_lid fv l
  | uu___ -> false
let coercion_source_and_target (env : FStarC_TypeChecker_Env.env)
  (f_typ : FStarC_Syntax_Syntax.typ) :
  (FStarC_Syntax_Syntax.fv * FStarC_Syntax_Syntax.fv)
    FStar_Pervasives_Native.option=
  let uu___ = FStarC_Syntax_Util.arrow_formals_comp f_typ in
  match uu___ with
  | (f_bs, f_c) ->
      if (match f_bs with | [] -> true | uu___1 -> false)
      then FStar_Pervasives_Native.None
      else
        (let src =
           let uu___1 =
             FStarC_TypeChecker_Env.push_binders env (FStarC_List.init f_bs) in
           base_head_fv uu___1
             ((FStarC_List.last f_bs).FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort in
         let tgt =
           let uu___1 = FStarC_TypeChecker_Env.push_binders env f_bs in
           base_head_fv uu___1 (FStarC_Syntax_Util.comp_result f_c) in
         match (src, tgt) with
         | (FStar_Pervasives_Native.Some src1, FStar_Pervasives_Native.Some
            tgt1) -> FStar_Pervasives_Native.Some (src1, tgt1)
         | uu___1 -> FStar_Pervasives_Native.None)
let user_coercions (env : FStarC_TypeChecker_Env.env) :
  (FStarC_Syntax_Syntax.fv * FStarC_Syntax_Syntax.fv) Prims.list=
  let uu___ =
    FStarC_TypeChecker_Env.lookup_attr env
      (FStarC_Ident.string_of_lid FStarC_Parser_Const.coercion_lid) in
  FStarC_List.collect
    (fun se ->
       let typ =
         match se.FStarC_Syntax_Syntax.sigel with
         | FStarC_Syntax_Syntax.Sig_let
             { FStarC_Syntax_Syntax.lbs1 = (uu___1, lb::[]);
               FStarC_Syntax_Syntax.lids1 = uu___2;_}
             ->
             FStar_Pervasives_Native.Some
               ((lb.FStarC_Syntax_Syntax.lbunivs),
                 (lb.FStarC_Syntax_Syntax.lbtyp))
         | FStarC_Syntax_Syntax.Sig_declare_typ
             { FStarC_Syntax_Syntax.lid2 = uu___1;
               FStarC_Syntax_Syntax.us2 = us; FStarC_Syntax_Syntax.t2 = t;_}
             -> FStar_Pervasives_Native.Some (us, t)
         | uu___1 -> FStar_Pervasives_Native.None in
       match typ with
       | FStar_Pervasives_Native.None -> []
       | FStar_Pervasives_Native.Some (us, t) ->
           let uu___1 = FStarC_Syntax_Subst.open_univ_vars us t in
           (match uu___1 with
            | (uu___2, t1) ->
                let uu___3 = coercion_source_and_target env t1 in
                (match uu___3 with
                 | FStar_Pervasives_Native.Some p -> [p]
                 | FStar_Pervasives_Native.None -> []))) uu___
let builtin_coercion (b1 : base_typ) (b2 : base_typ) : Prims.bool=
  let is_bool = is_base_lid FStarC_Parser_Const.bool_lid in
  let is_prop = is_base_lid FStarC_Parser_Const.prop_lid in
  ((((is_bool b1) && (is_prop b2)) ||
      ((is_prop b1) && (match b2 with | Base_type -> true | uu___ -> false)))
     ||
     ((is_bool b1) && (match b2 with | Base_type -> true | uu___ -> false)))
    || ((is_prop b1) && (is_bool b2))
let compatible (env : FStarC_TypeChecker_Env.env) (b1 : base_typ)
  (b2 : base_typ) : Prims.bool=
  let is_erased = is_base_lid FStarC_Parser_Const.erased_lid in
  match (b1, b2) with
  | (Base_unknown, uu___) -> true
  | (uu___, Base_unknown) -> true
  | (Base_type, Base_type) -> true
  | (Base_rigid fv1, Base_rigid fv2) when FStarC_Syntax_Syntax.fv_eq fv1 fv2
      -> true
  | uu___ ->
      if
        (((is_erased b1) || (is_erased b2)) || (builtin_coercion b1 b2)) ||
          (builtin_coercion b2 b1)
      then true
      else
        (let related uu___1 =
           match uu___1 with
           | (src, tgt) ->
               ((is_base_lid (FStarC_Syntax_Syntax.lid_of_fv src) b1) &&
                  (is_base_lid (FStarC_Syntax_Syntax.lid_of_fv tgt) b2))
                 ||
                 ((is_base_lid (FStarC_Syntax_Syntax.lid_of_fv src) b2) &&
                    (is_base_lid (FStarC_Syntax_Syntax.lid_of_fv tgt) b1)) in
         let uu___1 = user_coercions env in
         FStarC_List.existsb related uu___1)
let formals_of_typ (env : FStarC_TypeChecker_Env.env)
  (t : FStarC_Syntax_Syntax.typ) :
  (FStarC_Syntax_Syntax.binder Prims.list * FStarC_Syntax_Syntax.comp)=
  let uu___ = FStarC_TypeChecker_Normalize.unfold_whnf env t in
  FStarC_Syntax_Util.arrow_formals_comp uu___
let nth_explicit_formal_base (env : FStarC_TypeChecker_Env.env)
  (t : FStarC_Syntax_Syntax.typ) (i : Prims.int) : base_typ=
  let uu___ = formals_of_typ env t in
  match uu___ with
  | (bs, uu___1) ->
      let explicit =
        FStarC_List.filter
          (fun b ->
             Prims.not
               (FStarC_Syntax_Syntax.is_bqual_implicit_or_meta
                  b.FStarC_Syntax_Syntax.binder_qual)) bs in
      if (i < Prims.int_zero) || (i >= (FStarC_List.length explicit))
      then Base_unknown
      else
        base_of_typ env
          ((FStarC_List.nth explicit i).FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort
let arity_compatible (env : FStarC_TypeChecker_Env.env)
  (t : FStarC_Syntax_Syntax.typ) (n : Prims.int) : Prims.bool=
  let uu___ = formals_of_typ env t in
  match uu___ with
  | (bs, c) ->
      let n_explicit =
        let uu___1 =
          FStarC_List.filter
            (fun b ->
               Prims.not
                 (FStarC_Syntax_Syntax.is_bqual_implicit_or_meta
                    b.FStarC_Syntax_Syntax.binder_qual)) bs in
        FStarC_List.length uu___1 in
      if n <= n_explicit
      then true
      else
        (let uu___1 = base_of_typ env (FStarC_Syntax_Util.comp_result c) in
         match uu___1 with
         | Base_rigid uu___2 -> false
         | Base_type -> false
         | Base_unknown -> true)
let candidates_doc (env : FStarC_TypeChecker_Env.env)
  (cands : FStarC_Syntax_Syntax.fv Prims.list) :
  FStar_Pprint.document Prims.list=
  FStarC_List.map
    (fun fv ->
       let l = FStarC_Syntax_Syntax.lid_of_fv fv in
       let ty =
         let uu___ = FStarC_TypeChecker_Env.try_lookup_lid env l in
         match uu___ with
         | FStar_Pervasives_Native.Some ((uu___1, t), uu___2) ->
             FStarC_Class_PP.pp FStarC_Syntax_Print.pretty_term t
         | FStar_Pervasives_Native.None ->
             FStar_Pprint.doc_of_string "<unknown type>" in
       let uu___ =
         let uu___1 = FStarC_Class_PP.pp FStarC_Ident.pretty_lident l in
         FStar_Pprint.op_Hat_Hat uu___1
           (FStar_Pprint.op_Hat_Slash_Hat (FStar_Pprint.doc_of_string " :")
              (FStar_Pprint.align ty)) in
       FStar_Pprint.group uu___) cands
let base_of_typ_safe (env : FStarC_TypeChecker_Env.env)
  (t : FStarC_Syntax_Syntax.typ) : base_typ=
  try (fun uu___ -> match () with | () -> base_of_typ env t) ()
  with | uu___ -> Base_unknown
let type_of_fv (env : FStarC_TypeChecker_Env.env)
  (fv : FStarC_Syntax_Syntax.fv) :
  FStarC_Syntax_Syntax.typ FStar_Pervasives_Native.option=
  let uu___ =
    FStarC_TypeChecker_Env.try_lookup_lid env
      (FStarC_Syntax_Syntax.lid_of_fv fv) in
  match uu___ with
  | FStar_Pervasives_Native.Some ((uu___1, t), uu___2) ->
      FStar_Pervasives_Native.Some t
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
let explicit_shape (env : FStarC_TypeChecker_Env.env)
  (t : FStarC_Syntax_Syntax.typ) (n : Prims.int) :
  (FStarC_Syntax_Syntax.typ Prims.list * FStarC_Syntax_Syntax.typ)=
  let uu___ = formals_of_typ env t in
  match uu___ with
  | (bs, c) ->
      let rec go bs1 n1 =
        match bs1 with
        | [] -> ([], (FStarC_Syntax_Util.comp_result c))
        | b::bs2 ->
            if
              FStarC_Syntax_Syntax.is_bqual_implicit_or_meta
                b.FStarC_Syntax_Syntax.binder_qual
            then go bs2 n1
            else
              if n1 > Prims.int_zero
              then go bs2 (n1 - Prims.int_one)
              else
                (let uu___1 = go bs2 Prims.int_zero in
                 match uu___1 with
                 | (rest, r) ->
                     ((((b.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort)
                       :: rest), r)) in
      go bs n
let expected_compatible (env : FStarC_TypeChecker_Env.env)
  (t : FStarC_Syntax_Syntax.typ) (n : Prims.int)
  (te : FStarC_Syntax_Syntax.typ) : Prims.bool=
  let uu___ = explicit_shape env t n in
  match uu___ with
  | (ts, rt) ->
      let uu___1 = explicit_shape env te Prims.int_zero in
      (match uu___1 with
       | (es, re) ->
           let rec cmp ts1 es1 =
             match (ts1, es1) with
             | (t1::ts2, e1::es2) ->
                 let uu___2 =
                   let uu___3 = base_of_typ_safe env t1 in
                   let uu___4 = base_of_typ_safe env e1 in
                   compatible env uu___3 uu___4 in
                 if uu___2 then cmp ts2 es2 else false
             | ([], []) ->
                 let uu___2 = base_of_typ_safe env rt in
                 let uu___3 = base_of_typ_safe env re in
                 compatible env uu___2 uu___3
             | uu___2 -> true in
           cmp ts es)
let narrow_at (stage : Prims.string)
  (p :
    (FStarC_Syntax_Syntax.fv * FStarC_Syntax_Syntax.typ
      FStar_Pervasives_Native.option) -> Prims.bool)
  (cs :
    (FStarC_Syntax_Syntax.fv * FStarC_Syntax_Syntax.typ
      FStar_Pervasives_Native.option) Prims.list)
  :
  (FStarC_Syntax_Syntax.fv * FStarC_Syntax_Syntax.typ
    FStar_Pervasives_Native.option) Prims.list=
  let uu___ = FStarC_List.filter p cs in
  match uu___ with
  | [] ->
      ((let uu___2 =
          let uu___3 = FStarC_Effect.op_Bang dbg in
          if uu___3 then (FStarC_List.length cs) > Prims.int_one else false in
        if uu___2
        then
          FStarC_Format.print1
            "(Overload)   [%s] eliminated everything, keeping all\n" stage
        else ());
       cs)
  | cs' ->
      ((let uu___2 =
          let uu___3 = FStarC_Effect.op_Bang dbg in
          if uu___3
          then (FStarC_List.length cs') < (FStarC_List.length cs)
          else false in
        if uu___2
        then
          let uu___3 =
            let uu___4 =
              let uu___5 =
                FStarC_List.filter
                  (fun uu___6 ->
                     match uu___6 with
                     | (fv, uu___7) ->
                         let uu___8 =
                           FStarC_List.existsb
                             (fun uu___9 ->
                                match uu___9 with
                                | (fv', uu___10) ->
                                    FStarC_Syntax_Syntax.fv_eq fv fv') cs' in
                         Prims.not uu___8) cs in
              FStarC_List.map
                (fun uu___6 ->
                   match uu___6 with
                   | (fv, uu___7) -> FStarC_Syntax_Syntax.lid_of_fv fv)
                uu___5 in
            FStarC_Class_Show.show
              (FStarC_Class_Show.show_list FStarC_Ident.showable_lident)
              uu___4 in
          FStarC_Format.print2 "(Overload)   [%s] dropped %s\n" stage uu___3
        else ());
       cs')
let keep_if (f : FStarC_Syntax_Syntax.typ -> Prims.bool)
  (uu___ :
    (FStarC_Syntax_Syntax.fv * FStarC_Syntax_Syntax.typ
      FStar_Pervasives_Native.option))
  : Prims.bool=
  match uu___ with
  | (uu___1, ot) ->
      (match ot with
       | FStar_Pervasives_Native.None -> true
       | FStar_Pervasives_Native.Some t -> f t)
let reported :
  (Prims.string * Prims.string Prims.list) Prims.list FStarC_Effect.ref=
  FStarC_Effect.mk_ref []
let reset_ambiguity_reports (uu___ : unit) : unit=
  FStarC_Effect.op_Colon_Equals reported []
let already_reported (l : FStarC_Ident.lident)
  (cands : FStarC_Syntax_Syntax.fv Prims.list) : Prims.bool=
  let key =
    let uu___ =
      FStarC_Range_Ops.string_of_range (FStarC_Ident.range_of_lid l) in
    let uu___1 =
      FStarC_List.map
        (fun fv ->
           FStarC_Ident.string_of_lid (FStarC_Syntax_Syntax.lid_of_fv fv))
        cands in
    (uu___, uu___1) in
  let uu___ =
    let uu___1 = FStarC_Effect.op_Bang reported in FStarC_List.mem key uu___1 in
  if uu___
  then true
  else
    ((let uu___2 =
        let uu___3 = FStarC_Effect.op_Bang reported in key :: uu___3 in
      FStarC_Effect.op_Colon_Equals reported uu___2);
     false)
let resolve (env : FStarC_TypeChecker_Env.env)
  (speculate : FStarC_Syntax_Syntax.term -> base_typ)
  (primary : FStarC_Syntax_Syntax.fv)
  (alts : FStarC_Syntax_Syntax.fv Prims.list)
  (args : FStarC_Syntax_Syntax.term Prims.list)
  (expected : FStarC_Syntax_Syntax.typ FStar_Pervasives_Native.option) :
  FStarC_Syntax_Syntax.fv=
  let cands =
    FStarC_List.map (fun fv -> let uu___ = type_of_fv env fv in (fv, uu___))
      (primary :: alts) in
  let nargs = FStarC_List.length args in
  (let uu___1 = FStarC_Effect.op_Bang dbg in
   if uu___1
   then
     let uu___2 =
       FStarC_Class_Show.show FStarC_Ident.showable_lident
         (FStarC_Syntax_Syntax.lid_of_fv primary) in
     let uu___3 =
       let uu___4 =
         FStarC_List.map (fun fv -> FStarC_Syntax_Syntax.lid_of_fv fv)
           (primary :: alts) in
       FStarC_Class_Show.show
         (FStarC_Class_Show.show_list FStarC_Ident.showable_lident) uu___4 in
     FStarC_Format.print2 "(Overload) resolving %s among %s\n" uu___2 uu___3
   else ());
  (let cands1 =
     narrow_at "arity" (keep_if (fun t -> arity_compatible env t nargs))
       cands in
   let rec by_args i cands2 =
     if (i >= nargs) || ((FStarC_List.length cands2) <= Prims.int_one)
     then cands2
     else
       (let b_arg = speculate (FStarC_List.nth args i) in
        let cands3 =
          match b_arg with
          | Base_unknown -> cands2
          | uu___1 ->
              let uu___2 =
                let uu___3 =
                  FStarC_Class_Show.show FStarC_Class_Show.showable_int i in
                FStarC_Format.fmt1 "arg%s" uu___3 in
              narrow_at uu___2
                (keep_if
                   (fun t ->
                      let uu___3 = nth_explicit_formal_base env t i in
                      compatible env b_arg uu___3)) cands2 in
        by_args (i + Prims.int_one) cands3) in
   let cands2 = by_args Prims.int_zero cands1 in
   let cands3 =
     if (FStarC_List.length cands2) <= Prims.int_one
     then cands2
     else
       (match expected with
        | FStar_Pervasives_Native.None -> cands2
        | FStar_Pervasives_Native.Some te ->
            narrow_at "expected"
              (keep_if (fun t -> expected_compatible env t nargs te)) cands2) in
   match cands3 with
   | (fv, uu___1)::[] ->
       ((let uu___3 = FStarC_Effect.op_Bang dbg in
         if uu___3
         then
           let uu___4 =
             FStarC_Class_Show.show FStarC_Ident.showable_lident
               (FStarC_Syntax_Syntax.lid_of_fv fv) in
           FStarC_Format.print1 "(Overload) resolved to %s\n" uu___4
         else ());
        fv)
   | (fv, uu___1)::uu___2 ->
       let uu___3 =
         let uu___4 = FStarC_Options.overload_mode () in
         match uu___4 with
         | FStarC_Options.Overload_strict -> true
         | uu___5 -> false in
       if uu___3
       then
         ((let uu___5 =
             let uu___6 =
               let uu___7 =
                 FStarC_List.map FStar_Pervasives_Native.fst cands3 in
               already_reported (FStarC_Syntax_Syntax.lid_of_fv primary)
                 uu___7 in
             Prims.not uu___6 in
           if uu___5
           then
             let uu___6 =
               let uu___7 =
                 let uu___8 =
                   let uu___9 =
                     let uu___10 =
                       FStarC_Class_Show.show FStarC_Ident.showable_lident
                         (FStarC_Syntax_Syntax.lid_of_fv primary) in
                     FStarC_Format.fmt1
                       "The name %s is ambiguous; candidates are:" uu___10 in
                   FStarC_Errors_Msg.text uu___9 in
                 [uu___8] in
               let uu___8 =
                 let uu___9 =
                   FStarC_List.map FStar_Pervasives_Native.fst cands3 in
                 candidates_doc env uu___9 in
               FStarC_List.op_At uu___7 uu___8 in
             FStarC_Errors.log_issue FStarC_Ident.hasrange_lident
               (FStarC_Syntax_Syntax.lid_of_fv primary)
               FStarC_Errors_Codes.Error_AmbiguousName ()
               (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
               (Obj.magic uu___6)
           else ());
          fv)
       else
         ((let uu___5 = FStarC_Effect.op_Bang dbg in
           if uu___5
           then
             let uu___6 =
               FStarC_Class_Show.show FStarC_Ident.showable_lident
                 (FStarC_Syntax_Syntax.lid_of_fv fv) in
             FStarC_Format.print1 "(Overload) ambiguous, defaulting to %s\n"
               uu___6
           else ());
          fv)
   | [] -> primary)
