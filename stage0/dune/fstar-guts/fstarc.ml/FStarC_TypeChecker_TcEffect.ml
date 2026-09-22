open Prims
let open_comb (r : FStarC_Range_Type.t) (n : Prims.int)
  (mname : FStarC_Ident.lident) (name : Prims.string)
  (ts : FStarC_Syntax_Syntax.tscheme) :
  (FStarC_Syntax_Syntax.univ_name Prims.list * FStarC_Syntax_Syntax.term)=
  let uu___ = ts in
  match uu___ with
  | (us, t) ->
      if (match us with | [] -> true | uu___1 -> false)
      then
        let uu___1 =
          if n = Prims.int_one
          then
            let uu___2 =
              FStarC_Syntax_Syntax.new_univ_name
                (FStar_Pervasives_Native.Some r) in
            [uu___2]
          else
            (let uu___2 =
               FStarC_Syntax_Syntax.new_univ_name
                 (FStar_Pervasives_Native.Some r) in
             let uu___3 =
               let uu___4 =
                 FStarC_Syntax_Syntax.new_univ_name
                   (FStar_Pervasives_Native.Some r) in
               [uu___4] in
             uu___2 :: uu___3) in
        (uu___1, t)
      else
        if (FStarC_List.length us) = n
        then FStarC_Syntax_Subst.open_univ_vars us t
        else
          (let uu___1 =
             let uu___2 =
               FStarC_Class_Show.show FStarC_Class_Show.showable_int n in
             let uu___3 =
               FStarC_Class_Show.show FStarC_Class_Show.showable_nat
                 (FStarC_List.length us) in
             FStarC_Format.fmt4
               "The '%s' combinator of effect %s must be polymorphic in exactly %s universe(s), but it has %s"
               name (FStarC_Ident.string_of_lid mname) uu___2 uu___3 in
           FStarC_Errors.raise_error FStarC_Class_HasRange.hasRange_range r
             FStarC_Errors_Codes.Fatal_UnexpectedEffect ()
             (Obj.magic FStarC_Errors_Msg.is_error_message_string)
             (Obj.magic uu___1))
let u_type (r : FStarC_Range_Type.t) (u : FStarC_Syntax_Syntax.univ_name) :
  FStarC_Syntax_Syntax.term=
  FStarC_Syntax_Syntax.mk
    (FStarC_Syntax_Syntax.Tm_type (FStarC_Syntax_Syntax.U_name u)) r
let repr_app (repr_ts : FStarC_Syntax_Syntax.tscheme)
  (u : FStarC_Syntax_Syntax.univ_name) (a : FStarC_Syntax_Syntax.term)
  (r : FStarC_Range_Type.t) : FStarC_Syntax_Syntax.term=
  let uu___ =
    FStarC_TypeChecker_Env.inst_tscheme_with repr_ts
      [FStarC_Syntax_Syntax.U_name u] in
  match uu___ with
  | (uu___1, repr) ->
      FStarC_Syntax_Syntax.mk_Tm_app repr [FStarC_Syntax_Syntax.as_arg a] r
let check_comb (env : FStarC_TypeChecker_Env.env)
  (us : FStarC_Syntax_Syntax.univ_name Prims.list)
  (expected : FStarC_Syntax_Syntax.term) (t : FStarC_Syntax_Syntax.term) :
  FStarC_Syntax_Syntax.tscheme=
  let env1 = FStarC_TypeChecker_Env.push_univ_vars env us in
  let t1 = FStarC_TypeChecker_TcTerm.tc_check_trivial_guard env1 t expected in
  let uu___ = FStarC_Syntax_Subst.close_univ_vars us t1 in (us, uu___)
let check_total_repr (env : FStarC_TypeChecker_Env.env)
  (mname : FStarC_Ident.lident) (repr_ts : FStarC_Syntax_Syntax.tscheme)
  (r : FStarC_Range_Type.t) : unit=
  let uu___ = repr_ts in
  match uu___ with
  | (us, uu___1) ->
      let u_a = FStarC_List.hd us in
      let env1 = FStarC_TypeChecker_Env.push_univ_vars env us in
      let bv_a =
        let uu___2 = u_type r u_a in
        FStarC_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some r) uu___2 in
      let env2 = FStarC_TypeChecker_Env.push_bv env1 bv_a in
      let t =
        let uu___2 = FStarC_Syntax_Syntax.bv_to_name bv_a in
        repr_app repr_ts u_a uu___2 r in
      let t1 =
        FStarC_TypeChecker_Normalize.normalize
          [FStarC_TypeChecker_Env.Beta;
          FStarC_TypeChecker_Env.Eager_unfolding;
          FStarC_TypeChecker_Env.UnfoldUntil
            FStarC_Syntax_Syntax.delta_constant] env2 t in
      let t2 =
        let uu___2 = FStarC_Syntax_Subst.compress t1 in
        FStarC_Syntax_Util.unascribe uu___2 in
      (match t2.FStarC_Syntax_Syntax.n with
       | FStarC_Syntax_Syntax.Tm_arrow uu___2 ->
           let uu___3 = FStarC_Syntax_Util.arrow_formals_comp_ln t2 in
           (match uu___3 with
            | (uu___4, c) ->
                let uu___5 =
                  let uu___6 = FStarC_Syntax_Util.is_total_comp c in
                  Prims.not uu___6 in
                if uu___5
                then
                  let uu___6 =
                    let uu___7 =
                      FStarC_Class_Show.show FStarC_Ident.showable_lident
                        (FStarC_Syntax_Util.comp_effect_name c) in
                    FStarC_Format.fmt2
                      "Effect %s is marked total, but its representation is a function into %s"
                      (FStarC_Ident.string_of_lid mname) uu___7 in
                  FStarC_Errors.raise_error
                    FStarC_Class_HasRange.hasRange_range r
                    FStarC_Errors_Codes.Fatal_UnexpectedEffect ()
                    (Obj.magic FStarC_Errors_Msg.is_error_message_string)
                    (Obj.magic uu___6)
                else ())
       | uu___2 -> ())
let repr_universe (env : FStarC_TypeChecker_Env.env)
  (repr_ts : FStarC_Syntax_Syntax.tscheme) (r : FStarC_Range_Type.t) :
  FStarC_Syntax_Syntax.tscheme=
  let uu___ = repr_ts in
  match uu___ with
  | (us, uu___1) ->
      let u_a = FStarC_List.hd us in
      let env1 = FStarC_TypeChecker_Env.push_univ_vars env us in
      let bv_a =
        let uu___2 = u_type r u_a in
        FStarC_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some r) uu___2 in
      let env2 = FStarC_TypeChecker_Env.push_bv env1 bv_a in
      let u =
        let uu___2 =
          let uu___3 = FStarC_Syntax_Syntax.bv_to_name bv_a in
          repr_app repr_ts u_a uu___3 r in
        FStarC_TypeChecker_TcTerm.universe_of env2 uu___2 in
      let uu___2 =
        let uu___3 =
          FStarC_Syntax_Syntax.mk (FStarC_Syntax_Syntax.Tm_type u) r in
        FStarC_Syntax_Subst.close_univ_vars [u_a] uu___3 in
      ([u_a], uu___2)
let tc_eff_decl (env : FStarC_TypeChecker_Env.env)
  (ed : FStarC_Syntax_Syntax.eff_decl)
  (quals : FStarC_Syntax_Syntax.qualifier Prims.list)
  (_attrs : FStarC_Syntax_Syntax.attribute Prims.list) :
  FStarC_Syntax_Syntax.eff_decl=
  match ed.FStarC_Syntax_Syntax.combinators with
  | FStar_Pervasives_Native.None -> ed
  | FStar_Pervasives_Native.Some combs ->
      let r = FStarC_Ident.range_of_lid ed.FStarC_Syntax_Syntax.mname in
      let env0 = env in
      let repr_ts =
        let uu___ =
          open_comb r Prims.int_one ed.FStarC_Syntax_Syntax.mname "repr"
            combs.FStarC_Syntax_Syntax.repr in
        match uu___ with
        | (us, t) ->
            let u_a = FStarC_List.hd us in
            let b_a =
              let uu___1 =
                let uu___2 = u_type r u_a in
                FStarC_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some r)
                  uu___2 in
              FStarC_Syntax_Syntax.mk_binder uu___1 in
            let uu___1 = FStarC_Syntax_Util.type_u () in
            (match uu___1 with
             | (t_r, uu___2) ->
                 let expected =
                   let uu___3 = FStarC_Syntax_Syntax.mk_Total t_r in
                   FStarC_Syntax_Util.arrow [b_a] uu___3 in
                 check_comb env0 us expected t) in
      let return_ts =
        let uu___ =
          open_comb r Prims.int_one ed.FStarC_Syntax_Syntax.mname "return"
            combs.FStarC_Syntax_Syntax.return_repr in
        match uu___ with
        | (us, t) ->
            let u_a = FStarC_List.hd us in
            let bv_a =
              let uu___1 = u_type r u_a in
              FStarC_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some r)
                uu___1 in
            let a = FStarC_Syntax_Syntax.bv_to_name bv_a in
            let expected =
              let uu___1 =
                let uu___2 =
                  let uu___3 = FStarC_Syntax_Syntax.null_binder a in [uu___3] in
                (FStarC_Syntax_Syntax.mk_binder bv_a) :: uu___2 in
              let uu___2 =
                let uu___3 = repr_app repr_ts u_a a r in
                FStarC_Syntax_Syntax.mk_Total uu___3 in
              FStarC_Syntax_Util.arrow uu___1 uu___2 in
            check_comb env0 us expected t in
      let bind_ts =
        let uu___ =
          open_comb r (Prims.of_int 2) ed.FStarC_Syntax_Syntax.mname "bind"
            combs.FStarC_Syntax_Syntax.bind_repr in
        match uu___ with
        | (us, t) ->
            let uu___1 =
              ((FStarC_List.hd us), (FStarC_List.hd (FStarC_List.tl us))) in
            (match uu___1 with
             | (u_a, u_b) ->
                 let bv_a =
                   let uu___2 = u_type r u_a in
                   FStarC_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some r) uu___2 in
                 let bv_b =
                   let uu___2 = u_type r u_b in
                   FStarC_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some r) uu___2 in
                 let a = FStarC_Syntax_Syntax.bv_to_name bv_a in
                 let b = FStarC_Syntax_Syntax.bv_to_name bv_b in
                 let repr_b = repr_app repr_ts u_b b r in
                 let k =
                   let uu___2 =
                     let uu___3 = FStarC_Syntax_Syntax.null_binder a in
                     [uu___3] in
                   let uu___3 = FStarC_Syntax_Syntax.mk_Total repr_b in
                   FStarC_Syntax_Util.arrow uu___2 uu___3 in
                 let expected =
                   let uu___2 =
                     let uu___3 =
                       let uu___4 =
                         let uu___5 =
                           let uu___6 = repr_app repr_ts u_a a r in
                           FStarC_Syntax_Syntax.null_binder uu___6 in
                         let uu___6 =
                           let uu___7 = FStarC_Syntax_Syntax.null_binder k in
                           [uu___7] in
                         uu___5 :: uu___6 in
                       (FStarC_Syntax_Syntax.mk_binder bv_b) :: uu___4 in
                     (FStarC_Syntax_Syntax.mk_binder bv_a) :: uu___3 in
                   let uu___3 = FStarC_Syntax_Syntax.mk_Total repr_b in
                   FStarC_Syntax_Util.arrow uu___2 uu___3 in
                 check_comb env0 us expected t) in
      (if FStarC_List.contains FStarC_Syntax_Syntax.TotalEffect quals
       then check_total_repr env0 ed.FStarC_Syntax_Syntax.mname repr_ts r
       else ();
       (let uu___1 =
          let uu___2 =
            let uu___3 = repr_universe env0 repr_ts r in
            {
              FStarC_Syntax_Syntax.repr = repr_ts;
              FStarC_Syntax_Syntax.return_repr = return_ts;
              FStarC_Syntax_Syntax.bind_repr = bind_ts;
              FStarC_Syntax_Syntax.repr_universe = uu___3
            } in
          FStar_Pervasives_Native.Some uu___2 in
        {
          FStarC_Syntax_Syntax.mname = (ed.FStarC_Syntax_Syntax.mname);
          FStarC_Syntax_Syntax.cattributes =
            (ed.FStarC_Syntax_Syntax.cattributes);
          FStarC_Syntax_Syntax.combinators = uu___1;
          FStarC_Syntax_Syntax.eff_attrs =
            (ed.FStarC_Syntax_Syntax.eff_attrs);
          FStarC_Syntax_Syntax.extraction_mode =
            (ed.FStarC_Syntax_Syntax.extraction_mode)
        }))
let tc_lift (env : FStarC_TypeChecker_Env.env)
  (sub : FStarC_Syntax_Syntax.sub_eff) (r : FStarC_Range_Type.t) :
  FStarC_Syntax_Syntax.sub_eff=
  let uu___ =
    FStarC_TypeChecker_Env.get_effect_decl env
      sub.FStarC_Syntax_Syntax.source in
  let ed_tgt =
    FStarC_TypeChecker_Env.get_effect_decl env
      sub.FStarC_Syntax_Syntax.target in
  let lift =
    match sub.FStarC_Syntax_Syntax.lift with
    | FStar_Pervasives_Native.None ->
        (if
           (match ed_tgt.FStarC_Syntax_Syntax.combinators with
            | FStar_Pervasives_Native.Some v -> true
            | uu___2 -> false) &&
             (Prims.not
                ((((FStarC_Syntax_Util.is_pure_effect
                      sub.FStarC_Syntax_Syntax.source)
                     ||
                     (FStarC_Syntax_Util.is_div_effect
                        sub.FStarC_Syntax_Syntax.source))
                    ||
                    (FStarC_Syntax_Util.is_ndet_effect
                       sub.FStarC_Syntax_Syntax.source))
                   ||
                   (FStarC_Syntax_Util.is_ghost_effect
                      sub.FStarC_Syntax_Syntax.source)))
         then
           FStarC_Errors.raise_error FStarC_Class_HasRange.hasRange_range r
             FStarC_Errors_Codes.Fatal_UnexpectedEffect ()
             (Obj.magic FStarC_Errors_Msg.is_error_message_string)
             (Obj.magic
                (FStarC_Format.fmt2
                   "Effect %s has a representation, so the lift from %s must be given explicitly: only a pure, ghost, nondeterministic or divergent computation can be lifted with the target's return combinator"
                   (FStarC_Ident.string_of_lid
                      sub.FStarC_Syntax_Syntax.target)
                   (FStarC_Ident.string_of_lid
                      sub.FStarC_Syntax_Syntax.source)))
         else ();
         FStar_Pervasives_Native.None)
    | FStar_Pervasives_Native.Some ts ->
        let repr_ts =
          match FStarC_Syntax_Util.get_eff_repr ed_tgt with
          | FStar_Pervasives_Native.Some repr -> repr
          | FStar_Pervasives_Native.None ->
              FStarC_Errors.raise_error FStarC_Class_HasRange.hasRange_range
                r FStarC_Errors_Codes.Fatal_UnexpectedEffect ()
                (Obj.magic FStarC_Errors_Msg.is_error_message_string)
                (Obj.magic
                   (FStarC_Format.fmt1
                      "Effect %s has no representation, so it cannot be the target of a lift with a term"
                      (FStarC_Ident.string_of_lid
                         sub.FStarC_Syntax_Syntax.target))) in
        let uu___1 =
          open_comb r Prims.int_one sub.FStarC_Syntax_Syntax.target "lift" ts in
        (match uu___1 with
         | (us, t) ->
             let u_a = FStarC_List.hd us in
             let bv_a =
               let uu___2 = u_type r u_a in
               FStarC_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some r)
                 uu___2 in
             let a = FStarC_Syntax_Syntax.bv_to_name bv_a in
             let src_arg =
               let uu___2 =
                 FStarC_TypeChecker_Env.effect_decl_opt env
                   sub.FStarC_Syntax_Syntax.source in
               match uu___2 with
               | FStar_Pervasives_Native.Some (ed_src, uu___3) when
                   match ed_src.FStarC_Syntax_Syntax.combinators with
                   | FStar_Pervasives_Native.Some v -> true
                   | uu___4 -> false ->
                   let uu___4 =
                     FStarC_Option.must
                       (FStarC_Syntax_Util.get_eff_repr ed_src) in
                   repr_app uu___4 u_a a r
               | uu___3 ->
                   let c =
                     FStarC_Syntax_Syntax.mk_Comp
                       {
                         FStarC_Syntax_Syntax.effect_name =
                           (sub.FStarC_Syntax_Syntax.source);
                         FStarC_Syntax_Syntax.result_typ = a;
                         FStarC_Syntax_Syntax.flags = [];
                         FStarC_Syntax_Syntax.source_effect_name =
                           (sub.FStarC_Syntax_Syntax.source)
                       } in
                   let uu___4 =
                     let uu___5 =
                       FStarC_Syntax_Syntax.null_binder
                         FStarC_Syntax_Syntax.t_unit in
                     [uu___5] in
                   FStarC_Syntax_Util.arrow uu___4 c in
             let expected =
               let uu___2 =
                 let uu___3 =
                   let uu___4 = FStarC_Syntax_Syntax.null_binder src_arg in
                   [uu___4] in
                 (FStarC_Syntax_Syntax.mk_binder bv_a) :: uu___3 in
               let uu___3 =
                 let uu___4 = repr_app repr_ts u_a a r in
                 FStarC_Syntax_Syntax.mk_Total uu___4 in
               FStarC_Syntax_Util.arrow uu___2 uu___3 in
             let uu___2 = check_comb env us expected t in
             FStar_Pervasives_Native.Some uu___2) in
  {
    FStarC_Syntax_Syntax.source = (sub.FStarC_Syntax_Syntax.source);
    FStarC_Syntax_Syntax.target = (sub.FStarC_Syntax_Syntax.target);
    FStarC_Syntax_Syntax.lift = lift
  }
