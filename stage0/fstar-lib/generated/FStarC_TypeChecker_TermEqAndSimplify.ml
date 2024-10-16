open Prims
type eq_result =
  | Equal 
  | NotEqual 
  | Unknown 
let (uu___is_Equal : eq_result -> Prims.bool) =
  fun projectee -> match projectee with | Equal -> true | uu___ -> false
let (uu___is_NotEqual : eq_result -> Prims.bool) =
  fun projectee -> match projectee with | NotEqual -> true | uu___ -> false
let (uu___is_Unknown : eq_result -> Prims.bool) =
  fun projectee -> match projectee with | Unknown -> true | uu___ -> false
let (injectives : Prims.string Prims.list) =
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
  "FStar.SizeT.__uint_to_t"]
let (eq_inj : eq_result -> eq_result -> eq_result) =
  fun r ->
    fun s ->
      match (r, s) with
      | (Equal, Equal) -> Equal
      | (NotEqual, uu___) -> NotEqual
      | (uu___, NotEqual) -> NotEqual
      | (uu___, uu___1) -> Unknown
let (equal_if : Prims.bool -> eq_result) =
  fun uu___ -> if uu___ then Equal else Unknown
let (equal_iff : Prims.bool -> eq_result) =
  fun uu___ -> if uu___ then Equal else NotEqual
let (eq_and : eq_result -> (unit -> eq_result) -> eq_result) =
  fun r ->
    fun s ->
      let uu___ = (r = Equal) && (let uu___1 = s () in uu___1 = Equal) in
      if uu___ then Equal else Unknown
let rec (eq_tm :
  FStarC_TypeChecker_Env.env_t ->
    FStarC_Syntax_Syntax.term -> FStarC_Syntax_Syntax.term -> eq_result)
  =
  fun env ->
    fun t1 ->
      fun t2 ->
        let t11 = FStarC_Syntax_Util.canon_app t1 in
        let t21 = FStarC_Syntax_Util.canon_app t2 in
        let equal_data f1 args1 f2 args2 n_parms =
          let uu___ = FStarC_Syntax_Syntax.fv_eq f1 f2 in
          if uu___
          then
            let n1 = FStarC_Compiler_List.length args1 in
            let n2 = FStarC_Compiler_List.length args2 in
            (if (n1 = n2) && (n_parms <= n1)
             then
               let uu___1 = FStarC_Compiler_List.splitAt n_parms args1 in
               match uu___1 with
               | (parms1, args11) ->
                   let uu___2 = FStarC_Compiler_List.splitAt n_parms args2 in
                   (match uu___2 with
                    | (parms2, args21) ->
                        let eq_arg_list as1 as2 =
                          FStarC_Compiler_List.fold_left2
                            (fun acc ->
                               fun uu___3 ->
                                 fun uu___4 ->
                                   match (uu___3, uu___4) with
                                   | ((a1, q1), (a2, q2)) ->
                                       let uu___5 = eq_tm env a1 a2 in
                                       eq_inj acc uu___5) Equal as1 as2 in
                        eq_arg_list args11 args21)
             else Unknown)
          else NotEqual in
        let qual_is_inj uu___ =
          match uu___ with
          | FStar_Pervasives_Native.Some (FStarC_Syntax_Syntax.Data_ctor) ->
              true
          | FStar_Pervasives_Native.Some (FStarC_Syntax_Syntax.Record_ctor
              uu___1) -> true
          | uu___1 -> false in
        let heads_and_args_in_case_both_data =
          let uu___ =
            let uu___1 = FStarC_Syntax_Util.unmeta t11 in
            FStarC_Syntax_Util.head_and_args uu___1 in
          match uu___ with
          | (head1, args1) ->
              let uu___1 =
                let uu___2 = FStarC_Syntax_Util.unmeta t21 in
                FStarC_Syntax_Util.head_and_args uu___2 in
              (match uu___1 with
               | (head2, args2) ->
                   let uu___2 =
                     let uu___3 =
                       let uu___4 = FStarC_Syntax_Util.un_uinst head1 in
                       uu___4.FStarC_Syntax_Syntax.n in
                     let uu___4 =
                       let uu___5 = FStarC_Syntax_Util.un_uinst head2 in
                       uu___5.FStarC_Syntax_Syntax.n in
                     (uu___3, uu___4) in
                   (match uu___2 with
                    | (FStarC_Syntax_Syntax.Tm_fvar f,
                       FStarC_Syntax_Syntax.Tm_fvar g) when
                        (qual_is_inj f.FStarC_Syntax_Syntax.fv_qual) &&
                          (qual_is_inj g.FStarC_Syntax_Syntax.fv_qual)
                        ->
                        let uu___3 =
                          let uu___4 = FStarC_Syntax_Syntax.lid_of_fv f in
                          FStarC_TypeChecker_Env.num_datacon_non_injective_ty_params
                            env uu___4 in
                        (match uu___3 with
                         | FStar_Pervasives_Native.Some n ->
                             FStar_Pervasives_Native.Some
                               (f, args1, g, args2, n)
                         | uu___4 -> FStar_Pervasives_Native.None)
                    | uu___3 -> FStar_Pervasives_Native.None)) in
        let t12 = FStarC_Syntax_Util.unmeta t11 in
        let t22 = FStarC_Syntax_Util.unmeta t21 in
        match ((t12.FStarC_Syntax_Syntax.n), (t22.FStarC_Syntax_Syntax.n))
        with
        | (FStarC_Syntax_Syntax.Tm_bvar bv1, FStarC_Syntax_Syntax.Tm_bvar
           bv2) ->
            equal_if
              (bv1.FStarC_Syntax_Syntax.index =
                 bv2.FStarC_Syntax_Syntax.index)
        | (FStarC_Syntax_Syntax.Tm_lazy uu___, uu___1) ->
            let uu___2 = FStarC_Syntax_Util.unlazy t12 in
            eq_tm env uu___2 t22
        | (uu___, FStarC_Syntax_Syntax.Tm_lazy uu___1) ->
            let uu___2 = FStarC_Syntax_Util.unlazy t22 in
            eq_tm env t12 uu___2
        | (FStarC_Syntax_Syntax.Tm_name a, FStarC_Syntax_Syntax.Tm_name b) ->
            let uu___ = FStarC_Syntax_Syntax.bv_eq a b in equal_if uu___
        | uu___ when
            FStar_Pervasives_Native.uu___is_Some
              heads_and_args_in_case_both_data
            ->
            let uu___1 =
              FStarC_Compiler_Util.must heads_and_args_in_case_both_data in
            (match uu___1 with
             | (f, args1, g, args2, n) -> equal_data f args1 g args2 n)
        | (FStarC_Syntax_Syntax.Tm_fvar f, FStarC_Syntax_Syntax.Tm_fvar g) ->
            let uu___ = FStarC_Syntax_Syntax.fv_eq f g in equal_if uu___
        | (FStarC_Syntax_Syntax.Tm_uinst (f, us),
           FStarC_Syntax_Syntax.Tm_uinst (g, vs)) ->
            let uu___ = eq_tm env f g in
            eq_and uu___
              (fun uu___1 ->
                 let uu___2 = FStarC_Syntax_Util.eq_univs_list us vs in
                 equal_if uu___2)
        | (FStarC_Syntax_Syntax.Tm_constant (FStarC_Const.Const_range uu___),
           FStarC_Syntax_Syntax.Tm_constant (FStarC_Const.Const_range
           uu___1)) -> Unknown
        | (FStarC_Syntax_Syntax.Tm_constant (FStarC_Const.Const_real r1),
           FStarC_Syntax_Syntax.Tm_constant (FStarC_Const.Const_real r2)) ->
            equal_if (r1 = r2)
        | (FStarC_Syntax_Syntax.Tm_constant c,
           FStarC_Syntax_Syntax.Tm_constant d) ->
            let uu___ = FStarC_Const.eq_const c d in equal_iff uu___
        | (FStarC_Syntax_Syntax.Tm_uvar (u1, ([], uu___)),
           FStarC_Syntax_Syntax.Tm_uvar (u2, ([], uu___1))) ->
            let uu___2 =
              FStarC_Syntax_Unionfind.equiv
                u1.FStarC_Syntax_Syntax.ctx_uvar_head
                u2.FStarC_Syntax_Syntax.ctx_uvar_head in
            equal_if uu___2
        | (FStarC_Syntax_Syntax.Tm_app
           { FStarC_Syntax_Syntax.hd = h1;
             FStarC_Syntax_Syntax.args = args1;_},
           FStarC_Syntax_Syntax.Tm_app
           { FStarC_Syntax_Syntax.hd = h2;
             FStarC_Syntax_Syntax.args = args2;_})
            ->
            let uu___ =
              let uu___1 =
                let uu___2 = FStarC_Syntax_Util.un_uinst h1 in
                uu___2.FStarC_Syntax_Syntax.n in
              let uu___2 =
                let uu___3 = FStarC_Syntax_Util.un_uinst h2 in
                uu___3.FStarC_Syntax_Syntax.n in
              (uu___1, uu___2) in
            (match uu___ with
             | (FStarC_Syntax_Syntax.Tm_fvar f1, FStarC_Syntax_Syntax.Tm_fvar
                f2) when
                 (FStarC_Syntax_Syntax.fv_eq f1 f2) &&
                   (let uu___1 =
                      let uu___2 = FStarC_Syntax_Syntax.lid_of_fv f1 in
                      FStarC_Ident.string_of_lid uu___2 in
                    FStarC_Compiler_List.mem uu___1 injectives)
                 -> equal_data f1 args1 f2 args2 Prims.int_zero
             | uu___1 ->
                 let uu___2 = eq_tm env h1 h2 in
                 eq_and uu___2 (fun uu___3 -> eq_args env args1 args2))
        | (FStarC_Syntax_Syntax.Tm_match
           { FStarC_Syntax_Syntax.scrutinee = t13;
             FStarC_Syntax_Syntax.ret_opt = uu___;
             FStarC_Syntax_Syntax.brs = bs1;
             FStarC_Syntax_Syntax.rc_opt1 = uu___1;_},
           FStarC_Syntax_Syntax.Tm_match
           { FStarC_Syntax_Syntax.scrutinee = t23;
             FStarC_Syntax_Syntax.ret_opt = uu___2;
             FStarC_Syntax_Syntax.brs = bs2;
             FStarC_Syntax_Syntax.rc_opt1 = uu___3;_})
            ->
            if
              (FStarC_Compiler_List.length bs1) =
                (FStarC_Compiler_List.length bs2)
            then
              let uu___4 = FStarC_Compiler_List.zip bs1 bs2 in
              let uu___5 = eq_tm env t13 t23 in
              FStarC_Compiler_List.fold_right
                (fun uu___6 ->
                   fun a ->
                     match uu___6 with
                     | (b1, b2) ->
                         eq_and a (fun uu___7 -> branch_matches env b1 b2))
                uu___4 uu___5
            else Unknown
        | (FStarC_Syntax_Syntax.Tm_type u, FStarC_Syntax_Syntax.Tm_type v) ->
            let uu___ = FStarC_Syntax_Util.eq_univs u v in equal_if uu___
        | (FStarC_Syntax_Syntax.Tm_quoted (t13, q1),
           FStarC_Syntax_Syntax.Tm_quoted (t23, q2)) -> Unknown
        | (FStarC_Syntax_Syntax.Tm_refine
           { FStarC_Syntax_Syntax.b = t13; FStarC_Syntax_Syntax.phi = phi1;_},
           FStarC_Syntax_Syntax.Tm_refine
           { FStarC_Syntax_Syntax.b = t23; FStarC_Syntax_Syntax.phi = phi2;_})
            ->
            let uu___ =
              eq_tm env t13.FStarC_Syntax_Syntax.sort
                t23.FStarC_Syntax_Syntax.sort in
            eq_and uu___ (fun uu___1 -> eq_tm env phi1 phi2)
        | (FStarC_Syntax_Syntax.Tm_abs
           { FStarC_Syntax_Syntax.bs = bs1;
             FStarC_Syntax_Syntax.body = body1;
             FStarC_Syntax_Syntax.rc_opt = uu___;_},
           FStarC_Syntax_Syntax.Tm_abs
           { FStarC_Syntax_Syntax.bs = bs2;
             FStarC_Syntax_Syntax.body = body2;
             FStarC_Syntax_Syntax.rc_opt = uu___1;_})
            when
            (FStarC_Compiler_List.length bs1) =
              (FStarC_Compiler_List.length bs2)
            ->
            let uu___2 =
              FStarC_Compiler_List.fold_left2
                (fun r ->
                   fun b1 ->
                     fun b2 ->
                       eq_and r
                         (fun uu___3 ->
                            eq_tm env
                              (b1.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort
                              (b2.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort))
                Equal bs1 bs2 in
            eq_and uu___2 (fun uu___3 -> eq_tm env body1 body2)
        | (FStarC_Syntax_Syntax.Tm_arrow
           { FStarC_Syntax_Syntax.bs1 = bs1;
             FStarC_Syntax_Syntax.comp = c1;_},
           FStarC_Syntax_Syntax.Tm_arrow
           { FStarC_Syntax_Syntax.bs1 = bs2;
             FStarC_Syntax_Syntax.comp = c2;_})
            when
            (FStarC_Compiler_List.length bs1) =
              (FStarC_Compiler_List.length bs2)
            ->
            let uu___ =
              FStarC_Compiler_List.fold_left2
                (fun r ->
                   fun b1 ->
                     fun b2 ->
                       eq_and r
                         (fun uu___1 ->
                            eq_tm env
                              (b1.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort
                              (b2.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort))
                Equal bs1 bs2 in
            eq_and uu___ (fun uu___1 -> eq_comp env c1 c2)
        | uu___ -> Unknown
and (eq_antiquotations :
  FStarC_TypeChecker_Env.env_t ->
    FStarC_Syntax_Syntax.term Prims.list ->
      FStarC_Syntax_Syntax.term Prims.list -> eq_result)
  =
  fun env ->
    fun a1 ->
      fun a2 ->
        match (a1, a2) with
        | ([], []) -> Equal
        | ([], uu___) -> NotEqual
        | (uu___, []) -> NotEqual
        | (t1::a11, t2::a21) ->
            let uu___ = eq_tm env t1 t2 in
            (match uu___ with
             | NotEqual -> NotEqual
             | Unknown ->
                 let uu___1 = eq_antiquotations env a11 a21 in
                 (match uu___1 with
                  | NotEqual -> NotEqual
                  | uu___2 -> Unknown)
             | Equal -> eq_antiquotations env a11 a21)
and (branch_matches :
  FStarC_TypeChecker_Env.env_t ->
    (FStarC_Syntax_Syntax.pat' FStarC_Syntax_Syntax.withinfo_t *
      FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax
      FStar_Pervasives_Native.option * FStarC_Syntax_Syntax.term'
      FStarC_Syntax_Syntax.syntax) ->
      (FStarC_Syntax_Syntax.pat' FStarC_Syntax_Syntax.withinfo_t *
        FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax
        FStar_Pervasives_Native.option * FStarC_Syntax_Syntax.term'
        FStarC_Syntax_Syntax.syntax) -> eq_result)
  =
  fun env ->
    fun b1 ->
      fun b2 ->
        let related_by f o1 o2 =
          match (o1, o2) with
          | (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None) ->
              true
          | (FStar_Pervasives_Native.Some x, FStar_Pervasives_Native.Some y)
              -> f x y
          | (uu___, uu___1) -> false in
        let uu___ = b1 in
        match uu___ with
        | (p1, w1, t1) ->
            let uu___1 = b2 in
            (match uu___1 with
             | (p2, w2, t2) ->
                 let uu___2 = FStarC_Syntax_Syntax.eq_pat p1 p2 in
                 if uu___2
                 then
                   let uu___3 =
                     (let uu___4 = eq_tm env t1 t2 in uu___4 = Equal) &&
                       (related_by
                          (fun t11 ->
                             fun t21 ->
                               let uu___4 = eq_tm env t11 t21 in
                               uu___4 = Equal) w1 w2) in
                   (if uu___3 then Equal else Unknown)
                 else Unknown)
and (eq_args :
  FStarC_TypeChecker_Env.env_t ->
    FStarC_Syntax_Syntax.args -> FStarC_Syntax_Syntax.args -> eq_result)
  =
  fun env ->
    fun a1 ->
      fun a2 ->
        match (a1, a2) with
        | ([], []) -> Equal
        | ((a, uu___)::a11, (b, uu___1)::b1) ->
            let uu___2 = eq_tm env a b in
            (match uu___2 with
             | Equal -> eq_args env a11 b1
             | uu___3 -> Unknown)
        | uu___ -> Unknown
and (eq_comp :
  FStarC_TypeChecker_Env.env_t ->
    FStarC_Syntax_Syntax.comp -> FStarC_Syntax_Syntax.comp -> eq_result)
  =
  fun env ->
    fun c1 ->
      fun c2 ->
        match ((c1.FStarC_Syntax_Syntax.n), (c2.FStarC_Syntax_Syntax.n)) with
        | (FStarC_Syntax_Syntax.Total t1, FStarC_Syntax_Syntax.Total t2) ->
            eq_tm env t1 t2
        | (FStarC_Syntax_Syntax.GTotal t1, FStarC_Syntax_Syntax.GTotal t2) ->
            eq_tm env t1 t2
        | (FStarC_Syntax_Syntax.Comp ct1, FStarC_Syntax_Syntax.Comp ct2) ->
            let uu___ =
              let uu___1 =
                FStarC_Syntax_Util.eq_univs_list
                  ct1.FStarC_Syntax_Syntax.comp_univs
                  ct2.FStarC_Syntax_Syntax.comp_univs in
              equal_if uu___1 in
            eq_and uu___
              (fun uu___1 ->
                 let uu___2 =
                   let uu___3 =
                     FStarC_Ident.lid_equals
                       ct1.FStarC_Syntax_Syntax.effect_name
                       ct2.FStarC_Syntax_Syntax.effect_name in
                   equal_if uu___3 in
                 eq_and uu___2
                   (fun uu___3 ->
                      let uu___4 =
                        eq_tm env ct1.FStarC_Syntax_Syntax.result_typ
                          ct2.FStarC_Syntax_Syntax.result_typ in
                      eq_and uu___4
                        (fun uu___5 ->
                           eq_args env ct1.FStarC_Syntax_Syntax.effect_args
                             ct2.FStarC_Syntax_Syntax.effect_args)))
        | uu___ -> NotEqual
let (eq_tm_bool :
  FStarC_TypeChecker_Env.env_t ->
    FStarC_Syntax_Syntax.term -> FStarC_Syntax_Syntax.term -> Prims.bool)
  = fun e -> fun t1 -> fun t2 -> let uu___ = eq_tm e t1 t2 in uu___ = Equal
let (simplify :
  Prims.bool ->
    FStarC_TypeChecker_Env.env_t ->
      FStarC_Syntax_Syntax.term -> FStarC_Syntax_Syntax.term)
  =
  fun debug ->
    fun env ->
      fun tm ->
        let w t =
          {
            FStarC_Syntax_Syntax.n = (t.FStarC_Syntax_Syntax.n);
            FStarC_Syntax_Syntax.pos = (tm.FStarC_Syntax_Syntax.pos);
            FStarC_Syntax_Syntax.vars = (t.FStarC_Syntax_Syntax.vars);
            FStarC_Syntax_Syntax.hash_code =
              (t.FStarC_Syntax_Syntax.hash_code)
          } in
        let simp_t t =
          let uu___ =
            let uu___1 = FStarC_Syntax_Util.unmeta t in
            uu___1.FStarC_Syntax_Syntax.n in
          match uu___ with
          | FStarC_Syntax_Syntax.Tm_fvar fv when
              FStarC_Syntax_Syntax.fv_eq_lid fv FStarC_Parser_Const.true_lid
              -> FStar_Pervasives_Native.Some true
          | FStarC_Syntax_Syntax.Tm_fvar fv when
              FStarC_Syntax_Syntax.fv_eq_lid fv FStarC_Parser_Const.false_lid
              -> FStar_Pervasives_Native.Some false
          | uu___1 -> FStar_Pervasives_Native.None in
        let rec args_are_binders args bs =
          match (args, bs) with
          | ((t, uu___)::args1, b::bs1) ->
              let uu___1 =
                let uu___2 = FStarC_Syntax_Subst.compress t in
                uu___2.FStarC_Syntax_Syntax.n in
              (match uu___1 with
               | FStarC_Syntax_Syntax.Tm_name bv' ->
                   (FStarC_Syntax_Syntax.bv_eq
                      b.FStarC_Syntax_Syntax.binder_bv bv')
                     && (args_are_binders args1 bs1)
               | uu___2 -> false)
          | ([], []) -> true
          | (uu___, uu___1) -> false in
        let is_applied bs t =
          if debug
          then
            (let uu___1 =
               FStarC_Class_Show.show FStarC_Syntax_Print.showable_term t in
             let uu___2 =
               FStarC_Class_Tagged.tag_of FStarC_Syntax_Syntax.tagged_term t in
             FStarC_Compiler_Util.print2 "WPE> is_applied %s -- %s\n" uu___1
               uu___2)
          else ();
          (let uu___1 = FStarC_Syntax_Util.head_and_args_full t in
           match uu___1 with
           | (hd, args) ->
               let uu___2 =
                 let uu___3 = FStarC_Syntax_Subst.compress hd in
                 uu___3.FStarC_Syntax_Syntax.n in
               (match uu___2 with
                | FStarC_Syntax_Syntax.Tm_name bv when
                    args_are_binders args bs ->
                    (if debug
                     then
                       (let uu___4 =
                          FStarC_Class_Show.show
                            FStarC_Syntax_Print.showable_term t in
                        let uu___5 =
                          FStarC_Class_Show.show
                            FStarC_Syntax_Print.showable_bv bv in
                        let uu___6 =
                          FStarC_Class_Show.show
                            FStarC_Syntax_Print.showable_term hd in
                        FStarC_Compiler_Util.print3
                          "WPE> got it\n>>>>top = %s\n>>>>b = %s\n>>>>hd = %s\n"
                          uu___4 uu___5 uu___6)
                     else ();
                     FStar_Pervasives_Native.Some bv)
                | uu___3 -> FStar_Pervasives_Native.None)) in
        let is_applied_maybe_squashed bs t =
          if debug
          then
            (let uu___1 =
               FStarC_Class_Show.show FStarC_Syntax_Print.showable_term t in
             let uu___2 =
               FStarC_Class_Tagged.tag_of FStarC_Syntax_Syntax.tagged_term t in
             FStarC_Compiler_Util.print2
               "WPE> is_applied_maybe_squashed %s -- %s\n" uu___1 uu___2)
          else ();
          (let uu___1 = FStarC_Syntax_Util.is_squash t in
           match uu___1 with
           | FStar_Pervasives_Native.Some (uu___2, t') -> is_applied bs t'
           | uu___2 ->
               let uu___3 = FStarC_Syntax_Util.is_auto_squash t in
               (match uu___3 with
                | FStar_Pervasives_Native.Some (uu___4, t') ->
                    is_applied bs t'
                | uu___4 -> is_applied bs t)) in
        let is_const_match phi =
          let uu___ =
            let uu___1 = FStarC_Syntax_Subst.compress phi in
            uu___1.FStarC_Syntax_Syntax.n in
          match uu___ with
          | FStarC_Syntax_Syntax.Tm_match
              { FStarC_Syntax_Syntax.scrutinee = uu___1;
                FStarC_Syntax_Syntax.ret_opt = uu___2;
                FStarC_Syntax_Syntax.brs = br::brs;
                FStarC_Syntax_Syntax.rc_opt1 = uu___3;_}
              ->
              let uu___4 = br in
              (match uu___4 with
               | (uu___5, uu___6, e) ->
                   let r =
                     let uu___7 = simp_t e in
                     match uu___7 with
                     | FStar_Pervasives_Native.None ->
                         FStar_Pervasives_Native.None
                     | FStar_Pervasives_Native.Some b ->
                         let uu___8 =
                           FStarC_Compiler_List.for_all
                             (fun uu___9 ->
                                match uu___9 with
                                | (uu___10, uu___11, e') ->
                                    let uu___12 = simp_t e' in
                                    uu___12 =
                                      (FStar_Pervasives_Native.Some b)) brs in
                         if uu___8
                         then FStar_Pervasives_Native.Some b
                         else FStar_Pervasives_Native.None in
                   r)
          | uu___1 -> FStar_Pervasives_Native.None in
        let maybe_auto_squash t =
          let uu___ = FStarC_Syntax_Util.is_sub_singleton t in
          if uu___
          then t
          else
            FStarC_Syntax_Util.mk_auto_squash FStarC_Syntax_Syntax.U_zero t in
        let squashed_head_un_auto_squash_args t =
          let maybe_un_auto_squash_arg uu___ =
            match uu___ with
            | (t1, q) ->
                let uu___1 = FStarC_Syntax_Util.is_auto_squash t1 in
                (match uu___1 with
                 | FStar_Pervasives_Native.Some
                     (FStarC_Syntax_Syntax.U_zero, t2) -> (t2, q)
                 | uu___2 -> (t1, q)) in
          let uu___ = FStarC_Syntax_Util.head_and_args t in
          match uu___ with
          | (head, args) ->
              let args1 =
                FStarC_Compiler_List.map maybe_un_auto_squash_arg args in
              FStarC_Syntax_Syntax.mk_Tm_app head args1
                t.FStarC_Syntax_Syntax.pos in
        let rec clearly_inhabited ty =
          let uu___ =
            let uu___1 = FStarC_Syntax_Util.unmeta ty in
            uu___1.FStarC_Syntax_Syntax.n in
          match uu___ with
          | FStarC_Syntax_Syntax.Tm_uinst (t, uu___1) -> clearly_inhabited t
          | FStarC_Syntax_Syntax.Tm_arrow
              { FStarC_Syntax_Syntax.bs1 = uu___1;
                FStarC_Syntax_Syntax.comp = c;_}
              -> clearly_inhabited (FStarC_Syntax_Util.comp_result c)
          | FStarC_Syntax_Syntax.Tm_fvar fv ->
              let l = FStarC_Syntax_Syntax.lid_of_fv fv in
              (((FStarC_Ident.lid_equals l FStarC_Parser_Const.int_lid) ||
                  (FStarC_Ident.lid_equals l FStarC_Parser_Const.bool_lid))
                 ||
                 (FStarC_Ident.lid_equals l FStarC_Parser_Const.string_lid))
                || (FStarC_Ident.lid_equals l FStarC_Parser_Const.exn_lid)
          | uu___1 -> false in
        let simplify1 arg =
          let uu___ = simp_t (FStar_Pervasives_Native.fst arg) in
          (uu___, arg) in
        let uu___ =
          let uu___1 = FStarC_Syntax_Subst.compress tm in
          uu___1.FStarC_Syntax_Syntax.n in
        match uu___ with
        | FStarC_Syntax_Syntax.Tm_app
            {
              FStarC_Syntax_Syntax.hd =
                {
                  FStarC_Syntax_Syntax.n = FStarC_Syntax_Syntax.Tm_uinst
                    ({
                       FStarC_Syntax_Syntax.n = FStarC_Syntax_Syntax.Tm_fvar
                         fv;
                       FStarC_Syntax_Syntax.pos = uu___1;
                       FStarC_Syntax_Syntax.vars = uu___2;
                       FStarC_Syntax_Syntax.hash_code = uu___3;_},
                     uu___4);
                  FStarC_Syntax_Syntax.pos = uu___5;
                  FStarC_Syntax_Syntax.vars = uu___6;
                  FStarC_Syntax_Syntax.hash_code = uu___7;_};
              FStarC_Syntax_Syntax.args = args;_}
            ->
            let uu___8 =
              FStarC_Syntax_Syntax.fv_eq_lid fv
                FStarC_Parser_Const.squash_lid in
            if uu___8
            then squashed_head_un_auto_squash_args tm
            else
              (let uu___10 =
                 FStarC_Syntax_Syntax.fv_eq_lid fv
                   FStarC_Parser_Const.and_lid in
               if uu___10
               then
                 let uu___11 = FStarC_Compiler_List.map simplify1 args in
                 match uu___11 with
                 | (FStar_Pervasives_Native.Some (true), uu___12)::(uu___13,
                                                                    (arg,
                                                                    uu___14))::[]
                     -> maybe_auto_squash arg
                 | (uu___12, (arg, uu___13))::(FStar_Pervasives_Native.Some
                                               (true), uu___14)::[]
                     -> maybe_auto_squash arg
                 | (FStar_Pervasives_Native.Some (false), uu___12)::uu___13::[]
                     -> w FStarC_Syntax_Util.t_false
                 | uu___12::(FStar_Pervasives_Native.Some (false), uu___13)::[]
                     -> w FStarC_Syntax_Util.t_false
                 | uu___12 -> squashed_head_un_auto_squash_args tm
               else
                 (let uu___12 =
                    FStarC_Syntax_Syntax.fv_eq_lid fv
                      FStarC_Parser_Const.or_lid in
                  if uu___12
                  then
                    let uu___13 = FStarC_Compiler_List.map simplify1 args in
                    match uu___13 with
                    | (FStar_Pervasives_Native.Some (true), uu___14)::uu___15::[]
                        -> w FStarC_Syntax_Util.t_true
                    | uu___14::(FStar_Pervasives_Native.Some (true), uu___15)::[]
                        -> w FStarC_Syntax_Util.t_true
                    | (FStar_Pervasives_Native.Some (false), uu___14)::
                        (uu___15, (arg, uu___16))::[] ->
                        maybe_auto_squash arg
                    | (uu___14, (arg, uu___15))::(FStar_Pervasives_Native.Some
                                                  (false), uu___16)::[]
                        -> maybe_auto_squash arg
                    | uu___14 -> squashed_head_un_auto_squash_args tm
                  else
                    (let uu___14 =
                       FStarC_Syntax_Syntax.fv_eq_lid fv
                         FStarC_Parser_Const.imp_lid in
                     if uu___14
                     then
                       let uu___15 = FStarC_Compiler_List.map simplify1 args in
                       match uu___15 with
                       | uu___16::(FStar_Pervasives_Native.Some (true),
                                   uu___17)::[]
                           -> w FStarC_Syntax_Util.t_true
                       | (FStar_Pervasives_Native.Some (false), uu___16)::uu___17::[]
                           -> w FStarC_Syntax_Util.t_true
                       | (FStar_Pervasives_Native.Some (true), uu___16)::
                           (uu___17, (arg, uu___18))::[] ->
                           maybe_auto_squash arg
                       | (uu___16, (p, uu___17))::(uu___18, (q, uu___19))::[]
                           ->
                           let uu___20 = FStarC_Syntax_Util.term_eq p q in
                           (if uu___20
                            then w FStarC_Syntax_Util.t_true
                            else squashed_head_un_auto_squash_args tm)
                       | uu___16 -> squashed_head_un_auto_squash_args tm
                     else
                       (let uu___16 =
                          FStarC_Syntax_Syntax.fv_eq_lid fv
                            FStarC_Parser_Const.iff_lid in
                        if uu___16
                        then
                          let uu___17 =
                            FStarC_Compiler_List.map simplify1 args in
                          match uu___17 with
                          | (FStar_Pervasives_Native.Some (true), uu___18)::
                              (FStar_Pervasives_Native.Some (true), uu___19)::[]
                              -> w FStarC_Syntax_Util.t_true
                          | (FStar_Pervasives_Native.Some (false), uu___18)::
                              (FStar_Pervasives_Native.Some (false), uu___19)::[]
                              -> w FStarC_Syntax_Util.t_true
                          | (FStar_Pervasives_Native.Some (true), uu___18)::
                              (FStar_Pervasives_Native.Some (false), uu___19)::[]
                              -> w FStarC_Syntax_Util.t_false
                          | (FStar_Pervasives_Native.Some (false), uu___18)::
                              (FStar_Pervasives_Native.Some (true), uu___19)::[]
                              -> w FStarC_Syntax_Util.t_false
                          | (uu___18, (arg, uu___19))::(FStar_Pervasives_Native.Some
                                                        (true), uu___20)::[]
                              -> maybe_auto_squash arg
                          | (FStar_Pervasives_Native.Some (true), uu___18)::
                              (uu___19, (arg, uu___20))::[] ->
                              maybe_auto_squash arg
                          | (uu___18, (arg, uu___19))::(FStar_Pervasives_Native.Some
                                                        (false), uu___20)::[]
                              ->
                              let uu___21 = FStarC_Syntax_Util.mk_neg arg in
                              maybe_auto_squash uu___21
                          | (FStar_Pervasives_Native.Some (false), uu___18)::
                              (uu___19, (arg, uu___20))::[] ->
                              let uu___21 = FStarC_Syntax_Util.mk_neg arg in
                              maybe_auto_squash uu___21
                          | (uu___18, (p, uu___19))::(uu___20, (q, uu___21))::[]
                              ->
                              let uu___22 = FStarC_Syntax_Util.term_eq p q in
                              (if uu___22
                               then w FStarC_Syntax_Util.t_true
                               else squashed_head_un_auto_squash_args tm)
                          | uu___18 -> squashed_head_un_auto_squash_args tm
                        else
                          (let uu___18 =
                             FStarC_Syntax_Syntax.fv_eq_lid fv
                               FStarC_Parser_Const.not_lid in
                           if uu___18
                           then
                             let uu___19 =
                               FStarC_Compiler_List.map simplify1 args in
                             match uu___19 with
                             | (FStar_Pervasives_Native.Some (true), uu___20)::[]
                                 -> w FStarC_Syntax_Util.t_false
                             | (FStar_Pervasives_Native.Some (false),
                                uu___20)::[] -> w FStarC_Syntax_Util.t_true
                             | uu___20 ->
                                 squashed_head_un_auto_squash_args tm
                           else
                             (let uu___20 =
                                FStarC_Syntax_Syntax.fv_eq_lid fv
                                  FStarC_Parser_Const.forall_lid in
                              if uu___20
                              then
                                match args with
                                | (t, uu___21)::[] ->
                                    let uu___22 =
                                      let uu___23 =
                                        FStarC_Syntax_Subst.compress t in
                                      uu___23.FStarC_Syntax_Syntax.n in
                                    (match uu___22 with
                                     | FStarC_Syntax_Syntax.Tm_abs
                                         {
                                           FStarC_Syntax_Syntax.bs =
                                             uu___23::[];
                                           FStarC_Syntax_Syntax.body = body;
                                           FStarC_Syntax_Syntax.rc_opt =
                                             uu___24;_}
                                         ->
                                         let uu___25 = simp_t body in
                                         (match uu___25 with
                                          | FStar_Pervasives_Native.Some
                                              (true) ->
                                              w FStarC_Syntax_Util.t_true
                                          | uu___26 -> tm)
                                     | uu___23 -> tm)
                                | (ty, FStar_Pervasives_Native.Some
                                   {
                                     FStarC_Syntax_Syntax.aqual_implicit =
                                       true;
                                     FStarC_Syntax_Syntax.aqual_attributes =
                                       uu___21;_})::(t, uu___22)::[]
                                    ->
                                    let uu___23 =
                                      let uu___24 =
                                        FStarC_Syntax_Subst.compress t in
                                      uu___24.FStarC_Syntax_Syntax.n in
                                    (match uu___23 with
                                     | FStarC_Syntax_Syntax.Tm_abs
                                         {
                                           FStarC_Syntax_Syntax.bs =
                                             uu___24::[];
                                           FStarC_Syntax_Syntax.body = body;
                                           FStarC_Syntax_Syntax.rc_opt =
                                             uu___25;_}
                                         ->
                                         let uu___26 = simp_t body in
                                         (match uu___26 with
                                          | FStar_Pervasives_Native.Some
                                              (true) ->
                                              w FStarC_Syntax_Util.t_true
                                          | FStar_Pervasives_Native.Some
                                              (false) when
                                              clearly_inhabited ty ->
                                              w FStarC_Syntax_Util.t_false
                                          | uu___27 -> tm)
                                     | uu___24 -> tm)
                                | uu___21 -> tm
                              else
                                (let uu___22 =
                                   FStarC_Syntax_Syntax.fv_eq_lid fv
                                     FStarC_Parser_Const.exists_lid in
                                 if uu___22
                                 then
                                   match args with
                                   | (t, uu___23)::[] ->
                                       let uu___24 =
                                         let uu___25 =
                                           FStarC_Syntax_Subst.compress t in
                                         uu___25.FStarC_Syntax_Syntax.n in
                                       (match uu___24 with
                                        | FStarC_Syntax_Syntax.Tm_abs
                                            {
                                              FStarC_Syntax_Syntax.bs =
                                                uu___25::[];
                                              FStarC_Syntax_Syntax.body =
                                                body;
                                              FStarC_Syntax_Syntax.rc_opt =
                                                uu___26;_}
                                            ->
                                            let uu___27 = simp_t body in
                                            (match uu___27 with
                                             | FStar_Pervasives_Native.Some
                                                 (false) ->
                                                 w FStarC_Syntax_Util.t_false
                                             | uu___28 -> tm)
                                        | uu___25 -> tm)
                                   | (ty, FStar_Pervasives_Native.Some
                                      {
                                        FStarC_Syntax_Syntax.aqual_implicit =
                                          true;
                                        FStarC_Syntax_Syntax.aqual_attributes
                                          = uu___23;_})::(t, uu___24)::[]
                                       ->
                                       let uu___25 =
                                         let uu___26 =
                                           FStarC_Syntax_Subst.compress t in
                                         uu___26.FStarC_Syntax_Syntax.n in
                                       (match uu___25 with
                                        | FStarC_Syntax_Syntax.Tm_abs
                                            {
                                              FStarC_Syntax_Syntax.bs =
                                                uu___26::[];
                                              FStarC_Syntax_Syntax.body =
                                                body;
                                              FStarC_Syntax_Syntax.rc_opt =
                                                uu___27;_}
                                            ->
                                            let uu___28 = simp_t body in
                                            (match uu___28 with
                                             | FStar_Pervasives_Native.Some
                                                 (false) ->
                                                 w FStarC_Syntax_Util.t_false
                                             | FStar_Pervasives_Native.Some
                                                 (true) when
                                                 clearly_inhabited ty ->
                                                 w FStarC_Syntax_Util.t_true
                                             | uu___29 -> tm)
                                        | uu___26 -> tm)
                                   | uu___23 -> tm
                                 else
                                   (let uu___24 =
                                      FStarC_Syntax_Syntax.fv_eq_lid fv
                                        FStarC_Parser_Const.b2t_lid in
                                    if uu___24
                                    then
                                      match args with
                                      | ({
                                           FStarC_Syntax_Syntax.n =
                                             FStarC_Syntax_Syntax.Tm_constant
                                             (FStarC_Const.Const_bool (true));
                                           FStarC_Syntax_Syntax.pos = uu___25;
                                           FStarC_Syntax_Syntax.vars =
                                             uu___26;
                                           FStarC_Syntax_Syntax.hash_code =
                                             uu___27;_},
                                         uu___28)::[] ->
                                          w FStarC_Syntax_Util.t_true
                                      | ({
                                           FStarC_Syntax_Syntax.n =
                                             FStarC_Syntax_Syntax.Tm_constant
                                             (FStarC_Const.Const_bool
                                             (false));
                                           FStarC_Syntax_Syntax.pos = uu___25;
                                           FStarC_Syntax_Syntax.vars =
                                             uu___26;
                                           FStarC_Syntax_Syntax.hash_code =
                                             uu___27;_},
                                         uu___28)::[] ->
                                          w FStarC_Syntax_Util.t_false
                                      | uu___25 -> tm
                                    else
                                      (let uu___26 =
                                         FStarC_Syntax_Syntax.fv_eq_lid fv
                                           FStarC_Parser_Const.haseq_lid in
                                       if uu___26
                                       then
                                         let t_has_eq_for_sure t =
                                           let haseq_lids =
                                             [FStarC_Parser_Const.int_lid;
                                             FStarC_Parser_Const.bool_lid;
                                             FStarC_Parser_Const.unit_lid;
                                             FStarC_Parser_Const.string_lid] in
                                           let uu___27 =
                                             let uu___28 =
                                               FStarC_Syntax_Subst.compress t in
                                             uu___28.FStarC_Syntax_Syntax.n in
                                           match uu___27 with
                                           | FStarC_Syntax_Syntax.Tm_fvar fv1
                                               when
                                               FStarC_Compiler_List.existsb
                                                 (fun l ->
                                                    FStarC_Syntax_Syntax.fv_eq_lid
                                                      fv1 l) haseq_lids
                                               -> true
                                           | uu___28 -> false in
                                         (if
                                            (FStarC_Compiler_List.length args)
                                              = Prims.int_one
                                          then
                                            let t =
                                              let uu___27 =
                                                FStarC_Compiler_List.hd args in
                                              FStar_Pervasives_Native.fst
                                                uu___27 in
                                            let uu___27 = t_has_eq_for_sure t in
                                            (if uu___27
                                             then w FStarC_Syntax_Util.t_true
                                             else
                                               (let uu___29 =
                                                  let uu___30 =
                                                    FStarC_Syntax_Subst.compress
                                                      t in
                                                  uu___30.FStarC_Syntax_Syntax.n in
                                                match uu___29 with
                                                | FStarC_Syntax_Syntax.Tm_refine
                                                    uu___30 ->
                                                    let t1 =
                                                      FStarC_Syntax_Util.unrefine
                                                        t in
                                                    let uu___31 =
                                                      t_has_eq_for_sure t1 in
                                                    if uu___31
                                                    then
                                                      w
                                                        FStarC_Syntax_Util.t_true
                                                    else
                                                      (let haseq_tm =
                                                         let uu___33 =
                                                           let uu___34 =
                                                             FStarC_Syntax_Subst.compress
                                                               tm in
                                                           uu___34.FStarC_Syntax_Syntax.n in
                                                         match uu___33 with
                                                         | FStarC_Syntax_Syntax.Tm_app
                                                             {
                                                               FStarC_Syntax_Syntax.hd
                                                                 = hd;
                                                               FStarC_Syntax_Syntax.args
                                                                 = uu___34;_}
                                                             -> hd
                                                         | uu___34 ->
                                                             failwith
                                                               "Impossible! We have already checked that this is a Tm_app" in
                                                       let uu___33 =
                                                         let uu___34 =
                                                           FStarC_Syntax_Syntax.as_arg
                                                             t1 in
                                                         [uu___34] in
                                                       FStarC_Syntax_Util.mk_app
                                                         haseq_tm uu___33)
                                                | uu___30 -> tm))
                                          else tm)
                                       else
                                         (let uu___28 =
                                            FStarC_Syntax_Syntax.fv_eq_lid fv
                                              FStarC_Parser_Const.eq2_lid in
                                          if uu___28
                                          then
                                            match args with
                                            | (_typ, uu___29)::(a1, uu___30)::
                                                (a2, uu___31)::[] ->
                                                let uu___32 = eq_tm env a1 a2 in
                                                (match uu___32 with
                                                 | Equal ->
                                                     w
                                                       FStarC_Syntax_Util.t_true
                                                 | NotEqual ->
                                                     w
                                                       FStarC_Syntax_Util.t_false
                                                 | uu___33 -> tm)
                                            | uu___29 -> tm
                                          else
                                            (let uu___30 =
                                               FStarC_Syntax_Util.is_auto_squash
                                                 tm in
                                             match uu___30 with
                                             | FStar_Pervasives_Native.Some
                                                 (FStarC_Syntax_Syntax.U_zero,
                                                  t)
                                                 when
                                                 FStarC_Syntax_Util.is_sub_singleton
                                                   t
                                                 -> t
                                             | uu___31 -> tm)))))))))))
        | FStarC_Syntax_Syntax.Tm_app
            {
              FStarC_Syntax_Syntax.hd =
                { FStarC_Syntax_Syntax.n = FStarC_Syntax_Syntax.Tm_fvar fv;
                  FStarC_Syntax_Syntax.pos = uu___1;
                  FStarC_Syntax_Syntax.vars = uu___2;
                  FStarC_Syntax_Syntax.hash_code = uu___3;_};
              FStarC_Syntax_Syntax.args = args;_}
            ->
            let uu___4 =
              FStarC_Syntax_Syntax.fv_eq_lid fv
                FStarC_Parser_Const.squash_lid in
            if uu___4
            then squashed_head_un_auto_squash_args tm
            else
              (let uu___6 =
                 FStarC_Syntax_Syntax.fv_eq_lid fv
                   FStarC_Parser_Const.and_lid in
               if uu___6
               then
                 let uu___7 = FStarC_Compiler_List.map simplify1 args in
                 match uu___7 with
                 | (FStar_Pervasives_Native.Some (true), uu___8)::(uu___9,
                                                                   (arg,
                                                                    uu___10))::[]
                     -> maybe_auto_squash arg
                 | (uu___8, (arg, uu___9))::(FStar_Pervasives_Native.Some
                                             (true), uu___10)::[]
                     -> maybe_auto_squash arg
                 | (FStar_Pervasives_Native.Some (false), uu___8)::uu___9::[]
                     -> w FStarC_Syntax_Util.t_false
                 | uu___8::(FStar_Pervasives_Native.Some (false), uu___9)::[]
                     -> w FStarC_Syntax_Util.t_false
                 | uu___8 -> squashed_head_un_auto_squash_args tm
               else
                 (let uu___8 =
                    FStarC_Syntax_Syntax.fv_eq_lid fv
                      FStarC_Parser_Const.or_lid in
                  if uu___8
                  then
                    let uu___9 = FStarC_Compiler_List.map simplify1 args in
                    match uu___9 with
                    | (FStar_Pervasives_Native.Some (true), uu___10)::uu___11::[]
                        -> w FStarC_Syntax_Util.t_true
                    | uu___10::(FStar_Pervasives_Native.Some (true), uu___11)::[]
                        -> w FStarC_Syntax_Util.t_true
                    | (FStar_Pervasives_Native.Some (false), uu___10)::
                        (uu___11, (arg, uu___12))::[] ->
                        maybe_auto_squash arg
                    | (uu___10, (arg, uu___11))::(FStar_Pervasives_Native.Some
                                                  (false), uu___12)::[]
                        -> maybe_auto_squash arg
                    | uu___10 -> squashed_head_un_auto_squash_args tm
                  else
                    (let uu___10 =
                       FStarC_Syntax_Syntax.fv_eq_lid fv
                         FStarC_Parser_Const.imp_lid in
                     if uu___10
                     then
                       let uu___11 = FStarC_Compiler_List.map simplify1 args in
                       match uu___11 with
                       | uu___12::(FStar_Pervasives_Native.Some (true),
                                   uu___13)::[]
                           -> w FStarC_Syntax_Util.t_true
                       | (FStar_Pervasives_Native.Some (false), uu___12)::uu___13::[]
                           -> w FStarC_Syntax_Util.t_true
                       | (FStar_Pervasives_Native.Some (true), uu___12)::
                           (uu___13, (arg, uu___14))::[] ->
                           maybe_auto_squash arg
                       | (uu___12, (p, uu___13))::(uu___14, (q, uu___15))::[]
                           ->
                           let uu___16 = FStarC_Syntax_Util.term_eq p q in
                           (if uu___16
                            then w FStarC_Syntax_Util.t_true
                            else squashed_head_un_auto_squash_args tm)
                       | uu___12 -> squashed_head_un_auto_squash_args tm
                     else
                       (let uu___12 =
                          FStarC_Syntax_Syntax.fv_eq_lid fv
                            FStarC_Parser_Const.iff_lid in
                        if uu___12
                        then
                          let uu___13 =
                            FStarC_Compiler_List.map simplify1 args in
                          match uu___13 with
                          | (FStar_Pervasives_Native.Some (true), uu___14)::
                              (FStar_Pervasives_Native.Some (true), uu___15)::[]
                              -> w FStarC_Syntax_Util.t_true
                          | (FStar_Pervasives_Native.Some (false), uu___14)::
                              (FStar_Pervasives_Native.Some (false), uu___15)::[]
                              -> w FStarC_Syntax_Util.t_true
                          | (FStar_Pervasives_Native.Some (true), uu___14)::
                              (FStar_Pervasives_Native.Some (false), uu___15)::[]
                              -> w FStarC_Syntax_Util.t_false
                          | (FStar_Pervasives_Native.Some (false), uu___14)::
                              (FStar_Pervasives_Native.Some (true), uu___15)::[]
                              -> w FStarC_Syntax_Util.t_false
                          | (uu___14, (arg, uu___15))::(FStar_Pervasives_Native.Some
                                                        (true), uu___16)::[]
                              -> maybe_auto_squash arg
                          | (FStar_Pervasives_Native.Some (true), uu___14)::
                              (uu___15, (arg, uu___16))::[] ->
                              maybe_auto_squash arg
                          | (uu___14, (arg, uu___15))::(FStar_Pervasives_Native.Some
                                                        (false), uu___16)::[]
                              ->
                              let uu___17 = FStarC_Syntax_Util.mk_neg arg in
                              maybe_auto_squash uu___17
                          | (FStar_Pervasives_Native.Some (false), uu___14)::
                              (uu___15, (arg, uu___16))::[] ->
                              let uu___17 = FStarC_Syntax_Util.mk_neg arg in
                              maybe_auto_squash uu___17
                          | (uu___14, (p, uu___15))::(uu___16, (q, uu___17))::[]
                              ->
                              let uu___18 = FStarC_Syntax_Util.term_eq p q in
                              (if uu___18
                               then w FStarC_Syntax_Util.t_true
                               else squashed_head_un_auto_squash_args tm)
                          | uu___14 -> squashed_head_un_auto_squash_args tm
                        else
                          (let uu___14 =
                             FStarC_Syntax_Syntax.fv_eq_lid fv
                               FStarC_Parser_Const.not_lid in
                           if uu___14
                           then
                             let uu___15 =
                               FStarC_Compiler_List.map simplify1 args in
                             match uu___15 with
                             | (FStar_Pervasives_Native.Some (true), uu___16)::[]
                                 -> w FStarC_Syntax_Util.t_false
                             | (FStar_Pervasives_Native.Some (false),
                                uu___16)::[] -> w FStarC_Syntax_Util.t_true
                             | uu___16 ->
                                 squashed_head_un_auto_squash_args tm
                           else
                             (let uu___16 =
                                FStarC_Syntax_Syntax.fv_eq_lid fv
                                  FStarC_Parser_Const.forall_lid in
                              if uu___16
                              then
                                match args with
                                | (t, uu___17)::[] ->
                                    let uu___18 =
                                      let uu___19 =
                                        FStarC_Syntax_Subst.compress t in
                                      uu___19.FStarC_Syntax_Syntax.n in
                                    (match uu___18 with
                                     | FStarC_Syntax_Syntax.Tm_abs
                                         {
                                           FStarC_Syntax_Syntax.bs =
                                             uu___19::[];
                                           FStarC_Syntax_Syntax.body = body;
                                           FStarC_Syntax_Syntax.rc_opt =
                                             uu___20;_}
                                         ->
                                         let uu___21 = simp_t body in
                                         (match uu___21 with
                                          | FStar_Pervasives_Native.Some
                                              (true) ->
                                              w FStarC_Syntax_Util.t_true
                                          | uu___22 -> tm)
                                     | uu___19 -> tm)
                                | (ty, FStar_Pervasives_Native.Some
                                   {
                                     FStarC_Syntax_Syntax.aqual_implicit =
                                       true;
                                     FStarC_Syntax_Syntax.aqual_attributes =
                                       uu___17;_})::(t, uu___18)::[]
                                    ->
                                    let uu___19 =
                                      let uu___20 =
                                        FStarC_Syntax_Subst.compress t in
                                      uu___20.FStarC_Syntax_Syntax.n in
                                    (match uu___19 with
                                     | FStarC_Syntax_Syntax.Tm_abs
                                         {
                                           FStarC_Syntax_Syntax.bs =
                                             uu___20::[];
                                           FStarC_Syntax_Syntax.body = body;
                                           FStarC_Syntax_Syntax.rc_opt =
                                             uu___21;_}
                                         ->
                                         let uu___22 = simp_t body in
                                         (match uu___22 with
                                          | FStar_Pervasives_Native.Some
                                              (true) ->
                                              w FStarC_Syntax_Util.t_true
                                          | FStar_Pervasives_Native.Some
                                              (false) when
                                              clearly_inhabited ty ->
                                              w FStarC_Syntax_Util.t_false
                                          | uu___23 -> tm)
                                     | uu___20 -> tm)
                                | uu___17 -> tm
                              else
                                (let uu___18 =
                                   FStarC_Syntax_Syntax.fv_eq_lid fv
                                     FStarC_Parser_Const.exists_lid in
                                 if uu___18
                                 then
                                   match args with
                                   | (t, uu___19)::[] ->
                                       let uu___20 =
                                         let uu___21 =
                                           FStarC_Syntax_Subst.compress t in
                                         uu___21.FStarC_Syntax_Syntax.n in
                                       (match uu___20 with
                                        | FStarC_Syntax_Syntax.Tm_abs
                                            {
                                              FStarC_Syntax_Syntax.bs =
                                                uu___21::[];
                                              FStarC_Syntax_Syntax.body =
                                                body;
                                              FStarC_Syntax_Syntax.rc_opt =
                                                uu___22;_}
                                            ->
                                            let uu___23 = simp_t body in
                                            (match uu___23 with
                                             | FStar_Pervasives_Native.Some
                                                 (false) ->
                                                 w FStarC_Syntax_Util.t_false
                                             | uu___24 -> tm)
                                        | uu___21 -> tm)
                                   | (ty, FStar_Pervasives_Native.Some
                                      {
                                        FStarC_Syntax_Syntax.aqual_implicit =
                                          true;
                                        FStarC_Syntax_Syntax.aqual_attributes
                                          = uu___19;_})::(t, uu___20)::[]
                                       ->
                                       let uu___21 =
                                         let uu___22 =
                                           FStarC_Syntax_Subst.compress t in
                                         uu___22.FStarC_Syntax_Syntax.n in
                                       (match uu___21 with
                                        | FStarC_Syntax_Syntax.Tm_abs
                                            {
                                              FStarC_Syntax_Syntax.bs =
                                                uu___22::[];
                                              FStarC_Syntax_Syntax.body =
                                                body;
                                              FStarC_Syntax_Syntax.rc_opt =
                                                uu___23;_}
                                            ->
                                            let uu___24 = simp_t body in
                                            (match uu___24 with
                                             | FStar_Pervasives_Native.Some
                                                 (false) ->
                                                 w FStarC_Syntax_Util.t_false
                                             | FStar_Pervasives_Native.Some
                                                 (true) when
                                                 clearly_inhabited ty ->
                                                 w FStarC_Syntax_Util.t_true
                                             | uu___25 -> tm)
                                        | uu___22 -> tm)
                                   | uu___19 -> tm
                                 else
                                   (let uu___20 =
                                      FStarC_Syntax_Syntax.fv_eq_lid fv
                                        FStarC_Parser_Const.b2t_lid in
                                    if uu___20
                                    then
                                      match args with
                                      | ({
                                           FStarC_Syntax_Syntax.n =
                                             FStarC_Syntax_Syntax.Tm_constant
                                             (FStarC_Const.Const_bool (true));
                                           FStarC_Syntax_Syntax.pos = uu___21;
                                           FStarC_Syntax_Syntax.vars =
                                             uu___22;
                                           FStarC_Syntax_Syntax.hash_code =
                                             uu___23;_},
                                         uu___24)::[] ->
                                          w FStarC_Syntax_Util.t_true
                                      | ({
                                           FStarC_Syntax_Syntax.n =
                                             FStarC_Syntax_Syntax.Tm_constant
                                             (FStarC_Const.Const_bool
                                             (false));
                                           FStarC_Syntax_Syntax.pos = uu___21;
                                           FStarC_Syntax_Syntax.vars =
                                             uu___22;
                                           FStarC_Syntax_Syntax.hash_code =
                                             uu___23;_},
                                         uu___24)::[] ->
                                          w FStarC_Syntax_Util.t_false
                                      | uu___21 -> tm
                                    else
                                      (let uu___22 =
                                         FStarC_Syntax_Syntax.fv_eq_lid fv
                                           FStarC_Parser_Const.haseq_lid in
                                       if uu___22
                                       then
                                         let t_has_eq_for_sure t =
                                           let haseq_lids =
                                             [FStarC_Parser_Const.int_lid;
                                             FStarC_Parser_Const.bool_lid;
                                             FStarC_Parser_Const.unit_lid;
                                             FStarC_Parser_Const.string_lid] in
                                           let uu___23 =
                                             let uu___24 =
                                               FStarC_Syntax_Subst.compress t in
                                             uu___24.FStarC_Syntax_Syntax.n in
                                           match uu___23 with
                                           | FStarC_Syntax_Syntax.Tm_fvar fv1
                                               when
                                               FStarC_Compiler_List.existsb
                                                 (fun l ->
                                                    FStarC_Syntax_Syntax.fv_eq_lid
                                                      fv1 l) haseq_lids
                                               -> true
                                           | uu___24 -> false in
                                         (if
                                            (FStarC_Compiler_List.length args)
                                              = Prims.int_one
                                          then
                                            let t =
                                              let uu___23 =
                                                FStarC_Compiler_List.hd args in
                                              FStar_Pervasives_Native.fst
                                                uu___23 in
                                            let uu___23 = t_has_eq_for_sure t in
                                            (if uu___23
                                             then w FStarC_Syntax_Util.t_true
                                             else
                                               (let uu___25 =
                                                  let uu___26 =
                                                    FStarC_Syntax_Subst.compress
                                                      t in
                                                  uu___26.FStarC_Syntax_Syntax.n in
                                                match uu___25 with
                                                | FStarC_Syntax_Syntax.Tm_refine
                                                    uu___26 ->
                                                    let t1 =
                                                      FStarC_Syntax_Util.unrefine
                                                        t in
                                                    let uu___27 =
                                                      t_has_eq_for_sure t1 in
                                                    if uu___27
                                                    then
                                                      w
                                                        FStarC_Syntax_Util.t_true
                                                    else
                                                      (let haseq_tm =
                                                         let uu___29 =
                                                           let uu___30 =
                                                             FStarC_Syntax_Subst.compress
                                                               tm in
                                                           uu___30.FStarC_Syntax_Syntax.n in
                                                         match uu___29 with
                                                         | FStarC_Syntax_Syntax.Tm_app
                                                             {
                                                               FStarC_Syntax_Syntax.hd
                                                                 = hd;
                                                               FStarC_Syntax_Syntax.args
                                                                 = uu___30;_}
                                                             -> hd
                                                         | uu___30 ->
                                                             failwith
                                                               "Impossible! We have already checked that this is a Tm_app" in
                                                       let uu___29 =
                                                         let uu___30 =
                                                           FStarC_Syntax_Syntax.as_arg
                                                             t1 in
                                                         [uu___30] in
                                                       FStarC_Syntax_Util.mk_app
                                                         haseq_tm uu___29)
                                                | uu___26 -> tm))
                                          else tm)
                                       else
                                         (let uu___24 =
                                            FStarC_Syntax_Syntax.fv_eq_lid fv
                                              FStarC_Parser_Const.eq2_lid in
                                          if uu___24
                                          then
                                            match args with
                                            | (_typ, uu___25)::(a1, uu___26)::
                                                (a2, uu___27)::[] ->
                                                let uu___28 = eq_tm env a1 a2 in
                                                (match uu___28 with
                                                 | Equal ->
                                                     w
                                                       FStarC_Syntax_Util.t_true
                                                 | NotEqual ->
                                                     w
                                                       FStarC_Syntax_Util.t_false
                                                 | uu___29 -> tm)
                                            | uu___25 -> tm
                                          else
                                            (let uu___26 =
                                               FStarC_Syntax_Util.is_auto_squash
                                                 tm in
                                             match uu___26 with
                                             | FStar_Pervasives_Native.Some
                                                 (FStarC_Syntax_Syntax.U_zero,
                                                  t)
                                                 when
                                                 FStarC_Syntax_Util.is_sub_singleton
                                                   t
                                                 -> t
                                             | uu___27 -> tm)))))))))))
        | FStarC_Syntax_Syntax.Tm_refine
            { FStarC_Syntax_Syntax.b = bv; FStarC_Syntax_Syntax.phi = t;_} ->
            let uu___1 = simp_t t in
            (match uu___1 with
             | FStar_Pervasives_Native.Some (true) ->
                 bv.FStarC_Syntax_Syntax.sort
             | FStar_Pervasives_Native.Some (false) -> tm
             | FStar_Pervasives_Native.None -> tm)
        | FStarC_Syntax_Syntax.Tm_match uu___1 ->
            let uu___2 = is_const_match tm in
            (match uu___2 with
             | FStar_Pervasives_Native.Some (true) ->
                 w FStarC_Syntax_Util.t_true
             | FStar_Pervasives_Native.Some (false) ->
                 w FStarC_Syntax_Util.t_false
             | FStar_Pervasives_Native.None -> tm)
        | uu___1 -> tm