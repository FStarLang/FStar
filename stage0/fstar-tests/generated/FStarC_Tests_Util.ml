open Prims
let (always : Prims.int -> Prims.bool -> unit) =
  fun id ->
    fun b ->
      if b
      then ()
      else
        (let uu___1 =
           let uu___2 = FStarC_Compiler_Util.string_of_int id in
           FStarC_Compiler_Util.format1 "Assertion failed: test %s" uu___2 in
         FStarC_Errors.raise_error0
           FStarC_Errors_Codes.Fatal_AssertionFailure ()
           (Obj.magic FStarC_Errors_Msg.is_error_message_string)
           (Obj.magic uu___1))
let (x : FStarC_Syntax_Syntax.bv) =
  FStarC_Syntax_Syntax.gen_bv "x" FStar_Pervasives_Native.None
    FStarC_Syntax_Syntax.tun
let (y : FStarC_Syntax_Syntax.bv) =
  FStarC_Syntax_Syntax.gen_bv "y" FStar_Pervasives_Native.None
    FStarC_Syntax_Syntax.tun
let (n : FStarC_Syntax_Syntax.bv) =
  FStarC_Syntax_Syntax.gen_bv "n" FStar_Pervasives_Native.None
    FStarC_Syntax_Syntax.tun
let (h : FStarC_Syntax_Syntax.bv) =
  FStarC_Syntax_Syntax.gen_bv "h" FStar_Pervasives_Native.None
    FStarC_Syntax_Syntax.tun
let (m : FStarC_Syntax_Syntax.bv) =
  FStarC_Syntax_Syntax.gen_bv "m" FStar_Pervasives_Native.None
    FStarC_Syntax_Syntax.tun
let tm : 'uuuuu . 'uuuuu -> 'uuuuu FStarC_Syntax_Syntax.syntax =
  fun t -> FStarC_Syntax_Syntax.mk t FStarC_Compiler_Range_Type.dummyRange
let (nm : FStarC_Syntax_Syntax.bv -> FStarC_Syntax_Syntax.term) =
  fun x1 -> FStarC_Syntax_Syntax.bv_to_name x1
let (app :
  FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax ->
    FStarC_Syntax_Syntax.term Prims.list ->
      FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax)
  =
  fun x1 ->
    fun ts ->
      let uu___ =
        let uu___1 =
          let uu___2 =
            FStarC_Compiler_List.map FStarC_Syntax_Syntax.as_arg ts in
          { FStarC_Syntax_Syntax.hd = x1; FStarC_Syntax_Syntax.args = uu___2
          } in
        FStarC_Syntax_Syntax.Tm_app uu___1 in
      FStarC_Syntax_Syntax.mk uu___ FStarC_Compiler_Range_Type.dummyRange
let rec (term_eq' :
  FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax ->
    FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax -> Prims.bool)
  =
  fun t1 ->
    fun t2 ->
      let t11 = FStarC_Syntax_Subst.compress t1 in
      let t21 = FStarC_Syntax_Subst.compress t2 in
      let binders_eq xs ys =
        ((FStarC_Compiler_List.length xs) = (FStarC_Compiler_List.length ys))
          &&
          (FStarC_Compiler_List.forall2
             (fun x1 ->
                fun y1 ->
                  term_eq'
                    (x1.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort
                    (y1.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort)
             xs ys) in
      let args_eq xs ys =
        ((FStarC_Compiler_List.length xs) = (FStarC_Compiler_List.length ys))
          &&
          (FStarC_Compiler_List.forall2
             (fun uu___ ->
                fun uu___1 ->
                  match (uu___, uu___1) with
                  | ((a, imp), (b, imp')) ->
                      (term_eq' a b) &&
                        (FStarC_Syntax_Util.eq_aqual imp imp')) xs ys) in
      let comp_eq c d =
        match ((c.FStarC_Syntax_Syntax.n), (d.FStarC_Syntax_Syntax.n)) with
        | (FStarC_Syntax_Syntax.Total t, FStarC_Syntax_Syntax.Total s) ->
            term_eq' t s
        | (FStarC_Syntax_Syntax.Comp ct1, FStarC_Syntax_Syntax.Comp ct2) ->
            ((FStarC_Ident.lid_equals ct1.FStarC_Syntax_Syntax.effect_name
                ct2.FStarC_Syntax_Syntax.effect_name)
               &&
               (term_eq' ct1.FStarC_Syntax_Syntax.result_typ
                  ct2.FStarC_Syntax_Syntax.result_typ))
              &&
              (args_eq ct1.FStarC_Syntax_Syntax.effect_args
                 ct2.FStarC_Syntax_Syntax.effect_args)
        | uu___ -> false in
      match ((t11.FStarC_Syntax_Syntax.n), (t21.FStarC_Syntax_Syntax.n)) with
      | (FStarC_Syntax_Syntax.Tm_lazy l, uu___) ->
          let uu___1 =
            let uu___2 =
              let uu___3 =
                FStarC_Compiler_Effect.op_Bang
                  FStarC_Syntax_Syntax.lazy_chooser in
              FStarC_Compiler_Util.must uu___3 in
            uu___2 l.FStarC_Syntax_Syntax.lkind l in
          term_eq' uu___1 t21
      | (uu___, FStarC_Syntax_Syntax.Tm_lazy l) ->
          let uu___1 =
            let uu___2 =
              let uu___3 =
                FStarC_Compiler_Effect.op_Bang
                  FStarC_Syntax_Syntax.lazy_chooser in
              FStarC_Compiler_Util.must uu___3 in
            uu___2 l.FStarC_Syntax_Syntax.lkind l in
          term_eq' t11 uu___1
      | (FStarC_Syntax_Syntax.Tm_bvar x1, FStarC_Syntax_Syntax.Tm_bvar y1) ->
          x1.FStarC_Syntax_Syntax.index = y1.FStarC_Syntax_Syntax.index
      | (FStarC_Syntax_Syntax.Tm_name x1, FStarC_Syntax_Syntax.Tm_name y1) ->
          FStarC_Syntax_Syntax.bv_eq x1 y1
      | (FStarC_Syntax_Syntax.Tm_fvar f, FStarC_Syntax_Syntax.Tm_fvar g) ->
          FStarC_Syntax_Syntax.fv_eq f g
      | (FStarC_Syntax_Syntax.Tm_uinst (t, uu___),
         FStarC_Syntax_Syntax.Tm_uinst (s, uu___1)) -> term_eq' t s
      | (FStarC_Syntax_Syntax.Tm_constant c1,
         FStarC_Syntax_Syntax.Tm_constant c2) -> FStarC_Const.eq_const c1 c2
      | (FStarC_Syntax_Syntax.Tm_type u, FStarC_Syntax_Syntax.Tm_type v) ->
          u = v
      | (FStarC_Syntax_Syntax.Tm_abs
         { FStarC_Syntax_Syntax.bs = xs; FStarC_Syntax_Syntax.body = t;
           FStarC_Syntax_Syntax.rc_opt = uu___;_},
         FStarC_Syntax_Syntax.Tm_abs
         { FStarC_Syntax_Syntax.bs = ys; FStarC_Syntax_Syntax.body = u;
           FStarC_Syntax_Syntax.rc_opt = uu___1;_})
          when
          (FStarC_Compiler_List.length xs) = (FStarC_Compiler_List.length ys)
          -> (binders_eq xs ys) && (term_eq' t u)
      | (FStarC_Syntax_Syntax.Tm_abs
         { FStarC_Syntax_Syntax.bs = xs; FStarC_Syntax_Syntax.body = t;
           FStarC_Syntax_Syntax.rc_opt = uu___;_},
         FStarC_Syntax_Syntax.Tm_abs
         { FStarC_Syntax_Syntax.bs = ys; FStarC_Syntax_Syntax.body = u;
           FStarC_Syntax_Syntax.rc_opt = uu___1;_})
          ->
          if
            (FStarC_Compiler_List.length xs) >
              (FStarC_Compiler_List.length ys)
          then
            let uu___2 =
              FStarC_Compiler_Util.first_N (FStarC_Compiler_List.length ys)
                xs in
            (match uu___2 with
             | (xs1, xs') ->
                 let t12 =
                   let uu___3 =
                     let uu___4 =
                       let uu___5 =
                         FStarC_Syntax_Syntax.mk
                           (FStarC_Syntax_Syntax.Tm_abs
                              {
                                FStarC_Syntax_Syntax.bs = xs';
                                FStarC_Syntax_Syntax.body = t;
                                FStarC_Syntax_Syntax.rc_opt =
                                  FStar_Pervasives_Native.None
                              }) t11.FStarC_Syntax_Syntax.pos in
                       {
                         FStarC_Syntax_Syntax.bs = xs1;
                         FStarC_Syntax_Syntax.body = uu___5;
                         FStarC_Syntax_Syntax.rc_opt =
                           FStar_Pervasives_Native.None
                       } in
                     FStarC_Syntax_Syntax.Tm_abs uu___4 in
                   FStarC_Syntax_Syntax.mk uu___3
                     t11.FStarC_Syntax_Syntax.pos in
                 term_eq' t12 t21)
          else
            (let uu___3 =
               FStarC_Compiler_Util.first_N (FStarC_Compiler_List.length xs)
                 ys in
             match uu___3 with
             | (ys1, ys') ->
                 let t22 =
                   let uu___4 =
                     let uu___5 =
                       let uu___6 =
                         FStarC_Syntax_Syntax.mk
                           (FStarC_Syntax_Syntax.Tm_abs
                              {
                                FStarC_Syntax_Syntax.bs = ys';
                                FStarC_Syntax_Syntax.body = u;
                                FStarC_Syntax_Syntax.rc_opt =
                                  FStar_Pervasives_Native.None
                              }) t21.FStarC_Syntax_Syntax.pos in
                       {
                         FStarC_Syntax_Syntax.bs = ys1;
                         FStarC_Syntax_Syntax.body = uu___6;
                         FStarC_Syntax_Syntax.rc_opt =
                           FStar_Pervasives_Native.None
                       } in
                     FStarC_Syntax_Syntax.Tm_abs uu___5 in
                   FStarC_Syntax_Syntax.mk uu___4
                     t21.FStarC_Syntax_Syntax.pos in
                 term_eq' t11 t22)
      | (FStarC_Syntax_Syntax.Tm_arrow
         { FStarC_Syntax_Syntax.bs1 = xs; FStarC_Syntax_Syntax.comp = c;_},
         FStarC_Syntax_Syntax.Tm_arrow
         { FStarC_Syntax_Syntax.bs1 = ys; FStarC_Syntax_Syntax.comp = d;_})
          -> (binders_eq xs ys) && (comp_eq c d)
      | (FStarC_Syntax_Syntax.Tm_refine
         { FStarC_Syntax_Syntax.b = x1; FStarC_Syntax_Syntax.phi = t;_},
         FStarC_Syntax_Syntax.Tm_refine
         { FStarC_Syntax_Syntax.b = y1; FStarC_Syntax_Syntax.phi = u;_}) ->
          (term_eq' x1.FStarC_Syntax_Syntax.sort y1.FStarC_Syntax_Syntax.sort)
            && (term_eq' t u)
      | (FStarC_Syntax_Syntax.Tm_app
         {
           FStarC_Syntax_Syntax.hd =
             { FStarC_Syntax_Syntax.n = FStarC_Syntax_Syntax.Tm_fvar fv_eq_1;
               FStarC_Syntax_Syntax.pos = uu___;
               FStarC_Syntax_Syntax.vars = uu___1;
               FStarC_Syntax_Syntax.hash_code = uu___2;_};
           FStarC_Syntax_Syntax.args =
             (uu___3, FStar_Pervasives_Native.Some
              { FStarC_Syntax_Syntax.aqual_implicit = true;
                FStarC_Syntax_Syntax.aqual_attributes = uu___4;_})::t12::t22::[];_},
         FStarC_Syntax_Syntax.Tm_app
         {
           FStarC_Syntax_Syntax.hd =
             { FStarC_Syntax_Syntax.n = FStarC_Syntax_Syntax.Tm_fvar fv_eq_2;
               FStarC_Syntax_Syntax.pos = uu___5;
               FStarC_Syntax_Syntax.vars = uu___6;
               FStarC_Syntax_Syntax.hash_code = uu___7;_};
           FStarC_Syntax_Syntax.args =
             (uu___8, FStar_Pervasives_Native.Some
              { FStarC_Syntax_Syntax.aqual_implicit = true;
                FStarC_Syntax_Syntax.aqual_attributes = uu___9;_})::s1::s2::[];_})
          when
          (FStarC_Syntax_Syntax.fv_eq_lid fv_eq_1 FStarC_Parser_Const.eq2_lid)
            &&
            (FStarC_Syntax_Syntax.fv_eq_lid fv_eq_2
               FStarC_Parser_Const.eq2_lid)
          -> args_eq [s1; s2] [t12; t22]
      | (FStarC_Syntax_Syntax.Tm_app
         { FStarC_Syntax_Syntax.hd = t; FStarC_Syntax_Syntax.args = args;_},
         FStarC_Syntax_Syntax.Tm_app
         { FStarC_Syntax_Syntax.hd = s; FStarC_Syntax_Syntax.args = args';_})
          -> (term_eq' t s) && (args_eq args args')
      | (FStarC_Syntax_Syntax.Tm_match
         { FStarC_Syntax_Syntax.scrutinee = t;
           FStarC_Syntax_Syntax.ret_opt = FStar_Pervasives_Native.None;
           FStarC_Syntax_Syntax.brs = pats;
           FStarC_Syntax_Syntax.rc_opt1 = uu___;_},
         FStarC_Syntax_Syntax.Tm_match
         { FStarC_Syntax_Syntax.scrutinee = t';
           FStarC_Syntax_Syntax.ret_opt = FStar_Pervasives_Native.None;
           FStarC_Syntax_Syntax.brs = pats';
           FStarC_Syntax_Syntax.rc_opt1 = uu___1;_})
          ->
          (((FStarC_Compiler_List.length pats) =
              (FStarC_Compiler_List.length pats'))
             &&
             (FStarC_Compiler_List.forall2
                (fun uu___2 ->
                   fun uu___3 ->
                     match (uu___2, uu___3) with
                     | ((uu___4, uu___5, e), (uu___6, uu___7, e')) ->
                         term_eq' e e') pats pats'))
            && (term_eq' t t')
      | (FStarC_Syntax_Syntax.Tm_ascribed
         { FStarC_Syntax_Syntax.tm = t12;
           FStarC_Syntax_Syntax.asc =
             (FStar_Pervasives.Inl t22, uu___, uu___1);
           FStarC_Syntax_Syntax.eff_opt = uu___2;_},
         FStarC_Syntax_Syntax.Tm_ascribed
         { FStarC_Syntax_Syntax.tm = s1;
           FStarC_Syntax_Syntax.asc =
             (FStar_Pervasives.Inl s2, uu___3, uu___4);
           FStarC_Syntax_Syntax.eff_opt = uu___5;_})
          -> (term_eq' t12 s1) && (term_eq' t22 s2)
      | (FStarC_Syntax_Syntax.Tm_let
         { FStarC_Syntax_Syntax.lbs = (is_rec, lbs);
           FStarC_Syntax_Syntax.body1 = t;_},
         FStarC_Syntax_Syntax.Tm_let
         { FStarC_Syntax_Syntax.lbs = (is_rec', lbs');
           FStarC_Syntax_Syntax.body1 = s;_})
          when is_rec = is_rec' ->
          (((FStarC_Compiler_List.length lbs) =
              (FStarC_Compiler_List.length lbs'))
             &&
             (FStarC_Compiler_List.forall2
                (fun lb1 ->
                   fun lb2 ->
                     (term_eq' lb1.FStarC_Syntax_Syntax.lbtyp
                        lb2.FStarC_Syntax_Syntax.lbtyp)
                       &&
                       (term_eq' lb1.FStarC_Syntax_Syntax.lbdef
                          lb2.FStarC_Syntax_Syntax.lbdef)) lbs lbs'))
            && (term_eq' t s)
      | (FStarC_Syntax_Syntax.Tm_uvar (u, uu___),
         FStarC_Syntax_Syntax.Tm_uvar (u', uu___1)) ->
          FStarC_Syntax_Unionfind.equiv u.FStarC_Syntax_Syntax.ctx_uvar_head
            u'.FStarC_Syntax_Syntax.ctx_uvar_head
      | (FStarC_Syntax_Syntax.Tm_meta
         { FStarC_Syntax_Syntax.tm2 = t12;
           FStarC_Syntax_Syntax.meta = uu___;_},
         uu___1) -> term_eq' t12 t21
      | (uu___, FStarC_Syntax_Syntax.Tm_meta
         { FStarC_Syntax_Syntax.tm2 = t22;
           FStarC_Syntax_Syntax.meta = uu___1;_})
          -> term_eq' t11 t22
      | (FStarC_Syntax_Syntax.Tm_delayed uu___, uu___1) ->
          let uu___2 =
            let uu___3 =
              FStarC_Class_Tagged.tag_of FStarC_Syntax_Syntax.tagged_term t11 in
            let uu___4 =
              FStarC_Class_Tagged.tag_of FStarC_Syntax_Syntax.tagged_term t21 in
            FStarC_Compiler_Util.format2 "Impossible: %s and %s" uu___3
              uu___4 in
          failwith uu___2
      | (uu___, FStarC_Syntax_Syntax.Tm_delayed uu___1) ->
          let uu___2 =
            let uu___3 =
              FStarC_Class_Tagged.tag_of FStarC_Syntax_Syntax.tagged_term t11 in
            let uu___4 =
              FStarC_Class_Tagged.tag_of FStarC_Syntax_Syntax.tagged_term t21 in
            FStarC_Compiler_Util.format2 "Impossible: %s and %s" uu___3
              uu___4 in
          failwith uu___2
      | (FStarC_Syntax_Syntax.Tm_unknown, FStarC_Syntax_Syntax.Tm_unknown) ->
          true
      | uu___ -> false
let (term_eq :
  FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax ->
    FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax -> Prims.bool)
  =
  fun t1 ->
    fun t2 ->
      let b = term_eq' t1 t2 in
      if Prims.op_Negation b
      then
        (let uu___1 =
           FStarC_Class_Show.show FStarC_Syntax_Print.showable_term t1 in
         let uu___2 =
           FStarC_Class_Show.show FStarC_Syntax_Print.showable_term t2 in
         FStarC_Compiler_Util.print2
           ">>>>>>>>>>>Term %s is not equal to %s\n" uu___1 uu___2)
      else ();
      b