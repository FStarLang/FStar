open Prims
let (always : Prims.int -> Prims.bool -> unit) =
  fun id ->
    fun b ->
      if b
      then ()
      else
        (let uu___1 =
           let uu___2 =
             let uu___3 = FStar_Compiler_Util.string_of_int id in
             FStar_Compiler_Util.format1 "Assertion failed: test %s" uu___3 in
           (FStar_Errors_Codes.Fatal_AssertionFailure, uu___2) in
         FStar_Errors.raise_error uu___1 FStar_Compiler_Range_Type.dummyRange)
let (x : FStar_Syntax_Syntax.bv) =
  FStar_Syntax_Syntax.gen_bv "x" FStar_Pervasives_Native.None
    FStar_Syntax_Syntax.tun
let (y : FStar_Syntax_Syntax.bv) =
  FStar_Syntax_Syntax.gen_bv "y" FStar_Pervasives_Native.None
    FStar_Syntax_Syntax.tun
let (n : FStar_Syntax_Syntax.bv) =
  FStar_Syntax_Syntax.gen_bv "n" FStar_Pervasives_Native.None
    FStar_Syntax_Syntax.tun
let (h : FStar_Syntax_Syntax.bv) =
  FStar_Syntax_Syntax.gen_bv "h" FStar_Pervasives_Native.None
    FStar_Syntax_Syntax.tun
let (m : FStar_Syntax_Syntax.bv) =
  FStar_Syntax_Syntax.gen_bv "m" FStar_Pervasives_Native.None
    FStar_Syntax_Syntax.tun
let tm : 'uuuuu . 'uuuuu -> 'uuuuu FStar_Syntax_Syntax.syntax =
  fun t -> FStar_Syntax_Syntax.mk t FStar_Compiler_Range_Type.dummyRange
let (nm : FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.term) =
  fun x1 -> FStar_Syntax_Syntax.bv_to_name x1
let (app :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term Prims.list ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun x1 ->
    fun ts ->
      let uu___ =
        let uu___1 =
          let uu___2 = FStar_Compiler_List.map FStar_Syntax_Syntax.as_arg ts in
          { FStar_Syntax_Syntax.hd = x1; FStar_Syntax_Syntax.args = uu___2 } in
        FStar_Syntax_Syntax.Tm_app uu___1 in
      FStar_Syntax_Syntax.mk uu___ FStar_Compiler_Range_Type.dummyRange
let rec (term_eq' :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.bool)
  =
  fun t1 ->
    fun t2 ->
      let t11 = FStar_Syntax_Subst.compress t1 in
      let t21 = FStar_Syntax_Subst.compress t2 in
      let binders_eq xs ys =
        ((FStar_Compiler_List.length xs) = (FStar_Compiler_List.length ys))
          &&
          (FStar_Compiler_List.forall2
             (fun x1 ->
                fun y1 ->
                  term_eq'
                    (x1.FStar_Syntax_Syntax.binder_bv).FStar_Syntax_Syntax.sort
                    (y1.FStar_Syntax_Syntax.binder_bv).FStar_Syntax_Syntax.sort)
             xs ys) in
      let args_eq xs ys =
        ((FStar_Compiler_List.length xs) = (FStar_Compiler_List.length ys))
          &&
          (FStar_Compiler_List.forall2
             (fun uu___ ->
                fun uu___1 ->
                  match (uu___, uu___1) with
                  | ((a, imp), (b, imp')) ->
                      (term_eq' a b) &&
                        (let uu___2 = FStar_Syntax_Util.eq_aqual imp imp' in
                         uu___2 = FStar_Syntax_Util.Equal)) xs ys) in
      let comp_eq c d =
        match ((c.FStar_Syntax_Syntax.n), (d.FStar_Syntax_Syntax.n)) with
        | (FStar_Syntax_Syntax.Total t, FStar_Syntax_Syntax.Total s) ->
            term_eq' t s
        | (FStar_Syntax_Syntax.Comp ct1, FStar_Syntax_Syntax.Comp ct2) ->
            ((FStar_Ident.lid_equals ct1.FStar_Syntax_Syntax.effect_name
                ct2.FStar_Syntax_Syntax.effect_name)
               &&
               (term_eq' ct1.FStar_Syntax_Syntax.result_typ
                  ct2.FStar_Syntax_Syntax.result_typ))
              &&
              (args_eq ct1.FStar_Syntax_Syntax.effect_args
                 ct2.FStar_Syntax_Syntax.effect_args)
        | uu___ -> false in
      match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n)) with
      | (FStar_Syntax_Syntax.Tm_lazy l, uu___) ->
          let uu___1 =
            let uu___2 =
              let uu___3 =
                FStar_Compiler_Effect.op_Bang
                  FStar_Syntax_Syntax.lazy_chooser in
              FStar_Compiler_Util.must uu___3 in
            uu___2 l.FStar_Syntax_Syntax.lkind l in
          term_eq' uu___1 t21
      | (uu___, FStar_Syntax_Syntax.Tm_lazy l) ->
          let uu___1 =
            let uu___2 =
              let uu___3 =
                FStar_Compiler_Effect.op_Bang
                  FStar_Syntax_Syntax.lazy_chooser in
              FStar_Compiler_Util.must uu___3 in
            uu___2 l.FStar_Syntax_Syntax.lkind l in
          term_eq' t11 uu___1
      | (FStar_Syntax_Syntax.Tm_bvar x1, FStar_Syntax_Syntax.Tm_bvar y1) ->
          x1.FStar_Syntax_Syntax.index = y1.FStar_Syntax_Syntax.index
      | (FStar_Syntax_Syntax.Tm_name x1, FStar_Syntax_Syntax.Tm_name y1) ->
          FStar_Syntax_Syntax.bv_eq x1 y1
      | (FStar_Syntax_Syntax.Tm_fvar f, FStar_Syntax_Syntax.Tm_fvar g) ->
          FStar_Syntax_Syntax.fv_eq f g
      | (FStar_Syntax_Syntax.Tm_uinst (t, uu___),
         FStar_Syntax_Syntax.Tm_uinst (s, uu___1)) -> term_eq' t s
      | (FStar_Syntax_Syntax.Tm_constant c1, FStar_Syntax_Syntax.Tm_constant
         c2) -> FStar_Const.eq_const c1 c2
      | (FStar_Syntax_Syntax.Tm_type u, FStar_Syntax_Syntax.Tm_type v) ->
          u = v
      | (FStar_Syntax_Syntax.Tm_abs
         { FStar_Syntax_Syntax.bs = xs; FStar_Syntax_Syntax.body = t;
           FStar_Syntax_Syntax.rc_opt = uu___;_},
         FStar_Syntax_Syntax.Tm_abs
         { FStar_Syntax_Syntax.bs = ys; FStar_Syntax_Syntax.body = u;
           FStar_Syntax_Syntax.rc_opt = uu___1;_})
          when
          (FStar_Compiler_List.length xs) = (FStar_Compiler_List.length ys)
          -> (binders_eq xs ys) && (term_eq' t u)
      | (FStar_Syntax_Syntax.Tm_abs
         { FStar_Syntax_Syntax.bs = xs; FStar_Syntax_Syntax.body = t;
           FStar_Syntax_Syntax.rc_opt = uu___;_},
         FStar_Syntax_Syntax.Tm_abs
         { FStar_Syntax_Syntax.bs = ys; FStar_Syntax_Syntax.body = u;
           FStar_Syntax_Syntax.rc_opt = uu___1;_})
          ->
          if
            (FStar_Compiler_List.length xs) > (FStar_Compiler_List.length ys)
          then
            let uu___2 =
              FStar_Compiler_Util.first_N (FStar_Compiler_List.length ys) xs in
            (match uu___2 with
             | (xs1, xs') ->
                 let t12 =
                   let uu___3 =
                     let uu___4 =
                       let uu___5 =
                         FStar_Syntax_Syntax.mk
                           (FStar_Syntax_Syntax.Tm_abs
                              {
                                FStar_Syntax_Syntax.bs = xs';
                                FStar_Syntax_Syntax.body = t;
                                FStar_Syntax_Syntax.rc_opt =
                                  FStar_Pervasives_Native.None
                              }) t11.FStar_Syntax_Syntax.pos in
                       {
                         FStar_Syntax_Syntax.bs = xs1;
                         FStar_Syntax_Syntax.body = uu___5;
                         FStar_Syntax_Syntax.rc_opt =
                           FStar_Pervasives_Native.None
                       } in
                     FStar_Syntax_Syntax.Tm_abs uu___4 in
                   FStar_Syntax_Syntax.mk uu___3 t11.FStar_Syntax_Syntax.pos in
                 term_eq' t12 t21)
          else
            (let uu___3 =
               FStar_Compiler_Util.first_N (FStar_Compiler_List.length xs) ys in
             match uu___3 with
             | (ys1, ys') ->
                 let t22 =
                   let uu___4 =
                     let uu___5 =
                       let uu___6 =
                         FStar_Syntax_Syntax.mk
                           (FStar_Syntax_Syntax.Tm_abs
                              {
                                FStar_Syntax_Syntax.bs = ys';
                                FStar_Syntax_Syntax.body = u;
                                FStar_Syntax_Syntax.rc_opt =
                                  FStar_Pervasives_Native.None
                              }) t21.FStar_Syntax_Syntax.pos in
                       {
                         FStar_Syntax_Syntax.bs = ys1;
                         FStar_Syntax_Syntax.body = uu___6;
                         FStar_Syntax_Syntax.rc_opt =
                           FStar_Pervasives_Native.None
                       } in
                     FStar_Syntax_Syntax.Tm_abs uu___5 in
                   FStar_Syntax_Syntax.mk uu___4 t21.FStar_Syntax_Syntax.pos in
                 term_eq' t11 t22)
      | (FStar_Syntax_Syntax.Tm_arrow
         { FStar_Syntax_Syntax.bs1 = xs; FStar_Syntax_Syntax.comp = c;_},
         FStar_Syntax_Syntax.Tm_arrow
         { FStar_Syntax_Syntax.bs1 = ys; FStar_Syntax_Syntax.comp = d;_}) ->
          (binders_eq xs ys) && (comp_eq c d)
      | (FStar_Syntax_Syntax.Tm_refine
         { FStar_Syntax_Syntax.b = x1; FStar_Syntax_Syntax.phi = t;_},
         FStar_Syntax_Syntax.Tm_refine
         { FStar_Syntax_Syntax.b = y1; FStar_Syntax_Syntax.phi = u;_}) ->
          (term_eq' x1.FStar_Syntax_Syntax.sort y1.FStar_Syntax_Syntax.sort)
            && (term_eq' t u)
      | (FStar_Syntax_Syntax.Tm_app
         {
           FStar_Syntax_Syntax.hd =
             { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv_eq_1;
               FStar_Syntax_Syntax.pos = uu___;
               FStar_Syntax_Syntax.vars = uu___1;
               FStar_Syntax_Syntax.hash_code = uu___2;_};
           FStar_Syntax_Syntax.args =
             (uu___3, FStar_Pervasives_Native.Some
              { FStar_Syntax_Syntax.aqual_implicit = true;
                FStar_Syntax_Syntax.aqual_attributes = uu___4;_})::t12::t22::[];_},
         FStar_Syntax_Syntax.Tm_app
         {
           FStar_Syntax_Syntax.hd =
             { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv_eq_2;
               FStar_Syntax_Syntax.pos = uu___5;
               FStar_Syntax_Syntax.vars = uu___6;
               FStar_Syntax_Syntax.hash_code = uu___7;_};
           FStar_Syntax_Syntax.args =
             (uu___8, FStar_Pervasives_Native.Some
              { FStar_Syntax_Syntax.aqual_implicit = true;
                FStar_Syntax_Syntax.aqual_attributes = uu___9;_})::s1::s2::[];_})
          when
          (FStar_Syntax_Syntax.fv_eq_lid fv_eq_1 FStar_Parser_Const.eq2_lid)
            &&
            (FStar_Syntax_Syntax.fv_eq_lid fv_eq_2 FStar_Parser_Const.eq2_lid)
          -> args_eq [s1; s2] [t12; t22]
      | (FStar_Syntax_Syntax.Tm_app
         { FStar_Syntax_Syntax.hd = t; FStar_Syntax_Syntax.args = args;_},
         FStar_Syntax_Syntax.Tm_app
         { FStar_Syntax_Syntax.hd = s; FStar_Syntax_Syntax.args = args';_})
          -> (term_eq' t s) && (args_eq args args')
      | (FStar_Syntax_Syntax.Tm_match
         { FStar_Syntax_Syntax.scrutinee = t;
           FStar_Syntax_Syntax.ret_opt = FStar_Pervasives_Native.None;
           FStar_Syntax_Syntax.brs = pats;
           FStar_Syntax_Syntax.rc_opt1 = uu___;_},
         FStar_Syntax_Syntax.Tm_match
         { FStar_Syntax_Syntax.scrutinee = t';
           FStar_Syntax_Syntax.ret_opt = FStar_Pervasives_Native.None;
           FStar_Syntax_Syntax.brs = pats';
           FStar_Syntax_Syntax.rc_opt1 = uu___1;_})
          ->
          (((FStar_Compiler_List.length pats) =
              (FStar_Compiler_List.length pats'))
             &&
             (FStar_Compiler_List.forall2
                (fun uu___2 ->
                   fun uu___3 ->
                     match (uu___2, uu___3) with
                     | ((uu___4, uu___5, e), (uu___6, uu___7, e')) ->
                         term_eq' e e') pats pats'))
            && (term_eq' t t')
      | (FStar_Syntax_Syntax.Tm_ascribed
         { FStar_Syntax_Syntax.tm = t12;
           FStar_Syntax_Syntax.asc =
             (FStar_Pervasives.Inl t22, uu___, uu___1);
           FStar_Syntax_Syntax.eff_opt = uu___2;_},
         FStar_Syntax_Syntax.Tm_ascribed
         { FStar_Syntax_Syntax.tm = s1;
           FStar_Syntax_Syntax.asc =
             (FStar_Pervasives.Inl s2, uu___3, uu___4);
           FStar_Syntax_Syntax.eff_opt = uu___5;_})
          -> (term_eq' t12 s1) && (term_eq' t22 s2)
      | (FStar_Syntax_Syntax.Tm_let
         { FStar_Syntax_Syntax.lbs = (is_rec, lbs);
           FStar_Syntax_Syntax.body1 = t;_},
         FStar_Syntax_Syntax.Tm_let
         { FStar_Syntax_Syntax.lbs = (is_rec', lbs');
           FStar_Syntax_Syntax.body1 = s;_})
          when is_rec = is_rec' ->
          (((FStar_Compiler_List.length lbs) =
              (FStar_Compiler_List.length lbs'))
             &&
             (FStar_Compiler_List.forall2
                (fun lb1 ->
                   fun lb2 ->
                     (term_eq' lb1.FStar_Syntax_Syntax.lbtyp
                        lb2.FStar_Syntax_Syntax.lbtyp)
                       &&
                       (term_eq' lb1.FStar_Syntax_Syntax.lbdef
                          lb2.FStar_Syntax_Syntax.lbdef)) lbs lbs'))
            && (term_eq' t s)
      | (FStar_Syntax_Syntax.Tm_uvar (u, uu___), FStar_Syntax_Syntax.Tm_uvar
         (u', uu___1)) ->
          FStar_Syntax_Unionfind.equiv u.FStar_Syntax_Syntax.ctx_uvar_head
            u'.FStar_Syntax_Syntax.ctx_uvar_head
      | (FStar_Syntax_Syntax.Tm_meta
         { FStar_Syntax_Syntax.tm2 = t12; FStar_Syntax_Syntax.meta = uu___;_},
         uu___1) -> term_eq' t12 t21
      | (uu___, FStar_Syntax_Syntax.Tm_meta
         { FStar_Syntax_Syntax.tm2 = t22;
           FStar_Syntax_Syntax.meta = uu___1;_})
          -> term_eq' t11 t22
      | (FStar_Syntax_Syntax.Tm_delayed uu___, uu___1) ->
          let uu___2 =
            let uu___3 = FStar_Syntax_Print.tag_of_term t11 in
            let uu___4 = FStar_Syntax_Print.tag_of_term t21 in
            FStar_Compiler_Util.format2 "Impossible: %s and %s" uu___3 uu___4 in
          failwith uu___2
      | (uu___, FStar_Syntax_Syntax.Tm_delayed uu___1) ->
          let uu___2 =
            let uu___3 = FStar_Syntax_Print.tag_of_term t11 in
            let uu___4 = FStar_Syntax_Print.tag_of_term t21 in
            FStar_Compiler_Util.format2 "Impossible: %s and %s" uu___3 uu___4 in
          failwith uu___2
      | (FStar_Syntax_Syntax.Tm_unknown, FStar_Syntax_Syntax.Tm_unknown) ->
          true
      | uu___ -> false
let (term_eq :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.bool)
  =
  fun t1 ->
    fun t2 ->
      let b = term_eq' t1 t2 in
      if Prims.op_Negation b
      then
        (let uu___1 = FStar_Syntax_Print.term_to_string t1 in
         let uu___2 = FStar_Syntax_Print.term_to_string t2 in
         FStar_Compiler_Util.print2 ">>>>>>>>>>>Term %s is not equal to %s\n"
           uu___1 uu___2)
      else ();
      b