open Prims
let (always : Prims.int -> Prims.bool -> unit) =
  fun id ->
    fun b ->
      if b
      then ()
      else
        (let uu___1 =
           let uu___2 =
             let uu___3 = FStar_Util.string_of_int id in
             FStar_Util.format1 "Assertion failed: test %s" uu___3 in
           (FStar_Errors.Fatal_AssertionFailure, uu___2) in
         FStar_Errors.raise_error uu___1 FStar_Range.dummyRange)
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
  fun t -> FStar_Syntax_Syntax.mk t FStar_Range.dummyRange
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
          let uu___2 = FStar_List.map FStar_Syntax_Syntax.as_arg ts in
          (x1, uu___2) in
        FStar_Syntax_Syntax.Tm_app uu___1 in
      FStar_Syntax_Syntax.mk uu___ FStar_Range.dummyRange
let rec (term_eq' :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.bool)
  =
  fun t1 ->
    fun t2 ->
      let t11 = FStar_Syntax_Subst.compress t1 in
      let t21 = FStar_Syntax_Subst.compress t2 in
      let binders_eq xs ys =
        ((FStar_List.length xs) = (FStar_List.length ys)) &&
          (FStar_List.forall2
             (fun x1 ->
                fun y1 ->
                  term_eq'
                    (x1.FStar_Syntax_Syntax.binder_bv).FStar_Syntax_Syntax.sort
                    (y1.FStar_Syntax_Syntax.binder_bv).FStar_Syntax_Syntax.sort)
             xs ys) in
      let args_eq xs ys =
        ((FStar_List.length xs) = (FStar_List.length ys)) &&
          (FStar_List.forall2
             (fun uu___ ->
                fun uu___1 ->
                  match (uu___, uu___1) with
                  | ((a, imp), (b, imp')) ->
                      (term_eq' a b) &&
                        (let uu___2 = FStar_Syntax_Util.eq_aqual imp imp' in
                         uu___2 = FStar_Syntax_Util.Equal)) xs ys) in
      let comp_eq c d =
        match ((c.FStar_Syntax_Syntax.n), (d.FStar_Syntax_Syntax.n)) with
        | (FStar_Syntax_Syntax.Total (t, uu___), FStar_Syntax_Syntax.Total
           (s, uu___1)) -> term_eq' t s
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
              let uu___3 = FStar_ST.op_Bang FStar_Syntax_Syntax.lazy_chooser in
              FStar_Util.must uu___3 in
            uu___2 l.FStar_Syntax_Syntax.lkind l in
          term_eq' uu___1 t21
      | (uu___, FStar_Syntax_Syntax.Tm_lazy l) ->
          let uu___1 =
            let uu___2 =
              let uu___3 = FStar_ST.op_Bang FStar_Syntax_Syntax.lazy_chooser in
              FStar_Util.must uu___3 in
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
      | (FStar_Syntax_Syntax.Tm_abs (xs, t, uu___),
         FStar_Syntax_Syntax.Tm_abs (ys, u, uu___1)) when
          (FStar_List.length xs) = (FStar_List.length ys) ->
          (binders_eq xs ys) && (term_eq' t u)
      | (FStar_Syntax_Syntax.Tm_abs (xs, t, uu___),
         FStar_Syntax_Syntax.Tm_abs (ys, u, uu___1)) ->
          if (FStar_List.length xs) > (FStar_List.length ys)
          then
            let uu___2 = FStar_Util.first_N (FStar_List.length ys) xs in
            (match uu___2 with
             | (xs1, xs') ->
                 let t12 =
                   let uu___3 =
                     let uu___4 =
                       let uu___5 =
                         FStar_Syntax_Syntax.mk
                           (FStar_Syntax_Syntax.Tm_abs
                              (xs', t, FStar_Pervasives_Native.None))
                           t11.FStar_Syntax_Syntax.pos in
                       (xs1, uu___5, FStar_Pervasives_Native.None) in
                     FStar_Syntax_Syntax.Tm_abs uu___4 in
                   FStar_Syntax_Syntax.mk uu___3 t11.FStar_Syntax_Syntax.pos in
                 term_eq' t12 t21)
          else
            (let uu___3 = FStar_Util.first_N (FStar_List.length xs) ys in
             match uu___3 with
             | (ys1, ys') ->
                 let t22 =
                   let uu___4 =
                     let uu___5 =
                       let uu___6 =
                         FStar_Syntax_Syntax.mk
                           (FStar_Syntax_Syntax.Tm_abs
                              (ys', u, FStar_Pervasives_Native.None))
                           t21.FStar_Syntax_Syntax.pos in
                       (ys1, uu___6, FStar_Pervasives_Native.None) in
                     FStar_Syntax_Syntax.Tm_abs uu___5 in
                   FStar_Syntax_Syntax.mk uu___4 t21.FStar_Syntax_Syntax.pos in
                 term_eq' t11 t22)
      | (FStar_Syntax_Syntax.Tm_arrow (xs, c), FStar_Syntax_Syntax.Tm_arrow
         (ys, d)) -> (binders_eq xs ys) && (comp_eq c d)
      | (FStar_Syntax_Syntax.Tm_refine (x1, t), FStar_Syntax_Syntax.Tm_refine
         (y1, u)) ->
          (term_eq' x1.FStar_Syntax_Syntax.sort y1.FStar_Syntax_Syntax.sort)
            && (term_eq' t u)
      | (FStar_Syntax_Syntax.Tm_app
         ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv_eq_1;
            FStar_Syntax_Syntax.pos = uu___;
            FStar_Syntax_Syntax.vars = uu___1;_},
          (uu___2, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit
           uu___3))::t12::t22::[]),
         FStar_Syntax_Syntax.Tm_app
         ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv_eq_2;
            FStar_Syntax_Syntax.pos = uu___4;
            FStar_Syntax_Syntax.vars = uu___5;_},
          (uu___6, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit
           uu___7))::s1::s2::[]))
          when
          (FStar_Syntax_Syntax.fv_eq_lid fv_eq_1 FStar_Parser_Const.eq2_lid)
            &&
            (FStar_Syntax_Syntax.fv_eq_lid fv_eq_2 FStar_Parser_Const.eq2_lid)
          -> args_eq [s1; s2] [t12; t22]
      | (FStar_Syntax_Syntax.Tm_app (t, args), FStar_Syntax_Syntax.Tm_app
         (s, args')) -> (term_eq' t s) && (args_eq args args')
      | (FStar_Syntax_Syntax.Tm_match
         (t, FStar_Pervasives_Native.None, pats),
         FStar_Syntax_Syntax.Tm_match
         (t', FStar_Pervasives_Native.None, pats')) ->
          (((FStar_List.length pats) = (FStar_List.length pats')) &&
             (FStar_List.forall2
                (fun uu___ ->
                   fun uu___1 ->
                     match (uu___, uu___1) with
                     | ((uu___2, uu___3, e), (uu___4, uu___5, e')) ->
                         term_eq' e e') pats pats'))
            && (term_eq' t t')
      | (FStar_Syntax_Syntax.Tm_ascribed
         (t12, (FStar_Pervasives.Inl t22, uu___), uu___1),
         FStar_Syntax_Syntax.Tm_ascribed
         (s1, (FStar_Pervasives.Inl s2, uu___2), uu___3)) ->
          (term_eq' t12 s1) && (term_eq' t22 s2)
      | (FStar_Syntax_Syntax.Tm_let ((is_rec, lbs), t),
         FStar_Syntax_Syntax.Tm_let ((is_rec', lbs'), s)) when
          is_rec = is_rec' ->
          (((FStar_List.length lbs) = (FStar_List.length lbs')) &&
             (FStar_List.forall2
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
      | (FStar_Syntax_Syntax.Tm_meta (t12, uu___), uu___1) ->
          term_eq' t12 t21
      | (uu___, FStar_Syntax_Syntax.Tm_meta (t22, uu___1)) ->
          term_eq' t11 t22
      | (FStar_Syntax_Syntax.Tm_delayed uu___, uu___1) ->
          let uu___2 =
            let uu___3 = FStar_Syntax_Print.tag_of_term t11 in
            let uu___4 = FStar_Syntax_Print.tag_of_term t21 in
            FStar_Util.format2 "Impossible: %s and %s" uu___3 uu___4 in
          failwith uu___2
      | (uu___, FStar_Syntax_Syntax.Tm_delayed uu___1) ->
          let uu___2 =
            let uu___3 = FStar_Syntax_Print.tag_of_term t11 in
            let uu___4 = FStar_Syntax_Print.tag_of_term t21 in
            FStar_Util.format2 "Impossible: %s and %s" uu___3 uu___4 in
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
         FStar_Util.print2 ">>>>>>>>>>>Term %s is not equal to %s\n" uu___1
           uu___2)
      else ();
      b