open Prims
let always: Prims.int -> Prims.bool -> Prims.unit =
  fun id  ->
    fun b  ->
      if b
      then ()
      else
        (let uu____8 =
           let uu____9 =
             let uu____14 =
               let uu____15 = FStar_Util.string_of_int id in
               FStar_Util.format1 "Assertion failed: test %s" uu____15 in
             (uu____14, FStar_Range.dummyRange) in
           FStar_Errors.Error uu____9 in
         FStar_Exn.raise uu____8)
let x: FStar_Syntax_Syntax.bv =
  FStar_Syntax_Syntax.gen_bv "x" FStar_Pervasives_Native.None
    FStar_Syntax_Syntax.tun
let y: FStar_Syntax_Syntax.bv =
  FStar_Syntax_Syntax.gen_bv "y" FStar_Pervasives_Native.None
    FStar_Syntax_Syntax.tun
let n: FStar_Syntax_Syntax.bv =
  FStar_Syntax_Syntax.gen_bv "n" FStar_Pervasives_Native.None
    FStar_Syntax_Syntax.tun
let h: FStar_Syntax_Syntax.bv =
  FStar_Syntax_Syntax.gen_bv "h" FStar_Pervasives_Native.None
    FStar_Syntax_Syntax.tun
let m: FStar_Syntax_Syntax.bv =
  FStar_Syntax_Syntax.gen_bv "m" FStar_Pervasives_Native.None
    FStar_Syntax_Syntax.tun
let tm: 'Auu____18 . 'Auu____18 -> 'Auu____18 FStar_Syntax_Syntax.syntax =
  fun t  ->
    FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None
      FStar_Range.dummyRange
let nm: FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.term =
  fun x1  -> FStar_Syntax_Syntax.bv_to_name x1
let app:
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term Prims.list ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun x1  ->
    fun ts  ->
      let uu____44 =
        let uu____47 =
          let uu____48 =
            let uu____63 = FStar_List.map FStar_Syntax_Syntax.as_arg ts in
            (x1, uu____63) in
          FStar_Syntax_Syntax.Tm_app uu____48 in
        FStar_Syntax_Syntax.mk uu____47 in
      uu____44 FStar_Pervasives_Native.None FStar_Range.dummyRange
let rec term_eq':
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun t1  ->
    fun t2  ->
      let t11 = FStar_Syntax_Subst.compress t1 in
      let t21 = FStar_Syntax_Subst.compress t2 in
      let binders_eq xs ys =
        ((FStar_List.length xs) = (FStar_List.length ys)) &&
          (FStar_List.forall2
             (fun uu____102  ->
                fun uu____103  ->
                  match (uu____102, uu____103) with
                  | ((x1,uu____105),(y1,uu____107)) ->
                      term_eq' x1.FStar_Syntax_Syntax.sort
                        y1.FStar_Syntax_Syntax.sort) xs ys) in
      let args_eq xs ys =
        ((FStar_List.length xs) = (FStar_List.length ys)) &&
          (FStar_List.forall2
             (fun uu____169  ->
                fun uu____170  ->
                  match (uu____169, uu____170) with
                  | ((a,imp),(b,imp')) -> (term_eq' a b) && (imp = imp')) xs
             ys) in
      let comp_eq1 c d =
        match ((c.FStar_Syntax_Syntax.n), (d.FStar_Syntax_Syntax.n)) with
        | (FStar_Syntax_Syntax.Total (t,uu____207),FStar_Syntax_Syntax.Total
           (s,uu____209)) -> term_eq' t s
        | (FStar_Syntax_Syntax.Comp ct1,FStar_Syntax_Syntax.Comp ct2) ->
            ((FStar_Ident.lid_equals ct1.FStar_Syntax_Syntax.effect_name
                ct2.FStar_Syntax_Syntax.effect_name)
               &&
               (term_eq' ct1.FStar_Syntax_Syntax.result_typ
                  ct2.FStar_Syntax_Syntax.result_typ))
              &&
              (args_eq ct1.FStar_Syntax_Syntax.effect_args
                 ct2.FStar_Syntax_Syntax.effect_args)
        | uu____228 -> false in
      match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n)) with
      | (FStar_Syntax_Syntax.Tm_bvar x1,FStar_Syntax_Syntax.Tm_bvar y1) ->
          x1.FStar_Syntax_Syntax.index = y1.FStar_Syntax_Syntax.index
      | (FStar_Syntax_Syntax.Tm_name x1,FStar_Syntax_Syntax.Tm_name y1) ->
          FStar_Syntax_Syntax.bv_eq x1 y1
      | (FStar_Syntax_Syntax.Tm_fvar f,FStar_Syntax_Syntax.Tm_fvar g) ->
          FStar_Syntax_Syntax.fv_eq f g
      | (FStar_Syntax_Syntax.Tm_uinst
         (t,uu____240),FStar_Syntax_Syntax.Tm_uinst (s,uu____242)) ->
          term_eq' t s
      | (FStar_Syntax_Syntax.Tm_constant c1,FStar_Syntax_Syntax.Tm_constant
         c2) -> c1 = c2
      | (FStar_Syntax_Syntax.Tm_type u,FStar_Syntax_Syntax.Tm_type v1) ->
          u = v1
      | (FStar_Syntax_Syntax.Tm_abs
         (xs,t,uu____257),FStar_Syntax_Syntax.Tm_abs (ys,u,uu____260)) when
          (FStar_List.length xs) = (FStar_List.length ys) ->
          (binders_eq xs ys) && (term_eq' t u)
      | (FStar_Syntax_Syntax.Tm_abs
         (xs,t,uu____311),FStar_Syntax_Syntax.Tm_abs (ys,u,uu____314)) ->
          if (FStar_List.length xs) > (FStar_List.length ys)
          then
            let uu____363 = FStar_Util.first_N (FStar_List.length ys) xs in
            (match uu____363 with
             | (xs1,xs') ->
                 let t12 =
                   let uu____417 =
                     let uu____420 =
                       let uu____421 =
                         let uu____438 =
                           FStar_Syntax_Syntax.mk
                             (FStar_Syntax_Syntax.Tm_abs
                                (xs', t, FStar_Pervasives_Native.None))
                             FStar_Pervasives_Native.None
                             t11.FStar_Syntax_Syntax.pos in
                         (xs1, uu____438, FStar_Pervasives_Native.None) in
                       FStar_Syntax_Syntax.Tm_abs uu____421 in
                     FStar_Syntax_Syntax.mk uu____420 in
                   uu____417 FStar_Pervasives_Native.None
                     t11.FStar_Syntax_Syntax.pos in
                 term_eq' t12 t21)
          else
            (let uu____465 = FStar_Util.first_N (FStar_List.length xs) ys in
             match uu____465 with
             | (ys1,ys') ->
                 let t22 =
                   let uu____519 =
                     let uu____522 =
                       let uu____523 =
                         let uu____540 =
                           FStar_Syntax_Syntax.mk
                             (FStar_Syntax_Syntax.Tm_abs
                                (ys', u, FStar_Pervasives_Native.None))
                             FStar_Pervasives_Native.None
                             t21.FStar_Syntax_Syntax.pos in
                         (ys1, uu____540, FStar_Pervasives_Native.None) in
                       FStar_Syntax_Syntax.Tm_abs uu____523 in
                     FStar_Syntax_Syntax.mk uu____522 in
                   uu____519 FStar_Pervasives_Native.None
                     t21.FStar_Syntax_Syntax.pos in
                 term_eq' t11 t22)
      | (FStar_Syntax_Syntax.Tm_arrow (xs,c),FStar_Syntax_Syntax.Tm_arrow
         (ys,d)) -> (binders_eq xs ys) && (comp_eq1 c d)
      | (FStar_Syntax_Syntax.Tm_refine (x1,t),FStar_Syntax_Syntax.Tm_refine
         (y1,u)) ->
          (term_eq' x1.FStar_Syntax_Syntax.sort y1.FStar_Syntax_Syntax.sort)
            && (term_eq' t u)
      | (FStar_Syntax_Syntax.Tm_app
         ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv_eq_1;
            FStar_Syntax_Syntax.pos = uu____615;
            FStar_Syntax_Syntax.vars = uu____616;_},(uu____617,FStar_Pervasives_Native.Some
                                                     (FStar_Syntax_Syntax.Implicit
                                                     uu____618))::t12::t22::[]),FStar_Syntax_Syntax.Tm_app
         ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv_eq_2;
            FStar_Syntax_Syntax.pos = uu____622;
            FStar_Syntax_Syntax.vars = uu____623;_},(uu____624,FStar_Pervasives_Native.Some
                                                     (FStar_Syntax_Syntax.Implicit
                                                     uu____625))::s1::s2::[]))
          when
          (FStar_Syntax_Syntax.fv_eq_lid fv_eq_1 FStar_Parser_Const.eq2_lid)
            &&
            (FStar_Syntax_Syntax.fv_eq_lid fv_eq_2 FStar_Parser_Const.eq2_lid)
          -> args_eq [s1; s2] [t12; t22]
      | (FStar_Syntax_Syntax.Tm_app (t,args),FStar_Syntax_Syntax.Tm_app
         (s,args')) -> (term_eq' t s) && (args_eq args args')
      | (FStar_Syntax_Syntax.Tm_match (t,pats),FStar_Syntax_Syntax.Tm_match
         (t',pats')) ->
          (((FStar_List.length pats) = (FStar_List.length pats')) &&
             (FStar_List.forall2
                (fun uu____992  ->
                   fun uu____993  ->
                     match (uu____992, uu____993) with
                     | ((uu____1042,uu____1043,e),(uu____1045,uu____1046,e'))
                         -> term_eq' e e') pats pats'))
            && (term_eq' t t')
      | (FStar_Syntax_Syntax.Tm_ascribed
         (t12,(FStar_Util.Inl t22,uu____1098),uu____1099),FStar_Syntax_Syntax.Tm_ascribed
         (s1,(FStar_Util.Inl s2,uu____1102),uu____1103)) ->
          (term_eq' t12 s1) && (term_eq' t22 s2)
      | (FStar_Syntax_Syntax.Tm_let
         ((is_rec,lbs),t),FStar_Syntax_Syntax.Tm_let ((is_rec',lbs'),s)) when
          is_rec = is_rec' ->
          (((FStar_List.length lbs) = (FStar_List.length lbs')) &&
             (FStar_List.forall2
                (fun lb1  ->
                   fun lb2  ->
                     (term_eq' lb1.FStar_Syntax_Syntax.lbtyp
                        lb2.FStar_Syntax_Syntax.lbtyp)
                       &&
                       (term_eq' lb1.FStar_Syntax_Syntax.lbdef
                          lb2.FStar_Syntax_Syntax.lbdef)) lbs lbs'))
            && (term_eq' t s)
      | (FStar_Syntax_Syntax.Tm_uvar
         (u,uu____1235),FStar_Syntax_Syntax.Tm_uvar (u',uu____1237)) ->
          FStar_Syntax_Unionfind.equiv u u'
      | (FStar_Syntax_Syntax.Tm_meta (t12,uu____1287),uu____1288) ->
          term_eq' t12 t21
      | (uu____1293,FStar_Syntax_Syntax.Tm_meta (t22,uu____1295)) ->
          term_eq' t11 t22
      | (FStar_Syntax_Syntax.Tm_delayed uu____1300,uu____1301) ->
          let uu____1326 =
            let uu____1327 = FStar_Syntax_Print.tag_of_term t11 in
            let uu____1328 = FStar_Syntax_Print.tag_of_term t21 in
            FStar_Util.format2 "Impossible: %s and %s" uu____1327 uu____1328 in
          failwith uu____1326
      | (uu____1329,FStar_Syntax_Syntax.Tm_delayed uu____1330) ->
          let uu____1355 =
            let uu____1356 = FStar_Syntax_Print.tag_of_term t11 in
            let uu____1357 = FStar_Syntax_Print.tag_of_term t21 in
            FStar_Util.format2 "Impossible: %s and %s" uu____1356 uu____1357 in
          failwith uu____1355
      | (FStar_Syntax_Syntax.Tm_unknown ,FStar_Syntax_Syntax.Tm_unknown ) ->
          true
      | uu____1358 -> false
let term_eq:
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun t1  ->
    fun t2  ->
      let b = term_eq' t1 t2 in
      if Prims.op_Negation b
      then
        (let uu____1371 = FStar_Syntax_Print.term_to_string t1 in
         let uu____1372 = FStar_Syntax_Print.term_to_string t2 in
         FStar_Util.print2 ">>>>>>>>>>>Term %s is not equal to %s\n"
           uu____1371 uu____1372)
      else ();
      b