open Prims
let (always : Prims.int -> Prims.bool -> Prims.unit) =
  fun id1 ->
    fun b ->
      if b
      then ()
      else
        (let uu____8 =
           let uu____13 =
             let uu____14 = FStar_Util.string_of_int id1 in
             FStar_Util.format1 "Assertion failed: test %s" uu____14 in
           (FStar_Errors.Fatal_AssertionFailure, uu____13) in
         FStar_Errors.raise_error uu____8 FStar_Range.dummyRange)
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
let tm : 'Auu____17 . 'Auu____17 -> 'Auu____17 FStar_Syntax_Syntax.syntax =
  fun t ->
    FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None
      FStar_Range.dummyRange
let (nm : FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.term) =
  fun x1 -> FStar_Syntax_Syntax.bv_to_name x1
let (app :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term Prims.list ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun x1 ->
    fun ts ->
      let uu____43 =
        let uu____46 =
          let uu____47 =
            let uu____62 = FStar_List.map FStar_Syntax_Syntax.as_arg ts in
            (x1, uu____62) in
          FStar_Syntax_Syntax.Tm_app uu____47 in
        FStar_Syntax_Syntax.mk uu____46 in
      uu____43 FStar_Pervasives_Native.None FStar_Range.dummyRange
let rec (term_eq' :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t1 ->
    fun t2 ->
      let t11 = FStar_Syntax_Subst.compress t1 in
      let t21 = FStar_Syntax_Subst.compress t2 in
      let binders_eq xs ys =
        ((FStar_List.length xs) = (FStar_List.length ys)) &&
          (FStar_List.forall2
             (fun uu____101 ->
                fun uu____102 ->
                  match (uu____101, uu____102) with
                  | ((x1, uu____104), (y1, uu____106)) ->
                      term_eq' x1.FStar_Syntax_Syntax.sort
                        y1.FStar_Syntax_Syntax.sort) xs ys) in
      let args_eq xs ys =
        ((FStar_List.length xs) = (FStar_List.length ys)) &&
          (FStar_List.forall2
             (fun uu____168 ->
                fun uu____169 ->
                  match (uu____168, uu____169) with
                  | ((a, imp), (b, imp')) -> (term_eq' a b) && (imp = imp'))
             xs ys) in
      let comp_eq c d =
        match ((c.FStar_Syntax_Syntax.n), (d.FStar_Syntax_Syntax.n)) with
        | (FStar_Syntax_Syntax.Total (t, uu____206),
           FStar_Syntax_Syntax.Total (s, uu____208)) -> term_eq' t s
        | (FStar_Syntax_Syntax.Comp ct1, FStar_Syntax_Syntax.Comp ct2) ->
            ((FStar_Ident.lid_equals ct1.FStar_Syntax_Syntax.effect_name
                ct2.FStar_Syntax_Syntax.effect_name)
               &&
               (term_eq' ct1.FStar_Syntax_Syntax.result_typ
                  ct2.FStar_Syntax_Syntax.result_typ))
              &&
              (args_eq ct1.FStar_Syntax_Syntax.effect_args
                 ct2.FStar_Syntax_Syntax.effect_args)
        | uu____227 -> false in
      match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n)) with
      | (FStar_Syntax_Syntax.Tm_bvar x1, FStar_Syntax_Syntax.Tm_bvar y1) ->
          x1.FStar_Syntax_Syntax.index = y1.FStar_Syntax_Syntax.index
      | (FStar_Syntax_Syntax.Tm_name x1, FStar_Syntax_Syntax.Tm_name y1) ->
          FStar_Syntax_Syntax.bv_eq x1 y1
      | (FStar_Syntax_Syntax.Tm_fvar f, FStar_Syntax_Syntax.Tm_fvar g) ->
          FStar_Syntax_Syntax.fv_eq f g
      | (FStar_Syntax_Syntax.Tm_uinst (t, uu____239),
         FStar_Syntax_Syntax.Tm_uinst (s, uu____241)) -> term_eq' t s
      | (FStar_Syntax_Syntax.Tm_constant c1, FStar_Syntax_Syntax.Tm_constant
         c2) -> c1 = c2
      | (FStar_Syntax_Syntax.Tm_type u, FStar_Syntax_Syntax.Tm_type v1) ->
          u = v1
      | (FStar_Syntax_Syntax.Tm_abs (xs, t, uu____256),
         FStar_Syntax_Syntax.Tm_abs (ys, u, uu____259)) when
          (FStar_List.length xs) = (FStar_List.length ys) ->
          (binders_eq xs ys) && (term_eq' t u)
      | (FStar_Syntax_Syntax.Tm_abs (xs, t, uu____310),
         FStar_Syntax_Syntax.Tm_abs (ys, u, uu____313)) ->
          if (FStar_List.length xs) > (FStar_List.length ys)
          then
            let uu____362 = FStar_Util.first_N (FStar_List.length ys) xs in
            (match uu____362 with
             | (xs1, xs') ->
                 let t12 =
                   let uu____416 =
                     let uu____419 =
                       let uu____420 =
                         let uu____437 =
                           FStar_Syntax_Syntax.mk
                             (FStar_Syntax_Syntax.Tm_abs
                                (xs', t, FStar_Pervasives_Native.None))
                             FStar_Pervasives_Native.None
                             t11.FStar_Syntax_Syntax.pos in
                         (xs1, uu____437, FStar_Pervasives_Native.None) in
                       FStar_Syntax_Syntax.Tm_abs uu____420 in
                     FStar_Syntax_Syntax.mk uu____419 in
                   uu____416 FStar_Pervasives_Native.None
                     t11.FStar_Syntax_Syntax.pos in
                 term_eq' t12 t21)
          else
            (let uu____464 = FStar_Util.first_N (FStar_List.length xs) ys in
             match uu____464 with
             | (ys1, ys') ->
                 let t22 =
                   let uu____518 =
                     let uu____521 =
                       let uu____522 =
                         let uu____539 =
                           FStar_Syntax_Syntax.mk
                             (FStar_Syntax_Syntax.Tm_abs
                                (ys', u, FStar_Pervasives_Native.None))
                             FStar_Pervasives_Native.None
                             t21.FStar_Syntax_Syntax.pos in
                         (ys1, uu____539, FStar_Pervasives_Native.None) in
                       FStar_Syntax_Syntax.Tm_abs uu____522 in
                     FStar_Syntax_Syntax.mk uu____521 in
                   uu____518 FStar_Pervasives_Native.None
                     t21.FStar_Syntax_Syntax.pos in
                 term_eq' t11 t22)
      | (FStar_Syntax_Syntax.Tm_arrow (xs, c), FStar_Syntax_Syntax.Tm_arrow
         (ys, d)) -> (binders_eq xs ys) && (comp_eq c d)
      | (FStar_Syntax_Syntax.Tm_refine (x1, t), FStar_Syntax_Syntax.Tm_refine
         (y1, u)) ->
          (term_eq' x1.FStar_Syntax_Syntax.sort y1.FStar_Syntax_Syntax.sort)
            && (term_eq' t u)
      | (FStar_Syntax_Syntax.Tm_app
         ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv_eq_1;
            FStar_Syntax_Syntax.pos = uu____614;
            FStar_Syntax_Syntax.vars = uu____615;_},
          (uu____616, FStar_Pervasives_Native.Some
           (FStar_Syntax_Syntax.Implicit uu____617))::t12::t22::[]),
         FStar_Syntax_Syntax.Tm_app
         ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv_eq_2;
            FStar_Syntax_Syntax.pos = uu____621;
            FStar_Syntax_Syntax.vars = uu____622;_},
          (uu____623, FStar_Pervasives_Native.Some
           (FStar_Syntax_Syntax.Implicit uu____624))::s1::s2::[]))
          when
          (FStar_Syntax_Syntax.fv_eq_lid fv_eq_1 FStar_Parser_Const.eq2_lid)
            &&
            (FStar_Syntax_Syntax.fv_eq_lid fv_eq_2 FStar_Parser_Const.eq2_lid)
          -> args_eq [s1; s2] [t12; t22]
      | (FStar_Syntax_Syntax.Tm_app (t, args), FStar_Syntax_Syntax.Tm_app
         (s, args')) -> (term_eq' t s) && (args_eq args args')
      | (FStar_Syntax_Syntax.Tm_match (t, pats), FStar_Syntax_Syntax.Tm_match
         (t', pats')) ->
          (((FStar_List.length pats) = (FStar_List.length pats')) &&
             (FStar_List.forall2
                (fun uu____991 ->
                   fun uu____992 ->
                     match (uu____991, uu____992) with
                     | ((uu____1041, uu____1042, e),
                        (uu____1044, uu____1045, e')) -> term_eq' e e') pats
                pats'))
            && (term_eq' t t')
      | (FStar_Syntax_Syntax.Tm_ascribed
         (t12, (FStar_Util.Inl t22, uu____1097), uu____1098),
         FStar_Syntax_Syntax.Tm_ascribed
         (s1, (FStar_Util.Inl s2, uu____1101), uu____1102)) ->
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
      | (FStar_Syntax_Syntax.Tm_uvar (u, uu____1234),
         FStar_Syntax_Syntax.Tm_uvar (u', uu____1236)) ->
          FStar_Syntax_Unionfind.equiv u u'
      | (FStar_Syntax_Syntax.Tm_meta (t12, uu____1286), uu____1287) ->
          term_eq' t12 t21
      | (uu____1292, FStar_Syntax_Syntax.Tm_meta (t22, uu____1294)) ->
          term_eq' t11 t22
      | (FStar_Syntax_Syntax.Tm_delayed uu____1299, uu____1300) ->
          let uu____1325 =
            let uu____1326 = FStar_Syntax_Print.tag_of_term t11 in
            let uu____1327 = FStar_Syntax_Print.tag_of_term t21 in
            FStar_Util.format2 "Impossible: %s and %s" uu____1326 uu____1327 in
          failwith uu____1325
      | (uu____1328, FStar_Syntax_Syntax.Tm_delayed uu____1329) ->
          let uu____1354 =
            let uu____1355 = FStar_Syntax_Print.tag_of_term t11 in
            let uu____1356 = FStar_Syntax_Print.tag_of_term t21 in
            FStar_Util.format2 "Impossible: %s and %s" uu____1355 uu____1356 in
          failwith uu____1354
      | (FStar_Syntax_Syntax.Tm_unknown, FStar_Syntax_Syntax.Tm_unknown) ->
          true
      | uu____1357 -> false
let (term_eq :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t1 ->
    fun t2 ->
      let b = term_eq' t1 t2 in
      if Prims.op_Negation b
      then
        (let uu____1370 = FStar_Syntax_Print.term_to_string t1 in
         let uu____1371 = FStar_Syntax_Print.term_to_string t2 in
         FStar_Util.print2 ">>>>>>>>>>>Term %s is not equal to %s\n"
           uu____1370 uu____1371)
      else ();
      b