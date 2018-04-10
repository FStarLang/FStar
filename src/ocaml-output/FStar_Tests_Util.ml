open Prims
let (always : Prims.int -> Prims.bool -> unit) =
  fun id1  ->
    fun b  ->
      if b
      then ()
      else
        (let uu____12 =
           let uu____17 =
             let uu____18 = FStar_Util.string_of_int id1  in
             FStar_Util.format1 "Assertion failed: test %s" uu____18  in
           (FStar_Errors.Fatal_AssertionFailure, uu____17)  in
         FStar_Errors.raise_error uu____12 FStar_Range.dummyRange)
  
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
  
let tm : 'Auu____23 . 'Auu____23 -> 'Auu____23 FStar_Syntax_Syntax.syntax =
  fun t  ->
    FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None
      FStar_Range.dummyRange
  
let (nm : FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.term) =
  fun x1  -> FStar_Syntax_Syntax.bv_to_name x1 
let (app :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term Prims.list ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun x1  ->
    fun ts  ->
      let uu____56 =
        let uu____61 =
          let uu____62 =
            let uu____77 = FStar_List.map FStar_Syntax_Syntax.as_arg ts  in
            (x1, uu____77)  in
          FStar_Syntax_Syntax.Tm_app uu____62  in
        FStar_Syntax_Syntax.mk uu____61  in
      uu____56 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let rec (term_eq' :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t1  ->
    fun t2  ->
      let t11 = FStar_Syntax_Subst.compress t1  in
      let t21 = FStar_Syntax_Subst.compress t2  in
      let binders_eq xs ys =
        ((FStar_List.length xs) = (FStar_List.length ys)) &&
          (FStar_List.forall2
             (fun uu____122  ->
                fun uu____123  ->
                  match (uu____122, uu____123) with
                  | ((x1,uu____125),(y1,uu____127)) ->
                      term_eq' x1.FStar_Syntax_Syntax.sort
                        y1.FStar_Syntax_Syntax.sort) xs ys)
         in
      let args_eq xs ys =
        ((FStar_List.length xs) = (FStar_List.length ys)) &&
          (FStar_List.forall2
             (fun uu____191  ->
                fun uu____192  ->
                  match (uu____191, uu____192) with
                  | ((a,imp),(b,imp')) -> (term_eq' a b) && (imp = imp')) xs
             ys)
         in
      let comp_eq c d =
        match ((c.FStar_Syntax_Syntax.n), (d.FStar_Syntax_Syntax.n)) with
        | (FStar_Syntax_Syntax.Total (t,uu____231),FStar_Syntax_Syntax.Total
           (s,uu____233)) -> term_eq' t s
        | (FStar_Syntax_Syntax.Comp ct1,FStar_Syntax_Syntax.Comp ct2) ->
            ((FStar_Ident.lid_equals ct1.FStar_Syntax_Syntax.effect_name
                ct2.FStar_Syntax_Syntax.effect_name)
               &&
               (term_eq' ct1.FStar_Syntax_Syntax.result_typ
                  ct2.FStar_Syntax_Syntax.result_typ))
              &&
              (args_eq ct1.FStar_Syntax_Syntax.effect_args
                 ct2.FStar_Syntax_Syntax.effect_args)
        | uu____252 -> false  in
      match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n)) with
      | (FStar_Syntax_Syntax.Tm_bvar x1,FStar_Syntax_Syntax.Tm_bvar y1) ->
          x1.FStar_Syntax_Syntax.index = y1.FStar_Syntax_Syntax.index
      | (FStar_Syntax_Syntax.Tm_name x1,FStar_Syntax_Syntax.Tm_name y1) ->
          FStar_Syntax_Syntax.bv_eq x1 y1
      | (FStar_Syntax_Syntax.Tm_fvar f,FStar_Syntax_Syntax.Tm_fvar g) ->
          FStar_Syntax_Syntax.fv_eq f g
      | (FStar_Syntax_Syntax.Tm_uinst
         (t,uu____264),FStar_Syntax_Syntax.Tm_uinst (s,uu____266)) ->
          term_eq' t s
      | (FStar_Syntax_Syntax.Tm_constant c1,FStar_Syntax_Syntax.Tm_constant
         c2) -> c1 = c2
      | (FStar_Syntax_Syntax.Tm_type u,FStar_Syntax_Syntax.Tm_type v1) ->
          u = v1
      | (FStar_Syntax_Syntax.Tm_abs
         (xs,t,uu____281),FStar_Syntax_Syntax.Tm_abs (ys,u,uu____284)) when
          (FStar_List.length xs) = (FStar_List.length ys) ->
          (binders_eq xs ys) && (term_eq' t u)
      | (FStar_Syntax_Syntax.Tm_abs
         (xs,t,uu____335),FStar_Syntax_Syntax.Tm_abs (ys,u,uu____338)) ->
          if (FStar_List.length xs) > (FStar_List.length ys)
          then
            let uu____387 = FStar_Util.first_N (FStar_List.length ys) xs  in
            (match uu____387 with
             | (xs1,xs') ->
                 let t12 =
                   let uu____441 =
                     let uu____446 =
                       let uu____447 =
                         let uu____464 =
                           FStar_Syntax_Syntax.mk
                             (FStar_Syntax_Syntax.Tm_abs
                                (xs', t, FStar_Pervasives_Native.None))
                             FStar_Pervasives_Native.None
                             t11.FStar_Syntax_Syntax.pos
                            in
                         (xs1, uu____464, FStar_Pervasives_Native.None)  in
                       FStar_Syntax_Syntax.Tm_abs uu____447  in
                     FStar_Syntax_Syntax.mk uu____446  in
                   uu____441 FStar_Pervasives_Native.None
                     t11.FStar_Syntax_Syntax.pos
                    in
                 term_eq' t12 t21)
          else
            (let uu____491 = FStar_Util.first_N (FStar_List.length xs) ys  in
             match uu____491 with
             | (ys1,ys') ->
                 let t22 =
                   let uu____545 =
                     let uu____550 =
                       let uu____551 =
                         let uu____568 =
                           FStar_Syntax_Syntax.mk
                             (FStar_Syntax_Syntax.Tm_abs
                                (ys', u, FStar_Pervasives_Native.None))
                             FStar_Pervasives_Native.None
                             t21.FStar_Syntax_Syntax.pos
                            in
                         (ys1, uu____568, FStar_Pervasives_Native.None)  in
                       FStar_Syntax_Syntax.Tm_abs uu____551  in
                     FStar_Syntax_Syntax.mk uu____550  in
                   uu____545 FStar_Pervasives_Native.None
                     t21.FStar_Syntax_Syntax.pos
                    in
                 term_eq' t11 t22)
      | (FStar_Syntax_Syntax.Tm_arrow (xs,c),FStar_Syntax_Syntax.Tm_arrow
         (ys,d)) -> (binders_eq xs ys) && (comp_eq c d)
      | (FStar_Syntax_Syntax.Tm_refine (x1,t),FStar_Syntax_Syntax.Tm_refine
         (y1,u)) ->
          (term_eq' x1.FStar_Syntax_Syntax.sort y1.FStar_Syntax_Syntax.sort)
            && (term_eq' t u)
      | (FStar_Syntax_Syntax.Tm_app
         ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv_eq_1;
            FStar_Syntax_Syntax.pos = uu____643;
            FStar_Syntax_Syntax.vars = uu____644;_},(uu____645,FStar_Pervasives_Native.Some
                                                     (FStar_Syntax_Syntax.Implicit
                                                     uu____646))::t12::t22::[]),FStar_Syntax_Syntax.Tm_app
         ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv_eq_2;
            FStar_Syntax_Syntax.pos = uu____650;
            FStar_Syntax_Syntax.vars = uu____651;_},(uu____652,FStar_Pervasives_Native.Some
                                                     (FStar_Syntax_Syntax.Implicit
                                                     uu____653))::s1::s2::[]))
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
                (fun uu____1020  ->
                   fun uu____1021  ->
                     match (uu____1020, uu____1021) with
                     | ((uu____1070,uu____1071,e),(uu____1073,uu____1074,e'))
                         -> term_eq' e e') pats pats'))
            && (term_eq' t t')
      | (FStar_Syntax_Syntax.Tm_ascribed
         (t12,(FStar_Util.Inl t22,uu____1126),uu____1127),FStar_Syntax_Syntax.Tm_ascribed
         (s1,(FStar_Util.Inl s2,uu____1130),uu____1131)) ->
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
         (u,uu____1263),FStar_Syntax_Syntax.Tm_uvar (u',uu____1265)) ->
          FStar_Syntax_Unionfind.equiv u u'
      | (FStar_Syntax_Syntax.Tm_meta (t12,uu____1315),uu____1316) ->
          term_eq' t12 t21
      | (uu____1321,FStar_Syntax_Syntax.Tm_meta (t22,uu____1323)) ->
          term_eq' t11 t22
      | (FStar_Syntax_Syntax.Tm_delayed uu____1328,uu____1329) ->
          let uu____1354 =
            let uu____1355 = FStar_Syntax_Print.tag_of_term t11  in
            let uu____1356 = FStar_Syntax_Print.tag_of_term t21  in
            FStar_Util.format2 "Impossible: %s and %s" uu____1355 uu____1356
             in
          failwith uu____1354
      | (uu____1357,FStar_Syntax_Syntax.Tm_delayed uu____1358) ->
          let uu____1383 =
            let uu____1384 = FStar_Syntax_Print.tag_of_term t11  in
            let uu____1385 = FStar_Syntax_Print.tag_of_term t21  in
            FStar_Util.format2 "Impossible: %s and %s" uu____1384 uu____1385
             in
          failwith uu____1383
      | (FStar_Syntax_Syntax.Tm_unknown ,FStar_Syntax_Syntax.Tm_unknown ) ->
          true
      | uu____1386 -> false
  
let (term_eq :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t1  ->
    fun t2  ->
      let b = term_eq' t1 t2  in
      let uu____1402 =
        if Prims.op_Negation b
        then
          let uu____1403 = FStar_Syntax_Print.term_to_string t1  in
          let uu____1404 = FStar_Syntax_Print.term_to_string t2  in
          FStar_Util.print2 ">>>>>>>>>>>Term %s is not equal to %s\n"
            uu____1403 uu____1404
        else ()  in
      b
  