open Prims
let (always : Prims.int -> Prims.bool -> unit) =
  fun id  ->
    fun b  ->
      if b
      then ()
      else
        (let uu____17 =
           let uu____23 =
             let uu____25 = FStar_Util.string_of_int id  in
             FStar_Util.format1 "Assertion failed: test %s" uu____25  in
           (FStar_Errors.Fatal_AssertionFailure, uu____23)  in
         FStar_Errors.raise_error uu____17 FStar_Range.dummyRange)
  
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
  
let tm : 'uuuuuu44 . 'uuuuuu44 -> 'uuuuuu44 FStar_Syntax_Syntax.syntax =
  fun t  -> FStar_Syntax_Syntax.mk t FStar_Range.dummyRange 
let (nm : FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.term) =
  fun x1  -> FStar_Syntax_Syntax.bv_to_name x1 
let (app :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term Prims.list ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun x1  ->
    fun ts  ->
      let uu____79 =
        let uu____80 =
          let uu____97 = FStar_List.map FStar_Syntax_Syntax.as_arg ts  in
          (x1, uu____97)  in
        FStar_Syntax_Syntax.Tm_app uu____80  in
      FStar_Syntax_Syntax.mk uu____79 FStar_Range.dummyRange
  
let rec (term_eq' :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.bool)
  =
  fun t1  ->
    fun t2  ->
      let t11 = FStar_Syntax_Subst.compress t1  in
      let t21 = FStar_Syntax_Subst.compress t2  in
      let binders_eq xs ys =
        ((FStar_List.length xs) = (FStar_List.length ys)) &&
          (FStar_List.forall2
             (fun uu____176  ->
                fun uu____177  ->
                  match (uu____176, uu____177) with
                  | ((x1,uu____192),(y1,uu____194)) ->
                      term_eq' x1.FStar_Syntax_Syntax.sort
                        y1.FStar_Syntax_Syntax.sort) xs ys)
         in
      let args_eq xs ys =
        ((FStar_List.length xs) = (FStar_List.length ys)) &&
          (FStar_List.forall2
             (fun uu____305  ->
                fun uu____306  ->
                  match (uu____305, uu____306) with
                  | ((a,imp),(b,imp')) ->
                      (term_eq' a b) &&
                        (let uu____377 = FStar_Syntax_Util.eq_aqual imp imp'
                            in
                         uu____377 = FStar_Syntax_Util.Equal)) xs ys)
         in
      let comp_eq c d =
        match ((c.FStar_Syntax_Syntax.n), (d.FStar_Syntax_Syntax.n)) with
        | (FStar_Syntax_Syntax.Total (t,uu____392),FStar_Syntax_Syntax.Total
           (s,uu____394)) -> term_eq' t s
        | (FStar_Syntax_Syntax.Comp ct1,FStar_Syntax_Syntax.Comp ct2) ->
            ((FStar_Ident.lid_equals ct1.FStar_Syntax_Syntax.effect_name
                ct2.FStar_Syntax_Syntax.effect_name)
               &&
               (term_eq' ct1.FStar_Syntax_Syntax.result_typ
                  ct2.FStar_Syntax_Syntax.result_typ))
              &&
              (args_eq ct1.FStar_Syntax_Syntax.effect_args
                 ct2.FStar_Syntax_Syntax.effect_args)
        | uu____413 -> false  in
      match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n)) with
      | (FStar_Syntax_Syntax.Tm_lazy l,uu____421) ->
          let uu____422 =
            let uu____425 =
              let uu____434 =
                FStar_ST.op_Bang FStar_Syntax_Syntax.lazy_chooser  in
              FStar_Util.must uu____434  in
            uu____425 l.FStar_Syntax_Syntax.lkind l  in
          term_eq' uu____422 t21
      | (uu____484,FStar_Syntax_Syntax.Tm_lazy l) ->
          let uu____486 =
            let uu____489 =
              let uu____498 =
                FStar_ST.op_Bang FStar_Syntax_Syntax.lazy_chooser  in
              FStar_Util.must uu____498  in
            uu____489 l.FStar_Syntax_Syntax.lkind l  in
          term_eq' t11 uu____486
      | (FStar_Syntax_Syntax.Tm_bvar x1,FStar_Syntax_Syntax.Tm_bvar y1) ->
          x1.FStar_Syntax_Syntax.index = y1.FStar_Syntax_Syntax.index
      | (FStar_Syntax_Syntax.Tm_name x1,FStar_Syntax_Syntax.Tm_name y1) ->
          FStar_Syntax_Syntax.bv_eq x1 y1
      | (FStar_Syntax_Syntax.Tm_fvar f,FStar_Syntax_Syntax.Tm_fvar g) ->
          FStar_Syntax_Syntax.fv_eq f g
      | (FStar_Syntax_Syntax.Tm_uinst
         (t,uu____556),FStar_Syntax_Syntax.Tm_uinst (s,uu____558)) ->
          term_eq' t s
      | (FStar_Syntax_Syntax.Tm_constant c1,FStar_Syntax_Syntax.Tm_constant
         c2) -> FStar_Const.eq_const c1 c2
      | (FStar_Syntax_Syntax.Tm_type u,FStar_Syntax_Syntax.Tm_type v) ->
          u = v
      | (FStar_Syntax_Syntax.Tm_abs
         (xs,t,uu____573),FStar_Syntax_Syntax.Tm_abs (ys,u,uu____576)) when
          (FStar_List.length xs) = (FStar_List.length ys) ->
          (binders_eq xs ys) && (term_eq' t u)
      | (FStar_Syntax_Syntax.Tm_abs
         (xs,t,uu____639),FStar_Syntax_Syntax.Tm_abs (ys,u,uu____642)) ->
          if (FStar_List.length xs) > (FStar_List.length ys)
          then
            let uu____705 = FStar_Util.first_N (FStar_List.length ys) xs  in
            (match uu____705 with
             | (xs1,xs') ->
                 let t12 =
                   let uu____776 =
                     let uu____777 =
                       let uu____796 =
                         FStar_Syntax_Syntax.mk
                           (FStar_Syntax_Syntax.Tm_abs
                              (xs', t, FStar_Pervasives_Native.None))
                           t11.FStar_Syntax_Syntax.pos
                          in
                       (xs1, uu____796, FStar_Pervasives_Native.None)  in
                     FStar_Syntax_Syntax.Tm_abs uu____777  in
                   FStar_Syntax_Syntax.mk uu____776
                     t11.FStar_Syntax_Syntax.pos
                    in
                 term_eq' t12 t21)
          else
            (let uu____825 = FStar_Util.first_N (FStar_List.length xs) ys  in
             match uu____825 with
             | (ys1,ys') ->
                 let t22 =
                   let uu____896 =
                     let uu____897 =
                       let uu____916 =
                         FStar_Syntax_Syntax.mk
                           (FStar_Syntax_Syntax.Tm_abs
                              (ys', u, FStar_Pervasives_Native.None))
                           t21.FStar_Syntax_Syntax.pos
                          in
                       (ys1, uu____916, FStar_Pervasives_Native.None)  in
                     FStar_Syntax_Syntax.Tm_abs uu____897  in
                   FStar_Syntax_Syntax.mk uu____896
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
            FStar_Syntax_Syntax.pos = uu____1000;
            FStar_Syntax_Syntax.vars = uu____1001;_},(uu____1002,FStar_Pervasives_Native.Some
                                                      (FStar_Syntax_Syntax.Implicit
                                                      uu____1003))::t12::t22::[]),FStar_Syntax_Syntax.Tm_app
         ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv_eq_2;
            FStar_Syntax_Syntax.pos = uu____1007;
            FStar_Syntax_Syntax.vars = uu____1008;_},(uu____1009,FStar_Pervasives_Native.Some
                                                      (FStar_Syntax_Syntax.Implicit
                                                      uu____1010))::s1::s2::[]))
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
                (fun uu____1391  ->
                   fun uu____1392  ->
                     match (uu____1391, uu____1392) with
                     | ((uu____1450,uu____1451,e),(uu____1453,uu____1454,e'))
                         -> term_eq' e e') pats pats'))
            && (term_eq' t t')
      | (FStar_Syntax_Syntax.Tm_ascribed
         (t12,(FStar_Util.Inl t22,uu____1518),uu____1519),FStar_Syntax_Syntax.Tm_ascribed
         (s1,(FStar_Util.Inl s2,uu____1522),uu____1523)) ->
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
         (u,uu____1662),FStar_Syntax_Syntax.Tm_uvar (u',uu____1664)) ->
          FStar_Syntax_Unionfind.equiv u.FStar_Syntax_Syntax.ctx_uvar_head
            u'.FStar_Syntax_Syntax.ctx_uvar_head
      | (FStar_Syntax_Syntax.Tm_meta (t12,uu____1698),uu____1699) ->
          term_eq' t12 t21
      | (uu____1704,FStar_Syntax_Syntax.Tm_meta (t22,uu____1706)) ->
          term_eq' t11 t22
      | (FStar_Syntax_Syntax.Tm_delayed uu____1711,uu____1712) ->
          let uu____1727 =
            let uu____1729 = FStar_Syntax_Print.tag_of_term t11  in
            let uu____1731 = FStar_Syntax_Print.tag_of_term t21  in
            FStar_Util.format2 "Impossible: %s and %s" uu____1729 uu____1731
             in
          failwith uu____1727
      | (uu____1735,FStar_Syntax_Syntax.Tm_delayed uu____1736) ->
          let uu____1751 =
            let uu____1753 = FStar_Syntax_Print.tag_of_term t11  in
            let uu____1755 = FStar_Syntax_Print.tag_of_term t21  in
            FStar_Util.format2 "Impossible: %s and %s" uu____1753 uu____1755
             in
          failwith uu____1751
      | (FStar_Syntax_Syntax.Tm_unknown ,FStar_Syntax_Syntax.Tm_unknown ) ->
          true
      | uu____1760 -> false
  
let (term_eq :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.bool)
  =
  fun t1  ->
    fun t2  ->
      let b = term_eq' t1 t2  in
      if Prims.op_Negation b
      then
        (let uu____1790 = FStar_Syntax_Print.term_to_string t1  in
         let uu____1792 = FStar_Syntax_Print.term_to_string t2  in
         FStar_Util.print2 ">>>>>>>>>>>Term %s is not equal to %s\n"
           uu____1790 uu____1792)
      else ();
      b
  