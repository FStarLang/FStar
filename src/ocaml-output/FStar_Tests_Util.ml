open Prims
let (always : Prims.int -> Prims.bool -> unit) =
  fun id1  ->
    fun b  ->
      if b
      then ()
      else
        (let uu____17 =
           let uu____23 =
             let uu____25 = FStar_Util.string_of_int id1  in
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
  
let tm : 'Auu____94 . 'Auu____94 -> 'Auu____94 FStar_Syntax_Syntax.syntax =
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
      let uu____167 =
        let uu____174 =
          let uu____175 =
            let uu____200 = FStar_List.map FStar_Syntax_Syntax.as_arg ts  in
            (x1, uu____200)  in
          FStar_Syntax_Syntax.Tm_app uu____175  in
        FStar_Syntax_Syntax.mk uu____174  in
      uu____167 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
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
             (fun uu____331  ->
                fun uu____332  ->
                  match (uu____331, uu____332) with
                  | ((x1,uu____357),(y1,uu____359)) ->
                      term_eq' x1.FStar_Syntax_Syntax.sort
                        y1.FStar_Syntax_Syntax.sort) xs ys)
         in
      let args_eq xs ys =
        ((FStar_List.length xs) = (FStar_List.length ys)) &&
          (FStar_List.forall2
             (fun uu____532  ->
                fun uu____533  ->
                  match (uu____532, uu____533) with
                  | ((a,imp),(b,imp')) ->
                      (term_eq' a b) &&
                        (let uu____644 = FStar_Syntax_Util.eq_aqual imp imp'
                            in
                         uu____644 = FStar_Syntax_Util.Equal)) xs ys)
         in
      let comp_eq c d =
        match ((c.FStar_Syntax_Syntax.n), (d.FStar_Syntax_Syntax.n)) with
        | (FStar_Syntax_Syntax.Total (t,uu____675),FStar_Syntax_Syntax.Total
           (s,uu____677)) -> term_eq' t s
        | (FStar_Syntax_Syntax.Comp ct1,FStar_Syntax_Syntax.Comp ct2) ->
            ((FStar_Ident.lid_equals ct1.FStar_Syntax_Syntax.effect_name
                ct2.FStar_Syntax_Syntax.effect_name)
               &&
               (term_eq' ct1.FStar_Syntax_Syntax.result_typ
                  ct2.FStar_Syntax_Syntax.result_typ))
              &&
              (args_eq ct1.FStar_Syntax_Syntax.effect_args
                 ct2.FStar_Syntax_Syntax.effect_args)
        | uu____722 -> false  in
      match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n)) with
      | (FStar_Syntax_Syntax.Tm_lazy l,uu____730) ->
          let uu____735 =
            let uu____746 =
              let uu____763 =
                FStar_ST.op_Bang FStar_Syntax_Syntax.lazy_chooser  in
              FStar_Util.must uu____763  in
            uu____746 l.FStar_Syntax_Syntax.lkind l  in
          term_eq' uu____735 t21
      | (uu____845,FStar_Syntax_Syntax.Tm_lazy l) ->
          let uu____851 =
            let uu____862 =
              let uu____879 =
                FStar_ST.op_Bang FStar_Syntax_Syntax.lazy_chooser  in
              FStar_Util.must uu____879  in
            uu____862 l.FStar_Syntax_Syntax.lkind l  in
          term_eq' t11 uu____851
      | (FStar_Syntax_Syntax.Tm_bvar x1,FStar_Syntax_Syntax.Tm_bvar y1) ->
          x1.FStar_Syntax_Syntax.index = y1.FStar_Syntax_Syntax.index
      | (FStar_Syntax_Syntax.Tm_name x1,FStar_Syntax_Syntax.Tm_name y1) ->
          FStar_Syntax_Syntax.bv_eq x1 y1
      | (FStar_Syntax_Syntax.Tm_fvar f,FStar_Syntax_Syntax.Tm_fvar g) ->
          FStar_Syntax_Syntax.fv_eq f g
      | (FStar_Syntax_Syntax.Tm_uinst
         (t,uu____995),FStar_Syntax_Syntax.Tm_uinst (s,uu____997)) ->
          term_eq' t s
      | (FStar_Syntax_Syntax.Tm_constant c1,FStar_Syntax_Syntax.Tm_constant
         c2) -> FStar_Const.eq_const c1 c2
      | (FStar_Syntax_Syntax.Tm_type u,FStar_Syntax_Syntax.Tm_type v1) ->
          u = v1
      | (FStar_Syntax_Syntax.Tm_abs
         (xs,t,uu____1028),FStar_Syntax_Syntax.Tm_abs (ys,u,uu____1031)) when
          (FStar_List.length xs) = (FStar_List.length ys) ->
          (binders_eq xs ys) && (term_eq' t u)
      | (FStar_Syntax_Syntax.Tm_abs
         (xs,t,uu____1168),FStar_Syntax_Syntax.Tm_abs (ys,u,uu____1171)) ->
          if (FStar_List.length xs) > (FStar_List.length ys)
          then
            let uu____1308 = FStar_Util.first_N (FStar_List.length ys) xs  in
            (match uu____1308 with
             | (xs1,xs') ->
                 let t12 =
                   let uu____1427 =
                     let uu____1434 =
                       let uu____1435 =
                         let uu____1470 =
                           FStar_Syntax_Syntax.mk
                             (FStar_Syntax_Syntax.Tm_abs
                                (xs', t, FStar_Pervasives_Native.None))
                             FStar_Pervasives_Native.None
                             t11.FStar_Syntax_Syntax.pos
                            in
                         (xs1, uu____1470, FStar_Pervasives_Native.None)  in
                       FStar_Syntax_Syntax.Tm_abs uu____1435  in
                     FStar_Syntax_Syntax.mk uu____1434  in
                   uu____1427 FStar_Pervasives_Native.None
                     t11.FStar_Syntax_Syntax.pos
                    in
                 term_eq' t12 t21)
          else
            (let uu____1553 = FStar_Util.first_N (FStar_List.length xs) ys
                in
             match uu____1553 with
             | (ys1,ys') ->
                 let t22 =
                   let uu____1672 =
                     let uu____1679 =
                       let uu____1680 =
                         let uu____1715 =
                           FStar_Syntax_Syntax.mk
                             (FStar_Syntax_Syntax.Tm_abs
                                (ys', u, FStar_Pervasives_Native.None))
                             FStar_Pervasives_Native.None
                             t21.FStar_Syntax_Syntax.pos
                            in
                         (ys1, uu____1715, FStar_Pervasives_Native.None)  in
                       FStar_Syntax_Syntax.Tm_abs uu____1680  in
                     FStar_Syntax_Syntax.mk uu____1679  in
                   uu____1672 FStar_Pervasives_Native.None
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
            FStar_Syntax_Syntax.pos = uu____1925;
            FStar_Syntax_Syntax.vars = uu____1926;_},(uu____1927,FStar_Pervasives_Native.Some
                                                      (FStar_Syntax_Syntax.Implicit
                                                      uu____1928))::t12::t22::[]),FStar_Syntax_Syntax.Tm_app
         ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv_eq_2;
            FStar_Syntax_Syntax.pos = uu____1932;
            FStar_Syntax_Syntax.vars = uu____1933;_},(uu____1934,FStar_Pervasives_Native.Some
                                                      (FStar_Syntax_Syntax.Implicit
                                                      uu____1935))::s1::s2::[]))
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
                (fun uu____2570  ->
                   fun uu____2571  ->
                     match (uu____2570, uu____2571) with
                     | ((uu____2667,uu____2668,e),(uu____2670,uu____2671,e'))
                         -> term_eq' e e') pats pats'))
            && (term_eq' t t')
      | (FStar_Syntax_Syntax.Tm_ascribed
         (t12,(FStar_Util.Inl t22,uu____2801),uu____2802),FStar_Syntax_Syntax.Tm_ascribed
         (s1,(FStar_Util.Inl s2,uu____2805),uu____2806)) ->
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
         (u,uu____3157),FStar_Syntax_Syntax.Tm_uvar (u',uu____3159)) ->
          FStar_Syntax_Unionfind.equiv u.FStar_Syntax_Syntax.ctx_uvar_head
            u'.FStar_Syntax_Syntax.ctx_uvar_head
      | (FStar_Syntax_Syntax.Tm_meta (t12,uu____3225),uu____3226) ->
          term_eq' t12 t21
      | (uu____3239,FStar_Syntax_Syntax.Tm_meta (t22,uu____3241)) ->
          term_eq' t11 t22
      | (FStar_Syntax_Syntax.Tm_delayed uu____3254,uu____3255) ->
          let uu____3286 =
            let uu____3288 = FStar_Syntax_Print.tag_of_term t11  in
            let uu____3290 = FStar_Syntax_Print.tag_of_term t21  in
            FStar_Util.format2 "Impossible: %s and %s" uu____3288 uu____3290
             in
          failwith uu____3286
      | (uu____3294,FStar_Syntax_Syntax.Tm_delayed uu____3295) ->
          let uu____3326 =
            let uu____3328 = FStar_Syntax_Print.tag_of_term t11  in
            let uu____3330 = FStar_Syntax_Print.tag_of_term t21  in
            FStar_Util.format2 "Impossible: %s and %s" uu____3328 uu____3330
             in
          failwith uu____3326
      | (FStar_Syntax_Syntax.Tm_unknown ,FStar_Syntax_Syntax.Tm_unknown ) ->
          true
      | uu____3335 -> false
  
let (term_eq :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.bool)
  =
  fun t1  ->
    fun t2  ->
      let b = term_eq' t1 t2  in
      if Prims.op_Negation b
      then
        (let uu____3381 = FStar_Syntax_Print.term_to_string t1  in
         let uu____3383 = FStar_Syntax_Print.term_to_string t2  in
         FStar_Util.print2 ">>>>>>>>>>>Term %s is not equal to %s\n"
           uu____3381 uu____3383)
      else ();
      b
  