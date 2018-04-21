open Prims
let always : Prims.int -> Prims.bool -> unit =
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
  
let x : FStar_Syntax_Syntax.bv =
  FStar_Syntax_Syntax.gen_bv "x" FStar_Pervasives_Native.None
    FStar_Syntax_Syntax.tun
  
let y : FStar_Syntax_Syntax.bv =
  FStar_Syntax_Syntax.gen_bv "y" FStar_Pervasives_Native.None
    FStar_Syntax_Syntax.tun
  
let n : FStar_Syntax_Syntax.bv =
  FStar_Syntax_Syntax.gen_bv "n" FStar_Pervasives_Native.None
    FStar_Syntax_Syntax.tun
  
let h : FStar_Syntax_Syntax.bv =
  FStar_Syntax_Syntax.gen_bv "h" FStar_Pervasives_Native.None
    FStar_Syntax_Syntax.tun
  
let m : FStar_Syntax_Syntax.bv =
  FStar_Syntax_Syntax.gen_bv "m" FStar_Pervasives_Native.None
    FStar_Syntax_Syntax.tun
  
let tm : 'Auu____23 . 'Auu____23 -> 'Auu____23 FStar_Syntax_Syntax.syntax =
  fun t  ->
    FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None
      FStar_Range.dummyRange
  
let nm : FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.term =
  fun x1  -> FStar_Syntax_Syntax.bv_to_name x1 
let app :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term Prims.list ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun x1  ->
    fun ts  ->
      let uu____56 =
        let uu____63 =
          let uu____64 =
            let uu____79 = FStar_List.map FStar_Syntax_Syntax.as_arg ts  in
            (x1, uu____79)  in
          FStar_Syntax_Syntax.Tm_app uu____64  in
        FStar_Syntax_Syntax.mk uu____63  in
      uu____56 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let rec term_eq' :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun t1  ->
    fun t2  ->
      let t11 = FStar_Syntax_Subst.compress t1  in
      let t21 = FStar_Syntax_Subst.compress t2  in
      let binders_eq xs ys =
        ((FStar_List.length xs) = (FStar_List.length ys)) &&
          (FStar_List.forall2
             (fun uu____126  ->
                fun uu____127  ->
                  match (uu____126, uu____127) with
                  | ((x1,uu____129),(y1,uu____131)) ->
                      term_eq' x1.FStar_Syntax_Syntax.sort
                        y1.FStar_Syntax_Syntax.sort) xs ys)
         in
      let args_eq xs ys =
        ((FStar_List.length xs) = (FStar_List.length ys)) &&
          (FStar_List.forall2
             (fun uu____197  ->
                fun uu____198  ->
                  match (uu____197, uu____198) with
                  | ((a,imp),(b,imp')) -> (term_eq' a b) && (imp = imp')) xs
             ys)
         in
      let comp_eq c d =
        match ((c.FStar_Syntax_Syntax.n), (d.FStar_Syntax_Syntax.n)) with
        | (FStar_Syntax_Syntax.Total (t,uu____239),FStar_Syntax_Syntax.Total
           (s,uu____241)) -> term_eq' t s
        | (FStar_Syntax_Syntax.Comp ct1,FStar_Syntax_Syntax.Comp ct2) ->
            ((FStar_Ident.lid_equals ct1.FStar_Syntax_Syntax.effect_name
                ct2.FStar_Syntax_Syntax.effect_name)
               &&
               (term_eq' ct1.FStar_Syntax_Syntax.result_typ
                  ct2.FStar_Syntax_Syntax.result_typ))
              &&
              (args_eq ct1.FStar_Syntax_Syntax.effect_args
                 ct2.FStar_Syntax_Syntax.effect_args)
        | uu____260 -> false  in
      match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n)) with
      | (FStar_Syntax_Syntax.Tm_bvar x1,FStar_Syntax_Syntax.Tm_bvar y1) ->
          x1.FStar_Syntax_Syntax.index = y1.FStar_Syntax_Syntax.index
      | (FStar_Syntax_Syntax.Tm_name x1,FStar_Syntax_Syntax.Tm_name y1) ->
          FStar_Syntax_Syntax.bv_eq x1 y1
      | (FStar_Syntax_Syntax.Tm_fvar f,FStar_Syntax_Syntax.Tm_fvar g) ->
          FStar_Syntax_Syntax.fv_eq f g
      | (FStar_Syntax_Syntax.Tm_uinst
         (t,uu____272),FStar_Syntax_Syntax.Tm_uinst (s,uu____274)) ->
          term_eq' t s
      | (FStar_Syntax_Syntax.Tm_constant c1,FStar_Syntax_Syntax.Tm_constant
         c2) -> c1 = c2
      | (FStar_Syntax_Syntax.Tm_type u,FStar_Syntax_Syntax.Tm_type v1) ->
          u = v1
      | (FStar_Syntax_Syntax.Tm_abs
         (xs,t,uu____289),FStar_Syntax_Syntax.Tm_abs (ys,u,uu____292)) when
          (FStar_List.length xs) = (FStar_List.length ys) ->
          (binders_eq xs ys) && (term_eq' t u)
      | (FStar_Syntax_Syntax.Tm_abs
         (xs,t,uu____343),FStar_Syntax_Syntax.Tm_abs (ys,u,uu____346)) ->
          if (FStar_List.length xs) > (FStar_List.length ys)
          then
            let uu____395 = FStar_Util.first_N (FStar_List.length ys) xs  in
            (match uu____395 with
             | (xs1,xs') ->
                 let t12 =
                   let uu____449 =
                     let uu____456 =
                       let uu____457 =
                         let uu____474 =
                           FStar_Syntax_Syntax.mk
                             (FStar_Syntax_Syntax.Tm_abs
                                (xs', t, FStar_Pervasives_Native.None))
                             FStar_Pervasives_Native.None
                             t11.FStar_Syntax_Syntax.pos
                            in
                         (xs1, uu____474, FStar_Pervasives_Native.None)  in
                       FStar_Syntax_Syntax.Tm_abs uu____457  in
                     FStar_Syntax_Syntax.mk uu____456  in
                   uu____449 FStar_Pervasives_Native.None
                     t11.FStar_Syntax_Syntax.pos
                    in
                 term_eq' t12 t21)
          else
            (let uu____501 = FStar_Util.first_N (FStar_List.length xs) ys  in
             match uu____501 with
             | (ys1,ys') ->
                 let t22 =
                   let uu____555 =
                     let uu____562 =
                       let uu____563 =
                         let uu____580 =
                           FStar_Syntax_Syntax.mk
                             (FStar_Syntax_Syntax.Tm_abs
                                (ys', u, FStar_Pervasives_Native.None))
                             FStar_Pervasives_Native.None
                             t21.FStar_Syntax_Syntax.pos
                            in
                         (ys1, uu____580, FStar_Pervasives_Native.None)  in
                       FStar_Syntax_Syntax.Tm_abs uu____563  in
                     FStar_Syntax_Syntax.mk uu____562  in
                   uu____555 FStar_Pervasives_Native.None
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
            FStar_Syntax_Syntax.pos = uu____655;
            FStar_Syntax_Syntax.vars = uu____656;_},(uu____657,FStar_Pervasives_Native.Some
                                                     (FStar_Syntax_Syntax.Implicit
                                                     uu____658))::t12::t22::[]),FStar_Syntax_Syntax.Tm_app
         ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv_eq_2;
            FStar_Syntax_Syntax.pos = uu____662;
            FStar_Syntax_Syntax.vars = uu____663;_},(uu____664,FStar_Pervasives_Native.Some
                                                     (FStar_Syntax_Syntax.Implicit
                                                     uu____665))::s1::s2::[]))
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
                (fun uu____1032  ->
                   fun uu____1033  ->
                     match (uu____1032, uu____1033) with
                     | ((uu____1082,uu____1083,e),(uu____1085,uu____1086,e'))
                         -> term_eq' e e') pats pats'))
            && (term_eq' t t')
      | (FStar_Syntax_Syntax.Tm_ascribed
         (t12,(FStar_Util.Inl t22,uu____1138),uu____1139),FStar_Syntax_Syntax.Tm_ascribed
         (s1,(FStar_Util.Inl s2,uu____1142),uu____1143)) ->
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
         (u,uu____1275),FStar_Syntax_Syntax.Tm_uvar (u',uu____1277)) ->
          FStar_Syntax_Unionfind.equiv u u'
      | (FStar_Syntax_Syntax.Tm_meta (t12,uu____1327),uu____1328) ->
          term_eq' t12 t21
      | (uu____1333,FStar_Syntax_Syntax.Tm_meta (t22,uu____1335)) ->
          term_eq' t11 t22
      | (FStar_Syntax_Syntax.Tm_delayed uu____1340,uu____1341) ->
          let uu____1366 =
            let uu____1367 = FStar_Syntax_Print.tag_of_term t11  in
            let uu____1368 = FStar_Syntax_Print.tag_of_term t21  in
            FStar_Util.format2 "Impossible: %s and %s" uu____1367 uu____1368
             in
          failwith uu____1366
      | (uu____1369,FStar_Syntax_Syntax.Tm_delayed uu____1370) ->
          let uu____1395 =
            let uu____1396 = FStar_Syntax_Print.tag_of_term t11  in
            let uu____1397 = FStar_Syntax_Print.tag_of_term t21  in
            FStar_Util.format2 "Impossible: %s and %s" uu____1396 uu____1397
             in
          failwith uu____1395
      | (FStar_Syntax_Syntax.Tm_unknown ,FStar_Syntax_Syntax.Tm_unknown ) ->
          true
      | uu____1398 -> false
  
let term_eq :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun t1  ->
    fun t2  ->
      let b = term_eq' t1 t2  in
      if Prims.op_Negation b
      then
        (let uu____1415 = FStar_Syntax_Print.term_to_string t1  in
         let uu____1416 = FStar_Syntax_Print.term_to_string t2  in
         FStar_Util.print2 ">>>>>>>>>>>Term %s is not equal to %s\n"
           uu____1415 uu____1416)
      else ();
      b
  