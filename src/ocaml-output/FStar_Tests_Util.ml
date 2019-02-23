open Prims
let (always : Prims.int -> Prims.bool -> unit) =
  fun id1  ->
    fun b  ->
      if b
      then ()
      else
        (let uu____55233 =
           let uu____55239 =
             let uu____55241 = FStar_Util.string_of_int id1  in
             FStar_Util.format1 "Assertion failed: test %s" uu____55241  in
           (FStar_Errors.Fatal_AssertionFailure, uu____55239)  in
         FStar_Errors.raise_error uu____55233 FStar_Range.dummyRange)
  
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
  
let tm :
  'Auu____55260 . 'Auu____55260 -> 'Auu____55260 FStar_Syntax_Syntax.syntax =
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
      let uu____55295 =
        let uu____55302 =
          let uu____55303 =
            let uu____55320 = FStar_List.map FStar_Syntax_Syntax.as_arg ts
               in
            (x1, uu____55320)  in
          FStar_Syntax_Syntax.Tm_app uu____55303  in
        FStar_Syntax_Syntax.mk uu____55302  in
      uu____55295 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
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
             (fun uu____55402  ->
                fun uu____55403  ->
                  match (uu____55402, uu____55403) with
                  | ((x1,uu____55418),(y1,uu____55420)) ->
                      term_eq' x1.FStar_Syntax_Syntax.sort
                        y1.FStar_Syntax_Syntax.sort) xs ys)
         in
      let args_eq xs ys =
        ((FStar_List.length xs) = (FStar_List.length ys)) &&
          (FStar_List.forall2
             (fun uu____55531  ->
                fun uu____55532  ->
                  match (uu____55531, uu____55532) with
                  | ((a,imp),(b,imp')) ->
                      (term_eq' a b) &&
                        (let uu____55603 =
                           FStar_Syntax_Util.eq_aqual imp imp'  in
                         uu____55603 = FStar_Syntax_Util.Equal)) xs ys)
         in
      let comp_eq c d =
        match ((c.FStar_Syntax_Syntax.n), (d.FStar_Syntax_Syntax.n)) with
        | (FStar_Syntax_Syntax.Total
           (t,uu____55618),FStar_Syntax_Syntax.Total (s,uu____55620)) ->
            term_eq' t s
        | (FStar_Syntax_Syntax.Comp ct1,FStar_Syntax_Syntax.Comp ct2) ->
            ((FStar_Ident.lid_equals ct1.FStar_Syntax_Syntax.effect_name
                ct2.FStar_Syntax_Syntax.effect_name)
               &&
               (term_eq' ct1.FStar_Syntax_Syntax.result_typ
                  ct2.FStar_Syntax_Syntax.result_typ))
              &&
              (args_eq ct1.FStar_Syntax_Syntax.effect_args
                 ct2.FStar_Syntax_Syntax.effect_args)
        | uu____55639 -> false  in
      match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n)) with
      | (FStar_Syntax_Syntax.Tm_lazy l,uu____55647) ->
          let uu____55648 =
            let uu____55651 =
              let uu____55660 =
                FStar_ST.op_Bang FStar_Syntax_Syntax.lazy_chooser  in
              FStar_Util.must uu____55660  in
            uu____55651 l.FStar_Syntax_Syntax.lkind l  in
          term_eq' uu____55648 t21
      | (uu____55710,FStar_Syntax_Syntax.Tm_lazy l) ->
          let uu____55712 =
            let uu____55715 =
              let uu____55724 =
                FStar_ST.op_Bang FStar_Syntax_Syntax.lazy_chooser  in
              FStar_Util.must uu____55724  in
            uu____55715 l.FStar_Syntax_Syntax.lkind l  in
          term_eq' t11 uu____55712
      | (FStar_Syntax_Syntax.Tm_bvar x1,FStar_Syntax_Syntax.Tm_bvar y1) ->
          x1.FStar_Syntax_Syntax.index = y1.FStar_Syntax_Syntax.index
      | (FStar_Syntax_Syntax.Tm_name x1,FStar_Syntax_Syntax.Tm_name y1) ->
          FStar_Syntax_Syntax.bv_eq x1 y1
      | (FStar_Syntax_Syntax.Tm_fvar f,FStar_Syntax_Syntax.Tm_fvar g) ->
          FStar_Syntax_Syntax.fv_eq f g
      | (FStar_Syntax_Syntax.Tm_uinst
         (t,uu____55782),FStar_Syntax_Syntax.Tm_uinst (s,uu____55784)) ->
          term_eq' t s
      | (FStar_Syntax_Syntax.Tm_constant c1,FStar_Syntax_Syntax.Tm_constant
         c2) -> FStar_Const.eq_const c1 c2
      | (FStar_Syntax_Syntax.Tm_type u,FStar_Syntax_Syntax.Tm_type v1) ->
          u = v1
      | (FStar_Syntax_Syntax.Tm_abs
         (xs,t,uu____55799),FStar_Syntax_Syntax.Tm_abs (ys,u,uu____55802))
          when (FStar_List.length xs) = (FStar_List.length ys) ->
          (binders_eq xs ys) && (term_eq' t u)
      | (FStar_Syntax_Syntax.Tm_abs
         (xs,t,uu____55865),FStar_Syntax_Syntax.Tm_abs (ys,u,uu____55868)) ->
          if (FStar_List.length xs) > (FStar_List.length ys)
          then
            let uu____55931 = FStar_Util.first_N (FStar_List.length ys) xs
               in
            (match uu____55931 with
             | (xs1,xs') ->
                 let t12 =
                   let uu____56002 =
                     let uu____56009 =
                       let uu____56010 =
                         let uu____56029 =
                           FStar_Syntax_Syntax.mk
                             (FStar_Syntax_Syntax.Tm_abs
                                (xs', t, FStar_Pervasives_Native.None))
                             FStar_Pervasives_Native.None
                             t11.FStar_Syntax_Syntax.pos
                            in
                         (xs1, uu____56029, FStar_Pervasives_Native.None)  in
                       FStar_Syntax_Syntax.Tm_abs uu____56010  in
                     FStar_Syntax_Syntax.mk uu____56009  in
                   uu____56002 FStar_Pervasives_Native.None
                     t11.FStar_Syntax_Syntax.pos
                    in
                 term_eq' t12 t21)
          else
            (let uu____56061 = FStar_Util.first_N (FStar_List.length xs) ys
                in
             match uu____56061 with
             | (ys1,ys') ->
                 let t22 =
                   let uu____56132 =
                     let uu____56139 =
                       let uu____56140 =
                         let uu____56159 =
                           FStar_Syntax_Syntax.mk
                             (FStar_Syntax_Syntax.Tm_abs
                                (ys', u, FStar_Pervasives_Native.None))
                             FStar_Pervasives_Native.None
                             t21.FStar_Syntax_Syntax.pos
                            in
                         (ys1, uu____56159, FStar_Pervasives_Native.None)  in
                       FStar_Syntax_Syntax.Tm_abs uu____56140  in
                     FStar_Syntax_Syntax.mk uu____56139  in
                   uu____56132 FStar_Pervasives_Native.None
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
            FStar_Syntax_Syntax.pos = uu____56246;
            FStar_Syntax_Syntax.vars = uu____56247;_},(uu____56248,FStar_Pervasives_Native.Some
                                                       (FStar_Syntax_Syntax.Implicit
                                                       uu____56249))::t12::t22::[]),FStar_Syntax_Syntax.Tm_app
         ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv_eq_2;
            FStar_Syntax_Syntax.pos = uu____56253;
            FStar_Syntax_Syntax.vars = uu____56254;_},(uu____56255,FStar_Pervasives_Native.Some
                                                       (FStar_Syntax_Syntax.Implicit
                                                       uu____56256))::s1::s2::[]))
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
                (fun uu____56637  ->
                   fun uu____56638  ->
                     match (uu____56637, uu____56638) with
                     | ((uu____56696,uu____56697,e),(uu____56699,uu____56700,e'))
                         -> term_eq' e e') pats pats'))
            && (term_eq' t t')
      | (FStar_Syntax_Syntax.Tm_ascribed
         (t12,(FStar_Util.Inl t22,uu____56764),uu____56765),FStar_Syntax_Syntax.Tm_ascribed
         (s1,(FStar_Util.Inl s2,uu____56768),uu____56769)) ->
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
         (u,uu____56908),FStar_Syntax_Syntax.Tm_uvar (u',uu____56910)) ->
          FStar_Syntax_Unionfind.equiv u.FStar_Syntax_Syntax.ctx_uvar_head
            u'.FStar_Syntax_Syntax.ctx_uvar_head
      | (FStar_Syntax_Syntax.Tm_meta (t12,uu____56944),uu____56945) ->
          term_eq' t12 t21
      | (uu____56950,FStar_Syntax_Syntax.Tm_meta (t22,uu____56952)) ->
          term_eq' t11 t22
      | (FStar_Syntax_Syntax.Tm_delayed uu____56957,uu____56958) ->
          let uu____56981 =
            let uu____56983 = FStar_Syntax_Print.tag_of_term t11  in
            let uu____56985 = FStar_Syntax_Print.tag_of_term t21  in
            FStar_Util.format2 "Impossible: %s and %s" uu____56983
              uu____56985
             in
          failwith uu____56981
      | (uu____56989,FStar_Syntax_Syntax.Tm_delayed uu____56990) ->
          let uu____57013 =
            let uu____57015 = FStar_Syntax_Print.tag_of_term t11  in
            let uu____57017 = FStar_Syntax_Print.tag_of_term t21  in
            FStar_Util.format2 "Impossible: %s and %s" uu____57015
              uu____57017
             in
          failwith uu____57013
      | (FStar_Syntax_Syntax.Tm_unknown ,FStar_Syntax_Syntax.Tm_unknown ) ->
          true
      | uu____57022 -> false
  
let (term_eq :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.bool)
  =
  fun t1  ->
    fun t2  ->
      let b = term_eq' t1 t2  in
      if Prims.op_Negation b
      then
        (let uu____57052 = FStar_Syntax_Print.term_to_string t1  in
         let uu____57054 = FStar_Syntax_Print.term_to_string t2  in
         FStar_Util.print2 ">>>>>>>>>>>Term %s is not equal to %s\n"
           uu____57052 uu____57054)
      else ();
      b
  