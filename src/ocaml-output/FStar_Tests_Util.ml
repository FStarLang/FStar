open Prims
let (always : Prims.int -> Prims.bool -> unit) =
  fun id1  ->
    fun b  ->
      if b
      then ()
      else
        (let uu____50675 =
           let uu____50681 =
             let uu____50683 = FStar_Util.string_of_int id1  in
             FStar_Util.format1 "Assertion failed: test %s" uu____50683  in
           (FStar_Errors.Fatal_AssertionFailure, uu____50681)  in
         FStar_Errors.raise_error uu____50675 FStar_Range.dummyRange)
  
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
  'Auu____50702 . 'Auu____50702 -> 'Auu____50702 FStar_Syntax_Syntax.syntax =
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
      let uu____50737 =
        let uu____50744 =
          let uu____50745 =
            let uu____50762 = FStar_List.map FStar_Syntax_Syntax.as_arg ts
               in
            (x1, uu____50762)  in
          FStar_Syntax_Syntax.Tm_app uu____50745  in
        FStar_Syntax_Syntax.mk uu____50744  in
      uu____50737 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
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
             (fun uu____50841  ->
                fun uu____50842  ->
                  match (uu____50841, uu____50842) with
                  | ((x1,uu____50857),(y1,uu____50859)) ->
                      term_eq' x1.FStar_Syntax_Syntax.sort
                        y1.FStar_Syntax_Syntax.sort) xs ys)
         in
      let args_eq xs ys =
        ((FStar_List.length xs) = (FStar_List.length ys)) &&
          (FStar_List.forall2
             (fun uu____50970  ->
                fun uu____50971  ->
                  match (uu____50970, uu____50971) with
                  | ((a,imp),(b,imp')) ->
                      (term_eq' a b) &&
                        (let uu____51042 =
                           FStar_Syntax_Util.eq_aqual imp imp'  in
                         uu____51042 = FStar_Syntax_Util.Equal)) xs ys)
         in
      let comp_eq c d =
        match ((c.FStar_Syntax_Syntax.n), (d.FStar_Syntax_Syntax.n)) with
        | (FStar_Syntax_Syntax.Total
           (t,uu____51057),FStar_Syntax_Syntax.Total (s,uu____51059)) ->
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
        | uu____51078 -> false  in
      match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n)) with
      | (FStar_Syntax_Syntax.Tm_lazy l,uu____51086) ->
          let uu____51087 =
            let uu____51090 =
              let uu____51099 =
                FStar_ST.op_Bang FStar_Syntax_Syntax.lazy_chooser  in
              FStar_Util.must uu____51099  in
            uu____51090 l.FStar_Syntax_Syntax.lkind l  in
          term_eq' uu____51087 t21
      | (uu____51149,FStar_Syntax_Syntax.Tm_lazy l) ->
          let uu____51151 =
            let uu____51154 =
              let uu____51163 =
                FStar_ST.op_Bang FStar_Syntax_Syntax.lazy_chooser  in
              FStar_Util.must uu____51163  in
            uu____51154 l.FStar_Syntax_Syntax.lkind l  in
          term_eq' t11 uu____51151
      | (FStar_Syntax_Syntax.Tm_bvar x1,FStar_Syntax_Syntax.Tm_bvar y1) ->
          x1.FStar_Syntax_Syntax.index = y1.FStar_Syntax_Syntax.index
      | (FStar_Syntax_Syntax.Tm_name x1,FStar_Syntax_Syntax.Tm_name y1) ->
          FStar_Syntax_Syntax.bv_eq x1 y1
      | (FStar_Syntax_Syntax.Tm_fvar f,FStar_Syntax_Syntax.Tm_fvar g) ->
          FStar_Syntax_Syntax.fv_eq f g
      | (FStar_Syntax_Syntax.Tm_uinst
         (t,uu____51221),FStar_Syntax_Syntax.Tm_uinst (s,uu____51223)) ->
          term_eq' t s
      | (FStar_Syntax_Syntax.Tm_constant c1,FStar_Syntax_Syntax.Tm_constant
         c2) -> FStar_Const.eq_const c1 c2
      | (FStar_Syntax_Syntax.Tm_type u,FStar_Syntax_Syntax.Tm_type v1) ->
          u = v1
      | (FStar_Syntax_Syntax.Tm_abs
         (xs,t,uu____51238),FStar_Syntax_Syntax.Tm_abs (ys,u,uu____51241))
          when (FStar_List.length xs) = (FStar_List.length ys) ->
          (binders_eq xs ys) && (term_eq' t u)
      | (FStar_Syntax_Syntax.Tm_abs
         (xs,t,uu____51304),FStar_Syntax_Syntax.Tm_abs (ys,u,uu____51307)) ->
          if (FStar_List.length xs) > (FStar_List.length ys)
          then
            let uu____51370 = FStar_Util.first_N (FStar_List.length ys) xs
               in
            (match uu____51370 with
             | (xs1,xs') ->
                 let t12 =
                   let uu____51441 =
                     let uu____51448 =
                       let uu____51449 =
                         let uu____51468 =
                           FStar_Syntax_Syntax.mk
                             (FStar_Syntax_Syntax.Tm_abs
                                (xs', t, FStar_Pervasives_Native.None))
                             FStar_Pervasives_Native.None
                             t11.FStar_Syntax_Syntax.pos
                            in
                         (xs1, uu____51468, FStar_Pervasives_Native.None)  in
                       FStar_Syntax_Syntax.Tm_abs uu____51449  in
                     FStar_Syntax_Syntax.mk uu____51448  in
                   uu____51441 FStar_Pervasives_Native.None
                     t11.FStar_Syntax_Syntax.pos
                    in
                 term_eq' t12 t21)
          else
            (let uu____51497 = FStar_Util.first_N (FStar_List.length xs) ys
                in
             match uu____51497 with
             | (ys1,ys') ->
                 let t22 =
                   let uu____51568 =
                     let uu____51575 =
                       let uu____51576 =
                         let uu____51595 =
                           FStar_Syntax_Syntax.mk
                             (FStar_Syntax_Syntax.Tm_abs
                                (ys', u, FStar_Pervasives_Native.None))
                             FStar_Pervasives_Native.None
                             t21.FStar_Syntax_Syntax.pos
                            in
                         (ys1, uu____51595, FStar_Pervasives_Native.None)  in
                       FStar_Syntax_Syntax.Tm_abs uu____51576  in
                     FStar_Syntax_Syntax.mk uu____51575  in
                   uu____51568 FStar_Pervasives_Native.None
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
            FStar_Syntax_Syntax.pos = uu____51679;
            FStar_Syntax_Syntax.vars = uu____51680;_},(uu____51681,FStar_Pervasives_Native.Some
                                                       (FStar_Syntax_Syntax.Implicit
                                                       uu____51682))::t12::t22::[]),FStar_Syntax_Syntax.Tm_app
         ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv_eq_2;
            FStar_Syntax_Syntax.pos = uu____51686;
            FStar_Syntax_Syntax.vars = uu____51687;_},(uu____51688,FStar_Pervasives_Native.Some
                                                       (FStar_Syntax_Syntax.Implicit
                                                       uu____51689))::s1::s2::[]))
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
                (fun uu____52070  ->
                   fun uu____52071  ->
                     match (uu____52070, uu____52071) with
                     | ((uu____52129,uu____52130,e),(uu____52132,uu____52133,e'))
                         -> term_eq' e e') pats pats'))
            && (term_eq' t t')
      | (FStar_Syntax_Syntax.Tm_ascribed
         (t12,(FStar_Util.Inl t22,uu____52197),uu____52198),FStar_Syntax_Syntax.Tm_ascribed
         (s1,(FStar_Util.Inl s2,uu____52201),uu____52202)) ->
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
         (u,uu____52341),FStar_Syntax_Syntax.Tm_uvar (u',uu____52343)) ->
          FStar_Syntax_Unionfind.equiv u.FStar_Syntax_Syntax.ctx_uvar_head
            u'.FStar_Syntax_Syntax.ctx_uvar_head
      | (FStar_Syntax_Syntax.Tm_meta (t12,uu____52377),uu____52378) ->
          term_eq' t12 t21
      | (uu____52383,FStar_Syntax_Syntax.Tm_meta (t22,uu____52385)) ->
          term_eq' t11 t22
      | (FStar_Syntax_Syntax.Tm_delayed uu____52390,uu____52391) ->
          let uu____52414 =
            let uu____52416 = FStar_Syntax_Print.tag_of_term t11  in
            let uu____52418 = FStar_Syntax_Print.tag_of_term t21  in
            FStar_Util.format2 "Impossible: %s and %s" uu____52416
              uu____52418
             in
          failwith uu____52414
      | (uu____52422,FStar_Syntax_Syntax.Tm_delayed uu____52423) ->
          let uu____52446 =
            let uu____52448 = FStar_Syntax_Print.tag_of_term t11  in
            let uu____52450 = FStar_Syntax_Print.tag_of_term t21  in
            FStar_Util.format2 "Impossible: %s and %s" uu____52448
              uu____52450
             in
          failwith uu____52446
      | (FStar_Syntax_Syntax.Tm_unknown ,FStar_Syntax_Syntax.Tm_unknown ) ->
          true
      | uu____52455 -> false
  
let (term_eq :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.bool)
  =
  fun t1  ->
    fun t2  ->
      let b = term_eq' t1 t2  in
      if Prims.op_Negation b
      then
        (let uu____52485 = FStar_Syntax_Print.term_to_string t1  in
         let uu____52487 = FStar_Syntax_Print.term_to_string t2  in
         FStar_Util.print2 ">>>>>>>>>>>Term %s is not equal to %s\n"
           uu____52485 uu____52487)
      else ();
      b
  