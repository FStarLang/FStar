open Prims
let (always : Prims.int -> Prims.bool -> unit) =
  fun id1  ->
    fun b  ->
      if b
      then ()
      else
        (let uu____55238 =
           let uu____55244 =
             let uu____55246 = FStar_Util.string_of_int id1  in
             FStar_Util.format1 "Assertion failed: test %s" uu____55246  in
           (FStar_Errors.Fatal_AssertionFailure, uu____55244)  in
         FStar_Errors.raise_error uu____55238 FStar_Range.dummyRange)
  
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
  'Auu____55265 . 'Auu____55265 -> 'Auu____55265 FStar_Syntax_Syntax.syntax =
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
      let uu____55300 =
        let uu____55307 =
          let uu____55308 =
            let uu____55325 = FStar_List.map FStar_Syntax_Syntax.as_arg ts
               in
            (x1, uu____55325)  in
          FStar_Syntax_Syntax.Tm_app uu____55308  in
        FStar_Syntax_Syntax.mk uu____55307  in
      uu____55300 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
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
             (fun uu____55407  ->
                fun uu____55408  ->
                  match (uu____55407, uu____55408) with
                  | ((x1,uu____55423),(y1,uu____55425)) ->
                      term_eq' x1.FStar_Syntax_Syntax.sort
                        y1.FStar_Syntax_Syntax.sort) xs ys)
         in
      let args_eq xs ys =
        ((FStar_List.length xs) = (FStar_List.length ys)) &&
          (FStar_List.forall2
             (fun uu____55536  ->
                fun uu____55537  ->
                  match (uu____55536, uu____55537) with
                  | ((a,imp),(b,imp')) ->
                      (term_eq' a b) &&
                        (let uu____55608 =
                           FStar_Syntax_Util.eq_aqual imp imp'  in
                         uu____55608 = FStar_Syntax_Util.Equal)) xs ys)
         in
      let comp_eq c d =
        match ((c.FStar_Syntax_Syntax.n), (d.FStar_Syntax_Syntax.n)) with
        | (FStar_Syntax_Syntax.Total
           (t,uu____55623),FStar_Syntax_Syntax.Total (s,uu____55625)) ->
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
        | uu____55644 -> false  in
      match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n)) with
      | (FStar_Syntax_Syntax.Tm_lazy l,uu____55652) ->
          let uu____55653 =
            let uu____55656 =
              let uu____55665 =
                FStar_ST.op_Bang FStar_Syntax_Syntax.lazy_chooser  in
              FStar_Util.must uu____55665  in
            uu____55656 l.FStar_Syntax_Syntax.lkind l  in
          term_eq' uu____55653 t21
      | (uu____55715,FStar_Syntax_Syntax.Tm_lazy l) ->
          let uu____55717 =
            let uu____55720 =
              let uu____55729 =
                FStar_ST.op_Bang FStar_Syntax_Syntax.lazy_chooser  in
              FStar_Util.must uu____55729  in
            uu____55720 l.FStar_Syntax_Syntax.lkind l  in
          term_eq' t11 uu____55717
      | (FStar_Syntax_Syntax.Tm_bvar x1,FStar_Syntax_Syntax.Tm_bvar y1) ->
          x1.FStar_Syntax_Syntax.index = y1.FStar_Syntax_Syntax.index
      | (FStar_Syntax_Syntax.Tm_name x1,FStar_Syntax_Syntax.Tm_name y1) ->
          FStar_Syntax_Syntax.bv_eq x1 y1
      | (FStar_Syntax_Syntax.Tm_fvar f,FStar_Syntax_Syntax.Tm_fvar g) ->
          FStar_Syntax_Syntax.fv_eq f g
      | (FStar_Syntax_Syntax.Tm_uinst
         (t,uu____55787),FStar_Syntax_Syntax.Tm_uinst (s,uu____55789)) ->
          term_eq' t s
      | (FStar_Syntax_Syntax.Tm_constant c1,FStar_Syntax_Syntax.Tm_constant
         c2) -> FStar_Const.eq_const c1 c2
      | (FStar_Syntax_Syntax.Tm_type u,FStar_Syntax_Syntax.Tm_type v1) ->
          u = v1
      | (FStar_Syntax_Syntax.Tm_abs
         (xs,t,uu____55804),FStar_Syntax_Syntax.Tm_abs (ys,u,uu____55807))
          when (FStar_List.length xs) = (FStar_List.length ys) ->
          (binders_eq xs ys) && (term_eq' t u)
      | (FStar_Syntax_Syntax.Tm_abs
         (xs,t,uu____55870),FStar_Syntax_Syntax.Tm_abs (ys,u,uu____55873)) ->
          if (FStar_List.length xs) > (FStar_List.length ys)
          then
            let uu____55936 = FStar_Util.first_N (FStar_List.length ys) xs
               in
            (match uu____55936 with
             | (xs1,xs') ->
                 let t12 =
                   let uu____56007 =
                     let uu____56014 =
                       let uu____56015 =
                         let uu____56034 =
                           FStar_Syntax_Syntax.mk
                             (FStar_Syntax_Syntax.Tm_abs
                                (xs', t, FStar_Pervasives_Native.None))
                             FStar_Pervasives_Native.None
                             t11.FStar_Syntax_Syntax.pos
                            in
                         (xs1, uu____56034, FStar_Pervasives_Native.None)  in
                       FStar_Syntax_Syntax.Tm_abs uu____56015  in
                     FStar_Syntax_Syntax.mk uu____56014  in
                   uu____56007 FStar_Pervasives_Native.None
                     t11.FStar_Syntax_Syntax.pos
                    in
                 term_eq' t12 t21)
          else
            (let uu____56066 = FStar_Util.first_N (FStar_List.length xs) ys
                in
             match uu____56066 with
             | (ys1,ys') ->
                 let t22 =
                   let uu____56137 =
                     let uu____56144 =
                       let uu____56145 =
                         let uu____56164 =
                           FStar_Syntax_Syntax.mk
                             (FStar_Syntax_Syntax.Tm_abs
                                (ys', u, FStar_Pervasives_Native.None))
                             FStar_Pervasives_Native.None
                             t21.FStar_Syntax_Syntax.pos
                            in
                         (ys1, uu____56164, FStar_Pervasives_Native.None)  in
                       FStar_Syntax_Syntax.Tm_abs uu____56145  in
                     FStar_Syntax_Syntax.mk uu____56144  in
                   uu____56137 FStar_Pervasives_Native.None
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
            FStar_Syntax_Syntax.pos = uu____56251;
            FStar_Syntax_Syntax.vars = uu____56252;_},(uu____56253,FStar_Pervasives_Native.Some
                                                       (FStar_Syntax_Syntax.Implicit
                                                       uu____56254))::t12::t22::[]),FStar_Syntax_Syntax.Tm_app
         ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv_eq_2;
            FStar_Syntax_Syntax.pos = uu____56258;
            FStar_Syntax_Syntax.vars = uu____56259;_},(uu____56260,FStar_Pervasives_Native.Some
                                                       (FStar_Syntax_Syntax.Implicit
                                                       uu____56261))::s1::s2::[]))
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
                (fun uu____56642  ->
                   fun uu____56643  ->
                     match (uu____56642, uu____56643) with
                     | ((uu____56701,uu____56702,e),(uu____56704,uu____56705,e'))
                         -> term_eq' e e') pats pats'))
            && (term_eq' t t')
      | (FStar_Syntax_Syntax.Tm_ascribed
         (t12,(FStar_Util.Inl t22,uu____56769),uu____56770),FStar_Syntax_Syntax.Tm_ascribed
         (s1,(FStar_Util.Inl s2,uu____56773),uu____56774)) ->
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
         (u,uu____56913),FStar_Syntax_Syntax.Tm_uvar (u',uu____56915)) ->
          FStar_Syntax_Unionfind.equiv u.FStar_Syntax_Syntax.ctx_uvar_head
            u'.FStar_Syntax_Syntax.ctx_uvar_head
      | (FStar_Syntax_Syntax.Tm_meta (t12,uu____56949),uu____56950) ->
          term_eq' t12 t21
      | (uu____56955,FStar_Syntax_Syntax.Tm_meta (t22,uu____56957)) ->
          term_eq' t11 t22
      | (FStar_Syntax_Syntax.Tm_delayed uu____56962,uu____56963) ->
          let uu____56986 =
            let uu____56988 = FStar_Syntax_Print.tag_of_term t11  in
            let uu____56990 = FStar_Syntax_Print.tag_of_term t21  in
            FStar_Util.format2 "Impossible: %s and %s" uu____56988
              uu____56990
             in
          failwith uu____56986
      | (uu____56994,FStar_Syntax_Syntax.Tm_delayed uu____56995) ->
          let uu____57018 =
            let uu____57020 = FStar_Syntax_Print.tag_of_term t11  in
            let uu____57022 = FStar_Syntax_Print.tag_of_term t21  in
            FStar_Util.format2 "Impossible: %s and %s" uu____57020
              uu____57022
             in
          failwith uu____57018
      | (FStar_Syntax_Syntax.Tm_unknown ,FStar_Syntax_Syntax.Tm_unknown ) ->
          true
      | uu____57027 -> false
  
let (term_eq :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.bool)
  =
  fun t1  ->
    fun t2  ->
      let b = term_eq' t1 t2  in
      if Prims.op_Negation b
      then
        (let uu____57057 = FStar_Syntax_Print.term_to_string t1  in
         let uu____57059 = FStar_Syntax_Print.term_to_string t2  in
         FStar_Util.print2 ">>>>>>>>>>>Term %s is not equal to %s\n"
           uu____57057 uu____57059)
      else ();
      b
  