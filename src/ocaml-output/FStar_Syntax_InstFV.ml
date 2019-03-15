open Prims
type inst_t = (FStar_Ident.lident * FStar_Syntax_Syntax.universes) Prims.list
let mk :
  'Auu____37992 'Auu____37993 .
    'Auu____37992 FStar_Syntax_Syntax.syntax ->
      'Auu____37993 -> 'Auu____37993 FStar_Syntax_Syntax.syntax
  =
  fun t  ->
    fun s  ->
      FStar_Syntax_Syntax.mk s FStar_Pervasives_Native.None
        t.FStar_Syntax_Syntax.pos
  
let rec (inst :
  (FStar_Syntax_Syntax.term ->
     FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.term)
    -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun s  ->
    fun t  ->
      let t1 = FStar_Syntax_Subst.compress t  in
      let mk1 = mk t1  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed uu____38123 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_name uu____38147 -> t1
      | FStar_Syntax_Syntax.Tm_uvar uu____38148 -> t1
      | FStar_Syntax_Syntax.Tm_uvar uu____38161 -> t1
      | FStar_Syntax_Syntax.Tm_type uu____38174 -> t1
      | FStar_Syntax_Syntax.Tm_bvar uu____38175 -> t1
      | FStar_Syntax_Syntax.Tm_constant uu____38176 -> t1
      | FStar_Syntax_Syntax.Tm_quoted uu____38177 -> t1
      | FStar_Syntax_Syntax.Tm_unknown  -> t1
      | FStar_Syntax_Syntax.Tm_uinst uu____38184 -> t1
      | FStar_Syntax_Syntax.Tm_lazy uu____38191 -> t1
      | FStar_Syntax_Syntax.Tm_fvar fv -> s t1 fv
      | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
          let bs1 = inst_binders s bs  in
          let body1 = inst s body  in
          let uu____38222 =
            let uu____38223 =
              let uu____38242 = inst_lcomp_opt s lopt  in
              (bs1, body1, uu____38242)  in
            FStar_Syntax_Syntax.Tm_abs uu____38223  in
          mk1 uu____38222
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let bs1 = inst_binders s bs  in
          let c1 = inst_comp s c  in
          mk1 (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
      | FStar_Syntax_Syntax.Tm_refine (bv,t2) ->
          let bv1 =
            let uu___438_38300 = bv  in
            let uu____38301 = inst s bv.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___438_38300.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___438_38300.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____38301
            }  in
          let t3 = inst s t2  in
          mk1 (FStar_Syntax_Syntax.Tm_refine (bv1, t3))
      | FStar_Syntax_Syntax.Tm_app (t2,args) ->
          let uu____38333 =
            let uu____38334 =
              let uu____38351 = inst s t2  in
              let uu____38354 = inst_args s args  in
              (uu____38351, uu____38354)  in
            FStar_Syntax_Syntax.Tm_app uu____38334  in
          mk1 uu____38333
      | FStar_Syntax_Syntax.Tm_match (t2,pats) ->
          let pats1 =
            FStar_All.pipe_right pats
              (FStar_List.map
                 (fun uu____38486  ->
                    match uu____38486 with
                    | (p,wopt,t3) ->
                        let wopt1 =
                          match wopt with
                          | FStar_Pervasives_Native.None  ->
                              FStar_Pervasives_Native.None
                          | FStar_Pervasives_Native.Some w ->
                              let uu____38524 = inst s w  in
                              FStar_Pervasives_Native.Some uu____38524
                           in
                        let t4 = inst s t3  in (p, wopt1, t4)))
             in
          let uu____38530 =
            let uu____38531 =
              let uu____38554 = inst s t2  in (uu____38554, pats1)  in
            FStar_Syntax_Syntax.Tm_match uu____38531  in
          mk1 uu____38530
      | FStar_Syntax_Syntax.Tm_ascribed (t11,asc,f) ->
          let inst_asc uu____38647 =
            match uu____38647 with
            | (annot,topt) ->
                let topt1 = FStar_Util.map_opt topt (inst s)  in
                let annot1 =
                  match annot with
                  | FStar_Util.Inl t2 ->
                      let uu____38709 = inst s t2  in
                      FStar_Util.Inl uu____38709
                  | FStar_Util.Inr c ->
                      let uu____38717 = inst_comp s c  in
                      FStar_Util.Inr uu____38717
                   in
                (annot1, topt1)
             in
          let uu____38730 =
            let uu____38731 =
              let uu____38758 = inst s t11  in
              let uu____38761 = inst_asc asc  in
              (uu____38758, uu____38761, f)  in
            FStar_Syntax_Syntax.Tm_ascribed uu____38731  in
          mk1 uu____38730
      | FStar_Syntax_Syntax.Tm_let (lbs,t2) ->
          let lbs1 =
            let uu____38826 =
              FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                (FStar_List.map
                   (fun lb  ->
                      let uu___480_38841 = lb  in
                      let uu____38842 = inst s lb.FStar_Syntax_Syntax.lbtyp
                         in
                      let uu____38845 = inst s lb.FStar_Syntax_Syntax.lbdef
                         in
                      {
                        FStar_Syntax_Syntax.lbname =
                          (uu___480_38841.FStar_Syntax_Syntax.lbname);
                        FStar_Syntax_Syntax.lbunivs =
                          (uu___480_38841.FStar_Syntax_Syntax.lbunivs);
                        FStar_Syntax_Syntax.lbtyp = uu____38842;
                        FStar_Syntax_Syntax.lbeff =
                          (uu___480_38841.FStar_Syntax_Syntax.lbeff);
                        FStar_Syntax_Syntax.lbdef = uu____38845;
                        FStar_Syntax_Syntax.lbattrs =
                          (uu___480_38841.FStar_Syntax_Syntax.lbattrs);
                        FStar_Syntax_Syntax.lbpos =
                          (uu___480_38841.FStar_Syntax_Syntax.lbpos)
                      }))
               in
            ((FStar_Pervasives_Native.fst lbs), uu____38826)  in
          let uu____38854 =
            let uu____38855 =
              let uu____38869 = inst s t2  in (lbs1, uu____38869)  in
            FStar_Syntax_Syntax.Tm_let uu____38855  in
          mk1 uu____38854
      | FStar_Syntax_Syntax.Tm_meta
          (t2,FStar_Syntax_Syntax.Meta_pattern args) ->
          let uu____38899 =
            let uu____38900 =
              let uu____38907 = inst s t2  in
              let uu____38910 =
                let uu____38911 =
                  FStar_All.pipe_right args (FStar_List.map (inst_args s))
                   in
                FStar_Syntax_Syntax.Meta_pattern uu____38911  in
              (uu____38907, uu____38910)  in
            FStar_Syntax_Syntax.Tm_meta uu____38900  in
          mk1 uu____38899
      | FStar_Syntax_Syntax.Tm_meta
          (t2,FStar_Syntax_Syntax.Meta_monadic (m,t')) ->
          let uu____38981 =
            let uu____38982 =
              let uu____38989 = inst s t2  in
              let uu____38992 =
                let uu____38993 =
                  let uu____39000 = inst s t'  in (m, uu____39000)  in
                FStar_Syntax_Syntax.Meta_monadic uu____38993  in
              (uu____38989, uu____38992)  in
            FStar_Syntax_Syntax.Tm_meta uu____38982  in
          mk1 uu____38981
      | FStar_Syntax_Syntax.Tm_meta (t2,tag) ->
          let uu____39013 =
            let uu____39014 =
              let uu____39021 = inst s t2  in (uu____39021, tag)  in
            FStar_Syntax_Syntax.Tm_meta uu____39014  in
          mk1 uu____39013

and (inst_binders :
  (FStar_Syntax_Syntax.term ->
     FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.term)
    -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun s  ->
    fun bs  ->
      FStar_All.pipe_right bs
        (FStar_List.map
           (fun uu____39056  ->
              match uu____39056 with
              | (x,imp) ->
                  let uu____39075 =
                    let uu___504_39076 = x  in
                    let uu____39077 = inst s x.FStar_Syntax_Syntax.sort  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___504_39076.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___504_39076.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = uu____39077
                    }  in
                  (uu____39075, imp)))

and (inst_args :
  (FStar_Syntax_Syntax.term ->
     FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.term)
    ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
      FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
      Prims.list ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
        FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
        Prims.list)
  =
  fun s  ->
    fun args  ->
      FStar_All.pipe_right args
        (FStar_List.map
           (fun uu____39132  ->
              match uu____39132 with
              | (a,imp) -> let uu____39151 = inst s a  in (uu____39151, imp)))

and (inst_comp :
  (FStar_Syntax_Syntax.term ->
     FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.term)
    ->
    FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax)
  =
  fun s  ->
    fun c  ->
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total (t,uopt) ->
          let uu____39174 = inst s t  in
          FStar_Syntax_Syntax.mk_Total' uu____39174 uopt
      | FStar_Syntax_Syntax.GTotal (t,uopt) ->
          let uu____39185 = inst s t  in
          FStar_Syntax_Syntax.mk_GTotal' uu____39185 uopt
      | FStar_Syntax_Syntax.Comp ct ->
          let ct1 =
            let uu___523_39188 = ct  in
            let uu____39189 = inst s ct.FStar_Syntax_Syntax.result_typ  in
            let uu____39192 = inst_args s ct.FStar_Syntax_Syntax.effect_args
               in
            let uu____39203 =
              FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                (FStar_List.map
                   (fun uu___391_39213  ->
                      match uu___391_39213 with
                      | FStar_Syntax_Syntax.DECREASES t ->
                          let uu____39217 = inst s t  in
                          FStar_Syntax_Syntax.DECREASES uu____39217
                      | f -> f))
               in
            {
              FStar_Syntax_Syntax.comp_univs =
                (uu___523_39188.FStar_Syntax_Syntax.comp_univs);
              FStar_Syntax_Syntax.effect_name =
                (uu___523_39188.FStar_Syntax_Syntax.effect_name);
              FStar_Syntax_Syntax.result_typ = uu____39189;
              FStar_Syntax_Syntax.effect_args = uu____39192;
              FStar_Syntax_Syntax.flags = uu____39203
            }  in
          FStar_Syntax_Syntax.mk_Comp ct1

and (inst_lcomp_opt :
  (FStar_Syntax_Syntax.term ->
     FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.term)
    ->
    FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option)
  =
  fun s  ->
    fun l  ->
      match l with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some rc ->
          let uu____39232 =
            let uu___535_39233 = rc  in
            let uu____39234 =
              FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (inst s)
               in
            {
              FStar_Syntax_Syntax.residual_effect =
                (uu___535_39233.FStar_Syntax_Syntax.residual_effect);
              FStar_Syntax_Syntax.residual_typ = uu____39234;
              FStar_Syntax_Syntax.residual_flags =
                (uu___535_39233.FStar_Syntax_Syntax.residual_flags)
            }  in
          FStar_Pervasives_Native.Some uu____39232

let (instantiate :
  inst_t -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun i  ->
    fun t  ->
      match i with
      | [] -> t
      | uu____39258 ->
          let inst_fv t1 fv =
            let uu____39270 =
              FStar_Util.find_opt
                (fun uu____39284  ->
                   match uu____39284 with
                   | (x,uu____39291) ->
                       FStar_Ident.lid_equals x
                         (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                i
               in
            match uu____39270 with
            | FStar_Pervasives_Native.None  -> t1
            | FStar_Pervasives_Native.Some (uu____39296,us) ->
                mk t1 (FStar_Syntax_Syntax.Tm_uinst (t1, us))
             in
          inst inst_fv t
  