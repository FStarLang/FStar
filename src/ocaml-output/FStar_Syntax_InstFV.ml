open Prims
type inst_t = (FStar_Ident.lident * FStar_Syntax_Syntax.universes) Prims.list
let mk :
  'Auu____38588 'Auu____38589 .
    'Auu____38588 FStar_Syntax_Syntax.syntax ->
      'Auu____38589 -> 'Auu____38589 FStar_Syntax_Syntax.syntax
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
      | FStar_Syntax_Syntax.Tm_delayed uu____38719 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_name uu____38743 -> t1
      | FStar_Syntax_Syntax.Tm_uvar uu____38744 -> t1
      | FStar_Syntax_Syntax.Tm_uvar uu____38757 -> t1
      | FStar_Syntax_Syntax.Tm_type uu____38770 -> t1
      | FStar_Syntax_Syntax.Tm_bvar uu____38771 -> t1
      | FStar_Syntax_Syntax.Tm_constant uu____38772 -> t1
      | FStar_Syntax_Syntax.Tm_quoted uu____38773 -> t1
      | FStar_Syntax_Syntax.Tm_unknown  -> t1
      | FStar_Syntax_Syntax.Tm_uinst uu____38780 -> t1
      | FStar_Syntax_Syntax.Tm_lazy uu____38787 -> t1
      | FStar_Syntax_Syntax.Tm_fvar fv -> s t1 fv
      | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
          let bs1 = inst_binders s bs  in
          let body1 = inst s body  in
          let uu____38818 =
            let uu____38819 =
              let uu____38838 = inst_lcomp_opt s lopt  in
              (bs1, body1, uu____38838)  in
            FStar_Syntax_Syntax.Tm_abs uu____38819  in
          mk1 uu____38818
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let bs1 = inst_binders s bs  in
          let c1 = inst_comp s c  in
          mk1 (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
      | FStar_Syntax_Syntax.Tm_refine (bv,t2) ->
          let bv1 =
            let uu___438_38896 = bv  in
            let uu____38897 = inst s bv.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___438_38896.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___438_38896.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____38897
            }  in
          let t3 = inst s t2  in
          mk1 (FStar_Syntax_Syntax.Tm_refine (bv1, t3))
      | FStar_Syntax_Syntax.Tm_app (t2,args) ->
          let uu____38929 =
            let uu____38930 =
              let uu____38947 = inst s t2  in
              let uu____38950 = inst_args s args  in
              (uu____38947, uu____38950)  in
            FStar_Syntax_Syntax.Tm_app uu____38930  in
          mk1 uu____38929
      | FStar_Syntax_Syntax.Tm_match (t2,pats) ->
          let pats1 =
            FStar_All.pipe_right pats
              (FStar_List.map
                 (fun uu____39082  ->
                    match uu____39082 with
                    | (p,wopt,t3) ->
                        let wopt1 =
                          match wopt with
                          | FStar_Pervasives_Native.None  ->
                              FStar_Pervasives_Native.None
                          | FStar_Pervasives_Native.Some w ->
                              let uu____39120 = inst s w  in
                              FStar_Pervasives_Native.Some uu____39120
                           in
                        let t4 = inst s t3  in (p, wopt1, t4)))
             in
          let uu____39126 =
            let uu____39127 =
              let uu____39150 = inst s t2  in (uu____39150, pats1)  in
            FStar_Syntax_Syntax.Tm_match uu____39127  in
          mk1 uu____39126
      | FStar_Syntax_Syntax.Tm_ascribed (t11,asc,f) ->
          let inst_asc uu____39243 =
            match uu____39243 with
            | (annot,topt) ->
                let topt1 = FStar_Util.map_opt topt (inst s)  in
                let annot1 =
                  match annot with
                  | FStar_Util.Inl t2 ->
                      let uu____39305 = inst s t2  in
                      FStar_Util.Inl uu____39305
                  | FStar_Util.Inr c ->
                      let uu____39313 = inst_comp s c  in
                      FStar_Util.Inr uu____39313
                   in
                (annot1, topt1)
             in
          let uu____39326 =
            let uu____39327 =
              let uu____39354 = inst s t11  in
              let uu____39357 = inst_asc asc  in
              (uu____39354, uu____39357, f)  in
            FStar_Syntax_Syntax.Tm_ascribed uu____39327  in
          mk1 uu____39326
      | FStar_Syntax_Syntax.Tm_let (lbs,t2) ->
          let lbs1 =
            let uu____39422 =
              FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                (FStar_List.map
                   (fun lb  ->
                      let uu___480_39437 = lb  in
                      let uu____39438 = inst s lb.FStar_Syntax_Syntax.lbtyp
                         in
                      let uu____39441 = inst s lb.FStar_Syntax_Syntax.lbdef
                         in
                      {
                        FStar_Syntax_Syntax.lbname =
                          (uu___480_39437.FStar_Syntax_Syntax.lbname);
                        FStar_Syntax_Syntax.lbunivs =
                          (uu___480_39437.FStar_Syntax_Syntax.lbunivs);
                        FStar_Syntax_Syntax.lbtyp = uu____39438;
                        FStar_Syntax_Syntax.lbeff =
                          (uu___480_39437.FStar_Syntax_Syntax.lbeff);
                        FStar_Syntax_Syntax.lbdef = uu____39441;
                        FStar_Syntax_Syntax.lbattrs =
                          (uu___480_39437.FStar_Syntax_Syntax.lbattrs);
                        FStar_Syntax_Syntax.lbpos =
                          (uu___480_39437.FStar_Syntax_Syntax.lbpos)
                      }))
               in
            ((FStar_Pervasives_Native.fst lbs), uu____39422)  in
          let uu____39450 =
            let uu____39451 =
              let uu____39465 = inst s t2  in (lbs1, uu____39465)  in
            FStar_Syntax_Syntax.Tm_let uu____39451  in
          mk1 uu____39450
      | FStar_Syntax_Syntax.Tm_meta
          (t2,FStar_Syntax_Syntax.Meta_pattern args) ->
          let uu____39495 =
            let uu____39496 =
              let uu____39503 = inst s t2  in
              let uu____39506 =
                let uu____39507 =
                  FStar_All.pipe_right args (FStar_List.map (inst_args s))
                   in
                FStar_Syntax_Syntax.Meta_pattern uu____39507  in
              (uu____39503, uu____39506)  in
            FStar_Syntax_Syntax.Tm_meta uu____39496  in
          mk1 uu____39495
      | FStar_Syntax_Syntax.Tm_meta
          (t2,FStar_Syntax_Syntax.Meta_monadic (m,t')) ->
          let uu____39577 =
            let uu____39578 =
              let uu____39585 = inst s t2  in
              let uu____39588 =
                let uu____39589 =
                  let uu____39596 = inst s t'  in (m, uu____39596)  in
                FStar_Syntax_Syntax.Meta_monadic uu____39589  in
              (uu____39585, uu____39588)  in
            FStar_Syntax_Syntax.Tm_meta uu____39578  in
          mk1 uu____39577
      | FStar_Syntax_Syntax.Tm_meta (t2,tag) ->
          let uu____39609 =
            let uu____39610 =
              let uu____39617 = inst s t2  in (uu____39617, tag)  in
            FStar_Syntax_Syntax.Tm_meta uu____39610  in
          mk1 uu____39609

and (inst_binders :
  (FStar_Syntax_Syntax.term ->
     FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.term)
    -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun s  ->
    fun bs  ->
      FStar_All.pipe_right bs
        (FStar_List.map
           (fun uu____39652  ->
              match uu____39652 with
              | (x,imp) ->
                  let uu____39671 =
                    let uu___504_39672 = x  in
                    let uu____39673 = inst s x.FStar_Syntax_Syntax.sort  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___504_39672.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___504_39672.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = uu____39673
                    }  in
                  (uu____39671, imp)))

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
           (fun uu____39728  ->
              match uu____39728 with
              | (a,imp) -> let uu____39747 = inst s a  in (uu____39747, imp)))

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
          let uu____39770 = inst s t  in
          FStar_Syntax_Syntax.mk_Total' uu____39770 uopt
      | FStar_Syntax_Syntax.GTotal (t,uopt) ->
          let uu____39781 = inst s t  in
          FStar_Syntax_Syntax.mk_GTotal' uu____39781 uopt
      | FStar_Syntax_Syntax.Comp ct ->
          let ct1 =
            let uu___523_39784 = ct  in
            let uu____39785 = inst s ct.FStar_Syntax_Syntax.result_typ  in
            let uu____39788 = inst_args s ct.FStar_Syntax_Syntax.effect_args
               in
            let uu____39799 =
              FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                (FStar_List.map
                   (fun uu___391_39809  ->
                      match uu___391_39809 with
                      | FStar_Syntax_Syntax.DECREASES t ->
                          let uu____39813 = inst s t  in
                          FStar_Syntax_Syntax.DECREASES uu____39813
                      | f -> f))
               in
            {
              FStar_Syntax_Syntax.comp_univs =
                (uu___523_39784.FStar_Syntax_Syntax.comp_univs);
              FStar_Syntax_Syntax.effect_name =
                (uu___523_39784.FStar_Syntax_Syntax.effect_name);
              FStar_Syntax_Syntax.result_typ = uu____39785;
              FStar_Syntax_Syntax.effect_args = uu____39788;
              FStar_Syntax_Syntax.flags = uu____39799
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
          let uu____39828 =
            let uu___535_39829 = rc  in
            let uu____39830 =
              FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (inst s)
               in
            {
              FStar_Syntax_Syntax.residual_effect =
                (uu___535_39829.FStar_Syntax_Syntax.residual_effect);
              FStar_Syntax_Syntax.residual_typ = uu____39830;
              FStar_Syntax_Syntax.residual_flags =
                (uu___535_39829.FStar_Syntax_Syntax.residual_flags)
            }  in
          FStar_Pervasives_Native.Some uu____39828

let (instantiate :
  inst_t -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun i  ->
    fun t  ->
      match i with
      | [] -> t
      | uu____39854 ->
          let inst_fv t1 fv =
            let uu____39866 =
              FStar_Util.find_opt
                (fun uu____39880  ->
                   match uu____39880 with
                   | (x,uu____39887) ->
                       FStar_Ident.lid_equals x
                         (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                i
               in
            match uu____39866 with
            | FStar_Pervasives_Native.None  -> t1
            | FStar_Pervasives_Native.Some (uu____39892,us) ->
                mk t1 (FStar_Syntax_Syntax.Tm_uinst (t1, us))
             in
          inst inst_fv t
  