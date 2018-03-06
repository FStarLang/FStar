open Prims
type inst_t =
  (FStar_Ident.lident,FStar_Syntax_Syntax.universes)
    FStar_Pervasives_Native.tuple2 Prims.list[@@deriving show]
let mk :
  'Auu____11 'Auu____12 .
    'Auu____11 FStar_Syntax_Syntax.syntax ->
      'Auu____12 -> 'Auu____12 FStar_Syntax_Syntax.syntax
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
      | FStar_Syntax_Syntax.Tm_delayed uu____113 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_name uu____138 -> t1
      | FStar_Syntax_Syntax.Tm_uvar uu____139 -> t1
      | FStar_Syntax_Syntax.Tm_uvar uu____156 -> t1
      | FStar_Syntax_Syntax.Tm_type uu____173 -> t1
      | FStar_Syntax_Syntax.Tm_bvar uu____174 -> t1
      | FStar_Syntax_Syntax.Tm_constant uu____175 -> t1
      | FStar_Syntax_Syntax.Tm_unknown  -> t1
      | FStar_Syntax_Syntax.Tm_uinst uu____176 -> t1
      | FStar_Syntax_Syntax.Tm_lazy uu____183 -> t1
      | FStar_Syntax_Syntax.Tm_fvar fv -> s t1 fv
      | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
          let bs1 = inst_binders s bs  in
          let body1 = inst s body  in
          let uu____210 =
            let uu____211 =
              let uu____228 = inst_lcomp_opt s lopt  in
              (bs1, body1, uu____228)  in
            FStar_Syntax_Syntax.Tm_abs uu____211  in
          mk1 uu____210
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let bs1 = inst_binders s bs  in
          let c1 = inst_comp s c  in
          mk1 (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
      | FStar_Syntax_Syntax.Tm_refine (bv,t2) ->
          let bv1 =
            let uu___25_264 = bv  in
            let uu____265 = inst s bv.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___25_264.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___25_264.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____265
            }  in
          let t3 = inst s t2  in
          mk1 (FStar_Syntax_Syntax.Tm_refine (bv1, t3))
      | FStar_Syntax_Syntax.Tm_app (t2,args) ->
          let uu____291 =
            let uu____292 =
              let uu____307 = inst s t2  in
              let uu____308 = inst_args s args  in (uu____307, uu____308)  in
            FStar_Syntax_Syntax.Tm_app uu____292  in
          mk1 uu____291
      | FStar_Syntax_Syntax.Tm_match (t2,pats) ->
          let pats1 =
            FStar_All.pipe_right pats
              (FStar_List.map
                 (fun uu____430  ->
                    match uu____430 with
                    | (p,wopt,t3) ->
                        let wopt1 =
                          match wopt with
                          | FStar_Pervasives_Native.None  ->
                              FStar_Pervasives_Native.None
                          | FStar_Pervasives_Native.Some w ->
                              let uu____468 = inst s w  in
                              FStar_Pervasives_Native.Some uu____468
                           in
                        let t4 = inst s t3  in (p, wopt1, t4)))
             in
          let uu____474 =
            let uu____475 = let uu____498 = inst s t2  in (uu____498, pats1)
               in
            FStar_Syntax_Syntax.Tm_match uu____475  in
          mk1 uu____474
      | FStar_Syntax_Syntax.Tm_ascribed (t11,asc,f) ->
          let inst_asc uu____581 =
            match uu____581 with
            | (annot,topt) ->
                let topt1 = FStar_Util.map_opt topt (inst s)  in
                let annot1 =
                  match annot with
                  | FStar_Util.Inl t2 ->
                      let uu____643 = inst s t2  in FStar_Util.Inl uu____643
                  | FStar_Util.Inr c ->
                      let uu____651 = inst_comp s c  in
                      FStar_Util.Inr uu____651
                   in
                (annot1, topt1)
             in
          let uu____664 =
            let uu____665 =
              let uu____692 = inst s t11  in
              let uu____693 = inst_asc asc  in (uu____692, uu____693, f)  in
            FStar_Syntax_Syntax.Tm_ascribed uu____665  in
          mk1 uu____664
      | FStar_Syntax_Syntax.Tm_let (lbs,t2) ->
          let lbs1 =
            let uu____745 =
              FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                (FStar_List.map
                   (fun lb  ->
                      let uu___26_759 = lb  in
                      let uu____760 = inst s lb.FStar_Syntax_Syntax.lbtyp  in
                      let uu____763 = inst s lb.FStar_Syntax_Syntax.lbdef  in
                      {
                        FStar_Syntax_Syntax.lbname =
                          (uu___26_759.FStar_Syntax_Syntax.lbname);
                        FStar_Syntax_Syntax.lbunivs =
                          (uu___26_759.FStar_Syntax_Syntax.lbunivs);
                        FStar_Syntax_Syntax.lbtyp = uu____760;
                        FStar_Syntax_Syntax.lbeff =
                          (uu___26_759.FStar_Syntax_Syntax.lbeff);
                        FStar_Syntax_Syntax.lbdef = uu____763;
                        FStar_Syntax_Syntax.lbattrs =
                          (uu___26_759.FStar_Syntax_Syntax.lbattrs)
                      }))
               in
            ((FStar_Pervasives_Native.fst lbs), uu____745)  in
          let uu____770 =
            let uu____771 = let uu____784 = inst s t2  in (lbs1, uu____784)
               in
            FStar_Syntax_Syntax.Tm_let uu____771  in
          mk1 uu____770
      | FStar_Syntax_Syntax.Tm_meta
          (t2,FStar_Syntax_Syntax.Meta_pattern args) ->
          let uu____807 =
            let uu____808 =
              let uu____815 = inst s t2  in
              let uu____816 =
                let uu____817 =
                  FStar_All.pipe_right args (FStar_List.map (inst_args s))
                   in
                FStar_Syntax_Syntax.Meta_pattern uu____817  in
              (uu____815, uu____816)  in
            FStar_Syntax_Syntax.Tm_meta uu____808  in
          mk1 uu____807
      | FStar_Syntax_Syntax.Tm_meta
          (t2,FStar_Syntax_Syntax.Meta_monadic (m,t')) ->
          let uu____875 =
            let uu____876 =
              let uu____883 = inst s t2  in
              let uu____884 =
                let uu____885 = let uu____892 = inst s t'  in (m, uu____892)
                   in
                FStar_Syntax_Syntax.Meta_monadic uu____885  in
              (uu____883, uu____884)  in
            FStar_Syntax_Syntax.Tm_meta uu____876  in
          mk1 uu____875
      | FStar_Syntax_Syntax.Tm_meta (t2,tag) ->
          let uu____899 =
            let uu____900 = let uu____907 = inst s t2  in (uu____907, tag)
               in
            FStar_Syntax_Syntax.Tm_meta uu____900  in
          mk1 uu____899

and (inst_binders :
  (FStar_Syntax_Syntax.term ->
     FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.term)
    -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun s  ->
    fun bs  ->
      FStar_All.pipe_right bs
        (FStar_List.map
           (fun uu____932  ->
              match uu____932 with
              | (x,imp) ->
                  let uu____943 =
                    let uu___27_944 = x  in
                    let uu____945 = inst s x.FStar_Syntax_Syntax.sort  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___27_944.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___27_944.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = uu____945
                    }  in
                  (uu____943, imp)))

and (inst_args :
  (FStar_Syntax_Syntax.term ->
     FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.term)
    ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
        FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun s  ->
    fun args  ->
      FStar_All.pipe_right args
        (FStar_List.map
           (fun uu____988  ->
              match uu____988 with
              | (a,imp) -> let uu____999 = inst s a  in (uu____999, imp)))

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
          let uu____1020 = inst s t  in
          FStar_Syntax_Syntax.mk_Total' uu____1020 uopt
      | FStar_Syntax_Syntax.GTotal (t,uopt) ->
          let uu____1031 = inst s t  in
          FStar_Syntax_Syntax.mk_GTotal' uu____1031 uopt
      | FStar_Syntax_Syntax.Comp ct ->
          let ct1 =
            let uu___28_1034 = ct  in
            let uu____1035 = inst s ct.FStar_Syntax_Syntax.result_typ  in
            let uu____1038 = inst_args s ct.FStar_Syntax_Syntax.effect_args
               in
            let uu____1047 =
              FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                (FStar_List.map
                   (fun uu___24_1057  ->
                      match uu___24_1057 with
                      | FStar_Syntax_Syntax.DECREASES t ->
                          let uu____1061 = inst s t  in
                          FStar_Syntax_Syntax.DECREASES uu____1061
                      | f -> f))
               in
            {
              FStar_Syntax_Syntax.comp_univs =
                (uu___28_1034.FStar_Syntax_Syntax.comp_univs);
              FStar_Syntax_Syntax.effect_name =
                (uu___28_1034.FStar_Syntax_Syntax.effect_name);
              FStar_Syntax_Syntax.result_typ = uu____1035;
              FStar_Syntax_Syntax.effect_args = uu____1038;
              FStar_Syntax_Syntax.flags = uu____1047
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
          let uu____1076 =
            let uu___29_1077 = rc  in
            let uu____1078 =
              FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (inst s)
               in
            {
              FStar_Syntax_Syntax.residual_effect =
                (uu___29_1077.FStar_Syntax_Syntax.residual_effect);
              FStar_Syntax_Syntax.residual_typ = uu____1078;
              FStar_Syntax_Syntax.residual_flags =
                (uu___29_1077.FStar_Syntax_Syntax.residual_flags)
            }  in
          FStar_Pervasives_Native.Some uu____1076

let (instantiate :
  inst_t -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun i  ->
    fun t  ->
      match i with
      | [] -> t
      | uu____1095 ->
          let inst_fv t1 fv =
            let uu____1103 =
              FStar_Util.find_opt
                (fun uu____1117  ->
                   match uu____1117 with
                   | (x,uu____1123) ->
                       FStar_Ident.lid_equals x
                         (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                i
               in
            match uu____1103 with
            | FStar_Pervasives_Native.None  -> t1
            | FStar_Pervasives_Native.Some (uu____1128,us) ->
                mk t1 (FStar_Syntax_Syntax.Tm_uinst (t1, us))
             in
          inst inst_fv t
  