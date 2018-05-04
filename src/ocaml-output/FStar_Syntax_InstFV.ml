open Prims
type inst_t =
  (FStar_Ident.lident,FStar_Syntax_Syntax.universes)
    FStar_Pervasives_Native.tuple2 Prims.list[@@deriving show]
let mk :
  'Auu____15 'Auu____16 .
    'Auu____15 FStar_Syntax_Syntax.syntax ->
      'Auu____16 -> 'Auu____16 FStar_Syntax_Syntax.syntax
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
      | FStar_Syntax_Syntax.Tm_delayed uu____141 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_name uu____166 -> t1
      | FStar_Syntax_Syntax.Tm_uvar uu____167 -> t1
      | FStar_Syntax_Syntax.Tm_uvar uu____174 -> t1
      | FStar_Syntax_Syntax.Tm_type uu____181 -> t1
      | FStar_Syntax_Syntax.Tm_bvar uu____182 -> t1
      | FStar_Syntax_Syntax.Tm_constant uu____183 -> t1
      | FStar_Syntax_Syntax.Tm_quoted uu____184 -> t1
      | FStar_Syntax_Syntax.Tm_unknown  -> t1
      | FStar_Syntax_Syntax.Tm_uinst uu____191 -> t1
      | FStar_Syntax_Syntax.Tm_lazy uu____198 -> t1
      | FStar_Syntax_Syntax.Tm_fvar fv -> s t1 fv
      | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
          let bs1 = inst_binders s bs  in
          let body1 = inst s body  in
          let uu____225 =
            let uu____226 =
              let uu____243 = inst_lcomp_opt s lopt  in
              (bs1, body1, uu____243)  in
            FStar_Syntax_Syntax.Tm_abs uu____226  in
          mk1 uu____225
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let bs1 = inst_binders s bs  in
          let c1 = inst_comp s c  in
          mk1 (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
      | FStar_Syntax_Syntax.Tm_refine (bv,t2) ->
          let bv1 =
            let uu___53_293 = bv  in
            let uu____294 = inst s bv.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___53_293.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___53_293.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____294
            }  in
          let t3 = inst s t2  in
          mk1 (FStar_Syntax_Syntax.Tm_refine (bv1, t3))
      | FStar_Syntax_Syntax.Tm_app (t2,args) ->
          let uu____322 =
            let uu____323 =
              let uu____338 = inst s t2  in
              let uu____341 = inst_args s args  in (uu____338, uu____341)  in
            FStar_Syntax_Syntax.Tm_app uu____323  in
          mk1 uu____322
      | FStar_Syntax_Syntax.Tm_match (t2,pats) ->
          let pats1 =
            FStar_All.pipe_right pats
              (FStar_List.map
                 (fun uu____469  ->
                    match uu____469 with
                    | (p,wopt,t3) ->
                        let wopt1 =
                          match wopt with
                          | FStar_Pervasives_Native.None  ->
                              FStar_Pervasives_Native.None
                          | FStar_Pervasives_Native.Some w ->
                              let uu____507 = inst s w  in
                              FStar_Pervasives_Native.Some uu____507
                           in
                        let t4 = inst s t3  in (p, wopt1, t4)))
             in
          let uu____513 =
            let uu____514 = let uu____537 = inst s t2  in (uu____537, pats1)
               in
            FStar_Syntax_Syntax.Tm_match uu____514  in
          mk1 uu____513
      | FStar_Syntax_Syntax.Tm_ascribed (t11,asc,f) ->
          let inst_asc uu____630 =
            match uu____630 with
            | (annot,topt) ->
                let topt1 = FStar_Util.map_opt topt (inst s)  in
                let annot1 =
                  match annot with
                  | FStar_Util.Inl t2 ->
                      let uu____692 = inst s t2  in FStar_Util.Inl uu____692
                  | FStar_Util.Inr c ->
                      let uu____700 = inst_comp s c  in
                      FStar_Util.Inr uu____700
                   in
                (annot1, topt1)
             in
          let uu____713 =
            let uu____714 =
              let uu____741 = inst s t11  in
              let uu____744 = inst_asc asc  in (uu____741, uu____744, f)  in
            FStar_Syntax_Syntax.Tm_ascribed uu____714  in
          mk1 uu____713
      | FStar_Syntax_Syntax.Tm_let (lbs,t2) ->
          let lbs1 =
            let uu____806 =
              FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                (FStar_List.map
                   (fun lb  ->
                      let uu___54_820 = lb  in
                      let uu____821 = inst s lb.FStar_Syntax_Syntax.lbtyp  in
                      let uu____824 = inst s lb.FStar_Syntax_Syntax.lbdef  in
                      {
                        FStar_Syntax_Syntax.lbname =
                          (uu___54_820.FStar_Syntax_Syntax.lbname);
                        FStar_Syntax_Syntax.lbunivs =
                          (uu___54_820.FStar_Syntax_Syntax.lbunivs);
                        FStar_Syntax_Syntax.lbtyp = uu____821;
                        FStar_Syntax_Syntax.lbeff =
                          (uu___54_820.FStar_Syntax_Syntax.lbeff);
                        FStar_Syntax_Syntax.lbdef = uu____824;
                        FStar_Syntax_Syntax.lbattrs =
                          (uu___54_820.FStar_Syntax_Syntax.lbattrs);
                        FStar_Syntax_Syntax.lbpos =
                          (uu___54_820.FStar_Syntax_Syntax.lbpos)
                      }))
               in
            ((FStar_Pervasives_Native.fst lbs), uu____806)  in
          let uu____831 =
            let uu____832 = let uu____845 = inst s t2  in (lbs1, uu____845)
               in
            FStar_Syntax_Syntax.Tm_let uu____832  in
          mk1 uu____831
      | FStar_Syntax_Syntax.Tm_meta
          (t2,FStar_Syntax_Syntax.Meta_pattern args) ->
          let uu____872 =
            let uu____873 =
              let uu____880 = inst s t2  in
              let uu____883 =
                let uu____884 =
                  FStar_All.pipe_right args (FStar_List.map (inst_args s))
                   in
                FStar_Syntax_Syntax.Meta_pattern uu____884  in
              (uu____880, uu____883)  in
            FStar_Syntax_Syntax.Tm_meta uu____873  in
          mk1 uu____872
      | FStar_Syntax_Syntax.Tm_meta
          (t2,FStar_Syntax_Syntax.Meta_monadic (m,t')) ->
          let uu____944 =
            let uu____945 =
              let uu____952 = inst s t2  in
              let uu____955 =
                let uu____956 = let uu____963 = inst s t'  in (m, uu____963)
                   in
                FStar_Syntax_Syntax.Meta_monadic uu____956  in
              (uu____952, uu____955)  in
            FStar_Syntax_Syntax.Tm_meta uu____945  in
          mk1 uu____944
      | FStar_Syntax_Syntax.Tm_meta (t2,tag) ->
          let uu____976 =
            let uu____977 = let uu____984 = inst s t2  in (uu____984, tag)
               in
            FStar_Syntax_Syntax.Tm_meta uu____977  in
          mk1 uu____976

and (inst_binders :
  (FStar_Syntax_Syntax.term ->
     FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.term)
    -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun s  ->
    fun bs  ->
      FStar_All.pipe_right bs
        (FStar_List.map
           (fun uu____1013  ->
              match uu____1013 with
              | (x,imp) ->
                  let uu____1024 =
                    let uu___55_1025 = x  in
                    let uu____1026 = inst s x.FStar_Syntax_Syntax.sort  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___55_1025.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___55_1025.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = uu____1026
                    }  in
                  (uu____1024, imp)))

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
           (fun uu____1069  ->
              match uu____1069 with
              | (a,imp) -> let uu____1080 = inst s a  in (uu____1080, imp)))

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
          let uu____1101 = inst s t  in
          FStar_Syntax_Syntax.mk_Total' uu____1101 uopt
      | FStar_Syntax_Syntax.GTotal (t,uopt) ->
          let uu____1112 = inst s t  in
          FStar_Syntax_Syntax.mk_GTotal' uu____1112 uopt
      | FStar_Syntax_Syntax.Comp ct ->
          let ct1 =
            let uu___56_1115 = ct  in
            let uu____1116 = inst s ct.FStar_Syntax_Syntax.result_typ  in
            let uu____1119 = inst_args s ct.FStar_Syntax_Syntax.effect_args
               in
            let uu____1128 =
              FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                (FStar_List.map
                   (fun uu___52_1138  ->
                      match uu___52_1138 with
                      | FStar_Syntax_Syntax.DECREASES t ->
                          let uu____1142 = inst s t  in
                          FStar_Syntax_Syntax.DECREASES uu____1142
                      | f -> f))
               in
            {
              FStar_Syntax_Syntax.comp_univs =
                (uu___56_1115.FStar_Syntax_Syntax.comp_univs);
              FStar_Syntax_Syntax.effect_name =
                (uu___56_1115.FStar_Syntax_Syntax.effect_name);
              FStar_Syntax_Syntax.result_typ = uu____1116;
              FStar_Syntax_Syntax.effect_args = uu____1119;
              FStar_Syntax_Syntax.flags = uu____1128
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
          let uu____1157 =
            let uu___57_1158 = rc  in
            let uu____1159 =
              FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (inst s)
               in
            {
              FStar_Syntax_Syntax.residual_effect =
                (uu___57_1158.FStar_Syntax_Syntax.residual_effect);
              FStar_Syntax_Syntax.residual_typ = uu____1159;
              FStar_Syntax_Syntax.residual_flags =
                (uu___57_1158.FStar_Syntax_Syntax.residual_flags)
            }  in
          FStar_Pervasives_Native.Some uu____1157

let (instantiate :
  inst_t -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun i  ->
    fun t  ->
      match i with
      | [] -> t
      | uu____1182 ->
          let inst_fv t1 fv =
            let uu____1194 =
              FStar_Util.find_opt
                (fun uu____1208  ->
                   match uu____1208 with
                   | (x,uu____1214) ->
                       FStar_Ident.lid_equals x
                         (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                i
               in
            match uu____1194 with
            | FStar_Pervasives_Native.None  -> t1
            | FStar_Pervasives_Native.Some (uu____1219,us) ->
                mk t1 (FStar_Syntax_Syntax.Tm_uinst (t1, us))
             in
          inst inst_fv t
  