open Prims
type inst_t = (FStar_Ident.lident * FStar_Syntax_Syntax.universes) Prims.list
let mk :
  'Auu____18 'Auu____19 .
    'Auu____18 FStar_Syntax_Syntax.syntax ->
      'Auu____19 -> 'Auu____19 FStar_Syntax_Syntax.syntax
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
      | FStar_Syntax_Syntax.Tm_delayed uu____285 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_name uu____321 -> t1
      | FStar_Syntax_Syntax.Tm_uvar uu____327 -> t1
      | FStar_Syntax_Syntax.Tm_uvar uu____348 -> t1
      | FStar_Syntax_Syntax.Tm_type uu____369 -> t1
      | FStar_Syntax_Syntax.Tm_bvar uu____370 -> t1
      | FStar_Syntax_Syntax.Tm_constant uu____376 -> t1
      | FStar_Syntax_Syntax.Tm_quoted uu____377 -> t1
      | FStar_Syntax_Syntax.Tm_unknown  -> t1
      | FStar_Syntax_Syntax.Tm_uinst uu____390 -> t1
      | FStar_Syntax_Syntax.Tm_lazy uu____401 -> t1
      | FStar_Syntax_Syntax.Tm_fvar fv -> s t1 fv
      | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
          let bs1 = inst_binders s bs  in
          let body1 = inst s body  in
          let uu____479 =
            let uu____480 =
              let uu____515 = inst_lcomp_opt s lopt  in
              (bs1, body1, uu____515)  in
            FStar_Syntax_Syntax.Tm_abs uu____480  in
          mk1 uu____479
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let bs1 = inst_binders s bs  in
          let c1 = inst_comp s c  in
          mk1 (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
      | FStar_Syntax_Syntax.Tm_refine (bv,t2) ->
          let bv1 =
            let uu___47_659 = bv  in
            let uu____670 = inst s bv.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___47_659.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___47_659.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____670
            }  in
          let t3 = inst s t2  in
          mk1 (FStar_Syntax_Syntax.Tm_refine (bv1, t3))
      | FStar_Syntax_Syntax.Tm_app (t2,args) ->
          let uu____743 =
            let uu____744 =
              let uu____769 = inst s t2  in
              let uu____780 = inst_args s args  in (uu____769, uu____780)  in
            FStar_Syntax_Syntax.Tm_app uu____744  in
          mk1 uu____743
      | FStar_Syntax_Syntax.Tm_match (t2,pats) ->
          let pats1 =
            FStar_All.pipe_right pats
              (FStar_List.map
                 (fun uu____1009  ->
                    match uu____1009 with
                    | (p,wopt,t3) ->
                        let wopt1 =
                          match wopt with
                          | FStar_Pervasives_Native.None  ->
                              FStar_Pervasives_Native.None
                          | FStar_Pervasives_Native.Some w ->
                              let uu____1112 = inst s w  in
                              FStar_Pervasives_Native.Some uu____1112
                           in
                        let t4 = inst s t3  in (p, wopt1, t4)))
             in
          let uu____1149 =
            let uu____1150 =
              let uu____1188 = inst s t2  in (uu____1188, pats1)  in
            FStar_Syntax_Syntax.Tm_match uu____1150  in
          mk1 uu____1149
      | FStar_Syntax_Syntax.Tm_ascribed (t11,asc,f) ->
          let inst_asc uu____1368 =
            match uu____1368 with
            | (annot,topt) ->
                let topt1 = FStar_Util.map_opt topt (inst s)  in
                let annot1 =
                  match annot with
                  | FStar_Util.Inl t2 ->
                      let uu____1518 = inst s t2  in
                      FStar_Util.Inl uu____1518
                  | FStar_Util.Inr c ->
                      let uu____1554 = inst_comp s c  in
                      FStar_Util.Inr uu____1554
                   in
                (annot1, topt1)
             in
          let uu____1595 =
            let uu____1596 =
              let uu____1643 = inst s t11  in
              let uu____1654 = inst_asc asc  in (uu____1643, uu____1654, f)
               in
            FStar_Syntax_Syntax.Tm_ascribed uu____1596  in
          mk1 uu____1595
      | FStar_Syntax_Syntax.Tm_let (lbs,t2) ->
          let lbs1 =
            let uu____1780 =
              FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                (FStar_List.map
                   (fun lb  ->
                      let uu___89_1844 = lb  in
                      let uu____1859 = inst s lb.FStar_Syntax_Syntax.lbtyp
                         in
                      let uu____1870 = inst s lb.FStar_Syntax_Syntax.lbdef
                         in
                      {
                        FStar_Syntax_Syntax.lbname =
                          (uu___89_1844.FStar_Syntax_Syntax.lbname);
                        FStar_Syntax_Syntax.lbunivs =
                          (uu___89_1844.FStar_Syntax_Syntax.lbunivs);
                        FStar_Syntax_Syntax.lbtyp = uu____1859;
                        FStar_Syntax_Syntax.lbeff =
                          (uu___89_1844.FStar_Syntax_Syntax.lbeff);
                        FStar_Syntax_Syntax.lbdef = uu____1870;
                        FStar_Syntax_Syntax.lbattrs =
                          (uu___89_1844.FStar_Syntax_Syntax.lbattrs);
                        FStar_Syntax_Syntax.lbpos =
                          (uu___89_1844.FStar_Syntax_Syntax.lbpos)
                      }))
               in
            ((FStar_Pervasives_Native.fst lbs), uu____1780)  in
          let uu____1901 =
            let uu____1902 =
              let uu____1927 = inst s t2  in (lbs1, uu____1927)  in
            FStar_Syntax_Syntax.Tm_let uu____1902  in
          mk1 uu____1901
      | FStar_Syntax_Syntax.Tm_meta
          (t2,FStar_Syntax_Syntax.Meta_pattern (bvs,args)) ->
          let uu____2021 =
            let uu____2022 =
              let uu____2033 = inst s t2  in
              let uu____2044 =
                let uu____2045 =
                  let uu____2074 =
                    FStar_All.pipe_right args (FStar_List.map (inst_args s))
                     in
                  (bvs, uu____2074)  in
                FStar_Syntax_Syntax.Meta_pattern uu____2045  in
              (uu____2033, uu____2044)  in
            FStar_Syntax_Syntax.Tm_meta uu____2022  in
          mk1 uu____2021
      | FStar_Syntax_Syntax.Tm_meta
          (t2,FStar_Syntax_Syntax.Meta_monadic (m,t')) ->
          let uu____2216 =
            let uu____2217 =
              let uu____2228 = inst s t2  in
              let uu____2239 =
                let uu____2240 =
                  let uu____2255 = inst s t'  in (m, uu____2255)  in
                FStar_Syntax_Syntax.Meta_monadic uu____2240  in
              (uu____2228, uu____2239)  in
            FStar_Syntax_Syntax.Tm_meta uu____2217  in
          mk1 uu____2216
      | FStar_Syntax_Syntax.Tm_meta (t2,tag) ->
          let uu____2296 =
            let uu____2297 = let uu____2308 = inst s t2  in (uu____2308, tag)
               in
            FStar_Syntax_Syntax.Tm_meta uu____2297  in
          mk1 uu____2296

and (inst_binders :
  (FStar_Syntax_Syntax.term ->
     FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.term)
    -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun s  ->
    fun bs  ->
      FStar_All.pipe_right bs
        (FStar_List.map
           (fun uu____2381  ->
              match uu____2381 with
              | (x,imp) ->
                  let uu____2420 =
                    let uu___115_2431 = x  in
                    let uu____2442 = inst s x.FStar_Syntax_Syntax.sort  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___115_2431.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___115_2431.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = uu____2442
                    }  in
                  (uu____2420, imp)))

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
           (fun uu____2541  ->
              match uu____2541 with
              | (a,imp) -> let uu____2576 = inst s a  in (uu____2576, imp)))

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
          let uu____2638 = inst s t  in
          FStar_Syntax_Syntax.mk_Total' uu____2638 uopt
      | FStar_Syntax_Syntax.GTotal (t,uopt) ->
          let uu____2665 = inst s t  in
          FStar_Syntax_Syntax.mk_GTotal' uu____2665 uopt
      | FStar_Syntax_Syntax.Comp ct ->
          let ct1 =
            let uu___134_2691 = ct  in
            let uu____2702 = inst s ct.FStar_Syntax_Syntax.result_typ  in
            let uu____2713 = inst_args s ct.FStar_Syntax_Syntax.effect_args
               in
            let uu____2728 =
              FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                (FStar_List.map
                   (fun uu___0_2738  ->
                      match uu___0_2738 with
                      | FStar_Syntax_Syntax.DECREASES t ->
                          let uu____2746 = inst s t  in
                          FStar_Syntax_Syntax.DECREASES uu____2746
                      | f -> f))
               in
            {
              FStar_Syntax_Syntax.comp_univs =
                (uu___134_2691.FStar_Syntax_Syntax.comp_univs);
              FStar_Syntax_Syntax.effect_name =
                (uu___134_2691.FStar_Syntax_Syntax.effect_name);
              FStar_Syntax_Syntax.result_typ = uu____2702;
              FStar_Syntax_Syntax.effect_args = uu____2713;
              FStar_Syntax_Syntax.flags = uu____2728
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
          let uu____2822 =
            let uu___146_2837 = rc  in
            let uu____2852 =
              FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (inst s)
               in
            {
              FStar_Syntax_Syntax.residual_effect =
                (uu___146_2837.FStar_Syntax_Syntax.residual_effect);
              FStar_Syntax_Syntax.residual_typ = uu____2852;
              FStar_Syntax_Syntax.residual_flags =
                (uu___146_2837.FStar_Syntax_Syntax.residual_flags)
            }  in
          FStar_Pervasives_Native.Some uu____2822

let (instantiate :
  inst_t -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun i  ->
    fun t  ->
      match i with
      | [] -> t
      | uu____2915 ->
          let inst_fv t1 fv =
            let uu____2949 =
              FStar_Util.find_opt
                (fun uu____2971  ->
                   match uu____2971 with
                   | (x,uu____2982) ->
                       FStar_Ident.lid_equals x
                         (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                i
               in
            match uu____2949 with
            | FStar_Pervasives_Native.None  -> t1
            | FStar_Pervasives_Native.Some (uu____3007,us) ->
                mk t1 (FStar_Syntax_Syntax.Tm_uinst (t1, us))
             in
          inst inst_fv t
  