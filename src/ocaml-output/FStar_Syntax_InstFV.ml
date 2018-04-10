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
      | FStar_Syntax_Syntax.Tm_delayed uu____140 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_name uu____165 -> t1
      | FStar_Syntax_Syntax.Tm_uvar uu____166 -> t1
      | FStar_Syntax_Syntax.Tm_uvar uu____183 -> t1
      | FStar_Syntax_Syntax.Tm_type uu____200 -> t1
      | FStar_Syntax_Syntax.Tm_bvar uu____201 -> t1
      | FStar_Syntax_Syntax.Tm_constant uu____202 -> t1
      | FStar_Syntax_Syntax.Tm_quoted uu____203 -> t1
      | FStar_Syntax_Syntax.Tm_unknown  -> t1
      | FStar_Syntax_Syntax.Tm_uinst uu____210 -> t1
      | FStar_Syntax_Syntax.Tm_lazy uu____217 -> t1
      | FStar_Syntax_Syntax.Tm_fvar fv -> s t1 fv
      | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
          let bs1 = inst_binders s bs  in
          let body1 = inst s body  in
          let uu____244 =
            let uu____245 =
              let uu____262 = inst_lcomp_opt s lopt  in
              (bs1, body1, uu____262)  in
            FStar_Syntax_Syntax.Tm_abs uu____245  in
          mk1 uu____244
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let bs1 = inst_binders s bs  in
          let c1 = inst_comp s c  in
          mk1 (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
      | FStar_Syntax_Syntax.Tm_refine (bv,t2) ->
          let bv1 =
            let uu___27_298 = bv  in
            let uu____299 = inst s bv.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___27_298.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___27_298.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____299
            }  in
          let t3 = inst s t2  in
          mk1 (FStar_Syntax_Syntax.Tm_refine (bv1, t3))
      | FStar_Syntax_Syntax.Tm_app (t2,args) ->
          let uu____325 =
            let uu____326 =
              let uu____341 = inst s t2  in
              let uu____342 = inst_args s args  in (uu____341, uu____342)  in
            FStar_Syntax_Syntax.Tm_app uu____326  in
          mk1 uu____325
      | FStar_Syntax_Syntax.Tm_match (t2,pats) ->
          let pats1 =
            FStar_All.pipe_right pats
              (FStar_List.map
                 (fun uu____464  ->
                    match uu____464 with
                    | (p,wopt,t3) ->
                        let wopt1 =
                          match wopt with
                          | FStar_Pervasives_Native.None  ->
                              FStar_Pervasives_Native.None
                          | FStar_Pervasives_Native.Some w ->
                              let uu____502 = inst s w  in
                              FStar_Pervasives_Native.Some uu____502
                           in
                        let t4 = inst s t3  in (p, wopt1, t4)))
             in
          let uu____508 =
            let uu____509 = let uu____532 = inst s t2  in (uu____532, pats1)
               in
            FStar_Syntax_Syntax.Tm_match uu____509  in
          mk1 uu____508
      | FStar_Syntax_Syntax.Tm_ascribed (t11,asc,f) ->
          let inst_asc uu____616 =
            match uu____616 with
            | (annot,topt) ->
                let topt1 = FStar_Util.map_opt topt (inst s)  in
                let annot1 =
                  match annot with
                  | FStar_Util.Inl t2 ->
                      let uu____678 = inst s t2  in FStar_Util.Inl uu____678
                  | FStar_Util.Inr c ->
                      let uu____686 = inst_comp s c  in
                      FStar_Util.Inr uu____686
                   in
                (annot1, topt1)
             in
          let uu____699 =
            let uu____700 =
              let uu____727 = inst s t11  in
              let uu____728 = inst_asc asc  in (uu____727, uu____728, f)  in
            FStar_Syntax_Syntax.Tm_ascribed uu____700  in
          mk1 uu____699
      | FStar_Syntax_Syntax.Tm_let (lbs,t2) ->
          let lbs1 =
            let uu____780 =
              FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                (FStar_List.map
                   (fun lb  ->
                      let uu___28_794 = lb  in
                      let uu____795 = inst s lb.FStar_Syntax_Syntax.lbtyp  in
                      let uu____798 = inst s lb.FStar_Syntax_Syntax.lbdef  in
                      {
                        FStar_Syntax_Syntax.lbname =
                          (uu___28_794.FStar_Syntax_Syntax.lbname);
                        FStar_Syntax_Syntax.lbunivs =
                          (uu___28_794.FStar_Syntax_Syntax.lbunivs);
                        FStar_Syntax_Syntax.lbtyp = uu____795;
                        FStar_Syntax_Syntax.lbeff =
                          (uu___28_794.FStar_Syntax_Syntax.lbeff);
                        FStar_Syntax_Syntax.lbdef = uu____798;
                        FStar_Syntax_Syntax.lbattrs =
                          (uu___28_794.FStar_Syntax_Syntax.lbattrs);
                        FStar_Syntax_Syntax.lbpos =
                          (uu___28_794.FStar_Syntax_Syntax.lbpos)
                      }))
               in
            ((FStar_Pervasives_Native.fst lbs), uu____780)  in
          let uu____805 =
            let uu____806 = let uu____819 = inst s t2  in (lbs1, uu____819)
               in
            FStar_Syntax_Syntax.Tm_let uu____806  in
          mk1 uu____805
      | FStar_Syntax_Syntax.Tm_meta
          (t2,FStar_Syntax_Syntax.Meta_pattern args) ->
          let uu____842 =
            let uu____843 =
              let uu____850 = inst s t2  in
              let uu____851 =
                let uu____852 =
                  FStar_All.pipe_right args (FStar_List.map (inst_args s))
                   in
                FStar_Syntax_Syntax.Meta_pattern uu____852  in
              (uu____850, uu____851)  in
            FStar_Syntax_Syntax.Tm_meta uu____843  in
          mk1 uu____842
      | FStar_Syntax_Syntax.Tm_meta
          (t2,FStar_Syntax_Syntax.Meta_monadic (m,t')) ->
          let uu____910 =
            let uu____911 =
              let uu____918 = inst s t2  in
              let uu____919 =
                let uu____920 = let uu____927 = inst s t'  in (m, uu____927)
                   in
                FStar_Syntax_Syntax.Meta_monadic uu____920  in
              (uu____918, uu____919)  in
            FStar_Syntax_Syntax.Tm_meta uu____911  in
          mk1 uu____910
      | FStar_Syntax_Syntax.Tm_meta (t2,tag) ->
          let uu____934 =
            let uu____935 = let uu____942 = inst s t2  in (uu____942, tag)
               in
            FStar_Syntax_Syntax.Tm_meta uu____935  in
          mk1 uu____934

and (inst_binders :
  (FStar_Syntax_Syntax.term ->
     FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.term)
    -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun s  ->
    fun bs  ->
      FStar_All.pipe_right bs
        (FStar_List.map
           (fun uu____967  ->
              match uu____967 with
              | (x,imp) ->
                  let uu____978 =
                    let uu___29_979 = x  in
                    let uu____980 = inst s x.FStar_Syntax_Syntax.sort  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___29_979.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___29_979.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = uu____980
                    }  in
                  (uu____978, imp)))

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
           (fun uu____1023  ->
              match uu____1023 with
              | (a,imp) -> let uu____1034 = inst s a  in (uu____1034, imp)))

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
          let uu____1055 = inst s t  in
          FStar_Syntax_Syntax.mk_Total' uu____1055 uopt
      | FStar_Syntax_Syntax.GTotal (t,uopt) ->
          let uu____1066 = inst s t  in
          FStar_Syntax_Syntax.mk_GTotal' uu____1066 uopt
      | FStar_Syntax_Syntax.Comp ct ->
          let ct1 =
            let uu___30_1069 = ct  in
            let uu____1070 = inst s ct.FStar_Syntax_Syntax.result_typ  in
            let uu____1073 = inst_args s ct.FStar_Syntax_Syntax.effect_args
               in
            let uu____1082 =
              FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                (FStar_List.map
                   (fun uu___26_1092  ->
                      match uu___26_1092 with
                      | FStar_Syntax_Syntax.DECREASES t ->
                          let uu____1096 = inst s t  in
                          FStar_Syntax_Syntax.DECREASES uu____1096
                      | f -> f))
               in
            {
              FStar_Syntax_Syntax.comp_univs =
                (uu___30_1069.FStar_Syntax_Syntax.comp_univs);
              FStar_Syntax_Syntax.effect_name =
                (uu___30_1069.FStar_Syntax_Syntax.effect_name);
              FStar_Syntax_Syntax.result_typ = uu____1070;
              FStar_Syntax_Syntax.effect_args = uu____1073;
              FStar_Syntax_Syntax.flags = uu____1082
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
          let uu____1111 =
            let uu___31_1112 = rc  in
            let uu____1113 =
              FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (inst s)
               in
            {
              FStar_Syntax_Syntax.residual_effect =
                (uu___31_1112.FStar_Syntax_Syntax.residual_effect);
              FStar_Syntax_Syntax.residual_typ = uu____1113;
              FStar_Syntax_Syntax.residual_flags =
                (uu___31_1112.FStar_Syntax_Syntax.residual_flags)
            }  in
          FStar_Pervasives_Native.Some uu____1111

let (instantiate :
  inst_t -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun i  ->
    fun t  ->
      match i with
      | [] -> t
      | uu____1134 ->
          let inst_fv t1 fv =
            let uu____1144 =
              FStar_Util.find_opt
                (fun uu____1158  ->
                   match uu____1158 with
                   | (x,uu____1164) ->
                       FStar_Ident.lid_equals x
                         (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                i
               in
            match uu____1144 with
            | FStar_Pervasives_Native.None  -> t1
            | FStar_Pervasives_Native.Some (uu____1169,us) ->
                mk t1 (FStar_Syntax_Syntax.Tm_uinst (t1, us))
             in
          inst inst_fv t
  