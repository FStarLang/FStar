open Prims
type inst_t =
  (FStar_Ident.lident,FStar_Syntax_Syntax.universes)
    FStar_Pervasives_Native.tuple2 Prims.list
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
      | FStar_Syntax_Syntax.Tm_name uu____164 -> t1
      | FStar_Syntax_Syntax.Tm_uvar uu____165 -> t1
      | FStar_Syntax_Syntax.Tm_uvar uu____178 -> t1
      | FStar_Syntax_Syntax.Tm_type uu____191 -> t1
      | FStar_Syntax_Syntax.Tm_bvar uu____192 -> t1
      | FStar_Syntax_Syntax.Tm_constant uu____193 -> t1
      | FStar_Syntax_Syntax.Tm_quoted uu____194 -> t1
      | FStar_Syntax_Syntax.Tm_unknown  -> t1
      | FStar_Syntax_Syntax.Tm_uinst uu____201 -> t1
      | FStar_Syntax_Syntax.Tm_lazy uu____208 -> t1
      | FStar_Syntax_Syntax.Tm_fvar fv -> s t1 fv
      | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
          let bs1 = inst_binders s bs  in
          let body1 = inst s body  in
          let uu____235 =
            let uu____236 =
              let uu____253 = inst_lcomp_opt s lopt  in
              (bs1, body1, uu____253)  in
            FStar_Syntax_Syntax.Tm_abs uu____236  in
          mk1 uu____235
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let bs1 = inst_binders s bs  in
          let c1 = inst_comp s c  in
          mk1 (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
      | FStar_Syntax_Syntax.Tm_refine (bv,t2) ->
          let bv1 =
            let uu___91_303 = bv  in
            let uu____304 = inst s bv.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___91_303.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___91_303.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____304
            }  in
          let t3 = inst s t2  in
          mk1 (FStar_Syntax_Syntax.Tm_refine (bv1, t3))
      | FStar_Syntax_Syntax.Tm_app (t2,args) ->
          let uu____332 =
            let uu____333 =
              let uu____348 = inst s t2  in
              let uu____351 = inst_args s args  in (uu____348, uu____351)  in
            FStar_Syntax_Syntax.Tm_app uu____333  in
          mk1 uu____332
      | FStar_Syntax_Syntax.Tm_match (t2,pats) ->
          let pats1 =
            FStar_All.pipe_right pats
              (FStar_List.map
                 (fun uu____479  ->
                    match uu____479 with
                    | (p,wopt,t3) ->
                        let wopt1 =
                          match wopt with
                          | FStar_Pervasives_Native.None  ->
                              FStar_Pervasives_Native.None
                          | FStar_Pervasives_Native.Some w ->
                              let uu____517 = inst s w  in
                              FStar_Pervasives_Native.Some uu____517
                           in
                        let t4 = inst s t3  in (p, wopt1, t4)))
             in
          let uu____523 =
            let uu____524 = let uu____547 = inst s t2  in (uu____547, pats1)
               in
            FStar_Syntax_Syntax.Tm_match uu____524  in
          mk1 uu____523
      | FStar_Syntax_Syntax.Tm_ascribed (t11,asc,f) ->
          let inst_asc uu____640 =
            match uu____640 with
            | (annot,topt) ->
                let topt1 = FStar_Util.map_opt topt (inst s)  in
                let annot1 =
                  match annot with
                  | FStar_Util.Inl t2 ->
                      let uu____702 = inst s t2  in FStar_Util.Inl uu____702
                  | FStar_Util.Inr c ->
                      let uu____710 = inst_comp s c  in
                      FStar_Util.Inr uu____710
                   in
                (annot1, topt1)
             in
          let uu____723 =
            let uu____724 =
              let uu____751 = inst s t11  in
              let uu____754 = inst_asc asc  in (uu____751, uu____754, f)  in
            FStar_Syntax_Syntax.Tm_ascribed uu____724  in
          mk1 uu____723
      | FStar_Syntax_Syntax.Tm_let (lbs,t2) ->
          let lbs1 =
            let uu____816 =
              FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                (FStar_List.map
                   (fun lb  ->
                      let uu___92_830 = lb  in
                      let uu____831 = inst s lb.FStar_Syntax_Syntax.lbtyp  in
                      let uu____834 = inst s lb.FStar_Syntax_Syntax.lbdef  in
                      {
                        FStar_Syntax_Syntax.lbname =
                          (uu___92_830.FStar_Syntax_Syntax.lbname);
                        FStar_Syntax_Syntax.lbunivs =
                          (uu___92_830.FStar_Syntax_Syntax.lbunivs);
                        FStar_Syntax_Syntax.lbtyp = uu____831;
                        FStar_Syntax_Syntax.lbeff =
                          (uu___92_830.FStar_Syntax_Syntax.lbeff);
                        FStar_Syntax_Syntax.lbdef = uu____834;
                        FStar_Syntax_Syntax.lbattrs =
                          (uu___92_830.FStar_Syntax_Syntax.lbattrs);
                        FStar_Syntax_Syntax.lbpos =
                          (uu___92_830.FStar_Syntax_Syntax.lbpos)
                      }))
               in
            ((FStar_Pervasives_Native.fst lbs), uu____816)  in
          let uu____841 =
            let uu____842 = let uu____855 = inst s t2  in (lbs1, uu____855)
               in
            FStar_Syntax_Syntax.Tm_let uu____842  in
          mk1 uu____841
      | FStar_Syntax_Syntax.Tm_meta
          (t2,FStar_Syntax_Syntax.Meta_pattern args) ->
          let uu____882 =
            let uu____883 =
              let uu____890 = inst s t2  in
              let uu____893 =
                let uu____894 =
                  FStar_All.pipe_right args (FStar_List.map (inst_args s))
                   in
                FStar_Syntax_Syntax.Meta_pattern uu____894  in
              (uu____890, uu____893)  in
            FStar_Syntax_Syntax.Tm_meta uu____883  in
          mk1 uu____882
      | FStar_Syntax_Syntax.Tm_meta
          (t2,FStar_Syntax_Syntax.Meta_monadic (m,t')) ->
          let uu____954 =
            let uu____955 =
              let uu____962 = inst s t2  in
              let uu____965 =
                let uu____966 = let uu____973 = inst s t'  in (m, uu____973)
                   in
                FStar_Syntax_Syntax.Meta_monadic uu____966  in
              (uu____962, uu____965)  in
            FStar_Syntax_Syntax.Tm_meta uu____955  in
          mk1 uu____954
      | FStar_Syntax_Syntax.Tm_meta (t2,tag) ->
          let uu____986 =
            let uu____987 = let uu____994 = inst s t2  in (uu____994, tag)
               in
            FStar_Syntax_Syntax.Tm_meta uu____987  in
          mk1 uu____986

and (inst_binders :
  (FStar_Syntax_Syntax.term ->
     FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.term)
    -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun s  ->
    fun bs  ->
      FStar_All.pipe_right bs
        (FStar_List.map
           (fun uu____1023  ->
              match uu____1023 with
              | (x,imp) ->
                  let uu____1034 =
                    let uu___93_1035 = x  in
                    let uu____1036 = inst s x.FStar_Syntax_Syntax.sort  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___93_1035.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___93_1035.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = uu____1036
                    }  in
                  (uu____1034, imp)))

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
           (fun uu____1079  ->
              match uu____1079 with
              | (a,imp) -> let uu____1090 = inst s a  in (uu____1090, imp)))

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
          let uu____1111 = inst s t  in
          FStar_Syntax_Syntax.mk_Total' uu____1111 uopt
      | FStar_Syntax_Syntax.GTotal (t,uopt) ->
          let uu____1122 = inst s t  in
          FStar_Syntax_Syntax.mk_GTotal' uu____1122 uopt
      | FStar_Syntax_Syntax.Comp ct ->
          let ct1 =
            let uu___94_1125 = ct  in
            let uu____1126 = inst s ct.FStar_Syntax_Syntax.result_typ  in
            let uu____1129 = inst_args s ct.FStar_Syntax_Syntax.effect_args
               in
            let uu____1138 =
              FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                (FStar_List.map
                   (fun uu___90_1148  ->
                      match uu___90_1148 with
                      | FStar_Syntax_Syntax.DECREASES t ->
                          let uu____1152 = inst s t  in
                          FStar_Syntax_Syntax.DECREASES uu____1152
                      | f -> f))
               in
            {
              FStar_Syntax_Syntax.comp_univs =
                (uu___94_1125.FStar_Syntax_Syntax.comp_univs);
              FStar_Syntax_Syntax.effect_name =
                (uu___94_1125.FStar_Syntax_Syntax.effect_name);
              FStar_Syntax_Syntax.result_typ = uu____1126;
              FStar_Syntax_Syntax.effect_args = uu____1129;
              FStar_Syntax_Syntax.flags = uu____1138
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
          let uu____1167 =
            let uu___95_1168 = rc  in
            let uu____1169 =
              FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (inst s)
               in
            {
              FStar_Syntax_Syntax.residual_effect =
                (uu___95_1168.FStar_Syntax_Syntax.residual_effect);
              FStar_Syntax_Syntax.residual_typ = uu____1169;
              FStar_Syntax_Syntax.residual_flags =
                (uu___95_1168.FStar_Syntax_Syntax.residual_flags)
            }  in
          FStar_Pervasives_Native.Some uu____1167

let (instantiate :
  inst_t -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun i  ->
    fun t  ->
      match i with
      | [] -> t
      | uu____1192 ->
          let inst_fv t1 fv =
            let uu____1204 =
              FStar_Util.find_opt
                (fun uu____1218  ->
                   match uu____1218 with
                   | (x,uu____1224) ->
                       FStar_Ident.lid_equals x
                         (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                i
               in
            match uu____1204 with
            | FStar_Pervasives_Native.None  -> t1
            | FStar_Pervasives_Native.Some (uu____1229,us) ->
                mk t1 (FStar_Syntax_Syntax.Tm_uinst (t1, us))
             in
          inst inst_fv t
  