open Prims
type inst_t =
  (FStar_Ident.lident,FStar_Syntax_Syntax.universes)
    FStar_Pervasives_Native.tuple2 Prims.list
let mk t s =
  let uu____40 = FStar_ST.read t.FStar_Syntax_Syntax.tk in
  FStar_Syntax_Syntax.mk s uu____40 t.FStar_Syntax_Syntax.pos
let rec inst:
  (FStar_Syntax_Syntax.term ->
     FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.term)
    -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun s  ->
    fun t  ->
      let t1 = FStar_Syntax_Subst.compress t in
      let mk1 = mk t1 in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed uu____141 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_name uu____170 -> t1
      | FStar_Syntax_Syntax.Tm_uvar uu____171 -> t1
      | FStar_Syntax_Syntax.Tm_uvar uu____192 -> t1
      | FStar_Syntax_Syntax.Tm_type uu____213 -> t1
      | FStar_Syntax_Syntax.Tm_bvar uu____214 -> t1
      | FStar_Syntax_Syntax.Tm_constant uu____215 -> t1
      | FStar_Syntax_Syntax.Tm_unknown  -> t1
      | FStar_Syntax_Syntax.Tm_uinst uu____216 -> t1
      | FStar_Syntax_Syntax.Tm_fvar fv -> s t1 fv
      | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
          let bs1 = inst_binders s bs in
          let body1 = inst s body in
          let uu____255 =
            let uu____256 =
              let uu____275 = inst_lcomp_opt s lopt in
              (bs1, body1, uu____275) in
            FStar_Syntax_Syntax.Tm_abs uu____256 in
          mk1 uu____255
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let bs1 = inst_binders s bs in
          let c1 = inst_comp s c in
          mk1 (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
      | FStar_Syntax_Syntax.Tm_refine (bv,t2) ->
          let bv1 =
            let uu___148_323 = bv in
            let uu____324 = inst s bv.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___148_323.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___148_323.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____324
            } in
          let t3 = inst s t2 in mk1 (FStar_Syntax_Syntax.Tm_refine (bv1, t3))
      | FStar_Syntax_Syntax.Tm_app (t2,args) ->
          let uu____360 =
            let uu____361 =
              let uu____380 = inst s t2 in
              let uu____381 = inst_args s args in (uu____380, uu____381) in
            FStar_Syntax_Syntax.Tm_app uu____361 in
          mk1 uu____360
      | FStar_Syntax_Syntax.Tm_match (t2,pats) ->
          let pats1 =
            FStar_All.pipe_right pats
              (FStar_List.map
                 (fun uu____523  ->
                    match uu____523 with
                    | (p,wopt,t3) ->
                        let wopt1 =
                          match wopt with
                          | FStar_Pervasives_Native.None  ->
                              FStar_Pervasives_Native.None
                          | FStar_Pervasives_Native.Some w ->
                              let uu____561 = inst s w in
                              FStar_Pervasives_Native.Some uu____561 in
                        let t4 = inst s t3 in (p, wopt1, t4))) in
          let uu____567 =
            let uu____568 = let uu____597 = inst s t2 in (uu____597, pats1) in
            FStar_Syntax_Syntax.Tm_match uu____568 in
          mk1 uu____567
      | FStar_Syntax_Syntax.Tm_ascribed (t11,asc,f) ->
          let inst_asc uu____700 =
            match uu____700 with
            | (annot,topt) ->
                let topt1 = FStar_Util.map_opt topt (inst s) in
                let annot1 =
                  match annot with
                  | FStar_Util.Inl t2 ->
                      let uu____776 = inst s t2 in FStar_Util.Inl uu____776
                  | FStar_Util.Inr c ->
                      let uu____790 = inst_comp s c in
                      FStar_Util.Inr uu____790 in
                (annot1, topt1) in
          let uu____809 =
            let uu____810 =
              let uu____845 = inst s t11 in
              let uu____846 = inst_asc asc in (uu____845, uu____846, f) in
            FStar_Syntax_Syntax.Tm_ascribed uu____810 in
          mk1 uu____809
      | FStar_Syntax_Syntax.Tm_let (lbs,t2) ->
          let lbs1 =
            let uu____906 =
              FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                (FStar_List.map
                   (fun lb  ->
                      let uu___149_920 = lb in
                      let uu____921 = inst s lb.FStar_Syntax_Syntax.lbtyp in
                      let uu____926 = inst s lb.FStar_Syntax_Syntax.lbdef in
                      {
                        FStar_Syntax_Syntax.lbname =
                          (uu___149_920.FStar_Syntax_Syntax.lbname);
                        FStar_Syntax_Syntax.lbunivs =
                          (uu___149_920.FStar_Syntax_Syntax.lbunivs);
                        FStar_Syntax_Syntax.lbtyp = uu____921;
                        FStar_Syntax_Syntax.lbeff =
                          (uu___149_920.FStar_Syntax_Syntax.lbeff);
                        FStar_Syntax_Syntax.lbdef = uu____926
                      })) in
            ((FStar_Pervasives_Native.fst lbs), uu____906) in
          let uu____935 =
            let uu____936 = let uu____951 = inst s t2 in (lbs1, uu____951) in
            FStar_Syntax_Syntax.Tm_let uu____936 in
          mk1 uu____935
      | FStar_Syntax_Syntax.Tm_meta
          (t2,FStar_Syntax_Syntax.Meta_pattern args) ->
          let uu____980 =
            let uu____981 =
              let uu____990 = inst s t2 in
              let uu____991 =
                let uu____992 =
                  FStar_All.pipe_right args (FStar_List.map (inst_args s)) in
                FStar_Syntax_Syntax.Meta_pattern uu____992 in
              (uu____990, uu____991) in
            FStar_Syntax_Syntax.Tm_meta uu____981 in
          mk1 uu____980
      | FStar_Syntax_Syntax.Tm_meta
          (t2,FStar_Syntax_Syntax.Meta_monadic (m,t')) ->
          let uu____1068 =
            let uu____1069 =
              let uu____1078 = inst s t2 in
              let uu____1079 =
                let uu____1080 =
                  let uu____1089 = inst s t' in (m, uu____1089) in
                FStar_Syntax_Syntax.Meta_monadic uu____1080 in
              (uu____1078, uu____1079) in
            FStar_Syntax_Syntax.Tm_meta uu____1069 in
          mk1 uu____1068
      | FStar_Syntax_Syntax.Tm_meta (t2,tag) ->
          let uu____1100 =
            let uu____1101 = let uu____1110 = inst s t2 in (uu____1110, tag) in
            FStar_Syntax_Syntax.Tm_meta uu____1101 in
          mk1 uu____1100
and inst_binders:
  (FStar_Syntax_Syntax.term ->
     FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.term)
    ->
    FStar_Syntax_Syntax.binders ->
      (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
        FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun s  ->
    fun bs  ->
      FStar_All.pipe_right bs
        (FStar_List.map
           (fun uu____1135  ->
              match uu____1135 with
              | (x,imp) ->
                  let uu____1146 =
                    let uu___150_1147 = x in
                    let uu____1148 = inst s x.FStar_Syntax_Syntax.sort in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___150_1147.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___150_1147.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = uu____1148
                    } in
                  (uu____1146, imp)))
and inst_args:
  (FStar_Syntax_Syntax.term ->
     FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.term)
    ->
    ((FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
       FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual)
        FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun s  ->
    fun args  ->
      FStar_All.pipe_right args
        (FStar_List.map
           (fun uu____1197  ->
              match uu____1197 with
              | (a,imp) -> let uu____1208 = inst s a in (uu____1208, imp)))
and inst_comp:
  (FStar_Syntax_Syntax.term ->
     FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.term)
    ->
    (FStar_Syntax_Syntax.comp',Prims.unit) FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.comp
  =
  fun s  ->
    fun c  ->
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total (t,uopt) ->
          let uu____1237 = inst s t in
          FStar_Syntax_Syntax.mk_Total' uu____1237 uopt
      | FStar_Syntax_Syntax.GTotal (t,uopt) ->
          let uu____1252 = inst s t in
          FStar_Syntax_Syntax.mk_GTotal' uu____1252 uopt
      | FStar_Syntax_Syntax.Comp ct ->
          let ct1 =
            let uu___151_1255 = ct in
            let uu____1256 = inst s ct.FStar_Syntax_Syntax.result_typ in
            let uu____1261 = inst_args s ct.FStar_Syntax_Syntax.effect_args in
            let uu____1272 =
              FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                (FStar_List.map
                   (fun uu___147_1282  ->
                      match uu___147_1282 with
                      | FStar_Syntax_Syntax.DECREASES t ->
                          let uu____1288 = inst s t in
                          FStar_Syntax_Syntax.DECREASES uu____1288
                      | f -> f)) in
            {
              FStar_Syntax_Syntax.comp_univs =
                (uu___151_1255.FStar_Syntax_Syntax.comp_univs);
              FStar_Syntax_Syntax.effect_name =
                (uu___151_1255.FStar_Syntax_Syntax.effect_name);
              FStar_Syntax_Syntax.result_typ = uu____1256;
              FStar_Syntax_Syntax.effect_args = uu____1261;
              FStar_Syntax_Syntax.flags = uu____1272
            } in
          FStar_Syntax_Syntax.mk_Comp ct1
and inst_lcomp_opt:
  (FStar_Syntax_Syntax.term ->
     FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.term)
    ->
    FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option
  =
  fun s  ->
    fun l  ->
      match l with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some rc ->
          let uu____1305 =
            let uu___152_1306 = rc in
            let uu____1307 =
              FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (inst s) in
            {
              FStar_Syntax_Syntax.residual_effect =
                (uu___152_1306.FStar_Syntax_Syntax.residual_effect);
              FStar_Syntax_Syntax.residual_typ = uu____1307;
              FStar_Syntax_Syntax.residual_flags =
                (uu___152_1306.FStar_Syntax_Syntax.residual_flags)
            } in
          FStar_Pervasives_Native.Some uu____1305
let instantiate:
  inst_t -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun i  ->
    fun t  ->
      match i with
      | [] -> t
      | uu____1330 ->
          let inst_fv t1 fv =
            let uu____1338 =
              FStar_Util.find_opt
                (fun uu____1352  ->
                   match uu____1352 with
                   | (x,uu____1358) ->
                       FStar_Ident.lid_equals x
                         (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                i in
            match uu____1338 with
            | FStar_Pervasives_Native.None  -> t1
            | FStar_Pervasives_Native.Some (uu____1363,us) ->
                mk t1 (FStar_Syntax_Syntax.Tm_uinst (t1, us)) in
          inst inst_fv t