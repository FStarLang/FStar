open Prims
type inst_t =
  (FStar_Ident.lident,FStar_Syntax_Syntax.universes)
    FStar_Pervasives_Native.tuple2 Prims.list
let mk t s =
  let uu____35 = FStar_ST.read t.FStar_Syntax_Syntax.tk in
  FStar_Syntax_Syntax.mk s uu____35 t.FStar_Syntax_Syntax.pos
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
      | FStar_Syntax_Syntax.Tm_delayed uu____156 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_name uu____195 -> t1
      | FStar_Syntax_Syntax.Tm_uvar uu____196 -> t1
      | FStar_Syntax_Syntax.Tm_uvar uu____213 -> t1
      | FStar_Syntax_Syntax.Tm_type uu____230 -> t1
      | FStar_Syntax_Syntax.Tm_bvar uu____231 -> t1
      | FStar_Syntax_Syntax.Tm_constant uu____232 -> t1
      | FStar_Syntax_Syntax.Tm_unknown  -> t1
      | FStar_Syntax_Syntax.Tm_uinst uu____233 -> t1
      | FStar_Syntax_Syntax.Tm_fvar fv -> s t1 fv
      | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
          let bs1 = inst_binders s bs in
          let body1 = inst s body in
          let uu____292 =
            let uu____293 =
              let uu____322 = inst_lcomp_opt s lopt in
              (bs1, body1, uu____322) in
            FStar_Syntax_Syntax.Tm_abs uu____293 in
          mk1 uu____292
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let bs1 = inst_binders s bs in
          let c1 = inst_comp s c in
          mk1 (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
      | FStar_Syntax_Syntax.Tm_refine (bv,t2) ->
          let bv1 =
            let uu___146_390 = bv in
            let uu____391 = inst s bv.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___146_390.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___146_390.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____391
            } in
          let t3 = inst s t2 in mk1 (FStar_Syntax_Syntax.Tm_refine (bv1, t3))
      | FStar_Syntax_Syntax.Tm_app (t2,args) ->
          let uu____427 =
            let uu____428 =
              let uu____447 = inst s t2 in
              let uu____448 = inst_args s args in (uu____447, uu____448) in
            FStar_Syntax_Syntax.Tm_app uu____428 in
          mk1 uu____427
      | FStar_Syntax_Syntax.Tm_match (t2,pats) ->
          let pats1 =
            FStar_All.pipe_right pats
              (FStar_List.map
                 (fun uu____598  ->
                    match uu____598 with
                    | (p,wopt,t3) ->
                        let wopt1 =
                          match wopt with
                          | FStar_Pervasives_Native.None  ->
                              FStar_Pervasives_Native.None
                          | FStar_Pervasives_Native.Some w ->
                              let uu____644 = inst s w in
                              FStar_Pervasives_Native.Some uu____644 in
                        let t4 = inst s t3 in (p, wopt1, t4))) in
          let uu____652 =
            let uu____653 = let uu____684 = inst s t2 in (uu____684, pats1) in
            FStar_Syntax_Syntax.Tm_match uu____653 in
          mk1 uu____652
      | FStar_Syntax_Syntax.Tm_ascribed (t11,asc,f) ->
          let inst_asc uu____789 =
            match uu____789 with
            | (annot,topt) ->
                let topt1 = FStar_Util.map_opt topt (inst s) in
                let annot1 =
                  match annot with
                  | FStar_Util.Inl t2 ->
                      let uu____865 = inst s t2 in FStar_Util.Inl uu____865
                  | FStar_Util.Inr c ->
                      let uu____879 = inst_comp s c in
                      FStar_Util.Inr uu____879 in
                (annot1, topt1) in
          let uu____898 =
            let uu____899 =
              let uu____934 = inst s t11 in
              let uu____935 = inst_asc asc in (uu____934, uu____935, f) in
            FStar_Syntax_Syntax.Tm_ascribed uu____899 in
          mk1 uu____898
      | FStar_Syntax_Syntax.Tm_let (lbs,t2) ->
          let lbs1 =
            let uu____995 =
              FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                (FStar_List.map
                   (fun lb  ->
                      let uu___147_1005 = lb in
                      let uu____1006 = inst s lb.FStar_Syntax_Syntax.lbtyp in
                      let uu____1011 = inst s lb.FStar_Syntax_Syntax.lbdef in
                      {
                        FStar_Syntax_Syntax.lbname =
                          (uu___147_1005.FStar_Syntax_Syntax.lbname);
                        FStar_Syntax_Syntax.lbunivs =
                          (uu___147_1005.FStar_Syntax_Syntax.lbunivs);
                        FStar_Syntax_Syntax.lbtyp = uu____1006;
                        FStar_Syntax_Syntax.lbeff =
                          (uu___147_1005.FStar_Syntax_Syntax.lbeff);
                        FStar_Syntax_Syntax.lbdef = uu____1011
                      })) in
            ((FStar_Pervasives_Native.fst lbs), uu____995) in
          let uu____1020 =
            let uu____1021 = let uu____1036 = inst s t2 in (lbs1, uu____1036) in
            FStar_Syntax_Syntax.Tm_let uu____1021 in
          mk1 uu____1020
      | FStar_Syntax_Syntax.Tm_meta
          (t2,FStar_Syntax_Syntax.Meta_pattern args) ->
          let uu____1065 =
            let uu____1066 =
              let uu____1075 = inst s t2 in
              let uu____1076 =
                let uu____1077 =
                  FStar_All.pipe_right args (FStar_List.map (inst_args s)) in
                FStar_Syntax_Syntax.Meta_pattern uu____1077 in
              (uu____1075, uu____1076) in
            FStar_Syntax_Syntax.Tm_meta uu____1066 in
          mk1 uu____1065
      | FStar_Syntax_Syntax.Tm_meta
          (t2,FStar_Syntax_Syntax.Meta_monadic (m,t')) ->
          let uu____1153 =
            let uu____1154 =
              let uu____1163 = inst s t2 in
              let uu____1164 =
                let uu____1165 =
                  let uu____1174 = inst s t' in (m, uu____1174) in
                FStar_Syntax_Syntax.Meta_monadic uu____1165 in
              (uu____1163, uu____1164) in
            FStar_Syntax_Syntax.Tm_meta uu____1154 in
          mk1 uu____1153
      | FStar_Syntax_Syntax.Tm_meta (t2,tag) ->
          let uu____1185 =
            let uu____1186 = let uu____1195 = inst s t2 in (uu____1195, tag) in
            FStar_Syntax_Syntax.Tm_meta uu____1186 in
          mk1 uu____1185
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
           (fun uu____1216  ->
              match uu____1216 with
              | (x,imp) ->
                  let uu____1227 =
                    let uu___148_1228 = x in
                    let uu____1229 = inst s x.FStar_Syntax_Syntax.sort in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___148_1228.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___148_1228.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = uu____1229
                    } in
                  (uu____1227, imp)))
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
           (fun uu____1274  ->
              match uu____1274 with
              | (a,imp) -> let uu____1285 = inst s a in (uu____1285, imp)))
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
          let uu____1314 = inst s t in
          FStar_Syntax_Syntax.mk_Total' uu____1314 uopt
      | FStar_Syntax_Syntax.GTotal (t,uopt) ->
          let uu____1329 = inst s t in
          FStar_Syntax_Syntax.mk_GTotal' uu____1329 uopt
      | FStar_Syntax_Syntax.Comp ct ->
          let ct1 =
            let uu___149_1332 = ct in
            let uu____1333 = inst s ct.FStar_Syntax_Syntax.result_typ in
            let uu____1338 = inst_args s ct.FStar_Syntax_Syntax.effect_args in
            let uu____1349 =
              FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                (FStar_List.map
                   (fun uu___145_1356  ->
                      match uu___145_1356 with
                      | FStar_Syntax_Syntax.DECREASES t ->
                          let uu____1362 = inst s t in
                          FStar_Syntax_Syntax.DECREASES uu____1362
                      | f -> f)) in
            {
              FStar_Syntax_Syntax.comp_univs =
                (uu___149_1332.FStar_Syntax_Syntax.comp_univs);
              FStar_Syntax_Syntax.effect_name =
                (uu___149_1332.FStar_Syntax_Syntax.effect_name);
              FStar_Syntax_Syntax.result_typ = uu____1333;
              FStar_Syntax_Syntax.effect_args = uu____1338;
              FStar_Syntax_Syntax.flags = uu____1349
            } in
          FStar_Syntax_Syntax.mk_Comp ct1
and inst_lcomp_opt:
  (FStar_Syntax_Syntax.term ->
     FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.term)
    ->
    (FStar_Syntax_Syntax.lcomp,(FStar_Ident.lident,FStar_Syntax_Syntax.cflags
                                                     Prims.list)
                                 FStar_Pervasives_Native.tuple2)
      FStar_Util.either FStar_Pervasives_Native.option ->
      (FStar_Syntax_Syntax.lcomp,(FStar_Ident.lident,FStar_Syntax_Syntax.cflags
                                                       Prims.list)
                                   FStar_Pervasives_Native.tuple2)
        FStar_Util.either FStar_Pervasives_Native.option
  =
  fun s  ->
    fun l  ->
      match l with
      | FStar_Pervasives_Native.None  -> l
      | FStar_Pervasives_Native.Some (FStar_Util.Inr uu____1408) -> l
      | FStar_Pervasives_Native.Some (FStar_Util.Inl lc) ->
          let uu____1448 =
            let uu____1459 =
              let uu___150_1460 = lc in
              let uu____1461 = inst s lc.FStar_Syntax_Syntax.res_typ in
              {
                FStar_Syntax_Syntax.eff_name =
                  (uu___150_1460.FStar_Syntax_Syntax.eff_name);
                FStar_Syntax_Syntax.res_typ = uu____1461;
                FStar_Syntax_Syntax.cflags =
                  (uu___150_1460.FStar_Syntax_Syntax.cflags);
                FStar_Syntax_Syntax.comp =
                  (fun uu____1466  ->
                     let uu____1467 = lc.FStar_Syntax_Syntax.comp () in
                     inst_comp s uu____1467)
              } in
            FStar_Util.Inl uu____1459 in
          FStar_Pervasives_Native.Some uu____1448
let instantiate:
  inst_t -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun i  ->
    fun t  ->
      match i with
      | [] -> t
      | uu____1498 ->
          let inst_fv t1 fv =
            let uu____1506 =
              FStar_Util.find_opt
                (fun uu____1517  ->
                   match uu____1517 with
                   | (x,uu____1523) ->
                       FStar_Ident.lid_equals x
                         (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                i in
            match uu____1506 with
            | FStar_Pervasives_Native.None  -> t1
            | FStar_Pervasives_Native.Some (uu____1532,us) ->
                mk t1 (FStar_Syntax_Syntax.Tm_uinst (t1, us)) in
          inst inst_fv t