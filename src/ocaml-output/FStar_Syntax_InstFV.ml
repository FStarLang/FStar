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
      | FStar_Syntax_Syntax.Tm_delayed uu____145 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_name uu____168 -> t1
      | FStar_Syntax_Syntax.Tm_uvar uu____169 -> t1
      | FStar_Syntax_Syntax.Tm_uvar uu____182 -> t1
      | FStar_Syntax_Syntax.Tm_type uu____195 -> t1
      | FStar_Syntax_Syntax.Tm_bvar uu____196 -> t1
      | FStar_Syntax_Syntax.Tm_constant uu____197 -> t1
      | FStar_Syntax_Syntax.Tm_quoted uu____198 -> t1
      | FStar_Syntax_Syntax.Tm_unknown  -> t1
      | FStar_Syntax_Syntax.Tm_uinst uu____205 -> t1
      | FStar_Syntax_Syntax.Tm_lazy uu____212 -> t1
      | FStar_Syntax_Syntax.Tm_fvar fv -> s t1 fv
      | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
          let bs1 = inst_binders s bs  in
          let body1 = inst s body  in
          let uu____243 =
            let uu____244 =
              let uu____263 = inst_lcomp_opt s lopt  in
              (bs1, body1, uu____263)  in
            FStar_Syntax_Syntax.Tm_abs uu____244  in
          mk1 uu____243
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let bs1 = inst_binders s bs  in
          let c1 = inst_comp s c  in
          mk1 (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
      | FStar_Syntax_Syntax.Tm_refine (bv,t2) ->
          let bv1 =
            let uu___97_321 = bv  in
            let uu____322 = inst s bv.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___97_321.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___97_321.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____322
            }  in
          let t3 = inst s t2  in
          mk1 (FStar_Syntax_Syntax.Tm_refine (bv1, t3))
      | FStar_Syntax_Syntax.Tm_app (t2,args) ->
          let uu____354 =
            let uu____355 =
              let uu____372 = inst s t2  in
              let uu____375 = inst_args s args  in (uu____372, uu____375)  in
            FStar_Syntax_Syntax.Tm_app uu____355  in
          mk1 uu____354
      | FStar_Syntax_Syntax.Tm_match (t2,pats) ->
          let pats1 =
            FStar_All.pipe_right pats
              (FStar_List.map
                 (fun uu____507  ->
                    match uu____507 with
                    | (p,wopt,t3) ->
                        let wopt1 =
                          match wopt with
                          | FStar_Pervasives_Native.None  ->
                              FStar_Pervasives_Native.None
                          | FStar_Pervasives_Native.Some w ->
                              let uu____545 = inst s w  in
                              FStar_Pervasives_Native.Some uu____545
                           in
                        let t4 = inst s t3  in (p, wopt1, t4)))
             in
          let uu____551 =
            let uu____552 = let uu____575 = inst s t2  in (uu____575, pats1)
               in
            FStar_Syntax_Syntax.Tm_match uu____552  in
          mk1 uu____551
      | FStar_Syntax_Syntax.Tm_ascribed (t11,asc,f) ->
          let inst_asc uu____668 =
            match uu____668 with
            | (annot,topt) ->
                let topt1 = FStar_Util.map_opt topt (inst s)  in
                let annot1 =
                  match annot with
                  | FStar_Util.Inl t2 ->
                      let uu____730 = inst s t2  in FStar_Util.Inl uu____730
                  | FStar_Util.Inr c ->
                      let uu____738 = inst_comp s c  in
                      FStar_Util.Inr uu____738
                   in
                (annot1, topt1)
             in
          let uu____751 =
            let uu____752 =
              let uu____779 = inst s t11  in
              let uu____782 = inst_asc asc  in (uu____779, uu____782, f)  in
            FStar_Syntax_Syntax.Tm_ascribed uu____752  in
          mk1 uu____751
      | FStar_Syntax_Syntax.Tm_let (lbs,t2) ->
          let lbs1 =
            let uu____844 =
              FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                (FStar_List.map
                   (fun lb  ->
                      let uu___98_858 = lb  in
                      let uu____859 = inst s lb.FStar_Syntax_Syntax.lbtyp  in
                      let uu____862 = inst s lb.FStar_Syntax_Syntax.lbdef  in
                      {
                        FStar_Syntax_Syntax.lbname =
                          (uu___98_858.FStar_Syntax_Syntax.lbname);
                        FStar_Syntax_Syntax.lbunivs =
                          (uu___98_858.FStar_Syntax_Syntax.lbunivs);
                        FStar_Syntax_Syntax.lbtyp = uu____859;
                        FStar_Syntax_Syntax.lbeff =
                          (uu___98_858.FStar_Syntax_Syntax.lbeff);
                        FStar_Syntax_Syntax.lbdef = uu____862;
                        FStar_Syntax_Syntax.lbattrs =
                          (uu___98_858.FStar_Syntax_Syntax.lbattrs);
                        FStar_Syntax_Syntax.lbpos =
                          (uu___98_858.FStar_Syntax_Syntax.lbpos)
                      }))
               in
            ((FStar_Pervasives_Native.fst lbs), uu____844)  in
          let uu____869 =
            let uu____870 = let uu____883 = inst s t2  in (lbs1, uu____883)
               in
            FStar_Syntax_Syntax.Tm_let uu____870  in
          mk1 uu____869
      | FStar_Syntax_Syntax.Tm_meta
          (t2,FStar_Syntax_Syntax.Meta_pattern args) ->
          let uu____912 =
            let uu____913 =
              let uu____920 = inst s t2  in
              let uu____923 =
                let uu____924 =
                  FStar_All.pipe_right args (FStar_List.map (inst_args s))
                   in
                FStar_Syntax_Syntax.Meta_pattern uu____924  in
              (uu____920, uu____923)  in
            FStar_Syntax_Syntax.Tm_meta uu____913  in
          mk1 uu____912
      | FStar_Syntax_Syntax.Tm_meta
          (t2,FStar_Syntax_Syntax.Meta_monadic (m,t')) ->
          let uu____994 =
            let uu____995 =
              let uu____1002 = inst s t2  in
              let uu____1005 =
                let uu____1006 =
                  let uu____1013 = inst s t'  in (m, uu____1013)  in
                FStar_Syntax_Syntax.Meta_monadic uu____1006  in
              (uu____1002, uu____1005)  in
            FStar_Syntax_Syntax.Tm_meta uu____995  in
          mk1 uu____994
      | FStar_Syntax_Syntax.Tm_meta (t2,tag) ->
          let uu____1026 =
            let uu____1027 = let uu____1034 = inst s t2  in (uu____1034, tag)
               in
            FStar_Syntax_Syntax.Tm_meta uu____1027  in
          mk1 uu____1026

and (inst_binders :
  (FStar_Syntax_Syntax.term ->
     FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.term)
    -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun s  ->
    fun bs  ->
      FStar_All.pipe_right bs
        (FStar_List.map
           (fun uu____1069  ->
              match uu____1069 with
              | (x,imp) ->
                  let uu____1088 =
                    let uu___99_1089 = x  in
                    let uu____1090 = inst s x.FStar_Syntax_Syntax.sort  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___99_1089.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___99_1089.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = uu____1090
                    }  in
                  (uu____1088, imp)))

and (inst_args :
  (FStar_Syntax_Syntax.term ->
     FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.term)
    ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.arg_qualifier
                                                            FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.arg_qualifier
                                                              FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun s  ->
    fun args  ->
      FStar_All.pipe_right args
        (FStar_List.map
           (fun uu____1145  ->
              match uu____1145 with
              | (a,imp) -> let uu____1164 = inst s a  in (uu____1164, imp)))

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
          let uu____1187 = inst s t  in
          FStar_Syntax_Syntax.mk_Total' uu____1187 uopt
      | FStar_Syntax_Syntax.GTotal (t,uopt) ->
          let uu____1198 = inst s t  in
          FStar_Syntax_Syntax.mk_GTotal' uu____1198 uopt
      | FStar_Syntax_Syntax.Comp ct ->
          let ct1 =
            let uu___100_1201 = ct  in
            let uu____1202 = inst s ct.FStar_Syntax_Syntax.result_typ  in
            let uu____1205 = inst_args s ct.FStar_Syntax_Syntax.effect_args
               in
            let uu____1216 =
              FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                (FStar_List.map
                   (fun uu___96_1226  ->
                      match uu___96_1226 with
                      | FStar_Syntax_Syntax.DECREASES t ->
                          let uu____1230 = inst s t  in
                          FStar_Syntax_Syntax.DECREASES uu____1230
                      | f -> f))
               in
            {
              FStar_Syntax_Syntax.comp_univs =
                (uu___100_1201.FStar_Syntax_Syntax.comp_univs);
              FStar_Syntax_Syntax.effect_name =
                (uu___100_1201.FStar_Syntax_Syntax.effect_name);
              FStar_Syntax_Syntax.result_typ = uu____1202;
              FStar_Syntax_Syntax.effect_args = uu____1205;
              FStar_Syntax_Syntax.flags = uu____1216
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
          let uu____1245 =
            let uu___101_1246 = rc  in
            let uu____1247 =
              FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (inst s)
               in
            {
              FStar_Syntax_Syntax.residual_effect =
                (uu___101_1246.FStar_Syntax_Syntax.residual_effect);
              FStar_Syntax_Syntax.residual_typ = uu____1247;
              FStar_Syntax_Syntax.residual_flags =
                (uu___101_1246.FStar_Syntax_Syntax.residual_flags)
            }  in
          FStar_Pervasives_Native.Some uu____1245

let (instantiate :
  inst_t -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun i  ->
    fun t  ->
      match i with
      | [] -> t
      | uu____1270 ->
          let inst_fv t1 fv =
            let uu____1282 =
              FStar_Util.find_opt
                (fun uu____1296  ->
                   match uu____1296 with
                   | (x,uu____1302) ->
                       FStar_Ident.lid_equals x
                         (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                i
               in
            match uu____1282 with
            | FStar_Pervasives_Native.None  -> t1
            | FStar_Pervasives_Native.Some (uu____1307,us) ->
                mk t1 (FStar_Syntax_Syntax.Tm_uinst (t1, us))
             in
          inst inst_fv t
  