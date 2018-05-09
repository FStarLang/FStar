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
      | FStar_Syntax_Syntax.Tm_name uu____166 -> t1
      | FStar_Syntax_Syntax.Tm_uvar uu____167 -> t1
      | FStar_Syntax_Syntax.Tm_uvar uu____182 -> t1
      | FStar_Syntax_Syntax.Tm_type uu____197 -> t1
      | FStar_Syntax_Syntax.Tm_bvar uu____198 -> t1
      | FStar_Syntax_Syntax.Tm_constant uu____199 -> t1
      | FStar_Syntax_Syntax.Tm_quoted uu____200 -> t1
      | FStar_Syntax_Syntax.Tm_unknown  -> t1
      | FStar_Syntax_Syntax.Tm_uinst uu____207 -> t1
      | FStar_Syntax_Syntax.Tm_lazy uu____214 -> t1
      | FStar_Syntax_Syntax.Tm_fvar fv -> s t1 fv
      | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
          let bs1 = inst_binders s bs  in
          let body1 = inst s body  in
          let uu____241 =
            let uu____242 =
              let uu____259 = inst_lcomp_opt s lopt  in
              (bs1, body1, uu____259)  in
            FStar_Syntax_Syntax.Tm_abs uu____242  in
          mk1 uu____241
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let bs1 = inst_binders s bs  in
          let c1 = inst_comp s c  in
          mk1 (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
      | FStar_Syntax_Syntax.Tm_refine (bv,t2) ->
          let bv1 =
            let uu___54_309 = bv  in
            let uu____310 = inst s bv.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___54_309.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___54_309.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____310
            }  in
          let t3 = inst s t2  in
          mk1 (FStar_Syntax_Syntax.Tm_refine (bv1, t3))
      | FStar_Syntax_Syntax.Tm_app (t2,args) ->
          let uu____338 =
            let uu____339 =
              let uu____354 = inst s t2  in
              let uu____357 = inst_args s args  in (uu____354, uu____357)  in
            FStar_Syntax_Syntax.Tm_app uu____339  in
          mk1 uu____338
      | FStar_Syntax_Syntax.Tm_match (t2,pats) ->
          let pats1 =
            FStar_All.pipe_right pats
              (FStar_List.map
                 (fun uu____485  ->
                    match uu____485 with
                    | (p,wopt,t3) ->
                        let wopt1 =
                          match wopt with
                          | FStar_Pervasives_Native.None  ->
                              FStar_Pervasives_Native.None
                          | FStar_Pervasives_Native.Some w ->
                              let uu____523 = inst s w  in
                              FStar_Pervasives_Native.Some uu____523
                           in
                        let t4 = inst s t3  in (p, wopt1, t4)))
             in
          let uu____529 =
            let uu____530 = let uu____553 = inst s t2  in (uu____553, pats1)
               in
            FStar_Syntax_Syntax.Tm_match uu____530  in
          mk1 uu____529
      | FStar_Syntax_Syntax.Tm_ascribed (t11,asc,f) ->
          let inst_asc uu____646 =
            match uu____646 with
            | (annot,topt) ->
                let topt1 = FStar_Util.map_opt topt (inst s)  in
                let annot1 =
                  match annot with
                  | FStar_Util.Inl t2 ->
                      let uu____708 = inst s t2  in FStar_Util.Inl uu____708
                  | FStar_Util.Inr c ->
                      let uu____716 = inst_comp s c  in
                      FStar_Util.Inr uu____716
                   in
                (annot1, topt1)
             in
          let uu____729 =
            let uu____730 =
              let uu____757 = inst s t11  in
              let uu____760 = inst_asc asc  in (uu____757, uu____760, f)  in
            FStar_Syntax_Syntax.Tm_ascribed uu____730  in
          mk1 uu____729
      | FStar_Syntax_Syntax.Tm_let (lbs,t2) ->
          let lbs1 =
            let uu____822 =
              FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                (FStar_List.map
                   (fun lb  ->
                      let uu___55_836 = lb  in
                      let uu____837 = inst s lb.FStar_Syntax_Syntax.lbtyp  in
                      let uu____840 = inst s lb.FStar_Syntax_Syntax.lbdef  in
                      {
                        FStar_Syntax_Syntax.lbname =
                          (uu___55_836.FStar_Syntax_Syntax.lbname);
                        FStar_Syntax_Syntax.lbunivs =
                          (uu___55_836.FStar_Syntax_Syntax.lbunivs);
                        FStar_Syntax_Syntax.lbtyp = uu____837;
                        FStar_Syntax_Syntax.lbeff =
                          (uu___55_836.FStar_Syntax_Syntax.lbeff);
                        FStar_Syntax_Syntax.lbdef = uu____840;
                        FStar_Syntax_Syntax.lbattrs =
                          (uu___55_836.FStar_Syntax_Syntax.lbattrs);
                        FStar_Syntax_Syntax.lbpos =
                          (uu___55_836.FStar_Syntax_Syntax.lbpos)
                      }))
               in
            ((FStar_Pervasives_Native.fst lbs), uu____822)  in
          let uu____847 =
            let uu____848 = let uu____861 = inst s t2  in (lbs1, uu____861)
               in
            FStar_Syntax_Syntax.Tm_let uu____848  in
          mk1 uu____847
      | FStar_Syntax_Syntax.Tm_meta
          (t2,FStar_Syntax_Syntax.Meta_pattern args) ->
          let uu____888 =
            let uu____889 =
              let uu____896 = inst s t2  in
              let uu____899 =
                let uu____900 =
                  FStar_All.pipe_right args (FStar_List.map (inst_args s))
                   in
                FStar_Syntax_Syntax.Meta_pattern uu____900  in
              (uu____896, uu____899)  in
            FStar_Syntax_Syntax.Tm_meta uu____889  in
          mk1 uu____888
      | FStar_Syntax_Syntax.Tm_meta
          (t2,FStar_Syntax_Syntax.Meta_monadic (m,t')) ->
          let uu____960 =
            let uu____961 =
              let uu____968 = inst s t2  in
              let uu____971 =
                let uu____972 = let uu____979 = inst s t'  in (m, uu____979)
                   in
                FStar_Syntax_Syntax.Meta_monadic uu____972  in
              (uu____968, uu____971)  in
            FStar_Syntax_Syntax.Tm_meta uu____961  in
          mk1 uu____960
      | FStar_Syntax_Syntax.Tm_meta (t2,tag) ->
          let uu____992 =
            let uu____993 = let uu____1000 = inst s t2  in (uu____1000, tag)
               in
            FStar_Syntax_Syntax.Tm_meta uu____993  in
          mk1 uu____992

and (inst_binders :
  (FStar_Syntax_Syntax.term ->
     FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.term)
    -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun s  ->
    fun bs  ->
      FStar_All.pipe_right bs
        (FStar_List.map
           (fun uu____1029  ->
              match uu____1029 with
              | (x,imp) ->
                  let uu____1040 =
                    let uu___56_1041 = x  in
                    let uu____1042 = inst s x.FStar_Syntax_Syntax.sort  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___56_1041.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___56_1041.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = uu____1042
                    }  in
                  (uu____1040, imp)))

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
           (fun uu____1085  ->
              match uu____1085 with
              | (a,imp) -> let uu____1096 = inst s a  in (uu____1096, imp)))

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
          let uu____1117 = inst s t  in
          FStar_Syntax_Syntax.mk_Total' uu____1117 uopt
      | FStar_Syntax_Syntax.GTotal (t,uopt) ->
          let uu____1128 = inst s t  in
          FStar_Syntax_Syntax.mk_GTotal' uu____1128 uopt
      | FStar_Syntax_Syntax.Comp ct ->
          let ct1 =
            let uu___57_1131 = ct  in
            let uu____1132 = inst s ct.FStar_Syntax_Syntax.result_typ  in
            let uu____1135 = inst_args s ct.FStar_Syntax_Syntax.effect_args
               in
            let uu____1144 =
              FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                (FStar_List.map
                   (fun uu___53_1154  ->
                      match uu___53_1154 with
                      | FStar_Syntax_Syntax.DECREASES t ->
                          let uu____1158 = inst s t  in
                          FStar_Syntax_Syntax.DECREASES uu____1158
                      | f -> f))
               in
            {
              FStar_Syntax_Syntax.comp_univs =
                (uu___57_1131.FStar_Syntax_Syntax.comp_univs);
              FStar_Syntax_Syntax.effect_name =
                (uu___57_1131.FStar_Syntax_Syntax.effect_name);
              FStar_Syntax_Syntax.result_typ = uu____1132;
              FStar_Syntax_Syntax.effect_args = uu____1135;
              FStar_Syntax_Syntax.flags = uu____1144
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
          let uu____1173 =
            let uu___58_1174 = rc  in
            let uu____1175 =
              FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (inst s)
               in
            {
              FStar_Syntax_Syntax.residual_effect =
                (uu___58_1174.FStar_Syntax_Syntax.residual_effect);
              FStar_Syntax_Syntax.residual_typ = uu____1175;
              FStar_Syntax_Syntax.residual_flags =
                (uu___58_1174.FStar_Syntax_Syntax.residual_flags)
            }  in
          FStar_Pervasives_Native.Some uu____1173

let (instantiate :
  inst_t -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun i  ->
    fun t  ->
      match i with
      | [] -> t
      | uu____1198 ->
          let inst_fv t1 fv =
            let uu____1210 =
              FStar_Util.find_opt
                (fun uu____1224  ->
                   match uu____1224 with
                   | (x,uu____1230) ->
                       FStar_Ident.lid_equals x
                         (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                i
               in
            match uu____1210 with
            | FStar_Pervasives_Native.None  -> t1
            | FStar_Pervasives_Native.Some (uu____1235,us) ->
                mk t1 (FStar_Syntax_Syntax.Tm_uinst (t1, us))
             in
          inst inst_fv t
  