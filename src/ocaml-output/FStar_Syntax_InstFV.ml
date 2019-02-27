open Prims
type inst_t = (FStar_Ident.lident * FStar_Syntax_Syntax.universes) Prims.list
let mk :
  'Auu____42430 'Auu____42431 .
    'Auu____42430 FStar_Syntax_Syntax.syntax ->
      'Auu____42431 -> 'Auu____42431 FStar_Syntax_Syntax.syntax
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
      | FStar_Syntax_Syntax.Tm_delayed uu____42561 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_name uu____42585 -> t1
      | FStar_Syntax_Syntax.Tm_uvar uu____42586 -> t1
      | FStar_Syntax_Syntax.Tm_uvar uu____42599 -> t1
      | FStar_Syntax_Syntax.Tm_type uu____42612 -> t1
      | FStar_Syntax_Syntax.Tm_bvar uu____42613 -> t1
      | FStar_Syntax_Syntax.Tm_constant uu____42614 -> t1
      | FStar_Syntax_Syntax.Tm_quoted uu____42615 -> t1
      | FStar_Syntax_Syntax.Tm_unknown  -> t1
      | FStar_Syntax_Syntax.Tm_uinst uu____42622 -> t1
      | FStar_Syntax_Syntax.Tm_lazy uu____42629 -> t1
      | FStar_Syntax_Syntax.Tm_fvar fv -> s t1 fv
      | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
          let bs1 = inst_binders s bs  in
          let body1 = inst s body  in
          let uu____42660 =
            let uu____42661 =
              let uu____42680 = inst_lcomp_opt s lopt  in
              (bs1, body1, uu____42680)  in
            FStar_Syntax_Syntax.Tm_abs uu____42661  in
          mk1 uu____42660
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let bs1 = inst_binders s bs  in
          let c1 = inst_comp s c  in
          mk1 (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
      | FStar_Syntax_Syntax.Tm_refine (bv,t2) ->
          let bv1 =
            let uu___438_42738 = bv  in
            let uu____42739 = inst s bv.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___438_42738.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___438_42738.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____42739
            }  in
          let t3 = inst s t2  in
          mk1 (FStar_Syntax_Syntax.Tm_refine (bv1, t3))
      | FStar_Syntax_Syntax.Tm_app (t2,args) ->
          let uu____42771 =
            let uu____42772 =
              let uu____42789 = inst s t2  in
              let uu____42792 = inst_args s args  in
              (uu____42789, uu____42792)  in
            FStar_Syntax_Syntax.Tm_app uu____42772  in
          mk1 uu____42771
      | FStar_Syntax_Syntax.Tm_match (t2,pats) ->
          let pats1 =
            FStar_All.pipe_right pats
              (FStar_List.map
                 (fun uu____42924  ->
                    match uu____42924 with
                    | (p,wopt,t3) ->
                        let wopt1 =
                          match wopt with
                          | FStar_Pervasives_Native.None  ->
                              FStar_Pervasives_Native.None
                          | FStar_Pervasives_Native.Some w ->
                              let uu____42962 = inst s w  in
                              FStar_Pervasives_Native.Some uu____42962
                           in
                        let t4 = inst s t3  in (p, wopt1, t4)))
             in
          let uu____42968 =
            let uu____42969 =
              let uu____42992 = inst s t2  in (uu____42992, pats1)  in
            FStar_Syntax_Syntax.Tm_match uu____42969  in
          mk1 uu____42968
      | FStar_Syntax_Syntax.Tm_ascribed (t11,asc,f) ->
          let inst_asc uu____43085 =
            match uu____43085 with
            | (annot,topt) ->
                let topt1 = FStar_Util.map_opt topt (inst s)  in
                let annot1 =
                  match annot with
                  | FStar_Util.Inl t2 ->
                      let uu____43147 = inst s t2  in
                      FStar_Util.Inl uu____43147
                  | FStar_Util.Inr c ->
                      let uu____43155 = inst_comp s c  in
                      FStar_Util.Inr uu____43155
                   in
                (annot1, topt1)
             in
          let uu____43168 =
            let uu____43169 =
              let uu____43196 = inst s t11  in
              let uu____43199 = inst_asc asc  in
              (uu____43196, uu____43199, f)  in
            FStar_Syntax_Syntax.Tm_ascribed uu____43169  in
          mk1 uu____43168
      | FStar_Syntax_Syntax.Tm_let (lbs,t2) ->
          let lbs1 =
            let uu____43264 =
              FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                (FStar_List.map
                   (fun lb  ->
                      let uu___480_43279 = lb  in
                      let uu____43280 = inst s lb.FStar_Syntax_Syntax.lbtyp
                         in
                      let uu____43283 = inst s lb.FStar_Syntax_Syntax.lbdef
                         in
                      {
                        FStar_Syntax_Syntax.lbname =
                          (uu___480_43279.FStar_Syntax_Syntax.lbname);
                        FStar_Syntax_Syntax.lbunivs =
                          (uu___480_43279.FStar_Syntax_Syntax.lbunivs);
                        FStar_Syntax_Syntax.lbtyp = uu____43280;
                        FStar_Syntax_Syntax.lbeff =
                          (uu___480_43279.FStar_Syntax_Syntax.lbeff);
                        FStar_Syntax_Syntax.lbdef = uu____43283;
                        FStar_Syntax_Syntax.lbattrs =
                          (uu___480_43279.FStar_Syntax_Syntax.lbattrs);
                        FStar_Syntax_Syntax.lbpos =
                          (uu___480_43279.FStar_Syntax_Syntax.lbpos)
                      }))
               in
            ((FStar_Pervasives_Native.fst lbs), uu____43264)  in
          let uu____43292 =
            let uu____43293 =
              let uu____43307 = inst s t2  in (lbs1, uu____43307)  in
            FStar_Syntax_Syntax.Tm_let uu____43293  in
          mk1 uu____43292
      | FStar_Syntax_Syntax.Tm_meta
          (t2,FStar_Syntax_Syntax.Meta_pattern args) ->
          let uu____43337 =
            let uu____43338 =
              let uu____43345 = inst s t2  in
              let uu____43348 =
                let uu____43349 =
                  FStar_All.pipe_right args (FStar_List.map (inst_args s))
                   in
                FStar_Syntax_Syntax.Meta_pattern uu____43349  in
              (uu____43345, uu____43348)  in
            FStar_Syntax_Syntax.Tm_meta uu____43338  in
          mk1 uu____43337
      | FStar_Syntax_Syntax.Tm_meta
          (t2,FStar_Syntax_Syntax.Meta_monadic (m,t')) ->
          let uu____43419 =
            let uu____43420 =
              let uu____43427 = inst s t2  in
              let uu____43430 =
                let uu____43431 =
                  let uu____43438 = inst s t'  in (m, uu____43438)  in
                FStar_Syntax_Syntax.Meta_monadic uu____43431  in
              (uu____43427, uu____43430)  in
            FStar_Syntax_Syntax.Tm_meta uu____43420  in
          mk1 uu____43419
      | FStar_Syntax_Syntax.Tm_meta (t2,tag) ->
          let uu____43451 =
            let uu____43452 =
              let uu____43459 = inst s t2  in (uu____43459, tag)  in
            FStar_Syntax_Syntax.Tm_meta uu____43452  in
          mk1 uu____43451

and (inst_binders :
  (FStar_Syntax_Syntax.term ->
     FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.term)
    -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun s  ->
    fun bs  ->
      FStar_All.pipe_right bs
        (FStar_List.map
           (fun uu____43494  ->
              match uu____43494 with
              | (x,imp) ->
                  let uu____43513 =
                    let uu___504_43514 = x  in
                    let uu____43515 = inst s x.FStar_Syntax_Syntax.sort  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___504_43514.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___504_43514.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = uu____43515
                    }  in
                  (uu____43513, imp)))

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
           (fun uu____43570  ->
              match uu____43570 with
              | (a,imp) -> let uu____43589 = inst s a  in (uu____43589, imp)))

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
          let uu____43612 = inst s t  in
          FStar_Syntax_Syntax.mk_Total' uu____43612 uopt
      | FStar_Syntax_Syntax.GTotal (t,uopt) ->
          let uu____43623 = inst s t  in
          FStar_Syntax_Syntax.mk_GTotal' uu____43623 uopt
      | FStar_Syntax_Syntax.Comp ct ->
          let ct1 =
            let uu___523_43626 = ct  in
            let uu____43627 = inst s ct.FStar_Syntax_Syntax.result_typ  in
            let uu____43630 = inst_args s ct.FStar_Syntax_Syntax.effect_args
               in
            let uu____43641 =
              FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                (FStar_List.map
                   (fun uu___391_43651  ->
                      match uu___391_43651 with
                      | FStar_Syntax_Syntax.DECREASES t ->
                          let uu____43655 = inst s t  in
                          FStar_Syntax_Syntax.DECREASES uu____43655
                      | f -> f))
               in
            {
              FStar_Syntax_Syntax.comp_univs =
                (uu___523_43626.FStar_Syntax_Syntax.comp_univs);
              FStar_Syntax_Syntax.effect_name =
                (uu___523_43626.FStar_Syntax_Syntax.effect_name);
              FStar_Syntax_Syntax.result_typ = uu____43627;
              FStar_Syntax_Syntax.effect_args = uu____43630;
              FStar_Syntax_Syntax.flags = uu____43641
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
          let uu____43670 =
            let uu___535_43671 = rc  in
            let uu____43672 =
              FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (inst s)
               in
            {
              FStar_Syntax_Syntax.residual_effect =
                (uu___535_43671.FStar_Syntax_Syntax.residual_effect);
              FStar_Syntax_Syntax.residual_typ = uu____43672;
              FStar_Syntax_Syntax.residual_flags =
                (uu___535_43671.FStar_Syntax_Syntax.residual_flags)
            }  in
          FStar_Pervasives_Native.Some uu____43670

let (instantiate :
  inst_t -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun i  ->
    fun t  ->
      match i with
      | [] -> t
      | uu____43696 ->
          let inst_fv t1 fv =
            let uu____43708 =
              FStar_Util.find_opt
                (fun uu____43722  ->
                   match uu____43722 with
                   | (x,uu____43729) ->
                       FStar_Ident.lid_equals x
                         (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                i
               in
            match uu____43708 with
            | FStar_Pervasives_Native.None  -> t1
            | FStar_Pervasives_Native.Some (uu____43734,us) ->
                mk t1 (FStar_Syntax_Syntax.Tm_uinst (t1, us))
             in
          inst inst_fv t
  