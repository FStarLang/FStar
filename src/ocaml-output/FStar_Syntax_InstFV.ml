open Prims
type inst_t = (FStar_Ident.lident * FStar_Syntax_Syntax.universes) Prims.list
let mk :
  'Auu____42361 'Auu____42362 .
    'Auu____42361 FStar_Syntax_Syntax.syntax ->
      'Auu____42362 -> 'Auu____42362 FStar_Syntax_Syntax.syntax
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
      | FStar_Syntax_Syntax.Tm_delayed uu____42492 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_name uu____42516 -> t1
      | FStar_Syntax_Syntax.Tm_uvar uu____42517 -> t1
      | FStar_Syntax_Syntax.Tm_uvar uu____42530 -> t1
      | FStar_Syntax_Syntax.Tm_type uu____42543 -> t1
      | FStar_Syntax_Syntax.Tm_bvar uu____42544 -> t1
      | FStar_Syntax_Syntax.Tm_constant uu____42545 -> t1
      | FStar_Syntax_Syntax.Tm_quoted uu____42546 -> t1
      | FStar_Syntax_Syntax.Tm_unknown  -> t1
      | FStar_Syntax_Syntax.Tm_uinst uu____42553 -> t1
      | FStar_Syntax_Syntax.Tm_lazy uu____42560 -> t1
      | FStar_Syntax_Syntax.Tm_fvar fv -> s t1 fv
      | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
          let bs1 = inst_binders s bs  in
          let body1 = inst s body  in
          let uu____42591 =
            let uu____42592 =
              let uu____42611 = inst_lcomp_opt s lopt  in
              (bs1, body1, uu____42611)  in
            FStar_Syntax_Syntax.Tm_abs uu____42592  in
          mk1 uu____42591
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let bs1 = inst_binders s bs  in
          let c1 = inst_comp s c  in
          mk1 (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
      | FStar_Syntax_Syntax.Tm_refine (bv,t2) ->
          let bv1 =
            let uu___438_42669 = bv  in
            let uu____42670 = inst s bv.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___438_42669.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___438_42669.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____42670
            }  in
          let t3 = inst s t2  in
          mk1 (FStar_Syntax_Syntax.Tm_refine (bv1, t3))
      | FStar_Syntax_Syntax.Tm_app (t2,args) ->
          let uu____42702 =
            let uu____42703 =
              let uu____42720 = inst s t2  in
              let uu____42723 = inst_args s args  in
              (uu____42720, uu____42723)  in
            FStar_Syntax_Syntax.Tm_app uu____42703  in
          mk1 uu____42702
      | FStar_Syntax_Syntax.Tm_match (t2,pats) ->
          let pats1 =
            FStar_All.pipe_right pats
              (FStar_List.map
                 (fun uu____42855  ->
                    match uu____42855 with
                    | (p,wopt,t3) ->
                        let wopt1 =
                          match wopt with
                          | FStar_Pervasives_Native.None  ->
                              FStar_Pervasives_Native.None
                          | FStar_Pervasives_Native.Some w ->
                              let uu____42893 = inst s w  in
                              FStar_Pervasives_Native.Some uu____42893
                           in
                        let t4 = inst s t3  in (p, wopt1, t4)))
             in
          let uu____42899 =
            let uu____42900 =
              let uu____42923 = inst s t2  in (uu____42923, pats1)  in
            FStar_Syntax_Syntax.Tm_match uu____42900  in
          mk1 uu____42899
      | FStar_Syntax_Syntax.Tm_ascribed (t11,asc,f) ->
          let inst_asc uu____43016 =
            match uu____43016 with
            | (annot,topt) ->
                let topt1 = FStar_Util.map_opt topt (inst s)  in
                let annot1 =
                  match annot with
                  | FStar_Util.Inl t2 ->
                      let uu____43078 = inst s t2  in
                      FStar_Util.Inl uu____43078
                  | FStar_Util.Inr c ->
                      let uu____43086 = inst_comp s c  in
                      FStar_Util.Inr uu____43086
                   in
                (annot1, topt1)
             in
          let uu____43099 =
            let uu____43100 =
              let uu____43127 = inst s t11  in
              let uu____43130 = inst_asc asc  in
              (uu____43127, uu____43130, f)  in
            FStar_Syntax_Syntax.Tm_ascribed uu____43100  in
          mk1 uu____43099
      | FStar_Syntax_Syntax.Tm_let (lbs,t2) ->
          let lbs1 =
            let uu____43195 =
              FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                (FStar_List.map
                   (fun lb  ->
                      let uu___480_43210 = lb  in
                      let uu____43211 = inst s lb.FStar_Syntax_Syntax.lbtyp
                         in
                      let uu____43214 = inst s lb.FStar_Syntax_Syntax.lbdef
                         in
                      {
                        FStar_Syntax_Syntax.lbname =
                          (uu___480_43210.FStar_Syntax_Syntax.lbname);
                        FStar_Syntax_Syntax.lbunivs =
                          (uu___480_43210.FStar_Syntax_Syntax.lbunivs);
                        FStar_Syntax_Syntax.lbtyp = uu____43211;
                        FStar_Syntax_Syntax.lbeff =
                          (uu___480_43210.FStar_Syntax_Syntax.lbeff);
                        FStar_Syntax_Syntax.lbdef = uu____43214;
                        FStar_Syntax_Syntax.lbattrs =
                          (uu___480_43210.FStar_Syntax_Syntax.lbattrs);
                        FStar_Syntax_Syntax.lbpos =
                          (uu___480_43210.FStar_Syntax_Syntax.lbpos)
                      }))
               in
            ((FStar_Pervasives_Native.fst lbs), uu____43195)  in
          let uu____43223 =
            let uu____43224 =
              let uu____43238 = inst s t2  in (lbs1, uu____43238)  in
            FStar_Syntax_Syntax.Tm_let uu____43224  in
          mk1 uu____43223
      | FStar_Syntax_Syntax.Tm_meta
          (t2,FStar_Syntax_Syntax.Meta_pattern args) ->
          let uu____43268 =
            let uu____43269 =
              let uu____43276 = inst s t2  in
              let uu____43279 =
                let uu____43280 =
                  FStar_All.pipe_right args (FStar_List.map (inst_args s))
                   in
                FStar_Syntax_Syntax.Meta_pattern uu____43280  in
              (uu____43276, uu____43279)  in
            FStar_Syntax_Syntax.Tm_meta uu____43269  in
          mk1 uu____43268
      | FStar_Syntax_Syntax.Tm_meta
          (t2,FStar_Syntax_Syntax.Meta_monadic (m,t')) ->
          let uu____43350 =
            let uu____43351 =
              let uu____43358 = inst s t2  in
              let uu____43361 =
                let uu____43362 =
                  let uu____43369 = inst s t'  in (m, uu____43369)  in
                FStar_Syntax_Syntax.Meta_monadic uu____43362  in
              (uu____43358, uu____43361)  in
            FStar_Syntax_Syntax.Tm_meta uu____43351  in
          mk1 uu____43350
      | FStar_Syntax_Syntax.Tm_meta (t2,tag) ->
          let uu____43382 =
            let uu____43383 =
              let uu____43390 = inst s t2  in (uu____43390, tag)  in
            FStar_Syntax_Syntax.Tm_meta uu____43383  in
          mk1 uu____43382

and (inst_binders :
  (FStar_Syntax_Syntax.term ->
     FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.term)
    -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun s  ->
    fun bs  ->
      FStar_All.pipe_right bs
        (FStar_List.map
           (fun uu____43425  ->
              match uu____43425 with
              | (x,imp) ->
                  let uu____43444 =
                    let uu___504_43445 = x  in
                    let uu____43446 = inst s x.FStar_Syntax_Syntax.sort  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___504_43445.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___504_43445.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = uu____43446
                    }  in
                  (uu____43444, imp)))

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
           (fun uu____43501  ->
              match uu____43501 with
              | (a,imp) -> let uu____43520 = inst s a  in (uu____43520, imp)))

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
          let uu____43543 = inst s t  in
          FStar_Syntax_Syntax.mk_Total' uu____43543 uopt
      | FStar_Syntax_Syntax.GTotal (t,uopt) ->
          let uu____43554 = inst s t  in
          FStar_Syntax_Syntax.mk_GTotal' uu____43554 uopt
      | FStar_Syntax_Syntax.Comp ct ->
          let ct1 =
            let uu___523_43557 = ct  in
            let uu____43558 = inst s ct.FStar_Syntax_Syntax.result_typ  in
            let uu____43561 = inst_args s ct.FStar_Syntax_Syntax.effect_args
               in
            let uu____43572 =
              FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                (FStar_List.map
                   (fun uu___391_43582  ->
                      match uu___391_43582 with
                      | FStar_Syntax_Syntax.DECREASES t ->
                          let uu____43586 = inst s t  in
                          FStar_Syntax_Syntax.DECREASES uu____43586
                      | f -> f))
               in
            {
              FStar_Syntax_Syntax.comp_univs =
                (uu___523_43557.FStar_Syntax_Syntax.comp_univs);
              FStar_Syntax_Syntax.effect_name =
                (uu___523_43557.FStar_Syntax_Syntax.effect_name);
              FStar_Syntax_Syntax.result_typ = uu____43558;
              FStar_Syntax_Syntax.effect_args = uu____43561;
              FStar_Syntax_Syntax.flags = uu____43572
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
          let uu____43601 =
            let uu___535_43602 = rc  in
            let uu____43603 =
              FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (inst s)
               in
            {
              FStar_Syntax_Syntax.residual_effect =
                (uu___535_43602.FStar_Syntax_Syntax.residual_effect);
              FStar_Syntax_Syntax.residual_typ = uu____43603;
              FStar_Syntax_Syntax.residual_flags =
                (uu___535_43602.FStar_Syntax_Syntax.residual_flags)
            }  in
          FStar_Pervasives_Native.Some uu____43601

let (instantiate :
  inst_t -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun i  ->
    fun t  ->
      match i with
      | [] -> t
      | uu____43627 ->
          let inst_fv t1 fv =
            let uu____43639 =
              FStar_Util.find_opt
                (fun uu____43653  ->
                   match uu____43653 with
                   | (x,uu____43660) ->
                       FStar_Ident.lid_equals x
                         (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                i
               in
            match uu____43639 with
            | FStar_Pervasives_Native.None  -> t1
            | FStar_Pervasives_Native.Some (uu____43665,us) ->
                mk t1 (FStar_Syntax_Syntax.Tm_uinst (t1, us))
             in
          inst inst_fv t
  