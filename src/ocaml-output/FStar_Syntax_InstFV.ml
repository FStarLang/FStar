open Prims
type inst_t = (FStar_Ident.lident * FStar_Syntax_Syntax.universes) Prims.list
let mk :
  'Auu____42366 'Auu____42367 .
    'Auu____42366 FStar_Syntax_Syntax.syntax ->
      'Auu____42367 -> 'Auu____42367 FStar_Syntax_Syntax.syntax
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
      | FStar_Syntax_Syntax.Tm_delayed uu____42497 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_name uu____42521 -> t1
      | FStar_Syntax_Syntax.Tm_uvar uu____42522 -> t1
      | FStar_Syntax_Syntax.Tm_uvar uu____42535 -> t1
      | FStar_Syntax_Syntax.Tm_type uu____42548 -> t1
      | FStar_Syntax_Syntax.Tm_bvar uu____42549 -> t1
      | FStar_Syntax_Syntax.Tm_constant uu____42550 -> t1
      | FStar_Syntax_Syntax.Tm_quoted uu____42551 -> t1
      | FStar_Syntax_Syntax.Tm_unknown  -> t1
      | FStar_Syntax_Syntax.Tm_uinst uu____42558 -> t1
      | FStar_Syntax_Syntax.Tm_lazy uu____42565 -> t1
      | FStar_Syntax_Syntax.Tm_fvar fv -> s t1 fv
      | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
          let bs1 = inst_binders s bs  in
          let body1 = inst s body  in
          let uu____42596 =
            let uu____42597 =
              let uu____42616 = inst_lcomp_opt s lopt  in
              (bs1, body1, uu____42616)  in
            FStar_Syntax_Syntax.Tm_abs uu____42597  in
          mk1 uu____42596
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let bs1 = inst_binders s bs  in
          let c1 = inst_comp s c  in
          mk1 (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
      | FStar_Syntax_Syntax.Tm_refine (bv,t2) ->
          let bv1 =
            let uu___438_42674 = bv  in
            let uu____42675 = inst s bv.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___438_42674.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___438_42674.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____42675
            }  in
          let t3 = inst s t2  in
          mk1 (FStar_Syntax_Syntax.Tm_refine (bv1, t3))
      | FStar_Syntax_Syntax.Tm_app (t2,args) ->
          let uu____42707 =
            let uu____42708 =
              let uu____42725 = inst s t2  in
              let uu____42728 = inst_args s args  in
              (uu____42725, uu____42728)  in
            FStar_Syntax_Syntax.Tm_app uu____42708  in
          mk1 uu____42707
      | FStar_Syntax_Syntax.Tm_match (t2,pats) ->
          let pats1 =
            FStar_All.pipe_right pats
              (FStar_List.map
                 (fun uu____42860  ->
                    match uu____42860 with
                    | (p,wopt,t3) ->
                        let wopt1 =
                          match wopt with
                          | FStar_Pervasives_Native.None  ->
                              FStar_Pervasives_Native.None
                          | FStar_Pervasives_Native.Some w ->
                              let uu____42898 = inst s w  in
                              FStar_Pervasives_Native.Some uu____42898
                           in
                        let t4 = inst s t3  in (p, wopt1, t4)))
             in
          let uu____42904 =
            let uu____42905 =
              let uu____42928 = inst s t2  in (uu____42928, pats1)  in
            FStar_Syntax_Syntax.Tm_match uu____42905  in
          mk1 uu____42904
      | FStar_Syntax_Syntax.Tm_ascribed (t11,asc,f) ->
          let inst_asc uu____43021 =
            match uu____43021 with
            | (annot,topt) ->
                let topt1 = FStar_Util.map_opt topt (inst s)  in
                let annot1 =
                  match annot with
                  | FStar_Util.Inl t2 ->
                      let uu____43083 = inst s t2  in
                      FStar_Util.Inl uu____43083
                  | FStar_Util.Inr c ->
                      let uu____43091 = inst_comp s c  in
                      FStar_Util.Inr uu____43091
                   in
                (annot1, topt1)
             in
          let uu____43104 =
            let uu____43105 =
              let uu____43132 = inst s t11  in
              let uu____43135 = inst_asc asc  in
              (uu____43132, uu____43135, f)  in
            FStar_Syntax_Syntax.Tm_ascribed uu____43105  in
          mk1 uu____43104
      | FStar_Syntax_Syntax.Tm_let (lbs,t2) ->
          let lbs1 =
            let uu____43200 =
              FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                (FStar_List.map
                   (fun lb  ->
                      let uu___480_43215 = lb  in
                      let uu____43216 = inst s lb.FStar_Syntax_Syntax.lbtyp
                         in
                      let uu____43219 = inst s lb.FStar_Syntax_Syntax.lbdef
                         in
                      {
                        FStar_Syntax_Syntax.lbname =
                          (uu___480_43215.FStar_Syntax_Syntax.lbname);
                        FStar_Syntax_Syntax.lbunivs =
                          (uu___480_43215.FStar_Syntax_Syntax.lbunivs);
                        FStar_Syntax_Syntax.lbtyp = uu____43216;
                        FStar_Syntax_Syntax.lbeff =
                          (uu___480_43215.FStar_Syntax_Syntax.lbeff);
                        FStar_Syntax_Syntax.lbdef = uu____43219;
                        FStar_Syntax_Syntax.lbattrs =
                          (uu___480_43215.FStar_Syntax_Syntax.lbattrs);
                        FStar_Syntax_Syntax.lbpos =
                          (uu___480_43215.FStar_Syntax_Syntax.lbpos)
                      }))
               in
            ((FStar_Pervasives_Native.fst lbs), uu____43200)  in
          let uu____43228 =
            let uu____43229 =
              let uu____43243 = inst s t2  in (lbs1, uu____43243)  in
            FStar_Syntax_Syntax.Tm_let uu____43229  in
          mk1 uu____43228
      | FStar_Syntax_Syntax.Tm_meta
          (t2,FStar_Syntax_Syntax.Meta_pattern args) ->
          let uu____43273 =
            let uu____43274 =
              let uu____43281 = inst s t2  in
              let uu____43284 =
                let uu____43285 =
                  FStar_All.pipe_right args (FStar_List.map (inst_args s))
                   in
                FStar_Syntax_Syntax.Meta_pattern uu____43285  in
              (uu____43281, uu____43284)  in
            FStar_Syntax_Syntax.Tm_meta uu____43274  in
          mk1 uu____43273
      | FStar_Syntax_Syntax.Tm_meta
          (t2,FStar_Syntax_Syntax.Meta_monadic (m,t')) ->
          let uu____43355 =
            let uu____43356 =
              let uu____43363 = inst s t2  in
              let uu____43366 =
                let uu____43367 =
                  let uu____43374 = inst s t'  in (m, uu____43374)  in
                FStar_Syntax_Syntax.Meta_monadic uu____43367  in
              (uu____43363, uu____43366)  in
            FStar_Syntax_Syntax.Tm_meta uu____43356  in
          mk1 uu____43355
      | FStar_Syntax_Syntax.Tm_meta (t2,tag) ->
          let uu____43387 =
            let uu____43388 =
              let uu____43395 = inst s t2  in (uu____43395, tag)  in
            FStar_Syntax_Syntax.Tm_meta uu____43388  in
          mk1 uu____43387

and (inst_binders :
  (FStar_Syntax_Syntax.term ->
     FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.term)
    -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun s  ->
    fun bs  ->
      FStar_All.pipe_right bs
        (FStar_List.map
           (fun uu____43430  ->
              match uu____43430 with
              | (x,imp) ->
                  let uu____43449 =
                    let uu___504_43450 = x  in
                    let uu____43451 = inst s x.FStar_Syntax_Syntax.sort  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___504_43450.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___504_43450.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = uu____43451
                    }  in
                  (uu____43449, imp)))

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
           (fun uu____43506  ->
              match uu____43506 with
              | (a,imp) -> let uu____43525 = inst s a  in (uu____43525, imp)))

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
          let uu____43548 = inst s t  in
          FStar_Syntax_Syntax.mk_Total' uu____43548 uopt
      | FStar_Syntax_Syntax.GTotal (t,uopt) ->
          let uu____43559 = inst s t  in
          FStar_Syntax_Syntax.mk_GTotal' uu____43559 uopt
      | FStar_Syntax_Syntax.Comp ct ->
          let ct1 =
            let uu___523_43562 = ct  in
            let uu____43563 = inst s ct.FStar_Syntax_Syntax.result_typ  in
            let uu____43566 = inst_args s ct.FStar_Syntax_Syntax.effect_args
               in
            let uu____43577 =
              FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                (FStar_List.map
                   (fun uu___391_43587  ->
                      match uu___391_43587 with
                      | FStar_Syntax_Syntax.DECREASES t ->
                          let uu____43591 = inst s t  in
                          FStar_Syntax_Syntax.DECREASES uu____43591
                      | f -> f))
               in
            {
              FStar_Syntax_Syntax.comp_univs =
                (uu___523_43562.FStar_Syntax_Syntax.comp_univs);
              FStar_Syntax_Syntax.effect_name =
                (uu___523_43562.FStar_Syntax_Syntax.effect_name);
              FStar_Syntax_Syntax.result_typ = uu____43563;
              FStar_Syntax_Syntax.effect_args = uu____43566;
              FStar_Syntax_Syntax.flags = uu____43577
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
          let uu____43606 =
            let uu___535_43607 = rc  in
            let uu____43608 =
              FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (inst s)
               in
            {
              FStar_Syntax_Syntax.residual_effect =
                (uu___535_43607.FStar_Syntax_Syntax.residual_effect);
              FStar_Syntax_Syntax.residual_typ = uu____43608;
              FStar_Syntax_Syntax.residual_flags =
                (uu___535_43607.FStar_Syntax_Syntax.residual_flags)
            }  in
          FStar_Pervasives_Native.Some uu____43606

let (instantiate :
  inst_t -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun i  ->
    fun t  ->
      match i with
      | [] -> t
      | uu____43632 ->
          let inst_fv t1 fv =
            let uu____43644 =
              FStar_Util.find_opt
                (fun uu____43658  ->
                   match uu____43658 with
                   | (x,uu____43665) ->
                       FStar_Ident.lid_equals x
                         (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                i
               in
            match uu____43644 with
            | FStar_Pervasives_Native.None  -> t1
            | FStar_Pervasives_Native.Some (uu____43670,us) ->
                mk t1 (FStar_Syntax_Syntax.Tm_uinst (t1, us))
             in
          inst inst_fv t
  