open Prims
type inst_t =
  (FStar_Ident.lident,FStar_Syntax_Syntax.universes)
    FStar_Pervasives_Native.tuple2 Prims.list
let mk t s =
  let uu____31 = FStar_ST.read t.FStar_Syntax_Syntax.tk  in
  FStar_Syntax_Syntax.mk s uu____31 t.FStar_Syntax_Syntax.pos 
let rec inst :
  (FStar_Syntax_Syntax.term ->
     FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.term)
    -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun s  ->
    fun t  ->
      let t1 = FStar_Syntax_Subst.compress t  in
      let mk1 = mk t1  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed uu____118 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_name uu____133 -> t1
      | FStar_Syntax_Syntax.Tm_uvar uu____134 -> t1
      | FStar_Syntax_Syntax.Tm_uvar uu____145 -> t1
      | FStar_Syntax_Syntax.Tm_type uu____156 -> t1
      | FStar_Syntax_Syntax.Tm_bvar uu____157 -> t1
      | FStar_Syntax_Syntax.Tm_constant uu____158 -> t1
      | FStar_Syntax_Syntax.Tm_unknown  -> t1
      | FStar_Syntax_Syntax.Tm_uinst uu____159 -> t1
      | FStar_Syntax_Syntax.Tm_fvar fv -> s t1 fv
      | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
          let bs1 = inst_binders s bs  in
          let body1 = inst s body  in
          let uu____182 =
            let uu____183 =
              let uu____193 = inst_lcomp_opt s lopt  in
              (bs1, body1, uu____193)  in
            FStar_Syntax_Syntax.Tm_abs uu____183  in
          mk1 uu____182
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let bs1 = inst_binders s bs  in
          let c1 = inst_comp s c  in
          mk1 (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
      | FStar_Syntax_Syntax.Tm_refine (bv,t2) ->
          let bv1 =
            let uu___148_221 = bv  in
            let uu____222 = inst s bv.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___148_221.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___148_221.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____222
            }  in
          let t3 = inst s t2  in
          mk1 (FStar_Syntax_Syntax.Tm_refine (bv1, t3))
      | FStar_Syntax_Syntax.Tm_app (t2,args) ->
          let uu____242 =
            let uu____243 =
              let uu____253 = inst s t2  in
              let uu____254 = inst_args s args  in (uu____253, uu____254)  in
            FStar_Syntax_Syntax.Tm_app uu____243  in
          mk1 uu____242
      | FStar_Syntax_Syntax.Tm_match (t2,pats) ->
          let pats1 =
            FStar_All.pipe_right pats
              (FStar_List.map
                 (fun uu____330  ->
                    match uu____330 with
                    | (p,wopt,t3) ->
                        let wopt1 =
                          match wopt with
                          | FStar_Pervasives_Native.None  ->
                              FStar_Pervasives_Native.None
                          | FStar_Pervasives_Native.Some w ->
                              let uu____352 = inst s w  in
                              FStar_Pervasives_Native.Some uu____352
                           in
                        let t4 = inst s t3  in (p, wopt1, t4)))
             in
          let uu____356 =
            let uu____357 = let uu____372 = inst s t2  in (uu____372, pats1)
               in
            FStar_Syntax_Syntax.Tm_match uu____357  in
          mk1 uu____356
      | FStar_Syntax_Syntax.Tm_ascribed (t11,asc,f) ->
          let inst_asc uu____427 =
            match uu____427 with
            | (annot,topt) ->
                let topt1 = FStar_Util.map_opt topt (inst s)  in
                let annot1 =
                  match annot with
                  | FStar_Util.Inl t2 ->
                      let uu____468 = inst s t2  in FStar_Util.Inl uu____468
                  | FStar_Util.Inr c ->
                      let uu____476 = inst_comp s c  in
                      FStar_Util.Inr uu____476
                   in
                (annot1, topt1)
             in
          let uu____486 =
            let uu____487 =
              let uu____505 = inst s t11  in
              let uu____506 = inst_asc asc  in (uu____505, uu____506, f)  in
            FStar_Syntax_Syntax.Tm_ascribed uu____487  in
          mk1 uu____486
      | FStar_Syntax_Syntax.Tm_let (lbs,t2) ->
          let lbs1 =
            let uu____538 =
              FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                (FStar_List.map
                   (fun lb  ->
                      let uu___149_548 = lb  in
                      let uu____549 = inst s lb.FStar_Syntax_Syntax.lbtyp  in
                      let uu____552 = inst s lb.FStar_Syntax_Syntax.lbdef  in
                      {
                        FStar_Syntax_Syntax.lbname =
                          (uu___149_548.FStar_Syntax_Syntax.lbname);
                        FStar_Syntax_Syntax.lbunivs =
                          (uu___149_548.FStar_Syntax_Syntax.lbunivs);
                        FStar_Syntax_Syntax.lbtyp = uu____549;
                        FStar_Syntax_Syntax.lbeff =
                          (uu___149_548.FStar_Syntax_Syntax.lbeff);
                        FStar_Syntax_Syntax.lbdef = uu____552
                      }))
               in
            ((FStar_Pervasives_Native.fst lbs), uu____538)  in
          let uu____557 =
            let uu____558 = let uu____566 = inst s t2  in (lbs1, uu____566)
               in
            FStar_Syntax_Syntax.Tm_let uu____558  in
          mk1 uu____557
      | FStar_Syntax_Syntax.Tm_meta
          (t2,FStar_Syntax_Syntax.Meta_pattern args) ->
          let uu____582 =
            let uu____583 =
              let uu____588 = inst s t2  in
              let uu____589 =
                let uu____590 =
                  FStar_All.pipe_right args (FStar_List.map (inst_args s))
                   in
                FStar_Syntax_Syntax.Meta_pattern uu____590  in
              (uu____588, uu____589)  in
            FStar_Syntax_Syntax.Tm_meta uu____583  in
          mk1 uu____582
      | FStar_Syntax_Syntax.Tm_meta
          (t2,FStar_Syntax_Syntax.Meta_monadic (m,t')) ->
          let uu____630 =
            let uu____631 =
              let uu____636 = inst s t2  in
              let uu____637 =
                let uu____638 = let uu____643 = inst s t'  in (m, uu____643)
                   in
                FStar_Syntax_Syntax.Meta_monadic uu____638  in
              (uu____636, uu____637)  in
            FStar_Syntax_Syntax.Tm_meta uu____631  in
          mk1 uu____630
      | FStar_Syntax_Syntax.Tm_meta (t2,tag) ->
          let uu____650 =
            let uu____651 = let uu____656 = inst s t2  in (uu____656, tag)
               in
            FStar_Syntax_Syntax.Tm_meta uu____651  in
          mk1 uu____650

and inst_binders :
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
           (fun uu____674  ->
              match uu____674 with
              | (x,imp) ->
                  let uu____681 =
                    let uu___150_682 = x  in
                    let uu____683 = inst s x.FStar_Syntax_Syntax.sort  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___150_682.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___150_682.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = uu____683
                    }  in
                  (uu____681, imp)))

and inst_args :
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
           (fun uu____713  ->
              match uu____713 with
              | (a,imp) -> let uu____720 = inst s a  in (uu____720, imp)))

and inst_comp :
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
          let uu____739 = inst s t  in
          FStar_Syntax_Syntax.mk_Total' uu____739 uopt
      | FStar_Syntax_Syntax.GTotal (t,uopt) ->
          let uu____748 = inst s t  in
          FStar_Syntax_Syntax.mk_GTotal' uu____748 uopt
      | FStar_Syntax_Syntax.Comp ct ->
          let ct1 =
            let uu___151_751 = ct  in
            let uu____752 = inst s ct.FStar_Syntax_Syntax.result_typ  in
            let uu____755 = inst_args s ct.FStar_Syntax_Syntax.effect_args
               in
            let uu____761 =
              FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                (FStar_List.map
                   (fun uu___147_768  ->
                      match uu___147_768 with
                      | FStar_Syntax_Syntax.DECREASES t ->
                          let uu____772 = inst s t  in
                          FStar_Syntax_Syntax.DECREASES uu____772
                      | f -> f))
               in
            {
              FStar_Syntax_Syntax.comp_univs =
                (uu___151_751.FStar_Syntax_Syntax.comp_univs);
              FStar_Syntax_Syntax.effect_name =
                (uu___151_751.FStar_Syntax_Syntax.effect_name);
              FStar_Syntax_Syntax.result_typ = uu____752;
              FStar_Syntax_Syntax.effect_args = uu____755;
              FStar_Syntax_Syntax.flags = uu____761
            }  in
          FStar_Syntax_Syntax.mk_Comp ct1

and inst_lcomp_opt :
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
          let uu____785 =
            let uu___152_786 = rc  in
            let uu____787 =
              FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (inst s)
               in
            {
              FStar_Syntax_Syntax.residual_effect =
                (uu___152_786.FStar_Syntax_Syntax.residual_effect);
              FStar_Syntax_Syntax.residual_typ = uu____787;
              FStar_Syntax_Syntax.residual_flags =
                (uu___152_786.FStar_Syntax_Syntax.residual_flags)
            }  in
          FStar_Pervasives_Native.Some uu____785

let instantiate :
  inst_t -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun i  ->
    fun t  ->
      match i with
      | [] -> t
      | uu____803 ->
          let inst_fv t1 fv =
            let uu____811 =
              FStar_Util.find_opt
                (fun uu____820  ->
                   match uu____820 with
                   | (x,uu____824) ->
                       FStar_Ident.lid_equals x
                         (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                i
               in
            match uu____811 with
            | FStar_Pervasives_Native.None  -> t1
            | FStar_Pervasives_Native.Some (uu____827,us) ->
                mk t1 (FStar_Syntax_Syntax.Tm_uinst (t1, us))
             in
          inst inst_fv t
  