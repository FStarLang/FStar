open Prims
type inst_t = (FStar_Ident.lident * FStar_Syntax_Syntax.universes) Prims.list
let mk :
  'Auu____38007 'Auu____38008 .
    'Auu____38007 FStar_Syntax_Syntax.syntax ->
      'Auu____38008 -> 'Auu____38008 FStar_Syntax_Syntax.syntax
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
      | FStar_Syntax_Syntax.Tm_delayed uu____38138 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_name uu____38162 -> t1
      | FStar_Syntax_Syntax.Tm_uvar uu____38163 -> t1
      | FStar_Syntax_Syntax.Tm_uvar uu____38176 -> t1
      | FStar_Syntax_Syntax.Tm_type uu____38189 -> t1
      | FStar_Syntax_Syntax.Tm_bvar uu____38190 -> t1
      | FStar_Syntax_Syntax.Tm_constant uu____38191 -> t1
      | FStar_Syntax_Syntax.Tm_quoted uu____38192 -> t1
      | FStar_Syntax_Syntax.Tm_unknown  -> t1
      | FStar_Syntax_Syntax.Tm_uinst uu____38199 -> t1
      | FStar_Syntax_Syntax.Tm_lazy uu____38206 -> t1
      | FStar_Syntax_Syntax.Tm_fvar fv -> s t1 fv
      | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
          let bs1 = inst_binders s bs  in
          let body1 = inst s body  in
          let uu____38237 =
            let uu____38238 =
              let uu____38257 = inst_lcomp_opt s lopt  in
              (bs1, body1, uu____38257)  in
            FStar_Syntax_Syntax.Tm_abs uu____38238  in
          mk1 uu____38237
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let bs1 = inst_binders s bs  in
          let c1 = inst_comp s c  in
          mk1 (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
      | FStar_Syntax_Syntax.Tm_refine (bv,t2) ->
          let bv1 =
            let uu___438_38315 = bv  in
            let uu____38316 = inst s bv.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___438_38315.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___438_38315.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____38316
            }  in
          let t3 = inst s t2  in
          mk1 (FStar_Syntax_Syntax.Tm_refine (bv1, t3))
      | FStar_Syntax_Syntax.Tm_app (t2,args) ->
          let uu____38348 =
            let uu____38349 =
              let uu____38366 = inst s t2  in
              let uu____38369 = inst_args s args  in
              (uu____38366, uu____38369)  in
            FStar_Syntax_Syntax.Tm_app uu____38349  in
          mk1 uu____38348
      | FStar_Syntax_Syntax.Tm_match (t2,pats) ->
          let pats1 =
            FStar_All.pipe_right pats
              (FStar_List.map
                 (fun uu____38501  ->
                    match uu____38501 with
                    | (p,wopt,t3) ->
                        let wopt1 =
                          match wopt with
                          | FStar_Pervasives_Native.None  ->
                              FStar_Pervasives_Native.None
                          | FStar_Pervasives_Native.Some w ->
                              let uu____38539 = inst s w  in
                              FStar_Pervasives_Native.Some uu____38539
                           in
                        let t4 = inst s t3  in (p, wopt1, t4)))
             in
          let uu____38545 =
            let uu____38546 =
              let uu____38569 = inst s t2  in (uu____38569, pats1)  in
            FStar_Syntax_Syntax.Tm_match uu____38546  in
          mk1 uu____38545
      | FStar_Syntax_Syntax.Tm_ascribed (t11,asc,f) ->
          let inst_asc uu____38662 =
            match uu____38662 with
            | (annot,topt) ->
                let topt1 = FStar_Util.map_opt topt (inst s)  in
                let annot1 =
                  match annot with
                  | FStar_Util.Inl t2 ->
                      let uu____38724 = inst s t2  in
                      FStar_Util.Inl uu____38724
                  | FStar_Util.Inr c ->
                      let uu____38732 = inst_comp s c  in
                      FStar_Util.Inr uu____38732
                   in
                (annot1, topt1)
             in
          let uu____38745 =
            let uu____38746 =
              let uu____38773 = inst s t11  in
              let uu____38776 = inst_asc asc  in
              (uu____38773, uu____38776, f)  in
            FStar_Syntax_Syntax.Tm_ascribed uu____38746  in
          mk1 uu____38745
      | FStar_Syntax_Syntax.Tm_let (lbs,t2) ->
          let lbs1 =
            let uu____38841 =
              FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                (FStar_List.map
                   (fun lb  ->
                      let uu___480_38856 = lb  in
                      let uu____38857 = inst s lb.FStar_Syntax_Syntax.lbtyp
                         in
                      let uu____38860 = inst s lb.FStar_Syntax_Syntax.lbdef
                         in
                      {
                        FStar_Syntax_Syntax.lbname =
                          (uu___480_38856.FStar_Syntax_Syntax.lbname);
                        FStar_Syntax_Syntax.lbunivs =
                          (uu___480_38856.FStar_Syntax_Syntax.lbunivs);
                        FStar_Syntax_Syntax.lbtyp = uu____38857;
                        FStar_Syntax_Syntax.lbeff =
                          (uu___480_38856.FStar_Syntax_Syntax.lbeff);
                        FStar_Syntax_Syntax.lbdef = uu____38860;
                        FStar_Syntax_Syntax.lbattrs =
                          (uu___480_38856.FStar_Syntax_Syntax.lbattrs);
                        FStar_Syntax_Syntax.lbpos =
                          (uu___480_38856.FStar_Syntax_Syntax.lbpos)
                      }))
               in
            ((FStar_Pervasives_Native.fst lbs), uu____38841)  in
          let uu____38869 =
            let uu____38870 =
              let uu____38884 = inst s t2  in (lbs1, uu____38884)  in
            FStar_Syntax_Syntax.Tm_let uu____38870  in
          mk1 uu____38869
      | FStar_Syntax_Syntax.Tm_meta
          (t2,FStar_Syntax_Syntax.Meta_pattern args) ->
          let uu____38914 =
            let uu____38915 =
              let uu____38922 = inst s t2  in
              let uu____38925 =
                let uu____38926 =
                  FStar_All.pipe_right args (FStar_List.map (inst_args s))
                   in
                FStar_Syntax_Syntax.Meta_pattern uu____38926  in
              (uu____38922, uu____38925)  in
            FStar_Syntax_Syntax.Tm_meta uu____38915  in
          mk1 uu____38914
      | FStar_Syntax_Syntax.Tm_meta
          (t2,FStar_Syntax_Syntax.Meta_monadic (m,t')) ->
          let uu____38996 =
            let uu____38997 =
              let uu____39004 = inst s t2  in
              let uu____39007 =
                let uu____39008 =
                  let uu____39015 = inst s t'  in (m, uu____39015)  in
                FStar_Syntax_Syntax.Meta_monadic uu____39008  in
              (uu____39004, uu____39007)  in
            FStar_Syntax_Syntax.Tm_meta uu____38997  in
          mk1 uu____38996
      | FStar_Syntax_Syntax.Tm_meta (t2,tag) ->
          let uu____39028 =
            let uu____39029 =
              let uu____39036 = inst s t2  in (uu____39036, tag)  in
            FStar_Syntax_Syntax.Tm_meta uu____39029  in
          mk1 uu____39028

and (inst_binders :
  (FStar_Syntax_Syntax.term ->
     FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.term)
    -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun s  ->
    fun bs  ->
      FStar_All.pipe_right bs
        (FStar_List.map
           (fun uu____39071  ->
              match uu____39071 with
              | (x,imp) ->
                  let uu____39090 =
                    let uu___504_39091 = x  in
                    let uu____39092 = inst s x.FStar_Syntax_Syntax.sort  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___504_39091.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___504_39091.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = uu____39092
                    }  in
                  (uu____39090, imp)))

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
           (fun uu____39147  ->
              match uu____39147 with
              | (a,imp) -> let uu____39166 = inst s a  in (uu____39166, imp)))

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
          let uu____39189 = inst s t  in
          FStar_Syntax_Syntax.mk_Total' uu____39189 uopt
      | FStar_Syntax_Syntax.GTotal (t,uopt) ->
          let uu____39200 = inst s t  in
          FStar_Syntax_Syntax.mk_GTotal' uu____39200 uopt
      | FStar_Syntax_Syntax.Comp ct ->
          let ct1 =
            let uu___523_39203 = ct  in
            let uu____39204 = inst s ct.FStar_Syntax_Syntax.result_typ  in
            let uu____39207 = inst_args s ct.FStar_Syntax_Syntax.effect_args
               in
            let uu____39218 =
              FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                (FStar_List.map
                   (fun uu___391_39228  ->
                      match uu___391_39228 with
                      | FStar_Syntax_Syntax.DECREASES t ->
                          let uu____39232 = inst s t  in
                          FStar_Syntax_Syntax.DECREASES uu____39232
                      | f -> f))
               in
            {
              FStar_Syntax_Syntax.comp_univs =
                (uu___523_39203.FStar_Syntax_Syntax.comp_univs);
              FStar_Syntax_Syntax.effect_name =
                (uu___523_39203.FStar_Syntax_Syntax.effect_name);
              FStar_Syntax_Syntax.result_typ = uu____39204;
              FStar_Syntax_Syntax.effect_args = uu____39207;
              FStar_Syntax_Syntax.flags = uu____39218
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
          let uu____39247 =
            let uu___535_39248 = rc  in
            let uu____39249 =
              FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (inst s)
               in
            {
              FStar_Syntax_Syntax.residual_effect =
                (uu___535_39248.FStar_Syntax_Syntax.residual_effect);
              FStar_Syntax_Syntax.residual_typ = uu____39249;
              FStar_Syntax_Syntax.residual_flags =
                (uu___535_39248.FStar_Syntax_Syntax.residual_flags)
            }  in
          FStar_Pervasives_Native.Some uu____39247

let (instantiate :
  inst_t -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun i  ->
    fun t  ->
      match i with
      | [] -> t
      | uu____39273 ->
          let inst_fv t1 fv =
            let uu____39285 =
              FStar_Util.find_opt
                (fun uu____39299  ->
                   match uu____39299 with
                   | (x,uu____39306) ->
                       FStar_Ident.lid_equals x
                         (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                i
               in
            match uu____39285 with
            | FStar_Pervasives_Native.None  -> t1
            | FStar_Pervasives_Native.Some (uu____39311,us) ->
                mk t1 (FStar_Syntax_Syntax.Tm_uinst (t1, us))
             in
          inst inst_fv t
  