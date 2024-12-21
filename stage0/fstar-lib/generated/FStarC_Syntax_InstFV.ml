open Prims
type inst_t =
  (FStarC_Ident.lident * FStarC_Syntax_Syntax.universes) Prims.list
let mk :
  'uuuuu 'uuuuu1 .
    'uuuuu FStarC_Syntax_Syntax.syntax ->
      'uuuuu1 -> 'uuuuu1 FStarC_Syntax_Syntax.syntax
  = fun t -> fun s -> FStarC_Syntax_Syntax.mk s t.FStarC_Syntax_Syntax.pos
let rec (inst :
  (FStarC_Syntax_Syntax.term ->
     FStarC_Syntax_Syntax.fv -> FStarC_Syntax_Syntax.term)
    -> FStarC_Syntax_Syntax.term -> FStarC_Syntax_Syntax.term)
  =
  fun s ->
    fun t ->
      let t1 = FStarC_Syntax_Subst.compress t in
      let mk1 = mk t1 in
      match t1.FStarC_Syntax_Syntax.n with
      | FStarC_Syntax_Syntax.Tm_delayed uu___ -> failwith "Impossible"
      | FStarC_Syntax_Syntax.Tm_name uu___ -> t1
      | FStarC_Syntax_Syntax.Tm_uvar uu___ -> t1
      | FStarC_Syntax_Syntax.Tm_uvar uu___ -> t1
      | FStarC_Syntax_Syntax.Tm_type uu___ -> t1
      | FStarC_Syntax_Syntax.Tm_bvar uu___ -> t1
      | FStarC_Syntax_Syntax.Tm_constant uu___ -> t1
      | FStarC_Syntax_Syntax.Tm_quoted uu___ -> t1
      | FStarC_Syntax_Syntax.Tm_unknown -> t1
      | FStarC_Syntax_Syntax.Tm_uinst uu___ -> t1
      | FStarC_Syntax_Syntax.Tm_lazy uu___ -> t1
      | FStarC_Syntax_Syntax.Tm_fvar fv -> s t1 fv
      | FStarC_Syntax_Syntax.Tm_abs
          { FStarC_Syntax_Syntax.bs = bs; FStarC_Syntax_Syntax.body = body;
            FStarC_Syntax_Syntax.rc_opt = lopt;_}
          ->
          let bs1 = inst_binders s bs in
          let body1 = inst s body in
          let uu___ =
            let uu___1 =
              let uu___2 = inst_lcomp_opt s lopt in
              {
                FStarC_Syntax_Syntax.bs = bs1;
                FStarC_Syntax_Syntax.body = body1;
                FStarC_Syntax_Syntax.rc_opt = uu___2
              } in
            FStarC_Syntax_Syntax.Tm_abs uu___1 in
          mk1 uu___
      | FStarC_Syntax_Syntax.Tm_arrow
          { FStarC_Syntax_Syntax.bs1 = bs; FStarC_Syntax_Syntax.comp = c;_}
          ->
          let bs1 = inst_binders s bs in
          let c1 = inst_comp s c in
          mk1
            (FStarC_Syntax_Syntax.Tm_arrow
               {
                 FStarC_Syntax_Syntax.bs1 = bs1;
                 FStarC_Syntax_Syntax.comp = c1
               })
      | FStarC_Syntax_Syntax.Tm_refine
          { FStarC_Syntax_Syntax.b = bv; FStarC_Syntax_Syntax.phi = t2;_} ->
          let bv1 =
            let uu___ = inst s bv.FStarC_Syntax_Syntax.sort in
            {
              FStarC_Syntax_Syntax.ppname = (bv.FStarC_Syntax_Syntax.ppname);
              FStarC_Syntax_Syntax.index = (bv.FStarC_Syntax_Syntax.index);
              FStarC_Syntax_Syntax.sort = uu___
            } in
          let t3 = inst s t2 in
          mk1
            (FStarC_Syntax_Syntax.Tm_refine
               { FStarC_Syntax_Syntax.b = bv1; FStarC_Syntax_Syntax.phi = t3
               })
      | FStarC_Syntax_Syntax.Tm_app
          { FStarC_Syntax_Syntax.hd = t2; FStarC_Syntax_Syntax.args = args;_}
          ->
          let uu___ =
            let uu___1 =
              let uu___2 = inst s t2 in
              let uu___3 = inst_args s args in
              {
                FStarC_Syntax_Syntax.hd = uu___2;
                FStarC_Syntax_Syntax.args = uu___3
              } in
            FStarC_Syntax_Syntax.Tm_app uu___1 in
          mk1 uu___
      | FStarC_Syntax_Syntax.Tm_match
          { FStarC_Syntax_Syntax.scrutinee = t2;
            FStarC_Syntax_Syntax.ret_opt = asc_opt;
            FStarC_Syntax_Syntax.brs = pats;
            FStarC_Syntax_Syntax.rc_opt1 = lopt;_}
          ->
          let pats1 =
            FStarC_Compiler_List.map
              (fun uu___ ->
                 match uu___ with
                 | (p, wopt, t3) ->
                     let wopt1 =
                       match wopt with
                       | FStar_Pervasives_Native.None ->
                           FStar_Pervasives_Native.None
                       | FStar_Pervasives_Native.Some w ->
                           let uu___1 = inst s w in
                           FStar_Pervasives_Native.Some uu___1 in
                     let t4 = inst s t3 in (p, wopt1, t4)) pats in
          let asc_opt1 =
            match asc_opt with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (b, asc) ->
                let uu___ =
                  let uu___1 = inst_binder s b in
                  let uu___2 = inst_ascription s asc in (uu___1, uu___2) in
                FStar_Pervasives_Native.Some uu___ in
          let uu___ =
            let uu___1 =
              let uu___2 = inst s t2 in
              let uu___3 = inst_lcomp_opt s lopt in
              {
                FStarC_Syntax_Syntax.scrutinee = uu___2;
                FStarC_Syntax_Syntax.ret_opt = asc_opt1;
                FStarC_Syntax_Syntax.brs = pats1;
                FStarC_Syntax_Syntax.rc_opt1 = uu___3
              } in
            FStarC_Syntax_Syntax.Tm_match uu___1 in
          mk1 uu___
      | FStarC_Syntax_Syntax.Tm_ascribed
          { FStarC_Syntax_Syntax.tm = t11; FStarC_Syntax_Syntax.asc = asc;
            FStarC_Syntax_Syntax.eff_opt = f;_}
          ->
          let uu___ =
            let uu___1 =
              let uu___2 = inst s t11 in
              let uu___3 = inst_ascription s asc in
              {
                FStarC_Syntax_Syntax.tm = uu___2;
                FStarC_Syntax_Syntax.asc = uu___3;
                FStarC_Syntax_Syntax.eff_opt = f
              } in
            FStarC_Syntax_Syntax.Tm_ascribed uu___1 in
          mk1 uu___
      | FStarC_Syntax_Syntax.Tm_let
          { FStarC_Syntax_Syntax.lbs = lbs;
            FStarC_Syntax_Syntax.body1 = t2;_}
          ->
          let lbs1 =
            let uu___ =
              FStarC_Compiler_List.map
                (fun lb ->
                   let uu___1 = inst s lb.FStarC_Syntax_Syntax.lbtyp in
                   let uu___2 = inst s lb.FStarC_Syntax_Syntax.lbdef in
                   {
                     FStarC_Syntax_Syntax.lbname =
                       (lb.FStarC_Syntax_Syntax.lbname);
                     FStarC_Syntax_Syntax.lbunivs =
                       (lb.FStarC_Syntax_Syntax.lbunivs);
                     FStarC_Syntax_Syntax.lbtyp = uu___1;
                     FStarC_Syntax_Syntax.lbeff =
                       (lb.FStarC_Syntax_Syntax.lbeff);
                     FStarC_Syntax_Syntax.lbdef = uu___2;
                     FStarC_Syntax_Syntax.lbattrs =
                       (lb.FStarC_Syntax_Syntax.lbattrs);
                     FStarC_Syntax_Syntax.lbpos =
                       (lb.FStarC_Syntax_Syntax.lbpos)
                   }) (FStar_Pervasives_Native.snd lbs) in
            ((FStar_Pervasives_Native.fst lbs), uu___) in
          let uu___ =
            let uu___1 =
              let uu___2 = inst s t2 in
              {
                FStarC_Syntax_Syntax.lbs = lbs1;
                FStarC_Syntax_Syntax.body1 = uu___2
              } in
            FStarC_Syntax_Syntax.Tm_let uu___1 in
          mk1 uu___
      | FStarC_Syntax_Syntax.Tm_meta
          { FStarC_Syntax_Syntax.tm2 = t2;
            FStarC_Syntax_Syntax.meta = FStarC_Syntax_Syntax.Meta_pattern
              (bvs, args);_}
          ->
          let uu___ =
            let uu___1 =
              let uu___2 = inst s t2 in
              let uu___3 =
                let uu___4 =
                  let uu___5 = FStarC_Compiler_List.map (inst_args s) args in
                  (bvs, uu___5) in
                FStarC_Syntax_Syntax.Meta_pattern uu___4 in
              {
                FStarC_Syntax_Syntax.tm2 = uu___2;
                FStarC_Syntax_Syntax.meta = uu___3
              } in
            FStarC_Syntax_Syntax.Tm_meta uu___1 in
          mk1 uu___
      | FStarC_Syntax_Syntax.Tm_meta
          { FStarC_Syntax_Syntax.tm2 = t2;
            FStarC_Syntax_Syntax.meta = FStarC_Syntax_Syntax.Meta_monadic
              (m, t');_}
          ->
          let uu___ =
            let uu___1 =
              let uu___2 = inst s t2 in
              let uu___3 =
                let uu___4 = let uu___5 = inst s t' in (m, uu___5) in
                FStarC_Syntax_Syntax.Meta_monadic uu___4 in
              {
                FStarC_Syntax_Syntax.tm2 = uu___2;
                FStarC_Syntax_Syntax.meta = uu___3
              } in
            FStarC_Syntax_Syntax.Tm_meta uu___1 in
          mk1 uu___
      | FStarC_Syntax_Syntax.Tm_meta
          { FStarC_Syntax_Syntax.tm2 = t2; FStarC_Syntax_Syntax.meta = tag;_}
          ->
          let uu___ =
            let uu___1 =
              let uu___2 = inst s t2 in
              {
                FStarC_Syntax_Syntax.tm2 = uu___2;
                FStarC_Syntax_Syntax.meta = tag
              } in
            FStarC_Syntax_Syntax.Tm_meta uu___1 in
          mk1 uu___
and (inst_binder :
  (FStarC_Syntax_Syntax.term ->
     FStarC_Syntax_Syntax.fv -> FStarC_Syntax_Syntax.term)
    -> FStarC_Syntax_Syntax.binder -> FStarC_Syntax_Syntax.binder)
  =
  fun s ->
    fun b ->
      let uu___ =
        let uu___1 = b.FStarC_Syntax_Syntax.binder_bv in
        let uu___2 =
          inst s (b.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort in
        {
          FStarC_Syntax_Syntax.ppname = (uu___1.FStarC_Syntax_Syntax.ppname);
          FStarC_Syntax_Syntax.index = (uu___1.FStarC_Syntax_Syntax.index);
          FStarC_Syntax_Syntax.sort = uu___2
        } in
      let uu___1 =
        FStarC_Compiler_List.map (inst s) b.FStarC_Syntax_Syntax.binder_attrs in
      {
        FStarC_Syntax_Syntax.binder_bv = uu___;
        FStarC_Syntax_Syntax.binder_qual =
          (b.FStarC_Syntax_Syntax.binder_qual);
        FStarC_Syntax_Syntax.binder_positivity =
          (b.FStarC_Syntax_Syntax.binder_positivity);
        FStarC_Syntax_Syntax.binder_attrs = uu___1
      }
and (inst_binders :
  (FStarC_Syntax_Syntax.term ->
     FStarC_Syntax_Syntax.fv -> FStarC_Syntax_Syntax.term)
    -> FStarC_Syntax_Syntax.binders -> FStarC_Syntax_Syntax.binders)
  = fun s -> fun bs -> FStarC_Compiler_List.map (inst_binder s) bs
and (inst_args :
  (FStarC_Syntax_Syntax.term ->
     FStarC_Syntax_Syntax.fv -> FStarC_Syntax_Syntax.term)
    ->
    (FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax *
      FStarC_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
      Prims.list ->
      (FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax *
        FStarC_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
        Prims.list)
  =
  fun s ->
    fun args ->
      FStarC_Compiler_List.map
        (fun uu___ ->
           match uu___ with
           | (a, imp) -> let uu___1 = inst s a in (uu___1, imp)) args
and (inst_comp :
  (FStarC_Syntax_Syntax.term ->
     FStarC_Syntax_Syntax.fv -> FStarC_Syntax_Syntax.term)
    ->
    FStarC_Syntax_Syntax.comp' FStarC_Syntax_Syntax.syntax ->
      FStarC_Syntax_Syntax.comp' FStarC_Syntax_Syntax.syntax)
  =
  fun s ->
    fun c ->
      match c.FStarC_Syntax_Syntax.n with
      | FStarC_Syntax_Syntax.Total t ->
          let uu___ = inst s t in FStarC_Syntax_Syntax.mk_Total uu___
      | FStarC_Syntax_Syntax.GTotal t ->
          let uu___ = inst s t in FStarC_Syntax_Syntax.mk_GTotal uu___
      | FStarC_Syntax_Syntax.Comp ct ->
          let ct1 =
            let uu___ = inst s ct.FStarC_Syntax_Syntax.result_typ in
            let uu___1 = inst_args s ct.FStarC_Syntax_Syntax.effect_args in
            let uu___2 =
              FStarC_Compiler_List.map
                (fun uu___3 ->
                   match uu___3 with
                   | FStarC_Syntax_Syntax.DECREASES dec_order ->
                       let uu___4 = inst_decreases_order s dec_order in
                       FStarC_Syntax_Syntax.DECREASES uu___4
                   | f -> f) ct.FStarC_Syntax_Syntax.flags in
            {
              FStarC_Syntax_Syntax.comp_univs =
                (ct.FStarC_Syntax_Syntax.comp_univs);
              FStarC_Syntax_Syntax.effect_name =
                (ct.FStarC_Syntax_Syntax.effect_name);
              FStarC_Syntax_Syntax.result_typ = uu___;
              FStarC_Syntax_Syntax.effect_args = uu___1;
              FStarC_Syntax_Syntax.flags = uu___2
            } in
          FStarC_Syntax_Syntax.mk_Comp ct1
and (inst_decreases_order :
  (FStarC_Syntax_Syntax.term ->
     FStarC_Syntax_Syntax.fv -> FStarC_Syntax_Syntax.term)
    ->
    FStarC_Syntax_Syntax.decreases_order ->
      FStarC_Syntax_Syntax.decreases_order)
  =
  fun s ->
    fun uu___ ->
      match uu___ with
      | FStarC_Syntax_Syntax.Decreases_lex l ->
          let uu___1 = FStarC_Compiler_List.map (inst s) l in
          FStarC_Syntax_Syntax.Decreases_lex uu___1
      | FStarC_Syntax_Syntax.Decreases_wf (rel, e) ->
          let uu___1 =
            let uu___2 = inst s rel in
            let uu___3 = inst s e in (uu___2, uu___3) in
          FStarC_Syntax_Syntax.Decreases_wf uu___1
and (inst_lcomp_opt :
  (FStarC_Syntax_Syntax.term ->
     FStarC_Syntax_Syntax.fv -> FStarC_Syntax_Syntax.term)
    ->
    FStarC_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option ->
      FStarC_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option)
  =
  fun s ->
    fun l ->
      match l with
      | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some rc ->
          let uu___ =
            let uu___1 =
              FStarC_Compiler_Util.map_opt
                rc.FStarC_Syntax_Syntax.residual_typ (inst s) in
            {
              FStarC_Syntax_Syntax.residual_effect =
                (rc.FStarC_Syntax_Syntax.residual_effect);
              FStarC_Syntax_Syntax.residual_typ = uu___1;
              FStarC_Syntax_Syntax.residual_flags =
                (rc.FStarC_Syntax_Syntax.residual_flags)
            } in
          FStar_Pervasives_Native.Some uu___
and (inst_ascription :
  (FStarC_Syntax_Syntax.term ->
     FStarC_Syntax_Syntax.fv -> FStarC_Syntax_Syntax.term)
    ->
    FStarC_Syntax_Syntax.ascription ->
      ((FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax,
        FStarC_Syntax_Syntax.comp' FStarC_Syntax_Syntax.syntax)
        FStar_Pervasives.either * FStarC_Syntax_Syntax.term'
        FStarC_Syntax_Syntax.syntax FStar_Pervasives_Native.option *
        Prims.bool))
  =
  fun s ->
    fun asc ->
      let uu___ = asc in
      match uu___ with
      | (annot, topt, use_eq) ->
          let annot1 =
            match annot with
            | FStar_Pervasives.Inl t ->
                let uu___1 = inst s t in FStar_Pervasives.Inl uu___1
            | FStar_Pervasives.Inr c ->
                let uu___1 = inst_comp s c in FStar_Pervasives.Inr uu___1 in
          let topt1 = FStarC_Compiler_Util.map_opt topt (inst s) in
          (annot1, topt1, use_eq)
let (instantiate :
  inst_t -> FStarC_Syntax_Syntax.term -> FStarC_Syntax_Syntax.term) =
  fun i ->
    fun t ->
      match i with
      | [] -> t
      | uu___ ->
          let inst_fv t1 fv =
            let uu___1 =
              FStarC_Compiler_Util.find_opt
                (fun uu___2 ->
                   match uu___2 with
                   | (x, uu___3) ->
                       FStarC_Ident.lid_equals x
                         (fv.FStarC_Syntax_Syntax.fv_name).FStarC_Syntax_Syntax.v)
                i in
            match uu___1 with
            | FStar_Pervasives_Native.None -> t1
            | FStar_Pervasives_Native.Some (uu___2, us) ->
                mk t1 (FStarC_Syntax_Syntax.Tm_uinst (t1, us)) in
          inst inst_fv t