open Prims
type free_vars =
  {
  free_names: FStar_Syntax_Syntax.bv FStar_Util.set;
  free_uvars: FStar_Syntax_Syntax.uvars;
  free_univs: FStar_Syntax_Syntax.universe_uvar FStar_Util.set;
  free_univ_names: FStar_Syntax_Syntax.univ_name FStar_Util.fifo_set;
  free_fvars: FStar_Ident.lident FStar_Util.set;}
let __proj__Mkfree_vars__item__free_names:
  free_vars -> FStar_Syntax_Syntax.bv FStar_Util.set =
  fun projectee  ->
    match projectee with
    | { free_names = __fname__free_names; free_uvars = __fname__free_uvars;
        free_univs = __fname__free_univs;
        free_univ_names = __fname__free_univ_names;
        free_fvars = __fname__free_fvars;_} -> __fname__free_names
let __proj__Mkfree_vars__item__free_uvars:
  free_vars -> FStar_Syntax_Syntax.uvars =
  fun projectee  ->
    match projectee with
    | { free_names = __fname__free_names; free_uvars = __fname__free_uvars;
        free_univs = __fname__free_univs;
        free_univ_names = __fname__free_univ_names;
        free_fvars = __fname__free_fvars;_} -> __fname__free_uvars
let __proj__Mkfree_vars__item__free_univs:
  free_vars -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set =
  fun projectee  ->
    match projectee with
    | { free_names = __fname__free_names; free_uvars = __fname__free_uvars;
        free_univs = __fname__free_univs;
        free_univ_names = __fname__free_univ_names;
        free_fvars = __fname__free_fvars;_} -> __fname__free_univs
let __proj__Mkfree_vars__item__free_univ_names:
  free_vars -> FStar_Syntax_Syntax.univ_name FStar_Util.fifo_set =
  fun projectee  ->
    match projectee with
    | { free_names = __fname__free_names; free_uvars = __fname__free_uvars;
        free_univs = __fname__free_univs;
        free_univ_names = __fname__free_univ_names;
        free_fvars = __fname__free_fvars;_} -> __fname__free_univ_names
let __proj__Mkfree_vars__item__free_fvars:
  free_vars -> FStar_Ident.lident FStar_Util.set =
  fun projectee  ->
    match projectee with
    | { free_names = __fname__free_names; free_uvars = __fname__free_uvars;
        free_univs = __fname__free_univs;
        free_univ_names = __fname__free_univ_names;
        free_fvars = __fname__free_fvars;_} -> __fname__free_fvars
let new_uv_set:
  Prims.unit ->
    (FStar_Syntax_Syntax.uvar,FStar_Syntax_Syntax.typ)
      FStar_Pervasives_Native.tuple2 FStar_Util.set
  =
  fun uu____105  ->
    FStar_Util.new_set
      (fun uu____116  ->
         fun uu____117  ->
           match (uu____116, uu____117) with
           | ((x,uu____127),(y,uu____129)) ->
               let uu____134 = FStar_Syntax_Unionfind.uvar_id x in
               let uu____135 = FStar_Syntax_Unionfind.uvar_id y in
               uu____134 - uu____135)
      (fun uu____139  ->
         match uu____139 with
         | (x,uu____143) -> FStar_Syntax_Unionfind.uvar_id x)
let new_universe_uvar_set:
  Prims.unit -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set =
  fun uu____148  ->
    FStar_Util.new_set
      (fun x  ->
         fun y  ->
           let uu____156 = FStar_Syntax_Unionfind.univ_uvar_id x in
           let uu____157 = FStar_Syntax_Unionfind.univ_uvar_id y in
           uu____156 - uu____157)
      (fun x  -> FStar_Syntax_Unionfind.univ_uvar_id x)
let no_uvs: FStar_Syntax_Syntax.uvars = new_uv_set ()
let no_universe_uvars: FStar_Syntax_Syntax.universe_uvar FStar_Util.set =
  new_universe_uvar_set ()
let no_free_vars: free_vars =
  let uu____161 = FStar_Syntax_Syntax.new_fv_set () in
  {
    free_names = FStar_Syntax_Syntax.no_names;
    free_uvars = no_uvs;
    free_univs = no_universe_uvars;
    free_univ_names = FStar_Syntax_Syntax.no_universe_names;
    free_fvars = uu____161
  }
let singleton_bv: FStar_Syntax_Syntax.bv -> free_vars =
  fun x  ->
    let uu___147_169 = no_free_vars in
    let uu____170 = FStar_Util.set_add x no_free_vars.free_names in
    {
      free_names = uu____170;
      free_uvars = (uu___147_169.free_uvars);
      free_univs = (uu___147_169.free_univs);
      free_univ_names = (uu___147_169.free_univ_names);
      free_fvars = (uu___147_169.free_fvars)
    }
let singleton_uv:
  (FStar_Syntax_Syntax.uvar,FStar_Syntax_Syntax.typ)
    FStar_Pervasives_Native.tuple2 -> free_vars
  =
  fun x  ->
    let uu___148_182 = no_free_vars in
    let uu____183 = FStar_Util.set_add x no_free_vars.free_uvars in
    {
      free_names = (uu___148_182.free_names);
      free_uvars = uu____183;
      free_univs = (uu___148_182.free_univs);
      free_univ_names = (uu___148_182.free_univ_names);
      free_fvars = (uu___148_182.free_fvars)
    }
let singleton_univ: FStar_Syntax_Syntax.universe_uvar -> free_vars =
  fun x  ->
    let uu___149_192 = no_free_vars in
    let uu____193 = FStar_Util.set_add x no_free_vars.free_univs in
    {
      free_names = (uu___149_192.free_names);
      free_uvars = (uu___149_192.free_uvars);
      free_univs = uu____193;
      free_univ_names = (uu___149_192.free_univ_names);
      free_fvars = (uu___149_192.free_fvars)
    }
let singleton_univ_name: FStar_Syntax_Syntax.univ_name -> free_vars =
  fun x  ->
    let uu___150_201 = no_free_vars in
    let uu____202 = FStar_Util.fifo_set_add x no_free_vars.free_univ_names in
    {
      free_names = (uu___150_201.free_names);
      free_uvars = (uu___150_201.free_uvars);
      free_univs = (uu___150_201.free_univs);
      free_univ_names = uu____202;
      free_fvars = (uu___150_201.free_fvars)
    }
let singleton_fvar: FStar_Syntax_Syntax.fv -> free_vars =
  fun fv  ->
    let uu___151_213 = no_free_vars in
    let uu____214 =
      FStar_Util.set_add
        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
        no_free_vars.free_fvars in
    {
      free_names = (uu___151_213.free_names);
      free_uvars = (uu___151_213.free_uvars);
      free_univs = (uu___151_213.free_univs);
      free_univ_names = (uu___151_213.free_univ_names);
      free_fvars = uu____214
    }
let union: free_vars -> free_vars -> free_vars =
  fun f1  ->
    fun f2  ->
      let uu____226 = FStar_Util.set_union f1.free_names f2.free_names in
      let uu____228 = FStar_Util.set_union f1.free_uvars f2.free_uvars in
      let uu____231 = FStar_Util.set_union f1.free_univs f2.free_univs in
      let uu____233 =
        FStar_Util.fifo_set_union f1.free_univ_names f2.free_univ_names in
      let uu____240 = FStar_Util.set_union f1.free_fvars f2.free_fvars in
      {
        free_names = uu____226;
        free_uvars = uu____228;
        free_univs = uu____231;
        free_univ_names = uu____233;
        free_fvars = uu____240
      }
let rec free_univs: FStar_Syntax_Syntax.universe -> free_vars =
  fun u  ->
    let uu____248 = FStar_Syntax_Subst.compress_univ u in
    match uu____248 with
    | FStar_Syntax_Syntax.U_zero  -> no_free_vars
    | FStar_Syntax_Syntax.U_bvar uu____249 -> no_free_vars
    | FStar_Syntax_Syntax.U_unknown  -> no_free_vars
    | FStar_Syntax_Syntax.U_name uname -> singleton_univ_name uname
    | FStar_Syntax_Syntax.U_succ u1 -> free_univs u1
    | FStar_Syntax_Syntax.U_max us ->
        FStar_List.fold_left
          (fun out  ->
             fun x  -> let uu____259 = free_univs x in union out uu____259)
          no_free_vars us
    | FStar_Syntax_Syntax.U_unif u1 -> singleton_univ u1
let rec free_names_and_uvs': FStar_Syntax_Syntax.term -> free_vars =
  fun tm  ->
    let aux_binders bs from_body =
      let from_binders =
        FStar_All.pipe_right bs
          (FStar_List.fold_left
             (fun n1  ->
                fun uu____314  ->
                  match uu____314 with
                  | (x,uu____318) ->
                      let uu____319 =
                        free_names_and_uvars x.FStar_Syntax_Syntax.sort in
                      union n1 uu____319) no_free_vars) in
      union from_binders from_body in
    let t = FStar_Syntax_Subst.compress tm in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____321 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_name x -> singleton_bv x
    | FStar_Syntax_Syntax.Tm_uvar (x,t1) -> singleton_uv (x, t1)
    | FStar_Syntax_Syntax.Tm_type u -> free_univs u
    | FStar_Syntax_Syntax.Tm_bvar uu____364 -> no_free_vars
    | FStar_Syntax_Syntax.Tm_fvar fv -> singleton_fvar fv
    | FStar_Syntax_Syntax.Tm_constant uu____366 -> no_free_vars
    | FStar_Syntax_Syntax.Tm_unknown  -> no_free_vars
    | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
        let f = free_names_and_uvars t1 in
        FStar_List.fold_left
          (fun out  ->
             fun u  -> let uu____379 = free_univs u in union out uu____379) f
          us
    | FStar_Syntax_Syntax.Tm_abs (bs,t1,uu____382) ->
        let uu____395 = free_names_and_uvars t1 in aux_binders bs uu____395
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____408 = free_names_and_uvars_comp c in
        aux_binders bs uu____408
    | FStar_Syntax_Syntax.Tm_refine (bv,t1) ->
        let uu____415 = free_names_and_uvars t1 in
        aux_binders [(bv, FStar_Pervasives_Native.None)] uu____415
    | FStar_Syntax_Syntax.Tm_app (t1,args) ->
        let uu____439 = free_names_and_uvars t1 in
        free_names_and_uvars_args args uu____439
    | FStar_Syntax_Syntax.Tm_match (t1,pats) ->
        let uu____466 =
          let uu____479 = free_names_and_uvars t1 in
          FStar_List.fold_left
            (fun n1  ->
               fun uu____498  ->
                 match uu____498 with
                 | (p,wopt,t2) ->
                     let n11 =
                       match wopt with
                       | FStar_Pervasives_Native.None  -> no_free_vars
                       | FStar_Pervasives_Native.Some w ->
                           free_names_and_uvars w in
                     let n2 = free_names_and_uvars t2 in
                     let n3 =
                       let uu____530 = FStar_Syntax_Syntax.pat_bvs p in
                       FStar_All.pipe_right uu____530
                         (FStar_List.fold_left
                            (fun n3  ->
                               fun x  ->
                                 let uu____538 =
                                   free_names_and_uvars
                                     x.FStar_Syntax_Syntax.sort in
                                 union n3 uu____538) n1) in
                     let uu____539 = union n11 n2 in union n3 uu____539)
            uu____479 in
        FStar_All.pipe_right pats uu____466
    | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,uu____552) ->
        let u1 = free_names_and_uvars t1 in
        let u2 =
          match FStar_Pervasives_Native.fst asc with
          | FStar_Util.Inl t2 -> free_names_and_uvars t2
          | FStar_Util.Inr c2 -> free_names_and_uvars_comp c2 in
        (match FStar_Pervasives_Native.snd asc with
         | FStar_Pervasives_Native.None  -> union u1 u2
         | FStar_Pervasives_Native.Some tac ->
             let uu____622 = union u1 u2 in
             let uu____623 = free_names_and_uvars tac in
             union uu____622 uu____623)
    | FStar_Syntax_Syntax.Tm_let (lbs,t1) ->
        let uu____636 =
          let uu____640 = free_names_and_uvars t1 in
          FStar_List.fold_left
            (fun n1  ->
               fun lb  ->
                 let uu____646 =
                   let uu____647 =
                     free_names_and_uvars lb.FStar_Syntax_Syntax.lbtyp in
                   let uu____648 =
                     free_names_and_uvars lb.FStar_Syntax_Syntax.lbdef in
                   union uu____647 uu____648 in
                 union n1 uu____646) uu____640 in
        FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs) uu____636
    | FStar_Syntax_Syntax.Tm_meta (t1,FStar_Syntax_Syntax.Meta_pattern args)
        ->
        let uu____663 = free_names_and_uvars t1 in
        FStar_List.fold_right
          (fun a  -> fun acc  -> free_names_and_uvars_args a acc) args
          uu____663
    | FStar_Syntax_Syntax.Tm_meta
        (t1,FStar_Syntax_Syntax.Meta_monadic (uu____679,t')) ->
        let uu____689 = free_names_and_uvars t1 in
        let uu____690 = free_names_and_uvars t' in union uu____689 uu____690
    | FStar_Syntax_Syntax.Tm_meta (t1,uu____692) -> free_names_and_uvars t1
and free_names_and_uvars:
  (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax -> free_vars
  =
  fun t  -> let t1 = FStar_Syntax_Subst.compress t in free_names_and_uvs' t1
and free_names_and_uvars_args:
  ((FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
     FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list -> free_vars -> free_vars
  =
  fun args  ->
    fun acc  ->
      FStar_All.pipe_right args
        (FStar_List.fold_left
           (fun n1  ->
              fun uu____723  ->
                match uu____723 with
                | (x,uu____729) ->
                    let uu____734 = free_names_and_uvars x in
                    union n1 uu____734) acc)
and free_names_and_uvars_binders:
  FStar_Syntax_Syntax.binders -> free_vars -> free_vars =
  fun bs  ->
    fun acc  ->
      FStar_All.pipe_right bs
        (FStar_List.fold_left
           (fun n1  ->
              fun uu____745  ->
                match uu____745 with
                | (x,uu____749) ->
                    let uu____750 =
                      free_names_and_uvars x.FStar_Syntax_Syntax.sort in
                    union n1 uu____750) acc)
and free_names_and_uvars_comp:
  (FStar_Syntax_Syntax.comp',Prims.unit) FStar_Syntax_Syntax.syntax ->
    free_vars
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.GTotal (t,FStar_Pervasives_Native.None ) ->
        free_names_and_uvars t
    | FStar_Syntax_Syntax.Total (t,FStar_Pervasives_Native.None ) ->
        free_names_and_uvars t
    | FStar_Syntax_Syntax.GTotal (t,FStar_Pervasives_Native.Some u) ->
        let uu____773 = free_univs u in
        let uu____774 = free_names_and_uvars t in union uu____773 uu____774
    | FStar_Syntax_Syntax.Total (t,FStar_Pervasives_Native.Some u) ->
        let uu____782 = free_univs u in
        let uu____783 = free_names_and_uvars t in union uu____782 uu____783
    | FStar_Syntax_Syntax.Comp ct ->
        let us =
          let uu____786 =
            free_names_and_uvars ct.FStar_Syntax_Syntax.result_typ in
          free_names_and_uvars_args ct.FStar_Syntax_Syntax.effect_args
            uu____786 in
        FStar_List.fold_left
          (fun us1  ->
             fun u  -> let uu____792 = free_univs u in union us1 uu____792)
          us ct.FStar_Syntax_Syntax.comp_univs
let names: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set
  = fun t  -> let uu____798 = free_names_and_uvars t in uu____798.free_names
let uvars: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.uvars =
  fun t  -> let uu____806 = free_names_and_uvars t in uu____806.free_uvars
let univs:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.universe_uvar FStar_Util.set
  = fun t  -> let uu____812 = free_names_and_uvars t in uu____812.free_univs
let univnames:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.univ_name FStar_Util.fifo_set
  =
  fun t  ->
    let uu____818 = free_names_and_uvars t in uu____818.free_univ_names
let fvars: FStar_Syntax_Syntax.term -> FStar_Ident.lident FStar_Util.set =
  fun t  -> let uu____825 = free_names_and_uvars t in uu____825.free_fvars
let names_of_binders:
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.bv FStar_Util.set =
  fun bs  ->
    let uu____831 = free_names_and_uvars_binders bs no_free_vars in
    uu____831.free_names