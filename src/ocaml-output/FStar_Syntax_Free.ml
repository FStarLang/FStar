open Prims
type free_vars_and_fvars =
  (FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set)
let (no_free_vars :
  (FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set)) =
  let uu____42570 = FStar_Syntax_Syntax.new_fv_set ()  in
  ({
     FStar_Syntax_Syntax.free_names = [];
     FStar_Syntax_Syntax.free_uvars = [];
     FStar_Syntax_Syntax.free_univs = [];
     FStar_Syntax_Syntax.free_univ_names = []
   }, uu____42570)
  
let (singleton_fvar :
  FStar_Syntax_Syntax.fv ->
    (FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set))
  =
  fun fv  ->
    let uu____42587 =
      let uu____42590 = FStar_Syntax_Syntax.new_fv_set ()  in
      FStar_Util.set_add
        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v uu____42590
       in
    ((FStar_Pervasives_Native.fst no_free_vars), uu____42587)
  
let (singleton_bv :
  FStar_Syntax_Syntax.bv ->
    (FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set))
  =
  fun x  ->
    ((let uu___393_42612 = FStar_Pervasives_Native.fst no_free_vars  in
      {
        FStar_Syntax_Syntax.free_names = [x];
        FStar_Syntax_Syntax.free_uvars =
          (uu___393_42612.FStar_Syntax_Syntax.free_uvars);
        FStar_Syntax_Syntax.free_univs =
          (uu___393_42612.FStar_Syntax_Syntax.free_univs);
        FStar_Syntax_Syntax.free_univ_names =
          (uu___393_42612.FStar_Syntax_Syntax.free_univ_names)
      }), (FStar_Pervasives_Native.snd no_free_vars))
  
let (singleton_uv :
  FStar_Syntax_Syntax.ctx_uvar ->
    (FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set))
  =
  fun x  ->
    ((let uu___396_42632 = FStar_Pervasives_Native.fst no_free_vars  in
      {
        FStar_Syntax_Syntax.free_names =
          (uu___396_42632.FStar_Syntax_Syntax.free_names);
        FStar_Syntax_Syntax.free_uvars = [x];
        FStar_Syntax_Syntax.free_univs =
          (uu___396_42632.FStar_Syntax_Syntax.free_univs);
        FStar_Syntax_Syntax.free_univ_names =
          (uu___396_42632.FStar_Syntax_Syntax.free_univ_names)
      }), (FStar_Pervasives_Native.snd no_free_vars))
  
let (singleton_univ :
  FStar_Syntax_Syntax.universe_uvar ->
    (FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set))
  =
  fun x  ->
    ((let uu___399_42652 = FStar_Pervasives_Native.fst no_free_vars  in
      {
        FStar_Syntax_Syntax.free_names =
          (uu___399_42652.FStar_Syntax_Syntax.free_names);
        FStar_Syntax_Syntax.free_uvars =
          (uu___399_42652.FStar_Syntax_Syntax.free_uvars);
        FStar_Syntax_Syntax.free_univs = [x];
        FStar_Syntax_Syntax.free_univ_names =
          (uu___399_42652.FStar_Syntax_Syntax.free_univ_names)
      }), (FStar_Pervasives_Native.snd no_free_vars))
  
let (singleton_univ_name :
  FStar_Syntax_Syntax.univ_name ->
    (FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set))
  =
  fun x  ->
    ((let uu___402_42672 = FStar_Pervasives_Native.fst no_free_vars  in
      {
        FStar_Syntax_Syntax.free_names =
          (uu___402_42672.FStar_Syntax_Syntax.free_names);
        FStar_Syntax_Syntax.free_uvars =
          (uu___402_42672.FStar_Syntax_Syntax.free_uvars);
        FStar_Syntax_Syntax.free_univs =
          (uu___402_42672.FStar_Syntax_Syntax.free_univs);
        FStar_Syntax_Syntax.free_univ_names = [x]
      }), (FStar_Pervasives_Native.snd no_free_vars))
  
let (union :
  free_vars_and_fvars ->
    free_vars_and_fvars ->
      (FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set))
  =
  fun f1  ->
    fun f2  ->
      let uu____42694 =
        FStar_Util.set_union (FStar_Pervasives_Native.snd f1)
          (FStar_Pervasives_Native.snd f2)
         in
      ({
         FStar_Syntax_Syntax.free_names =
           (FStar_List.append
              (FStar_Pervasives_Native.fst f1).FStar_Syntax_Syntax.free_names
              (FStar_Pervasives_Native.fst f2).FStar_Syntax_Syntax.free_names);
         FStar_Syntax_Syntax.free_uvars =
           (FStar_List.append
              (FStar_Pervasives_Native.fst f1).FStar_Syntax_Syntax.free_uvars
              (FStar_Pervasives_Native.fst f2).FStar_Syntax_Syntax.free_uvars);
         FStar_Syntax_Syntax.free_univs =
           (FStar_List.append
              (FStar_Pervasives_Native.fst f1).FStar_Syntax_Syntax.free_univs
              (FStar_Pervasives_Native.fst f2).FStar_Syntax_Syntax.free_univs);
         FStar_Syntax_Syntax.free_univ_names =
           (FStar_List.append
              (FStar_Pervasives_Native.fst f1).FStar_Syntax_Syntax.free_univ_names
              (FStar_Pervasives_Native.fst f2).FStar_Syntax_Syntax.free_univ_names)
       }, uu____42694)
  
let rec (free_univs : FStar_Syntax_Syntax.universe -> free_vars_and_fvars) =
  fun u  ->
    let uu____42725 = FStar_Syntax_Subst.compress_univ u  in
    match uu____42725 with
    | FStar_Syntax_Syntax.U_zero  -> no_free_vars
    | FStar_Syntax_Syntax.U_bvar uu____42726 -> no_free_vars
    | FStar_Syntax_Syntax.U_unknown  -> no_free_vars
    | FStar_Syntax_Syntax.U_name uname -> singleton_univ_name uname
    | FStar_Syntax_Syntax.U_succ u1 -> free_univs u1
    | FStar_Syntax_Syntax.U_max us ->
        FStar_List.fold_left
          (fun out  ->
             fun x  ->
               let uu____42738 = free_univs x  in union out uu____42738)
          no_free_vars us
    | FStar_Syntax_Syntax.U_unif u1 -> singleton_univ u1
  
let rec (free_names_and_uvs' :
  FStar_Syntax_Syntax.term -> Prims.bool -> free_vars_and_fvars) =
  fun tm  ->
    fun use_cache  ->
      let aux_binders bs from_body =
        let from_binders =
          FStar_All.pipe_right bs
            (FStar_List.fold_left
               (fun n1  ->
                  fun uu____42879  ->
                    match uu____42879 with
                    | (x,uu____42887) ->
                        let uu____42892 =
                          free_names_and_uvars x.FStar_Syntax_Syntax.sort
                            use_cache
                           in
                        union n1 uu____42892) no_free_vars)
           in
        union from_binders from_body  in
      let t = FStar_Syntax_Subst.compress tm  in
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed uu____42894 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_name x -> singleton_bv x
      | FStar_Syntax_Syntax.Tm_uvar (uv,uu____42920) -> singleton_uv uv
      | FStar_Syntax_Syntax.Tm_type u -> free_univs u
      | FStar_Syntax_Syntax.Tm_bvar uu____42938 -> no_free_vars
      | FStar_Syntax_Syntax.Tm_fvar fv -> singleton_fvar fv
      | FStar_Syntax_Syntax.Tm_constant uu____42940 -> no_free_vars
      | FStar_Syntax_Syntax.Tm_lazy uu____42941 -> no_free_vars
      | FStar_Syntax_Syntax.Tm_unknown  -> no_free_vars
      | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
          let f = free_names_and_uvars t1 use_cache  in
          FStar_List.fold_left
            (fun out  ->
               fun u  ->
                 let uu____42954 = free_univs u  in union out uu____42954) f
            us
      | FStar_Syntax_Syntax.Tm_abs (bs,t1,uu____42957) ->
          let uu____42982 = free_names_and_uvars t1 use_cache  in
          aux_binders bs uu____42982
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____43005 = free_names_and_uvars_comp c use_cache  in
          aux_binders bs uu____43005
      | FStar_Syntax_Syntax.Tm_refine (bv,t1) ->
          let uu____43012 = free_names_and_uvars t1 use_cache  in
          aux_binders [(bv, FStar_Pervasives_Native.None)] uu____43012
      | FStar_Syntax_Syntax.Tm_app (t1,args) ->
          let uu____43053 = free_names_and_uvars t1 use_cache  in
          free_names_and_uvars_args args uu____43053 use_cache
      | FStar_Syntax_Syntax.Tm_match (t1,pats) ->
          let uu____43098 =
            let uu____43117 = free_names_and_uvars t1 use_cache  in
            FStar_List.fold_left
              (fun n1  ->
                 fun uu____43140  ->
                   match uu____43140 with
                   | (p,wopt,t2) ->
                       let n11 =
                         match wopt with
                         | FStar_Pervasives_Native.None  -> no_free_vars
                         | FStar_Pervasives_Native.Some w ->
                             free_names_and_uvars w use_cache
                          in
                       let n2 = free_names_and_uvars t2 use_cache  in
                       let n3 =
                         let uu____43178 = FStar_Syntax_Syntax.pat_bvs p  in
                         FStar_All.pipe_right uu____43178
                           (FStar_List.fold_left
                              (fun n3  ->
                                 fun x  ->
                                   let uu____43188 =
                                     free_names_and_uvars
                                       x.FStar_Syntax_Syntax.sort use_cache
                                      in
                                   union n3 uu____43188) n1)
                          in
                       let uu____43189 = union n11 n2  in
                       union n3 uu____43189) uu____43117
             in
          FStar_All.pipe_right pats uu____43098
      | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,uu____43206) ->
          let u1 = free_names_and_uvars t1 use_cache  in
          let u2 =
            match FStar_Pervasives_Native.fst asc with
            | FStar_Util.Inl t2 -> free_names_and_uvars t2 use_cache
            | FStar_Util.Inr c2 -> free_names_and_uvars_comp c2 use_cache  in
          (match FStar_Pervasives_Native.snd asc with
           | FStar_Pervasives_Native.None  -> union u1 u2
           | FStar_Pervasives_Native.Some tac ->
               let uu____43294 = union u1 u2  in
               let uu____43295 = free_names_and_uvars tac use_cache  in
               union uu____43294 uu____43295)
      | FStar_Syntax_Syntax.Tm_let (lbs,t1) ->
          let uu____43316 =
            let uu____43323 = free_names_and_uvars t1 use_cache  in
            FStar_List.fold_left
              (fun n1  ->
                 fun lb  ->
                   let uu____43329 =
                     let uu____43330 =
                       free_names_and_uvars lb.FStar_Syntax_Syntax.lbtyp
                         use_cache
                        in
                     let uu____43331 =
                       free_names_and_uvars lb.FStar_Syntax_Syntax.lbdef
                         use_cache
                        in
                     union uu____43330 uu____43331  in
                   union n1 uu____43329) uu____43323
             in
          FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs) uu____43316
      | FStar_Syntax_Syntax.Tm_quoted (tm1,qi) ->
          (match qi.FStar_Syntax_Syntax.qkind with
           | FStar_Syntax_Syntax.Quote_static  -> no_free_vars
           | FStar_Syntax_Syntax.Quote_dynamic  ->
               free_names_and_uvars tm1 use_cache)
      | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
          let u1 = free_names_and_uvars t1 use_cache  in
          (match m with
           | FStar_Syntax_Syntax.Meta_pattern args ->
               FStar_List.fold_right
                 (fun a  ->
                    fun acc  -> free_names_and_uvars_args a acc use_cache)
                 args u1
           | FStar_Syntax_Syntax.Meta_monadic (uu____43399,t') ->
               let uu____43405 = free_names_and_uvars t' use_cache  in
               union u1 uu____43405
           | FStar_Syntax_Syntax.Meta_monadic_lift
               (uu____43406,uu____43407,t') ->
               let uu____43413 = free_names_and_uvars t' use_cache  in
               union u1 uu____43413
           | FStar_Syntax_Syntax.Meta_labeled uu____43414 -> u1
           | FStar_Syntax_Syntax.Meta_desugared uu____43423 -> u1
           | FStar_Syntax_Syntax.Meta_named uu____43424 -> u1)

and (free_names_and_uvars :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    Prims.bool -> free_vars_and_fvars)
  =
  fun t  ->
    fun use_cache  ->
      let t1 = FStar_Syntax_Subst.compress t  in
      let uu____43431 = FStar_ST.op_Bang t1.FStar_Syntax_Syntax.vars  in
      match uu____43431 with
      | FStar_Pervasives_Native.Some n1 when
          let uu____43458 = should_invalidate_cache n1 use_cache  in
          Prims.op_Negation uu____43458 ->
          let uu____43460 = FStar_Syntax_Syntax.new_fv_set ()  in
          (n1, uu____43460)
      | uu____43465 ->
          (FStar_ST.op_Colon_Equals t1.FStar_Syntax_Syntax.vars
             FStar_Pervasives_Native.None;
           (let n1 = free_names_and_uvs' t1 use_cache  in
            FStar_ST.op_Colon_Equals t1.FStar_Syntax_Syntax.vars
              (FStar_Pervasives_Native.Some (FStar_Pervasives_Native.fst n1));
            n1))

and (free_names_and_uvars_args :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
    FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
    Prims.list ->
    (FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set) ->
      Prims.bool ->
        (FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set))
  =
  fun args  ->
    fun acc  ->
      fun use_cache  ->
        FStar_All.pipe_right args
          (FStar_List.fold_left
             (fun n1  ->
                fun uu____43569  ->
                  match uu____43569 with
                  | (x,uu____43579) ->
                      let uu____43588 = free_names_and_uvars x use_cache  in
                      union n1 uu____43588) acc)

and (free_names_and_uvars_binders :
  FStar_Syntax_Syntax.binders ->
    free_vars_and_fvars -> Prims.bool -> free_vars_and_fvars)
  =
  fun bs  ->
    fun acc  ->
      fun use_cache  ->
        FStar_All.pipe_right bs
          (FStar_List.fold_left
             (fun n1  ->
                fun uu____43613  ->
                  match uu____43613 with
                  | (x,uu____43621) ->
                      let uu____43626 =
                        free_names_and_uvars x.FStar_Syntax_Syntax.sort
                          use_cache
                         in
                      union n1 uu____43626) acc)

and (free_names_and_uvars_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    Prims.bool -> free_vars_and_fvars)
  =
  fun c  ->
    fun use_cache  ->
      let uu____43632 = FStar_ST.op_Bang c.FStar_Syntax_Syntax.vars  in
      match uu____43632 with
      | FStar_Pervasives_Native.Some n1 ->
          let uu____43659 = should_invalidate_cache n1 use_cache  in
          if uu____43659
          then
            (FStar_ST.op_Colon_Equals c.FStar_Syntax_Syntax.vars
               FStar_Pervasives_Native.None;
             free_names_and_uvars_comp c use_cache)
          else
            (let uu____43688 = FStar_Syntax_Syntax.new_fv_set ()  in
             (n1, uu____43688))
      | uu____43693 ->
          let n1 =
            match c.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.GTotal (t,FStar_Pervasives_Native.None ) ->
                free_names_and_uvars t use_cache
            | FStar_Syntax_Syntax.Total (t,FStar_Pervasives_Native.None ) ->
                free_names_and_uvars t use_cache
            | FStar_Syntax_Syntax.GTotal (t,FStar_Pervasives_Native.Some u)
                ->
                let uu____43731 = free_univs u  in
                let uu____43732 = free_names_and_uvars t use_cache  in
                union uu____43731 uu____43732
            | FStar_Syntax_Syntax.Total (t,FStar_Pervasives_Native.Some u) ->
                let uu____43741 = free_univs u  in
                let uu____43742 = free_names_and_uvars t use_cache  in
                union uu____43741 uu____43742
            | FStar_Syntax_Syntax.Comp ct ->
                let us =
                  let uu____43751 =
                    free_names_and_uvars ct.FStar_Syntax_Syntax.result_typ
                      use_cache
                     in
                  free_names_and_uvars_args
                    ct.FStar_Syntax_Syntax.effect_args uu____43751 use_cache
                   in
                FStar_List.fold_left
                  (fun us1  ->
                     fun u  ->
                       let uu____43763 = free_univs u  in
                       union us1 uu____43763) us
                  ct.FStar_Syntax_Syntax.comp_univs
             in
          (FStar_ST.op_Colon_Equals c.FStar_Syntax_Syntax.vars
             (FStar_Pervasives_Native.Some (FStar_Pervasives_Native.fst n1));
           n1)

and (should_invalidate_cache :
  FStar_Syntax_Syntax.free_vars -> Prims.bool -> Prims.bool) =
  fun n1  ->
    fun use_cache  ->
      (Prims.op_Negation use_cache) ||
        ((FStar_All.pipe_right n1.FStar_Syntax_Syntax.free_uvars
            (FStar_Util.for_some
               (fun u  ->
                  let uu____43800 =
                    FStar_Syntax_Unionfind.find
                      u.FStar_Syntax_Syntax.ctx_uvar_head
                     in
                  match uu____43800 with
                  | FStar_Pervasives_Native.Some uu____43804 -> true
                  | uu____43806 -> false)))
           ||
           (FStar_All.pipe_right n1.FStar_Syntax_Syntax.free_univs
              (FStar_Util.for_some
                 (fun u  ->
                    let uu____43817 = FStar_Syntax_Unionfind.univ_find u  in
                    match uu____43817 with
                    | FStar_Pervasives_Native.Some uu____43821 -> true
                    | FStar_Pervasives_Native.None  -> false))))

let (compare_uv :
  FStar_Syntax_Syntax.ctx_uvar -> FStar_Syntax_Syntax.ctx_uvar -> Prims.int)
  =
  fun uv1  ->
    fun uv2  ->
      let uu____43836 =
        FStar_Syntax_Unionfind.uvar_id uv1.FStar_Syntax_Syntax.ctx_uvar_head
         in
      let uu____43838 =
        FStar_Syntax_Unionfind.uvar_id uv2.FStar_Syntax_Syntax.ctx_uvar_head
         in
      uu____43836 - uu____43838
  
let (new_uv_set : unit -> FStar_Syntax_Syntax.uvars) =
  fun uu____43845  -> FStar_Util.new_set compare_uv 
let (compare_universe_uvar :
  FStar_Syntax_Syntax.universe_uvar ->
    FStar_Syntax_Syntax.universe_uvar -> Prims.int)
  =
  fun x  ->
    fun y  ->
      let uu____43858 = FStar_Syntax_Unionfind.univ_uvar_id x  in
      let uu____43860 = FStar_Syntax_Unionfind.univ_uvar_id y  in
      uu____43858 - uu____43860
  
let (new_universe_uvar_set :
  unit -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set) =
  fun uu____43869  -> FStar_Util.new_set compare_universe_uvar 
let (empty : FStar_Syntax_Syntax.bv FStar_Util.set) =
  FStar_Util.new_set FStar_Syntax_Syntax.order_bv 
let (names :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set) =
  fun t  ->
    let uu____43883 =
      let uu____43886 =
        let uu____43887 = free_names_and_uvars t true  in
        FStar_Pervasives_Native.fst uu____43887  in
      uu____43886.FStar_Syntax_Syntax.free_names  in
    FStar_Util.as_set uu____43883 FStar_Syntax_Syntax.order_bv
  
let (uvars :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.ctx_uvar FStar_Util.set) =
  fun t  ->
    let uu____43905 =
      let uu____43908 =
        let uu____43909 = free_names_and_uvars t true  in
        FStar_Pervasives_Native.fst uu____43909  in
      uu____43908.FStar_Syntax_Syntax.free_uvars  in
    FStar_Util.as_set uu____43905 compare_uv
  
let (univs :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.universe_uvar FStar_Util.set)
  =
  fun t  ->
    let uu____43927 =
      let uu____43930 =
        let uu____43931 = free_names_and_uvars t true  in
        FStar_Pervasives_Native.fst uu____43931  in
      uu____43930.FStar_Syntax_Syntax.free_univs  in
    FStar_Util.as_set uu____43927 compare_universe_uvar
  
let (univnames :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.univ_name FStar_Util.set) =
  fun t  ->
    let uu____43949 =
      let uu____43952 =
        let uu____43953 = free_names_and_uvars t true  in
        FStar_Pervasives_Native.fst uu____43953  in
      uu____43952.FStar_Syntax_Syntax.free_univ_names  in
    FStar_Util.as_set uu____43949 FStar_Syntax_Syntax.order_univ_name
  
let (univnames_comp :
  FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.univ_name FStar_Util.set) =
  fun c  ->
    let uu____43971 =
      let uu____43974 =
        let uu____43975 = free_names_and_uvars_comp c true  in
        FStar_Pervasives_Native.fst uu____43975  in
      uu____43974.FStar_Syntax_Syntax.free_univ_names  in
    FStar_Util.as_set uu____43971 FStar_Syntax_Syntax.order_univ_name
  
let (fvars : FStar_Syntax_Syntax.term -> FStar_Ident.lident FStar_Util.set) =
  fun t  ->
    let uu____43993 = free_names_and_uvars t false  in
    FStar_Pervasives_Native.snd uu____43993
  
let (names_of_binders :
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.bv FStar_Util.set) =
  fun bs  ->
    let uu____44011 =
      let uu____44014 =
        let uu____44015 = free_names_and_uvars_binders bs no_free_vars true
           in
        FStar_Pervasives_Native.fst uu____44015  in
      uu____44014.FStar_Syntax_Syntax.free_names  in
    FStar_Util.as_set uu____44011 FStar_Syntax_Syntax.order_bv
  