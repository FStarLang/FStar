open Prims
type free_vars_and_fvars =
  (FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set)
let (no_free_vars :
  (FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set)) =
  let uu____42644 = FStar_Syntax_Syntax.new_fv_set ()  in
  ({
     FStar_Syntax_Syntax.free_names = [];
     FStar_Syntax_Syntax.free_uvars = [];
     FStar_Syntax_Syntax.free_univs = [];
     FStar_Syntax_Syntax.free_univ_names = []
   }, uu____42644)
  
let (singleton_fvar :
  FStar_Syntax_Syntax.fv ->
    (FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set))
  =
  fun fv  ->
    let uu____42661 =
      let uu____42664 = FStar_Syntax_Syntax.new_fv_set ()  in
      FStar_Util.set_add
        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v uu____42664
       in
    ((FStar_Pervasives_Native.fst no_free_vars), uu____42661)
  
let (singleton_bv :
  FStar_Syntax_Syntax.bv ->
    (FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set))
  =
  fun x  ->
    ((let uu___393_42686 = FStar_Pervasives_Native.fst no_free_vars  in
      {
        FStar_Syntax_Syntax.free_names = [x];
        FStar_Syntax_Syntax.free_uvars =
          (uu___393_42686.FStar_Syntax_Syntax.free_uvars);
        FStar_Syntax_Syntax.free_univs =
          (uu___393_42686.FStar_Syntax_Syntax.free_univs);
        FStar_Syntax_Syntax.free_univ_names =
          (uu___393_42686.FStar_Syntax_Syntax.free_univ_names)
      }), (FStar_Pervasives_Native.snd no_free_vars))
  
let (singleton_uv :
  FStar_Syntax_Syntax.ctx_uvar ->
    (FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set))
  =
  fun x  ->
    ((let uu___396_42706 = FStar_Pervasives_Native.fst no_free_vars  in
      {
        FStar_Syntax_Syntax.free_names =
          (uu___396_42706.FStar_Syntax_Syntax.free_names);
        FStar_Syntax_Syntax.free_uvars = [x];
        FStar_Syntax_Syntax.free_univs =
          (uu___396_42706.FStar_Syntax_Syntax.free_univs);
        FStar_Syntax_Syntax.free_univ_names =
          (uu___396_42706.FStar_Syntax_Syntax.free_univ_names)
      }), (FStar_Pervasives_Native.snd no_free_vars))
  
let (singleton_univ :
  FStar_Syntax_Syntax.universe_uvar ->
    (FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set))
  =
  fun x  ->
    ((let uu___399_42726 = FStar_Pervasives_Native.fst no_free_vars  in
      {
        FStar_Syntax_Syntax.free_names =
          (uu___399_42726.FStar_Syntax_Syntax.free_names);
        FStar_Syntax_Syntax.free_uvars =
          (uu___399_42726.FStar_Syntax_Syntax.free_uvars);
        FStar_Syntax_Syntax.free_univs = [x];
        FStar_Syntax_Syntax.free_univ_names =
          (uu___399_42726.FStar_Syntax_Syntax.free_univ_names)
      }), (FStar_Pervasives_Native.snd no_free_vars))
  
let (singleton_univ_name :
  FStar_Syntax_Syntax.univ_name ->
    (FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set))
  =
  fun x  ->
    ((let uu___402_42746 = FStar_Pervasives_Native.fst no_free_vars  in
      {
        FStar_Syntax_Syntax.free_names =
          (uu___402_42746.FStar_Syntax_Syntax.free_names);
        FStar_Syntax_Syntax.free_uvars =
          (uu___402_42746.FStar_Syntax_Syntax.free_uvars);
        FStar_Syntax_Syntax.free_univs =
          (uu___402_42746.FStar_Syntax_Syntax.free_univs);
        FStar_Syntax_Syntax.free_univ_names = [x]
      }), (FStar_Pervasives_Native.snd no_free_vars))
  
let (union :
  free_vars_and_fvars ->
    free_vars_and_fvars ->
      (FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set))
  =
  fun f1  ->
    fun f2  ->
      let uu____42768 =
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
       }, uu____42768)
  
let rec (free_univs : FStar_Syntax_Syntax.universe -> free_vars_and_fvars) =
  fun u  ->
    let uu____42799 = FStar_Syntax_Subst.compress_univ u  in
    match uu____42799 with
    | FStar_Syntax_Syntax.U_zero  -> no_free_vars
    | FStar_Syntax_Syntax.U_bvar uu____42800 -> no_free_vars
    | FStar_Syntax_Syntax.U_unknown  -> no_free_vars
    | FStar_Syntax_Syntax.U_name uname -> singleton_univ_name uname
    | FStar_Syntax_Syntax.U_succ u1 -> free_univs u1
    | FStar_Syntax_Syntax.U_max us ->
        FStar_List.fold_left
          (fun out  ->
             fun x  ->
               let uu____42812 = free_univs x  in union out uu____42812)
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
                  fun uu____42953  ->
                    match uu____42953 with
                    | (x,uu____42961) ->
                        let uu____42966 =
                          free_names_and_uvars x.FStar_Syntax_Syntax.sort
                            use_cache
                           in
                        union n1 uu____42966) no_free_vars)
           in
        union from_binders from_body  in
      let t = FStar_Syntax_Subst.compress tm  in
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed uu____42968 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_name x -> singleton_bv x
      | FStar_Syntax_Syntax.Tm_uvar (uv,uu____42994) -> singleton_uv uv
      | FStar_Syntax_Syntax.Tm_type u -> free_univs u
      | FStar_Syntax_Syntax.Tm_bvar uu____43012 -> no_free_vars
      | FStar_Syntax_Syntax.Tm_fvar fv -> singleton_fvar fv
      | FStar_Syntax_Syntax.Tm_constant uu____43014 -> no_free_vars
      | FStar_Syntax_Syntax.Tm_lazy uu____43015 -> no_free_vars
      | FStar_Syntax_Syntax.Tm_unknown  -> no_free_vars
      | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
          let f = free_names_and_uvars t1 use_cache  in
          FStar_List.fold_left
            (fun out  ->
               fun u  ->
                 let uu____43028 = free_univs u  in union out uu____43028) f
            us
      | FStar_Syntax_Syntax.Tm_abs (bs,t1,uu____43031) ->
          let uu____43056 = free_names_and_uvars t1 use_cache  in
          aux_binders bs uu____43056
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____43079 = free_names_and_uvars_comp c use_cache  in
          aux_binders bs uu____43079
      | FStar_Syntax_Syntax.Tm_refine (bv,t1) ->
          let uu____43086 = free_names_and_uvars t1 use_cache  in
          aux_binders [(bv, FStar_Pervasives_Native.None)] uu____43086
      | FStar_Syntax_Syntax.Tm_app (t1,args) ->
          let uu____43127 = free_names_and_uvars t1 use_cache  in
          free_names_and_uvars_args args uu____43127 use_cache
      | FStar_Syntax_Syntax.Tm_match (t1,pats) ->
          let uu____43172 =
            let uu____43191 = free_names_and_uvars t1 use_cache  in
            FStar_List.fold_left
              (fun n1  ->
                 fun uu____43214  ->
                   match uu____43214 with
                   | (p,wopt,t2) ->
                       let n11 =
                         match wopt with
                         | FStar_Pervasives_Native.None  -> no_free_vars
                         | FStar_Pervasives_Native.Some w ->
                             free_names_and_uvars w use_cache
                          in
                       let n2 = free_names_and_uvars t2 use_cache  in
                       let n3 =
                         let uu____43252 = FStar_Syntax_Syntax.pat_bvs p  in
                         FStar_All.pipe_right uu____43252
                           (FStar_List.fold_left
                              (fun n3  ->
                                 fun x  ->
                                   let uu____43262 =
                                     free_names_and_uvars
                                       x.FStar_Syntax_Syntax.sort use_cache
                                      in
                                   union n3 uu____43262) n1)
                          in
                       let uu____43263 = union n11 n2  in
                       union n3 uu____43263) uu____43191
             in
          FStar_All.pipe_right pats uu____43172
      | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,uu____43280) ->
          let u1 = free_names_and_uvars t1 use_cache  in
          let u2 =
            match FStar_Pervasives_Native.fst asc with
            | FStar_Util.Inl t2 -> free_names_and_uvars t2 use_cache
            | FStar_Util.Inr c2 -> free_names_and_uvars_comp c2 use_cache  in
          (match FStar_Pervasives_Native.snd asc with
           | FStar_Pervasives_Native.None  -> union u1 u2
           | FStar_Pervasives_Native.Some tac ->
               let uu____43368 = union u1 u2  in
               let uu____43369 = free_names_and_uvars tac use_cache  in
               union uu____43368 uu____43369)
      | FStar_Syntax_Syntax.Tm_let (lbs,t1) ->
          let uu____43390 =
            let uu____43397 = free_names_and_uvars t1 use_cache  in
            FStar_List.fold_left
              (fun n1  ->
                 fun lb  ->
                   let uu____43403 =
                     let uu____43404 =
                       free_names_and_uvars lb.FStar_Syntax_Syntax.lbtyp
                         use_cache
                        in
                     let uu____43405 =
                       free_names_and_uvars lb.FStar_Syntax_Syntax.lbdef
                         use_cache
                        in
                     union uu____43404 uu____43405  in
                   union n1 uu____43403) uu____43397
             in
          FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs) uu____43390
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
           | FStar_Syntax_Syntax.Meta_monadic (uu____43473,t') ->
               let uu____43479 = free_names_and_uvars t' use_cache  in
               union u1 uu____43479
           | FStar_Syntax_Syntax.Meta_monadic_lift
               (uu____43480,uu____43481,t') ->
               let uu____43487 = free_names_and_uvars t' use_cache  in
               union u1 uu____43487
           | FStar_Syntax_Syntax.Meta_labeled uu____43488 -> u1
           | FStar_Syntax_Syntax.Meta_desugared uu____43497 -> u1
           | FStar_Syntax_Syntax.Meta_named uu____43498 -> u1)

and (free_names_and_uvars :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    Prims.bool -> free_vars_and_fvars)
  =
  fun t  ->
    fun use_cache  ->
      let t1 = FStar_Syntax_Subst.compress t  in
      let uu____43505 = FStar_ST.op_Bang t1.FStar_Syntax_Syntax.vars  in
      match uu____43505 with
      | FStar_Pervasives_Native.Some n1 when
          let uu____43532 = should_invalidate_cache n1 use_cache  in
          Prims.op_Negation uu____43532 ->
          let uu____43534 = FStar_Syntax_Syntax.new_fv_set ()  in
          (n1, uu____43534)
      | uu____43539 ->
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
                fun uu____43643  ->
                  match uu____43643 with
                  | (x,uu____43653) ->
                      let uu____43662 = free_names_and_uvars x use_cache  in
                      union n1 uu____43662) acc)

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
                fun uu____43687  ->
                  match uu____43687 with
                  | (x,uu____43695) ->
                      let uu____43700 =
                        free_names_and_uvars x.FStar_Syntax_Syntax.sort
                          use_cache
                         in
                      union n1 uu____43700) acc)

and (free_names_and_uvars_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    Prims.bool -> free_vars_and_fvars)
  =
  fun c  ->
    fun use_cache  ->
      let uu____43706 = FStar_ST.op_Bang c.FStar_Syntax_Syntax.vars  in
      match uu____43706 with
      | FStar_Pervasives_Native.Some n1 ->
          let uu____43733 = should_invalidate_cache n1 use_cache  in
          if uu____43733
          then
            (FStar_ST.op_Colon_Equals c.FStar_Syntax_Syntax.vars
               FStar_Pervasives_Native.None;
             free_names_and_uvars_comp c use_cache)
          else
            (let uu____43762 = FStar_Syntax_Syntax.new_fv_set ()  in
             (n1, uu____43762))
      | uu____43767 ->
          let n1 =
            match c.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.GTotal (t,FStar_Pervasives_Native.None ) ->
                free_names_and_uvars t use_cache
            | FStar_Syntax_Syntax.Total (t,FStar_Pervasives_Native.None ) ->
                free_names_and_uvars t use_cache
            | FStar_Syntax_Syntax.GTotal (t,FStar_Pervasives_Native.Some u)
                ->
                let uu____43805 = free_univs u  in
                let uu____43806 = free_names_and_uvars t use_cache  in
                union uu____43805 uu____43806
            | FStar_Syntax_Syntax.Total (t,FStar_Pervasives_Native.Some u) ->
                let uu____43815 = free_univs u  in
                let uu____43816 = free_names_and_uvars t use_cache  in
                union uu____43815 uu____43816
            | FStar_Syntax_Syntax.Comp ct ->
                let us =
                  let uu____43825 =
                    free_names_and_uvars ct.FStar_Syntax_Syntax.result_typ
                      use_cache
                     in
                  free_names_and_uvars_args
                    ct.FStar_Syntax_Syntax.effect_args uu____43825 use_cache
                   in
                FStar_List.fold_left
                  (fun us1  ->
                     fun u  ->
                       let uu____43837 = free_univs u  in
                       union us1 uu____43837) us
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
                  let uu____43874 =
                    FStar_Syntax_Unionfind.find
                      u.FStar_Syntax_Syntax.ctx_uvar_head
                     in
                  match uu____43874 with
                  | FStar_Pervasives_Native.Some uu____43878 -> true
                  | uu____43880 -> false)))
           ||
           (FStar_All.pipe_right n1.FStar_Syntax_Syntax.free_univs
              (FStar_Util.for_some
                 (fun u  ->
                    let uu____43891 = FStar_Syntax_Unionfind.univ_find u  in
                    match uu____43891 with
                    | FStar_Pervasives_Native.Some uu____43895 -> true
                    | FStar_Pervasives_Native.None  -> false))))

let (compare_uv :
  FStar_Syntax_Syntax.ctx_uvar -> FStar_Syntax_Syntax.ctx_uvar -> Prims.int)
  =
  fun uv1  ->
    fun uv2  ->
      let uu____43910 =
        FStar_Syntax_Unionfind.uvar_id uv1.FStar_Syntax_Syntax.ctx_uvar_head
         in
      let uu____43912 =
        FStar_Syntax_Unionfind.uvar_id uv2.FStar_Syntax_Syntax.ctx_uvar_head
         in
      uu____43910 - uu____43912
  
let (new_uv_set : unit -> FStar_Syntax_Syntax.uvars) =
  fun uu____43919  -> FStar_Util.new_set compare_uv 
let (compare_universe_uvar :
  FStar_Syntax_Syntax.universe_uvar ->
    FStar_Syntax_Syntax.universe_uvar -> Prims.int)
  =
  fun x  ->
    fun y  ->
      let uu____43932 = FStar_Syntax_Unionfind.univ_uvar_id x  in
      let uu____43934 = FStar_Syntax_Unionfind.univ_uvar_id y  in
      uu____43932 - uu____43934
  
let (new_universe_uvar_set :
  unit -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set) =
  fun uu____43943  -> FStar_Util.new_set compare_universe_uvar 
let (empty : FStar_Syntax_Syntax.bv FStar_Util.set) =
  FStar_Util.new_set FStar_Syntax_Syntax.order_bv 
let (names :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set) =
  fun t  ->
    let uu____43957 =
      let uu____43960 =
        let uu____43961 = free_names_and_uvars t true  in
        FStar_Pervasives_Native.fst uu____43961  in
      uu____43960.FStar_Syntax_Syntax.free_names  in
    FStar_Util.as_set uu____43957 FStar_Syntax_Syntax.order_bv
  
let (uvars :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.ctx_uvar FStar_Util.set) =
  fun t  ->
    let uu____43979 =
      let uu____43982 =
        let uu____43983 = free_names_and_uvars t true  in
        FStar_Pervasives_Native.fst uu____43983  in
      uu____43982.FStar_Syntax_Syntax.free_uvars  in
    FStar_Util.as_set uu____43979 compare_uv
  
let (univs :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.universe_uvar FStar_Util.set)
  =
  fun t  ->
    let uu____44001 =
      let uu____44004 =
        let uu____44005 = free_names_and_uvars t true  in
        FStar_Pervasives_Native.fst uu____44005  in
      uu____44004.FStar_Syntax_Syntax.free_univs  in
    FStar_Util.as_set uu____44001 compare_universe_uvar
  
let (univnames :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.univ_name FStar_Util.set) =
  fun t  ->
    let uu____44023 =
      let uu____44026 =
        let uu____44027 = free_names_and_uvars t true  in
        FStar_Pervasives_Native.fst uu____44027  in
      uu____44026.FStar_Syntax_Syntax.free_univ_names  in
    FStar_Util.as_set uu____44023 FStar_Syntax_Syntax.order_univ_name
  
let (univnames_comp :
  FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.univ_name FStar_Util.set) =
  fun c  ->
    let uu____44045 =
      let uu____44048 =
        let uu____44049 = free_names_and_uvars_comp c true  in
        FStar_Pervasives_Native.fst uu____44049  in
      uu____44048.FStar_Syntax_Syntax.free_univ_names  in
    FStar_Util.as_set uu____44045 FStar_Syntax_Syntax.order_univ_name
  
let (fvars : FStar_Syntax_Syntax.term -> FStar_Ident.lident FStar_Util.set) =
  fun t  ->
    let uu____44067 = free_names_and_uvars t false  in
    FStar_Pervasives_Native.snd uu____44067
  
let (names_of_binders :
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.bv FStar_Util.set) =
  fun bs  ->
    let uu____44085 =
      let uu____44088 =
        let uu____44089 = free_names_and_uvars_binders bs no_free_vars true
           in
        FStar_Pervasives_Native.fst uu____44089  in
      uu____44088.FStar_Syntax_Syntax.free_names  in
    FStar_Util.as_set uu____44085 FStar_Syntax_Syntax.order_bv
  