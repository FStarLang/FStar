open Prims
let (max : Prims.int -> Prims.int -> Prims.int) =
  fun a  -> fun b  -> if a > b then a else b 
let map_rev : 'a 'b . ('a -> 'b) -> 'a Prims.list -> 'b Prims.list =
  fun f  ->
    fun l  ->
      let rec aux l1 acc =
        match l1 with
        | [] -> acc
        | x::xs ->
            let uu____80 = let uu____83 = f x  in uu____83 :: acc  in
            aux xs uu____80
         in
      aux l []
  
let map_rev_append :
  'a 'b . ('a -> 'b) -> 'a Prims.list -> 'b Prims.list -> 'b Prims.list =
  fun f  ->
    fun l1  ->
      fun l2  ->
        let rec aux l acc =
          match l with
          | [] -> l2
          | x::xs ->
              let uu____154 = let uu____157 = f x  in uu____157 :: acc  in
              aux xs uu____154
           in
        aux l1 l2
  
let rec map_append :
  'a 'b . ('a -> 'b) -> 'a Prims.list -> 'b Prims.list -> 'b Prims.list =
  fun f  ->
    fun l1  ->
      fun l2  ->
        match l1 with
        | [] -> l2
        | x::xs ->
            let uu____207 = f x  in
            let uu____208 = map_append f xs l2  in uu____207 :: uu____208
  
let rec drop : 'a . ('a -> Prims.bool) -> 'a Prims.list -> 'a Prims.list =
  fun p  ->
    fun l  ->
      match l with
      | [] -> []
      | x::xs ->
          let uu____247 = p x  in if uu____247 then x :: xs else drop p xs
  
let fmap_opt :
  'a 'b .
    ('a -> 'b) ->
      'a FStar_Pervasives_Native.option -> 'b FStar_Pervasives_Native.option
  =
  fun f  ->
    fun x  ->
      FStar_Util.bind_opt x
        (fun x1  ->
           let uu____289 = f x1  in FStar_Pervasives_Native.Some uu____289)
  
let drop_until : 'a . ('a -> Prims.bool) -> 'a Prims.list -> 'a Prims.list =
  fun f  ->
    fun l  ->
      let rec aux l1 =
        match l1 with
        | [] -> []
        | x::xs -> let uu____339 = f x  in if uu____339 then l1 else aux xs
         in
      aux l
  
let (trim : Prims.bool Prims.list -> Prims.bool Prims.list) =
  fun l  ->
    let uu____364 = drop_until FStar_Pervasives.id (FStar_List.rev l)  in
    FStar_List.rev uu____364
  
let (implies : Prims.bool -> Prims.bool -> Prims.bool) =
  fun b1  ->
    fun b2  ->
      match (b1, b2) with | (false ,uu____391) -> true | (true ,b21) -> b21
  
let (let_rec_arity :
  FStar_Syntax_Syntax.letbinding -> (Prims.int * Prims.bool Prims.list)) =
  fun b  ->
    let uu____424 = FStar_Syntax_Util.let_rec_arity b  in
    match uu____424 with
    | (ar,maybe_lst) ->
        (match maybe_lst with
         | FStar_Pervasives_Native.None  ->
             let uu____468 =
               FStar_Common.tabulate ar (fun uu____474  -> true)  in
             (ar, uu____468)
         | FStar_Pervasives_Native.Some lst -> (ar, lst))
  
let (debug_term : FStar_Syntax_Syntax.term -> unit) =
  fun t  ->
    let uu____498 = FStar_Syntax_Print.term_to_string t  in
    FStar_Util.print1 "%s\n" uu____498
  
let (debug_sigmap : FStar_Syntax_Syntax.sigelt FStar_Util.smap -> unit) =
  fun m  ->
    FStar_Util.smap_fold m
      (fun k  ->
         fun v  ->
           fun u  ->
             let uu____519 = FStar_Syntax_Print.sigelt_to_string_short v  in
             FStar_Util.print2 "%s -> %%s\n" k uu____519) ()
  
type config =
  {
  core_cfg: FStar_TypeChecker_Cfg.cfg ;
  fv_cache: FStar_TypeChecker_NBETerm.t FStar_Util.smap }
let (__proj__Mkconfig__item__core_cfg : config -> FStar_TypeChecker_Cfg.cfg)
  =
  fun projectee  ->
    match projectee with | { core_cfg; fv_cache;_} -> core_cfg
  
let (__proj__Mkconfig__item__fv_cache :
  config -> FStar_TypeChecker_NBETerm.t FStar_Util.smap) =
  fun projectee  ->
    match projectee with | { core_cfg; fv_cache;_} -> fv_cache
  
let (new_config : FStar_TypeChecker_Cfg.cfg -> config) =
  fun cfg  ->
    let uu____564 = FStar_Util.smap_create (Prims.of_int (51))  in
    { core_cfg = cfg; fv_cache = uu____564 }
  
let (reifying_false : config -> config) =
  fun cfg  ->
    if (cfg.core_cfg).FStar_TypeChecker_Cfg.reifying
    then
      new_config
        (let uu___92_577 = cfg.core_cfg  in
         {
           FStar_TypeChecker_Cfg.steps =
             (uu___92_577.FStar_TypeChecker_Cfg.steps);
           FStar_TypeChecker_Cfg.tcenv =
             (uu___92_577.FStar_TypeChecker_Cfg.tcenv);
           FStar_TypeChecker_Cfg.debug =
             (uu___92_577.FStar_TypeChecker_Cfg.debug);
           FStar_TypeChecker_Cfg.delta_level =
             (uu___92_577.FStar_TypeChecker_Cfg.delta_level);
           FStar_TypeChecker_Cfg.primitive_steps =
             (uu___92_577.FStar_TypeChecker_Cfg.primitive_steps);
           FStar_TypeChecker_Cfg.strong =
             (uu___92_577.FStar_TypeChecker_Cfg.strong);
           FStar_TypeChecker_Cfg.memoize_lazy =
             (uu___92_577.FStar_TypeChecker_Cfg.memoize_lazy);
           FStar_TypeChecker_Cfg.normalize_pure_lets =
             (uu___92_577.FStar_TypeChecker_Cfg.normalize_pure_lets);
           FStar_TypeChecker_Cfg.reifying = false
         })
    else cfg
  
let (reifying_true : config -> config) =
  fun cfg  ->
    if Prims.op_Negation (cfg.core_cfg).FStar_TypeChecker_Cfg.reifying
    then
      new_config
        (let uu___96_590 = cfg.core_cfg  in
         {
           FStar_TypeChecker_Cfg.steps =
             (uu___96_590.FStar_TypeChecker_Cfg.steps);
           FStar_TypeChecker_Cfg.tcenv =
             (uu___96_590.FStar_TypeChecker_Cfg.tcenv);
           FStar_TypeChecker_Cfg.debug =
             (uu___96_590.FStar_TypeChecker_Cfg.debug);
           FStar_TypeChecker_Cfg.delta_level =
             (uu___96_590.FStar_TypeChecker_Cfg.delta_level);
           FStar_TypeChecker_Cfg.primitive_steps =
             (uu___96_590.FStar_TypeChecker_Cfg.primitive_steps);
           FStar_TypeChecker_Cfg.strong =
             (uu___96_590.FStar_TypeChecker_Cfg.strong);
           FStar_TypeChecker_Cfg.memoize_lazy =
             (uu___96_590.FStar_TypeChecker_Cfg.memoize_lazy);
           FStar_TypeChecker_Cfg.normalize_pure_lets =
             (uu___96_590.FStar_TypeChecker_Cfg.normalize_pure_lets);
           FStar_TypeChecker_Cfg.reifying = true
         })
    else cfg
  
let (zeta_false : config -> config) =
  fun cfg  ->
    let cfg_core = cfg.core_cfg  in
    if (cfg_core.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta
    then
      let cfg_core' =
        let uu___101_603 = cfg_core  in
        {
          FStar_TypeChecker_Cfg.steps =
            (let uu___103_606 = cfg_core.FStar_TypeChecker_Cfg.steps  in
             {
               FStar_TypeChecker_Cfg.beta =
                 (uu___103_606.FStar_TypeChecker_Cfg.beta);
               FStar_TypeChecker_Cfg.iota =
                 (uu___103_606.FStar_TypeChecker_Cfg.iota);
               FStar_TypeChecker_Cfg.zeta = false;
               FStar_TypeChecker_Cfg.zeta_full =
                 (uu___103_606.FStar_TypeChecker_Cfg.zeta_full);
               FStar_TypeChecker_Cfg.weak =
                 (uu___103_606.FStar_TypeChecker_Cfg.weak);
               FStar_TypeChecker_Cfg.hnf =
                 (uu___103_606.FStar_TypeChecker_Cfg.hnf);
               FStar_TypeChecker_Cfg.primops =
                 (uu___103_606.FStar_TypeChecker_Cfg.primops);
               FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                 (uu___103_606.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
               FStar_TypeChecker_Cfg.unfold_until =
                 (uu___103_606.FStar_TypeChecker_Cfg.unfold_until);
               FStar_TypeChecker_Cfg.unfold_only =
                 (uu___103_606.FStar_TypeChecker_Cfg.unfold_only);
               FStar_TypeChecker_Cfg.unfold_fully =
                 (uu___103_606.FStar_TypeChecker_Cfg.unfold_fully);
               FStar_TypeChecker_Cfg.unfold_attr =
                 (uu___103_606.FStar_TypeChecker_Cfg.unfold_attr);
               FStar_TypeChecker_Cfg.unfold_tac =
                 (uu___103_606.FStar_TypeChecker_Cfg.unfold_tac);
               FStar_TypeChecker_Cfg.pure_subterms_within_computations =
                 (uu___103_606.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
               FStar_TypeChecker_Cfg.simplify =
                 (uu___103_606.FStar_TypeChecker_Cfg.simplify);
               FStar_TypeChecker_Cfg.erase_universes =
                 (uu___103_606.FStar_TypeChecker_Cfg.erase_universes);
               FStar_TypeChecker_Cfg.allow_unbound_universes =
                 (uu___103_606.FStar_TypeChecker_Cfg.allow_unbound_universes);
               FStar_TypeChecker_Cfg.reify_ =
                 (uu___103_606.FStar_TypeChecker_Cfg.reify_);
               FStar_TypeChecker_Cfg.compress_uvars =
                 (uu___103_606.FStar_TypeChecker_Cfg.compress_uvars);
               FStar_TypeChecker_Cfg.no_full_norm =
                 (uu___103_606.FStar_TypeChecker_Cfg.no_full_norm);
               FStar_TypeChecker_Cfg.check_no_uvars =
                 (uu___103_606.FStar_TypeChecker_Cfg.check_no_uvars);
               FStar_TypeChecker_Cfg.unmeta =
                 (uu___103_606.FStar_TypeChecker_Cfg.unmeta);
               FStar_TypeChecker_Cfg.unascribe =
                 (uu___103_606.FStar_TypeChecker_Cfg.unascribe);
               FStar_TypeChecker_Cfg.in_full_norm_request =
                 (uu___103_606.FStar_TypeChecker_Cfg.in_full_norm_request);
               FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                 (uu___103_606.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
               FStar_TypeChecker_Cfg.nbe_step =
                 (uu___103_606.FStar_TypeChecker_Cfg.nbe_step);
               FStar_TypeChecker_Cfg.for_extraction =
                 (uu___103_606.FStar_TypeChecker_Cfg.for_extraction)
             });
          FStar_TypeChecker_Cfg.tcenv =
            (uu___101_603.FStar_TypeChecker_Cfg.tcenv);
          FStar_TypeChecker_Cfg.debug =
            (uu___101_603.FStar_TypeChecker_Cfg.debug);
          FStar_TypeChecker_Cfg.delta_level =
            (uu___101_603.FStar_TypeChecker_Cfg.delta_level);
          FStar_TypeChecker_Cfg.primitive_steps =
            (uu___101_603.FStar_TypeChecker_Cfg.primitive_steps);
          FStar_TypeChecker_Cfg.strong =
            (uu___101_603.FStar_TypeChecker_Cfg.strong);
          FStar_TypeChecker_Cfg.memoize_lazy =
            (uu___101_603.FStar_TypeChecker_Cfg.memoize_lazy);
          FStar_TypeChecker_Cfg.normalize_pure_lets =
            (uu___101_603.FStar_TypeChecker_Cfg.normalize_pure_lets);
          FStar_TypeChecker_Cfg.reifying =
            (uu___101_603.FStar_TypeChecker_Cfg.reifying)
        }  in
      new_config cfg_core'
    else cfg
  
let (cache_add :
  config -> FStar_Syntax_Syntax.fv -> FStar_TypeChecker_NBETerm.t -> unit) =
  fun cfg  ->
    fun fv  ->
      fun v  ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
        let uu____627 = FStar_Ident.string_of_lid lid  in
        FStar_Util.smap_add cfg.fv_cache uu____627 v
  
let (try_in_cache :
  config ->
    FStar_Syntax_Syntax.fv ->
      FStar_TypeChecker_NBETerm.t FStar_Pervasives_Native.option)
  =
  fun cfg  ->
    fun fv  ->
      let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
      let uu____645 = FStar_Ident.string_of_lid lid  in
      FStar_Util.smap_try_find cfg.fv_cache uu____645
  
let (debug : config -> (unit -> unit) -> unit) =
  fun cfg  -> fun f  -> FStar_TypeChecker_Cfg.log_nbe cfg.core_cfg f 
let rec (unlazy_unmeta :
  FStar_TypeChecker_NBETerm.t -> FStar_TypeChecker_NBETerm.t) =
  fun t  ->
    match t.FStar_TypeChecker_NBETerm.nbe_t with
    | FStar_TypeChecker_NBETerm.Lazy (uu____669,t1) ->
        let uu____691 = FStar_Thunk.force t1  in unlazy_unmeta uu____691
    | FStar_TypeChecker_NBETerm.Meta (t0,m) ->
        let uu____698 = FStar_Thunk.force m  in
        (match uu____698 with
         | FStar_Syntax_Syntax.Meta_monadic (uu____699,uu____700) -> t
         | FStar_Syntax_Syntax.Meta_monadic_lift
             (uu____705,uu____706,uu____707) -> t
         | uu____712 -> unlazy_unmeta t0)
    | uu____713 -> t
  
let (pickBranch :
  config ->
    FStar_TypeChecker_NBETerm.t ->
      FStar_Syntax_Syntax.branch Prims.list ->
        (FStar_Syntax_Syntax.term * FStar_TypeChecker_NBETerm.t Prims.list)
          FStar_Pervasives_Native.option)
  =
  fun cfg  ->
    fun scrut  ->
      fun branches  ->
        let all_branches = branches  in
        let rec pickBranch_aux scrut1 branches1 branches0 =
          let rec matches_pat scrutinee0 p =
            debug cfg
              (fun uu____822  ->
                 let uu____823 =
                   FStar_TypeChecker_NBETerm.t_to_string scrutinee0  in
                 let uu____825 = FStar_Syntax_Print.pat_to_string p  in
                 FStar_Util.print2 "matches_pat (%s, %s)\n" uu____823
                   uu____825);
            (let scrutinee = unlazy_unmeta scrutinee0  in
             let r =
               match p.FStar_Syntax_Syntax.v with
               | FStar_Syntax_Syntax.Pat_var bv ->
                   FStar_Util.Inl [scrutinee0]
               | FStar_Syntax_Syntax.Pat_wild bv ->
                   FStar_Util.Inl [scrutinee0]
               | FStar_Syntax_Syntax.Pat_dot_term uu____852 ->
                   FStar_Util.Inl []
               | FStar_Syntax_Syntax.Pat_constant s ->
                   let matches_const c s1 =
                     debug cfg
                       (fun uu____879  ->
                          let uu____880 =
                            FStar_TypeChecker_NBETerm.t_to_string c  in
                          let uu____882 =
                            FStar_Syntax_Print.const_to_string s1  in
                          FStar_Util.print2
                            "Testing term %s against pattern %s\n" uu____880
                            uu____882);
                     (match c.FStar_TypeChecker_NBETerm.nbe_t with
                      | FStar_TypeChecker_NBETerm.Constant
                          (FStar_TypeChecker_NBETerm.Unit ) ->
                          s1 = FStar_Const.Const_unit
                      | FStar_TypeChecker_NBETerm.Constant
                          (FStar_TypeChecker_NBETerm.Bool b) ->
                          (match s1 with
                           | FStar_Const.Const_bool p1 -> b = p1
                           | uu____892 -> false)
                      | FStar_TypeChecker_NBETerm.Constant
                          (FStar_TypeChecker_NBETerm.Int i) ->
                          (match s1 with
                           | FStar_Const.Const_int
                               (p1,FStar_Pervasives_Native.None ) ->
                               let uu____909 =
                                 FStar_BigInt.big_int_of_string p1  in
                               i = uu____909
                           | uu____910 -> false)
                      | FStar_TypeChecker_NBETerm.Constant
                          (FStar_TypeChecker_NBETerm.String (st,uu____913))
                          ->
                          (match s1 with
                           | FStar_Const.Const_string (p1,uu____918) ->
                               st = p1
                           | uu____922 -> false)
                      | FStar_TypeChecker_NBETerm.Constant
                          (FStar_TypeChecker_NBETerm.Char c1) ->
                          (match s1 with
                           | FStar_Const.Const_char p1 -> c1 = p1
                           | uu____930 -> false)
                      | uu____932 -> false)
                      in
                   let uu____934 = matches_const scrutinee s  in
                   if uu____934
                   then FStar_Util.Inl []
                   else FStar_Util.Inr false
               | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                   let rec matches_args out a p1 =
                     match (a, p1) with
                     | ([],[]) -> FStar_Util.Inl out
                     | ((t,uu____1072)::rest_a,(p2,uu____1075)::rest_p) ->
                         let uu____1114 = matches_pat t p2  in
                         (match uu____1114 with
                          | FStar_Util.Inl s ->
                              matches_args (FStar_List.append out s) rest_a
                                rest_p
                          | m -> m)
                     | uu____1143 -> FStar_Util.Inr false  in
                   (match scrutinee.FStar_TypeChecker_NBETerm.nbe_t with
                    | FStar_TypeChecker_NBETerm.Construct (fv',_us,args_rev)
                        ->
                        let uu____1191 = FStar_Syntax_Syntax.fv_eq fv fv'  in
                        if uu____1191
                        then
                          matches_args [] (FStar_List.rev args_rev) arg_pats
                        else FStar_Util.Inr false
                    | uu____1211 -> FStar_Util.Inr true)
                in
             let res_to_string uu___0_1229 =
               match uu___0_1229 with
               | FStar_Util.Inr b ->
                   let uu____1243 = FStar_Util.string_of_bool b  in
                   Prims.op_Hat "Inr " uu____1243
               | FStar_Util.Inl bs ->
                   let uu____1252 =
                     FStar_Util.string_of_int (FStar_List.length bs)  in
                   Prims.op_Hat "Inl " uu____1252
                in
             debug cfg
               (fun uu____1260  ->
                  let uu____1261 =
                    FStar_TypeChecker_NBETerm.t_to_string scrutinee  in
                  let uu____1263 = FStar_Syntax_Print.pat_to_string p  in
                  let uu____1265 = res_to_string r  in
                  FStar_Util.print3 "matches_pat (%s, %s) = %s\n" uu____1261
                    uu____1263 uu____1265);
             r)
             in
          match branches1 with
          | [] -> FStar_Pervasives_Native.None
          | (p,_wopt,e)::branches2 ->
              let uu____1304 = matches_pat scrut1 p  in
              (match uu____1304 with
               | FStar_Util.Inl matches ->
                   (debug cfg
                      (fun uu____1329  ->
                         let uu____1330 = FStar_Syntax_Print.pat_to_string p
                            in
                         FStar_Util.print1 "Pattern %s matches\n" uu____1330);
                    FStar_Pervasives_Native.Some (e, matches))
               | FStar_Util.Inr (false ) ->
                   pickBranch_aux scrut1 branches2 branches0
               | FStar_Util.Inr (true ) -> FStar_Pervasives_Native.None)
           in
        pickBranch_aux scrut branches branches
  
let (should_reduce_recursive_definition :
  FStar_TypeChecker_NBETerm.args ->
    Prims.bool Prims.list ->
      (Prims.bool * FStar_TypeChecker_NBETerm.args *
        FStar_TypeChecker_NBETerm.args))
  =
  fun arguments  ->
    fun formals_in_decreases  ->
      let rec aux ts ar_list acc =
        match (ts, ar_list) with
        | (uu____1479,[]) -> (true, acc, ts)
        | ([],uu____1510::uu____1511) -> (false, acc, [])
        | (t::ts1,in_decreases_clause::bs) ->
            let uu____1580 =
              in_decreases_clause &&
                (FStar_TypeChecker_NBETerm.isAccu
                   (FStar_Pervasives_Native.fst t))
               in
            if uu____1580
            then (false, (FStar_List.rev_append ts1 acc), [])
            else aux ts1 bs (t :: acc)
         in
      aux arguments formals_in_decreases []
  
let (find_sigelt_in_gamma :
  config ->
    FStar_TypeChecker_Env.env ->
      FStar_Ident.lident ->
        FStar_Syntax_Syntax.sigelt FStar_Pervasives_Native.option)
  =
  fun cfg  ->
    fun env  ->
      fun lid  ->
        let mapper uu____1679 =
          match uu____1679 with
          | (lr,rng) ->
              (match lr with
               | FStar_Util.Inr (elt,FStar_Pervasives_Native.None ) ->
                   FStar_Pervasives_Native.Some elt
               | FStar_Util.Inr (elt,FStar_Pervasives_Native.Some us) ->
                   (debug cfg
                      (fun uu____1762  ->
                         let uu____1763 =
                           FStar_Syntax_Print.univs_to_string us  in
                         FStar_Util.print1
                           "Universes in local declaration: %s\n" uu____1763);
                    FStar_Pervasives_Native.Some elt)
               | uu____1766 -> FStar_Pervasives_Native.None)
           in
        let uu____1781 = FStar_TypeChecker_Env.lookup_qname env lid  in
        FStar_Util.bind_opt uu____1781 mapper
  
let (is_univ : FStar_TypeChecker_NBETerm.t -> Prims.bool) =
  fun tm  ->
    match tm.FStar_TypeChecker_NBETerm.nbe_t with
    | FStar_TypeChecker_NBETerm.Univ uu____1828 -> true
    | uu____1830 -> false
  
let (un_univ : FStar_TypeChecker_NBETerm.t -> FStar_Syntax_Syntax.universe) =
  fun tm  ->
    match tm.FStar_TypeChecker_NBETerm.nbe_t with
    | FStar_TypeChecker_NBETerm.Univ u -> u
    | uu____1839 ->
        let uu____1840 =
          let uu____1842 = FStar_TypeChecker_NBETerm.t_to_string tm  in
          Prims.op_Hat "Not a universe: " uu____1842  in
        failwith uu____1840
  
let (is_constr_fv : FStar_Syntax_Syntax.fv -> Prims.bool) =
  fun fvar  ->
    fvar.FStar_Syntax_Syntax.fv_qual =
      (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
  
let (is_constr : FStar_TypeChecker_Env.qninfo -> Prims.bool) =
  fun q  ->
    match q with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
              (uu____1864,uu____1865,uu____1866,uu____1867,uu____1868,uu____1869);
            FStar_Syntax_Syntax.sigrng = uu____1870;
            FStar_Syntax_Syntax.sigquals = uu____1871;
            FStar_Syntax_Syntax.sigmeta = uu____1872;
            FStar_Syntax_Syntax.sigattrs = uu____1873;
            FStar_Syntax_Syntax.sigopts = uu____1874;_},uu____1875),uu____1876)
        -> true
    | uu____1936 -> false
  
let (translate_univ :
  config ->
    FStar_TypeChecker_NBETerm.t Prims.list ->
      FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe)
  =
  fun cfg  ->
    fun bs  ->
      fun u  ->
        let rec aux u1 =
          let u2 = FStar_Syntax_Subst.compress_univ u1  in
          match u2 with
          | FStar_Syntax_Syntax.U_bvar i ->
              if i < (FStar_List.length bs)
              then let u' = FStar_List.nth bs i  in un_univ u'
              else
                if
                  ((cfg.core_cfg).FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.allow_unbound_universes
                then FStar_Syntax_Syntax.U_zero
                else failwith "Universe index out of bounds"
          | FStar_Syntax_Syntax.U_succ u3 ->
              let uu____1976 = aux u3  in
              FStar_Syntax_Syntax.U_succ uu____1976
          | FStar_Syntax_Syntax.U_max us ->
              let uu____1980 = FStar_List.map aux us  in
              FStar_Syntax_Syntax.U_max uu____1980
          | FStar_Syntax_Syntax.U_unknown  -> u2
          | FStar_Syntax_Syntax.U_name uu____1983 -> u2
          | FStar_Syntax_Syntax.U_unif uu____1984 -> u2
          | FStar_Syntax_Syntax.U_zero  -> u2  in
        aux u
  
let (find_let :
  FStar_Syntax_Syntax.letbinding Prims.list ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.letbinding FStar_Pervasives_Native.option)
  =
  fun lbs  ->
    fun fvar  ->
      FStar_Util.find_map lbs
        (fun lb  ->
           match lb.FStar_Syntax_Syntax.lbname with
           | FStar_Util.Inl uu____2017 -> failwith "find_let : impossible"
           | FStar_Util.Inr name ->
               let uu____2022 = FStar_Syntax_Syntax.fv_eq name fvar  in
               if uu____2022
               then FStar_Pervasives_Native.Some lb
               else FStar_Pervasives_Native.None)
  
let (mk_rt :
  FStar_Range.range ->
    FStar_TypeChecker_NBETerm.t' -> FStar_TypeChecker_NBETerm.t)
  =
  fun r  ->
    fun t  ->
      {
        FStar_TypeChecker_NBETerm.nbe_t = t;
        FStar_TypeChecker_NBETerm.nbe_r = r
      }
  
let (mk_t : FStar_TypeChecker_NBETerm.t' -> FStar_TypeChecker_NBETerm.t) =
  fun t  ->
    {
      FStar_TypeChecker_NBETerm.nbe_t = t;
      FStar_TypeChecker_NBETerm.nbe_r = FStar_Range.dummyRange
    }
  
let rec (translate :
  config ->
    FStar_TypeChecker_NBETerm.t Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_TypeChecker_NBETerm.t)
  =
  fun cfg  ->
    fun bs  ->
      fun e  ->
        let debug1 = debug cfg  in
        let mk_t1 t = mk_rt e.FStar_Syntax_Syntax.pos t  in
        debug1
          (fun uu____2316  ->
             let uu____2317 =
               let uu____2319 = FStar_Syntax_Subst.compress e  in
               FStar_Syntax_Print.tag_of_term uu____2319  in
             let uu____2320 =
               let uu____2322 = FStar_Syntax_Subst.compress e  in
               FStar_Syntax_Print.term_to_string uu____2322  in
             FStar_Util.print2 "Term: %s - %s\n" uu____2317 uu____2320);
        (let uu____2324 =
           let uu____2325 = FStar_Syntax_Subst.compress e  in
           uu____2325.FStar_Syntax_Syntax.n  in
         match uu____2324 with
         | FStar_Syntax_Syntax.Tm_delayed (uu____2328,uu____2329) ->
             failwith "Tm_delayed: Impossible"
         | FStar_Syntax_Syntax.Tm_unknown  ->
             mk_t1 FStar_TypeChecker_NBETerm.Unknown
         | FStar_Syntax_Syntax.Tm_constant c ->
             let uu____2352 =
               let uu____2353 = translate_constant c  in
               FStar_TypeChecker_NBETerm.Constant uu____2353  in
             FStar_All.pipe_left mk_t1 uu____2352
         | FStar_Syntax_Syntax.Tm_bvar db ->
             if db.FStar_Syntax_Syntax.index < (FStar_List.length bs)
             then
               let t = FStar_List.nth bs db.FStar_Syntax_Syntax.index  in
               (debug1
                  (fun uu____2364  ->
                     let uu____2365 = FStar_TypeChecker_NBETerm.t_to_string t
                        in
                     let uu____2367 =
                       let uu____2369 =
                         FStar_List.map FStar_TypeChecker_NBETerm.t_to_string
                           bs
                          in
                       FStar_All.pipe_right uu____2369
                         (FStar_String.concat "; ")
                        in
                     FStar_Util.print2
                       "Resolved bvar to %s\n\tcontext is [%s]\n" uu____2365
                       uu____2367);
                t)
             else failwith "de Bruijn index out of bounds"
         | FStar_Syntax_Syntax.Tm_uinst (t,us) ->
             (debug1
                (fun uu____2396  ->
                   let uu____2397 = FStar_Syntax_Print.term_to_string t  in
                   let uu____2399 =
                     let uu____2401 =
                       FStar_List.map FStar_Syntax_Print.univ_to_string us
                        in
                     FStar_All.pipe_right uu____2401
                       (FStar_String.concat ", ")
                      in
                   FStar_Util.print2 "Uinst term : %s\nUnivs : %s\n"
                     uu____2397 uu____2399);
              (let uu____2412 = translate cfg bs t  in
               let uu____2413 =
                 FStar_List.map
                   (fun x  ->
                      let uu____2417 =
                        let uu____2418 =
                          let uu____2419 = translate_univ cfg bs x  in
                          FStar_TypeChecker_NBETerm.Univ uu____2419  in
                        FStar_All.pipe_left mk_t1 uu____2418  in
                      FStar_TypeChecker_NBETerm.as_arg uu____2417) us
                  in
               iapp cfg uu____2412 uu____2413))
         | FStar_Syntax_Syntax.Tm_type u ->
             let uu____2421 =
               let uu____2422 = translate_univ cfg bs u  in
               FStar_TypeChecker_NBETerm.Type_t uu____2422  in
             FStar_All.pipe_left mk_t1 uu____2421
         | FStar_Syntax_Syntax.Tm_arrow (xs,c) ->
             let norm uu____2452 =
               let uu____2453 =
                 FStar_List.fold_left
                   (fun uu____2497  ->
                      fun uu____2498  ->
                        match (uu____2497, uu____2498) with
                        | ((ctx,binders_rev),(x,q)) ->
                            let t =
                              let uu____2602 =
                                translate cfg ctx x.FStar_Syntax_Syntax.sort
                                 in
                              readback cfg uu____2602  in
                            let x1 =
                              let uu___399_2604 =
                                FStar_Syntax_Syntax.freshen_bv x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___399_2604.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___399_2604.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t
                              }  in
                            let ctx1 =
                              let uu____2608 =
                                FStar_TypeChecker_NBETerm.mkAccuVar x1  in
                              uu____2608 :: ctx  in
                            (ctx1, ((x1, q) :: binders_rev))) (bs, []) xs
                  in
               match uu____2453 with
               | (ctx,binders_rev) ->
                   let c1 =
                     let uu____2668 = translate_comp cfg ctx c  in
                     readback_comp cfg uu____2668  in
                   FStar_Syntax_Util.arrow (FStar_List.rev binders_rev) c1
                in
             let uu____2675 =
               let uu____2676 =
                 let uu____2693 = FStar_Thunk.mk norm  in
                 FStar_Util.Inl uu____2693  in
               FStar_TypeChecker_NBETerm.Arrow uu____2676  in
             FStar_All.pipe_left mk_t1 uu____2675
         | FStar_Syntax_Syntax.Tm_refine (bv,tm) ->
             if
               ((cfg.core_cfg).FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.for_extraction
             then translate cfg bs bv.FStar_Syntax_Syntax.sort
             else
               FStar_All.pipe_left mk_t1
                 (FStar_TypeChecker_NBETerm.Refinement
                    ((fun y  -> translate cfg (y :: bs) tm),
                      (fun uu____2731  ->
                         let uu____2732 =
                           translate cfg bs bv.FStar_Syntax_Syntax.sort  in
                         FStar_TypeChecker_NBETerm.as_arg uu____2732)))
         | FStar_Syntax_Syntax.Tm_ascribed (t,uu____2734,uu____2735) ->
             translate cfg bs t
         | FStar_Syntax_Syntax.Tm_uvar (u,(subst,set_use_range)) ->
             let norm_uvar uu____2802 =
               let norm_subst_elt uu___1_2808 =
                 match uu___1_2808 with
                 | FStar_Syntax_Syntax.NT (x,t) ->
                     let uu____2815 =
                       let uu____2822 =
                         let uu____2825 = translate cfg bs t  in
                         readback cfg uu____2825  in
                       (x, uu____2822)  in
                     FStar_Syntax_Syntax.NT uu____2815
                 | FStar_Syntax_Syntax.NM (x,i) ->
                     let x_i =
                       FStar_Syntax_Syntax.bv_to_tm
                         (let uu___436_2835 = x  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___436_2835.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index = i;
                            FStar_Syntax_Syntax.sort =
                              (uu___436_2835.FStar_Syntax_Syntax.sort)
                          })
                        in
                     let t =
                       let uu____2837 = translate cfg bs x_i  in
                       readback cfg uu____2837  in
                     (match t.FStar_Syntax_Syntax.n with
                      | FStar_Syntax_Syntax.Tm_bvar x_j ->
                          FStar_Syntax_Syntax.NM
                            (x, (x_j.FStar_Syntax_Syntax.index))
                      | uu____2840 -> FStar_Syntax_Syntax.NT (x, t))
                 | uu____2843 ->
                     failwith "Impossible: subst invariant of uvar nodes"
                  in
               let subst1 =
                 FStar_List.map (FStar_List.map norm_subst_elt) subst  in
               let uu___446_2854 = e  in
               {
                 FStar_Syntax_Syntax.n =
                   (FStar_Syntax_Syntax.Tm_uvar (u, (subst1, set_use_range)));
                 FStar_Syntax_Syntax.pos =
                   (uu___446_2854.FStar_Syntax_Syntax.pos);
                 FStar_Syntax_Syntax.vars =
                   (uu___446_2854.FStar_Syntax_Syntax.vars)
               }  in
             let uu____2867 =
               let uu____2868 =
                 let uu____2879 =
                   let uu____2880 = FStar_Thunk.mk norm_uvar  in
                   FStar_TypeChecker_NBETerm.UVar uu____2880  in
                 (uu____2879, [])  in
               FStar_TypeChecker_NBETerm.Accu uu____2868  in
             FStar_All.pipe_left mk_t1 uu____2867
         | FStar_Syntax_Syntax.Tm_name x ->
             FStar_TypeChecker_NBETerm.mkAccuVar x
         | FStar_Syntax_Syntax.Tm_abs ([],uu____2894,uu____2895) ->
             failwith "Impossible: abstraction with no binders"
         | FStar_Syntax_Syntax.Tm_abs (xs,body,resc) ->
             FStar_All.pipe_left mk_t1
               (FStar_TypeChecker_NBETerm.Lam
                  ((fun ys  -> translate cfg (FStar_List.append ys bs) body),
                    (FStar_Util.Inl (bs, xs, resc)), (FStar_List.length xs)))
         | FStar_Syntax_Syntax.Tm_fvar fvar ->
             let uu____3003 = try_in_cache cfg fvar  in
             (match uu____3003 with
              | FStar_Pervasives_Native.Some t -> t
              | uu____3007 ->
                  let uu____3010 =
                    FStar_Syntax_Syntax.set_range_of_fv fvar
                      e.FStar_Syntax_Syntax.pos
                     in
                  translate_fv cfg bs uu____3010)
         | FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                  (FStar_Const.Const_reify );
                FStar_Syntax_Syntax.pos = uu____3011;
                FStar_Syntax_Syntax.vars = uu____3012;_},arg::more::args)
             ->
             let uu____3072 = FStar_Syntax_Util.head_and_args e  in
             (match uu____3072 with
              | (head,uu____3090) ->
                  let head1 =
                    FStar_Syntax_Syntax.mk_Tm_app head [arg]
                      e.FStar_Syntax_Syntax.pos
                     in
                  let uu____3132 =
                    FStar_Syntax_Syntax.mk_Tm_app head1 (more :: args)
                      e.FStar_Syntax_Syntax.pos
                     in
                  translate cfg bs uu____3132)
         | FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                  (FStar_Const.Const_reflect uu____3141);
                FStar_Syntax_Syntax.pos = uu____3142;
                FStar_Syntax_Syntax.vars = uu____3143;_},arg::more::args)
             ->
             let uu____3203 = FStar_Syntax_Util.head_and_args e  in
             (match uu____3203 with
              | (head,uu____3221) ->
                  let head1 =
                    FStar_Syntax_Syntax.mk_Tm_app head [arg]
                      e.FStar_Syntax_Syntax.pos
                     in
                  let uu____3263 =
                    FStar_Syntax_Syntax.mk_Tm_app head1 (more :: args)
                      e.FStar_Syntax_Syntax.pos
                     in
                  translate cfg bs uu____3263)
         | FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                  (FStar_Const.Const_reflect uu____3272);
                FStar_Syntax_Syntax.pos = uu____3273;
                FStar_Syntax_Syntax.vars = uu____3274;_},arg::[])
             when (cfg.core_cfg).FStar_TypeChecker_Cfg.reifying ->
             let cfg1 = reifying_false cfg  in
             translate cfg1 bs (FStar_Pervasives_Native.fst arg)
         | FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                  (FStar_Const.Const_reflect uu____3319);
                FStar_Syntax_Syntax.pos = uu____3320;
                FStar_Syntax_Syntax.vars = uu____3321;_},arg::[])
             ->
             let uu____3361 =
               let uu____3362 =
                 translate cfg bs (FStar_Pervasives_Native.fst arg)  in
               FStar_TypeChecker_NBETerm.Reflect uu____3362  in
             FStar_All.pipe_left mk_t1 uu____3361
         | FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                  (FStar_Const.Const_reify );
                FStar_Syntax_Syntax.pos = uu____3367;
                FStar_Syntax_Syntax.vars = uu____3368;_},arg::[])
             when
             ((cfg.core_cfg).FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.reify_
             ->
             let cfg1 = reifying_true cfg  in
             translate cfg1 bs (FStar_Pervasives_Native.fst arg)
         | FStar_Syntax_Syntax.Tm_app (head,args) ->
             (debug1
                (fun uu____3447  ->
                   let uu____3448 = FStar_Syntax_Print.term_to_string head
                      in
                   let uu____3450 = FStar_Syntax_Print.args_to_string args
                      in
                   FStar_Util.print2 "Application: %s @ %s\n" uu____3448
                     uu____3450);
              (let uu____3453 = translate cfg bs head  in
               let uu____3454 =
                 FStar_List.map
                   (fun x  ->
                      let uu____3476 =
                        translate cfg bs (FStar_Pervasives_Native.fst x)  in
                      (uu____3476, (FStar_Pervasives_Native.snd x))) args
                  in
               iapp cfg uu____3453 uu____3454))
         | FStar_Syntax_Syntax.Tm_match (scrut,branches) ->
             let make_branches uu____3528 =
               let cfg1 = zeta_false cfg  in
               let rec process_pattern bs1 p =
                 let uu____3559 =
                   match p.FStar_Syntax_Syntax.v with
                   | FStar_Syntax_Syntax.Pat_constant c ->
                       (bs1, (FStar_Syntax_Syntax.Pat_constant c))
                   | FStar_Syntax_Syntax.Pat_cons (fvar,args) ->
                       let uu____3595 =
                         FStar_List.fold_left
                           (fun uu____3636  ->
                              fun uu____3637  ->
                                match (uu____3636, uu____3637) with
                                | ((bs2,args1),(arg,b)) ->
                                    let uu____3729 = process_pattern bs2 arg
                                       in
                                    (match uu____3729 with
                                     | (bs',arg') ->
                                         (bs', ((arg', b) :: args1))))
                           (bs1, []) args
                          in
                       (match uu____3595 with
                        | (bs',args') ->
                            (bs',
                              (FStar_Syntax_Syntax.Pat_cons
                                 (fvar, (FStar_List.rev args')))))
                   | FStar_Syntax_Syntax.Pat_var bvar ->
                       let x =
                         let uu____3828 =
                           let uu____3829 =
                             translate cfg1 bs1 bvar.FStar_Syntax_Syntax.sort
                              in
                           readback cfg1 uu____3829  in
                         FStar_Syntax_Syntax.new_bv
                           FStar_Pervasives_Native.None uu____3828
                          in
                       let uu____3830 =
                         let uu____3833 =
                           FStar_TypeChecker_NBETerm.mkAccuVar x  in
                         uu____3833 :: bs1  in
                       (uu____3830, (FStar_Syntax_Syntax.Pat_var x))
                   | FStar_Syntax_Syntax.Pat_wild bvar ->
                       let x =
                         let uu____3838 =
                           let uu____3839 =
                             translate cfg1 bs1 bvar.FStar_Syntax_Syntax.sort
                              in
                           readback cfg1 uu____3839  in
                         FStar_Syntax_Syntax.new_bv
                           FStar_Pervasives_Native.None uu____3838
                          in
                       let uu____3840 =
                         let uu____3843 =
                           FStar_TypeChecker_NBETerm.mkAccuVar x  in
                         uu____3843 :: bs1  in
                       (uu____3840, (FStar_Syntax_Syntax.Pat_wild x))
                   | FStar_Syntax_Syntax.Pat_dot_term (bvar,tm) ->
                       let x =
                         let uu____3853 =
                           let uu____3854 =
                             translate cfg1 bs1 bvar.FStar_Syntax_Syntax.sort
                              in
                           readback cfg1 uu____3854  in
                         FStar_Syntax_Syntax.new_bv
                           FStar_Pervasives_Native.None uu____3853
                          in
                       let uu____3855 =
                         let uu____3856 =
                           let uu____3863 =
                             let uu____3866 = translate cfg1 bs1 tm  in
                             readback cfg1 uu____3866  in
                           (x, uu____3863)  in
                         FStar_Syntax_Syntax.Pat_dot_term uu____3856  in
                       (bs1, uu____3855)
                    in
                 match uu____3559 with
                 | (bs2,p_new) ->
                     (bs2,
                       (let uu___573_3886 = p  in
                        {
                          FStar_Syntax_Syntax.v = p_new;
                          FStar_Syntax_Syntax.p =
                            (uu___573_3886.FStar_Syntax_Syntax.p)
                        }))
                  in
               FStar_List.map
                 (fun uu____3905  ->
                    match uu____3905 with
                    | (pat,when_clause,e1) ->
                        let uu____3927 = process_pattern bs pat  in
                        (match uu____3927 with
                         | (bs',pat') ->
                             let uu____3940 =
                               let uu____3941 =
                                 let uu____3944 = translate cfg1 bs' e1  in
                                 readback cfg1 uu____3944  in
                               (pat', when_clause, uu____3941)  in
                             FStar_Syntax_Util.branch uu____3940)) branches
                in
             let scrut1 = translate cfg bs scrut  in
             (debug1
                (fun uu____3961  ->
                   let uu____3962 =
                     FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos
                      in
                   let uu____3964 = FStar_Syntax_Print.term_to_string e  in
                   FStar_Util.print2 "%s: Translating match %s\n" uu____3962
                     uu____3964);
              (let scrut2 = unlazy_unmeta scrut1  in
               match scrut2.FStar_TypeChecker_NBETerm.nbe_t with
               | FStar_TypeChecker_NBETerm.Construct (c,us,args) ->
                   (debug1
                      (fun uu____3992  ->
                         let uu____3993 =
                           let uu____3995 =
                             FStar_All.pipe_right args
                               (FStar_List.map
                                  (fun uu____4021  ->
                                     match uu____4021 with
                                     | (x,q) ->
                                         let uu____4035 =
                                           FStar_TypeChecker_NBETerm.t_to_string
                                             x
                                            in
                                         Prims.op_Hat
                                           (if FStar_Util.is_some q
                                            then "#"
                                            else "") uu____4035))
                              in
                           FStar_All.pipe_right uu____3995
                             (FStar_String.concat "; ")
                            in
                         FStar_Util.print1 "Match args: %s\n" uu____3993);
                    (let uu____4049 = pickBranch cfg scrut2 branches  in
                     match uu____4049 with
                     | FStar_Pervasives_Native.Some (branch,args1) ->
                         let uu____4070 =
                           FStar_List.fold_left
                             (fun bs1  -> fun x  -> x :: bs1) bs args1
                            in
                         translate cfg uu____4070 branch
                     | FStar_Pervasives_Native.None  ->
                         FStar_TypeChecker_NBETerm.mkAccuMatch scrut2
                           make_branches))
               | FStar_TypeChecker_NBETerm.Constant c ->
                   (debug1
                      (fun uu____4093  ->
                         let uu____4094 =
                           FStar_TypeChecker_NBETerm.t_to_string scrut2  in
                         FStar_Util.print1 "Match constant : %s\n" uu____4094);
                    (let uu____4097 = pickBranch cfg scrut2 branches  in
                     match uu____4097 with
                     | FStar_Pervasives_Native.Some (branch,[]) ->
                         translate cfg bs branch
                     | FStar_Pervasives_Native.Some (branch,arg::[]) ->
                         translate cfg (arg :: bs) branch
                     | FStar_Pervasives_Native.None  ->
                         FStar_TypeChecker_NBETerm.mkAccuMatch scrut2
                           make_branches
                     | FStar_Pervasives_Native.Some (uu____4131,hd::tl) ->
                         failwith
                           "Impossible: Matching on constants cannot bind more than one variable"))
               | uu____4145 ->
                   FStar_TypeChecker_NBETerm.mkAccuMatch scrut2 make_branches))
         | FStar_Syntax_Syntax.Tm_meta
             (e1,FStar_Syntax_Syntax.Meta_monadic (m,t)) when
             (cfg.core_cfg).FStar_TypeChecker_Cfg.reifying ->
             translate_monadic (m, t) cfg bs e1
         | FStar_Syntax_Syntax.Tm_meta
             (e1,FStar_Syntax_Syntax.Meta_monadic_lift (m,m',t)) when
             (cfg.core_cfg).FStar_TypeChecker_Cfg.reifying ->
             translate_monadic_lift (m, m', t) cfg bs e1
         | FStar_Syntax_Syntax.Tm_meta (e1,meta) ->
             let norm_meta uu____4184 =
               let norm t =
                 let uu____4191 = translate cfg bs t  in
                 readback cfg uu____4191  in
               match meta with
               | FStar_Syntax_Syntax.Meta_named uu____4192 -> meta
               | FStar_Syntax_Syntax.Meta_labeled uu____4193 -> meta
               | FStar_Syntax_Syntax.Meta_desugared uu____4202 -> meta
               | FStar_Syntax_Syntax.Meta_pattern (ts,args) ->
                   let uu____4237 =
                     let uu____4258 = FStar_List.map norm ts  in
                     let uu____4267 =
                       FStar_List.map
                         (FStar_List.map
                            (fun uu____4316  ->
                               match uu____4316 with
                               | (t,a) ->
                                   let uu____4335 = norm t  in
                                   (uu____4335, a))) args
                        in
                     (uu____4258, uu____4267)  in
                   FStar_Syntax_Syntax.Meta_pattern uu____4237
               | FStar_Syntax_Syntax.Meta_monadic (m,t) ->
                   let uu____4360 =
                     let uu____4367 = norm t  in (m, uu____4367)  in
                   FStar_Syntax_Syntax.Meta_monadic uu____4360
               | FStar_Syntax_Syntax.Meta_monadic_lift (m0,m1,t) ->
                   let uu____4379 =
                     let uu____4388 = norm t  in (m0, m1, uu____4388)  in
                   FStar_Syntax_Syntax.Meta_monadic_lift uu____4379
                in
             let uu____4393 =
               let uu____4394 =
                 let uu____4401 = translate cfg bs e1  in
                 let uu____4402 = FStar_Thunk.mk norm_meta  in
                 (uu____4401, uu____4402)  in
               FStar_TypeChecker_NBETerm.Meta uu____4394  in
             FStar_All.pipe_left mk_t1 uu____4393
         | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
             let uu____4424 =
               FStar_TypeChecker_Cfg.should_reduce_local_let cfg.core_cfg lb
                in
             if uu____4424
             then
               let uu____4427 =
                 (((cfg.core_cfg).FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.for_extraction
                    &&
                    (FStar_Syntax_Util.is_unit lb.FStar_Syntax_Syntax.lbtyp))
                   &&
                   (FStar_Syntax_Util.is_pure_or_ghost_effect
                      lb.FStar_Syntax_Syntax.lbeff)
                  in
               (if uu____4427
                then
                  let bs1 =
                    let uu____4433 =
                      let uu____4434 =
                        FStar_Syntax_Syntax.range_of_lbname
                          lb.FStar_Syntax_Syntax.lbname
                         in
                      mk_rt uu____4434
                        (FStar_TypeChecker_NBETerm.Constant
                           FStar_TypeChecker_NBETerm.Unit)
                       in
                    uu____4433 :: bs  in
                  translate cfg bs1 body
                else
                  (let bs1 =
                     let uu____4440 = translate_letbinding cfg bs lb  in
                     uu____4440 :: bs  in
                   translate cfg bs1 body))
             else
               (let def uu____4448 =
                  let uu____4449 =
                    (((cfg.core_cfg).FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.for_extraction
                       &&
                       (FStar_Syntax_Util.is_unit
                          lb.FStar_Syntax_Syntax.lbtyp))
                      &&
                      (FStar_Syntax_Util.is_pure_or_ghost_effect
                         lb.FStar_Syntax_Syntax.lbeff)
                     in
                  if uu____4449
                  then
                    FStar_All.pipe_left mk_t1
                      (FStar_TypeChecker_NBETerm.Constant
                         FStar_TypeChecker_NBETerm.Unit)
                  else translate cfg bs lb.FStar_Syntax_Syntax.lbdef  in
                let typ uu____4459 =
                  translate cfg bs lb.FStar_Syntax_Syntax.lbtyp  in
                let name =
                  let uu____4461 =
                    FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                  FStar_Syntax_Syntax.freshen_bv uu____4461  in
                let bs1 =
                  let uu____4465 =
                    let uu____4466 = FStar_Syntax_Syntax.range_of_bv name  in
                    mk_rt uu____4466
                      (FStar_TypeChecker_NBETerm.Accu
                         ((FStar_TypeChecker_NBETerm.Var name), []))
                     in
                  uu____4465 :: bs  in
                let body1 uu____4482 = translate cfg bs1 body  in
                let uu____4483 =
                  let uu____4484 =
                    let uu____4495 =
                      let uu____4496 =
                        let uu____4513 = FStar_Thunk.mk typ  in
                        let uu____4516 = FStar_Thunk.mk def  in
                        let uu____4519 = FStar_Thunk.mk body1  in
                        (name, uu____4513, uu____4516, uu____4519, lb)  in
                      FStar_TypeChecker_NBETerm.UnreducedLet uu____4496  in
                    (uu____4495, [])  in
                  FStar_TypeChecker_NBETerm.Accu uu____4484  in
                FStar_All.pipe_left mk_t1 uu____4483)
         | FStar_Syntax_Syntax.Tm_let ((_rec,lbs),body) ->
             if
               (Prims.op_Negation
                  ((cfg.core_cfg).FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta)
                 &&
                 ((cfg.core_cfg).FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.pure_subterms_within_computations
             then
               let vars =
                 FStar_List.map
                   (fun lb  ->
                      let uu____4565 =
                        FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                      FStar_Syntax_Syntax.freshen_bv uu____4565) lbs
                  in
               let typs =
                 FStar_List.map
                   (fun lb  -> translate cfg bs lb.FStar_Syntax_Syntax.lbtyp)
                   lbs
                  in
               let rec_bs =
                 let uu____4574 =
                   FStar_List.map
                     (fun v  ->
                        let uu____4580 =
                          let uu____4585 = FStar_Syntax_Syntax.range_of_bv v
                             in
                          mk_rt uu____4585  in
                        FStar_All.pipe_left uu____4580
                          (FStar_TypeChecker_NBETerm.Accu
                             ((FStar_TypeChecker_NBETerm.Var v), []))) vars
                    in
                 FStar_List.append uu____4574 bs  in
               let defs =
                 FStar_List.map
                   (fun lb  ->
                      translate cfg rec_bs lb.FStar_Syntax_Syntax.lbdef) lbs
                  in
               let body1 = translate cfg rec_bs body  in
               let uu____4602 =
                 let uu____4603 =
                   let uu____4614 =
                     let uu____4615 =
                       let uu____4632 = FStar_List.zip3 vars typs defs  in
                       (uu____4632, body1, lbs)  in
                     FStar_TypeChecker_NBETerm.UnreducedLetRec uu____4615  in
                   (uu____4614, [])  in
                 FStar_TypeChecker_NBETerm.Accu uu____4603  in
               FStar_All.pipe_left mk_t1 uu____4602
             else
               (let uu____4663 = make_rec_env lbs bs  in
                translate cfg uu____4663 body)
         | FStar_Syntax_Syntax.Tm_quoted (qt,qi) ->
             let close t =
               let bvs =
                 FStar_List.map
                   (fun uu____4682  ->
                      FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                        FStar_Syntax_Syntax.tun) bs
                  in
               let s1 =
                 FStar_List.mapi
                   (fun i  -> fun bv  -> FStar_Syntax_Syntax.DB (i, bv)) bvs
                  in
               let s2 =
                 let uu____4695 = FStar_List.zip bvs bs  in
                 FStar_List.map
                   (fun uu____4710  ->
                      match uu____4710 with
                      | (bv,t1) ->
                          let uu____4717 =
                            let uu____4724 = readback cfg t1  in
                            (bv, uu____4724)  in
                          FStar_Syntax_Syntax.NT uu____4717) uu____4695
                  in
               let uu____4729 = FStar_Syntax_Subst.subst s1 t  in
               FStar_Syntax_Subst.subst s2 uu____4729  in
             (match qi.FStar_Syntax_Syntax.qkind with
              | FStar_Syntax_Syntax.Quote_dynamic  ->
                  let qt1 = close qt  in
                  FStar_All.pipe_left mk_t1
                    (FStar_TypeChecker_NBETerm.Quote (qt1, qi))
              | FStar_Syntax_Syntax.Quote_static  ->
                  let qi1 = FStar_Syntax_Syntax.on_antiquoted close qi  in
                  FStar_All.pipe_left mk_t1
                    (FStar_TypeChecker_NBETerm.Quote (qt, qi1)))
         | FStar_Syntax_Syntax.Tm_lazy li ->
             let f uu____4738 =
               let t = FStar_Syntax_Util.unfold_lazy li  in
               debug1
                 (fun uu____4745  ->
                    let uu____4746 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.print1 ">> Unfolding Tm_lazy to %s\n"
                      uu____4746);
               translate cfg bs t  in
             let uu____4749 =
               let uu____4750 =
                 let uu____4765 = FStar_Thunk.mk f  in
                 ((FStar_Util.Inl li), uu____4765)  in
               FStar_TypeChecker_NBETerm.Lazy uu____4750  in
             FStar_All.pipe_left mk_t1 uu____4749)

and (translate_comp :
  config ->
    FStar_TypeChecker_NBETerm.t Prims.list ->
      FStar_Syntax_Syntax.comp -> FStar_TypeChecker_NBETerm.comp)
  =
  fun cfg  ->
    fun bs  ->
      fun c  ->
        match c.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total (typ,u) ->
            let uu____4797 =
              let uu____4804 = translate cfg bs typ  in
              let uu____4805 = fmap_opt (translate_univ cfg bs) u  in
              (uu____4804, uu____4805)  in
            FStar_TypeChecker_NBETerm.Tot uu____4797
        | FStar_Syntax_Syntax.GTotal (typ,u) ->
            let uu____4820 =
              let uu____4827 = translate cfg bs typ  in
              let uu____4828 = fmap_opt (translate_univ cfg bs) u  in
              (uu____4827, uu____4828)  in
            FStar_TypeChecker_NBETerm.GTot uu____4820
        | FStar_Syntax_Syntax.Comp ctyp ->
            let uu____4834 = translate_comp_typ cfg bs ctyp  in
            FStar_TypeChecker_NBETerm.Comp uu____4834

and (iapp :
  config ->
    FStar_TypeChecker_NBETerm.t ->
      FStar_TypeChecker_NBETerm.args -> FStar_TypeChecker_NBETerm.t)
  =
  fun cfg  ->
    fun f  ->
      fun args  ->
        let mk t = mk_rt f.FStar_TypeChecker_NBETerm.nbe_r t  in
        let uu____4844 =
          let uu____4845 = unlazy_unmeta f  in
          uu____4845.FStar_TypeChecker_NBETerm.nbe_t  in
        match uu____4844 with
        | FStar_TypeChecker_NBETerm.Lam (f1,binders,n) ->
            let m = FStar_List.length args  in
            if m < n
            then
              let arg_values_rev = map_rev FStar_Pervasives_Native.fst args
                 in
              let binders1 =
                match binders with
                | FStar_Util.Inr raw_args ->
                    let uu____4978 = FStar_List.splitAt m raw_args  in
                    (match uu____4978 with
                     | (uu____5019,raw_args1) -> FStar_Util.Inr raw_args1)
                | FStar_Util.Inl (ctx,xs,rc) ->
                    let uu____5088 = FStar_List.splitAt m xs  in
                    (match uu____5088 with
                     | (uu____5135,xs1) ->
                         let ctx1 = FStar_List.append arg_values_rev ctx  in
                         FStar_Util.Inl (ctx1, xs1, rc))
                 in
              FStar_All.pipe_left mk
                (FStar_TypeChecker_NBETerm.Lam
                   ((fun l  -> f1 (FStar_List.append l arg_values_rev)),
                     binders1, (n - m)))
            else
              if m = n
              then
                (let arg_values_rev =
                   map_rev FStar_Pervasives_Native.fst args  in
                 f1 arg_values_rev)
              else
                (let uu____5235 = FStar_List.splitAt n args  in
                 match uu____5235 with
                 | (args1,args') ->
                     let uu____5282 =
                       let uu____5283 =
                         map_rev FStar_Pervasives_Native.fst args1  in
                       f1 uu____5283  in
                     iapp cfg uu____5282 args')
        | FStar_TypeChecker_NBETerm.Accu (a,ts) ->
            FStar_All.pipe_left mk
              (FStar_TypeChecker_NBETerm.Accu
                 (a, (FStar_List.rev_append args ts)))
        | FStar_TypeChecker_NBETerm.Construct (i,us,ts) ->
            let rec aux args1 us1 ts1 =
              match args1 with
              | ({
                   FStar_TypeChecker_NBETerm.nbe_t =
                     FStar_TypeChecker_NBETerm.Univ u;
                   FStar_TypeChecker_NBETerm.nbe_r = uu____5402;_},uu____5403)::args2
                  -> aux args2 (u :: us1) ts1
              | a::args2 -> aux args2 us1 (a :: ts1)
              | [] -> (us1, ts1)  in
            let uu____5447 = aux args us ts  in
            (match uu____5447 with
             | (us',ts') ->
                 FStar_All.pipe_left mk
                   (FStar_TypeChecker_NBETerm.Construct (i, us', ts')))
        | FStar_TypeChecker_NBETerm.FV (i,us,ts) ->
            let rec aux args1 us1 ts1 =
              match args1 with
              | ({
                   FStar_TypeChecker_NBETerm.nbe_t =
                     FStar_TypeChecker_NBETerm.Univ u;
                   FStar_TypeChecker_NBETerm.nbe_r = uu____5574;_},uu____5575)::args2
                  -> aux args2 (u :: us1) ts1
              | a::args2 -> aux args2 us1 (a :: ts1)
              | [] -> (us1, ts1)  in
            let uu____5619 = aux args us ts  in
            (match uu____5619 with
             | (us',ts') ->
                 FStar_All.pipe_left mk
                   (FStar_TypeChecker_NBETerm.FV (i, us', ts')))
        | FStar_TypeChecker_NBETerm.TopLevelLet (lb,arity,args_rev) ->
            let args_rev1 = FStar_List.rev_append args args_rev  in
            let n_args_rev = FStar_List.length args_rev1  in
            let n_univs = FStar_List.length lb.FStar_Syntax_Syntax.lbunivs
               in
            (debug cfg
               (fun uu____5697  ->
                  let uu____5698 =
                    FStar_Syntax_Print.lbname_to_string
                      lb.FStar_Syntax_Syntax.lbname
                     in
                  let uu____5700 = FStar_Util.string_of_int arity  in
                  let uu____5702 = FStar_Util.string_of_int n_args_rev  in
                  FStar_Util.print3
                    "Reached iapp for %s with arity %s and n_args = %s\n"
                    uu____5698 uu____5700 uu____5702);
             if n_args_rev >= arity
             then
               (let uu____5706 =
                  let uu____5719 =
                    let uu____5720 =
                      FStar_Syntax_Util.unascribe
                        lb.FStar_Syntax_Syntax.lbdef
                       in
                    uu____5720.FStar_Syntax_Syntax.n  in
                  match uu____5719 with
                  | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____5737) ->
                      (bs, body)
                  | uu____5770 -> ([], (lb.FStar_Syntax_Syntax.lbdef))  in
                match uu____5706 with
                | (bs,body) ->
                    if (n_univs + (FStar_List.length bs)) = arity
                    then
                      let uu____5811 =
                        FStar_Util.first_N (n_args_rev - arity) args_rev1  in
                      (match uu____5811 with
                       | (extra,args_rev2) ->
                           (debug cfg
                              (fun uu____5863  ->
                                 let uu____5864 =
                                   FStar_Syntax_Print.lbname_to_string
                                     lb.FStar_Syntax_Syntax.lbname
                                    in
                                 let uu____5866 =
                                   FStar_Syntax_Print.term_to_string body  in
                                 let uu____5868 =
                                   let uu____5870 =
                                     FStar_List.map
                                       (fun uu____5882  ->
                                          match uu____5882 with
                                          | (x,uu____5889) ->
                                              FStar_TypeChecker_NBETerm.t_to_string
                                                x) args_rev2
                                      in
                                   FStar_All.pipe_right uu____5870
                                     (FStar_String.concat ", ")
                                    in
                                 FStar_Util.print3
                                   "Reducing body of %s = %s,\n\twith args = %s\n"
                                   uu____5864 uu____5866 uu____5868);
                            (let t =
                               let uu____5897 =
                                 FStar_List.map FStar_Pervasives_Native.fst
                                   args_rev2
                                  in
                               translate cfg uu____5897 body  in
                             match extra with
                             | [] -> t
                             | uu____5908 ->
                                 iapp cfg t (FStar_List.rev extra))))
                    else
                      (let uu____5921 =
                         FStar_Util.first_N (n_args_rev - n_univs) args_rev1
                          in
                       match uu____5921 with
                       | (extra,univs) ->
                           let uu____5968 =
                             let uu____5969 =
                               FStar_List.map FStar_Pervasives_Native.fst
                                 univs
                                in
                             translate cfg uu____5969
                               lb.FStar_Syntax_Syntax.lbdef
                              in
                           iapp cfg uu____5968 (FStar_List.rev extra)))
             else
               FStar_All.pipe_left mk
                 (FStar_TypeChecker_NBETerm.TopLevelLet
                    (lb, arity, args_rev1)))
        | FStar_TypeChecker_NBETerm.TopLevelRec
            (lb,arity,decreases_list,args') ->
            let args1 = FStar_List.append args' args  in
            if (FStar_List.length args1) >= arity
            then
              let uu____6029 =
                should_reduce_recursive_definition args1 decreases_list  in
              (match uu____6029 with
               | (should_reduce,uu____6038,uu____6039) ->
                   if Prims.op_Negation should_reduce
                   then
                     let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname
                        in
                     (debug cfg
                        (fun uu____6047  ->
                           let uu____6048 =
                             FStar_Syntax_Print.fv_to_string fv  in
                           FStar_Util.print1
                             "Decided to not unfold recursive definition %s\n"
                             uu____6048);
                      (let uu____6051 =
                         let uu____6052 = FStar_Syntax_Syntax.range_of_fv fv
                            in
                         mk_rt uu____6052
                           (FStar_TypeChecker_NBETerm.FV (fv, [], []))
                          in
                       iapp cfg uu____6051 args1))
                   else
                     (debug cfg
                        (fun uu____6070  ->
                           let uu____6071 =
                             let uu____6073 =
                               FStar_Util.right lb.FStar_Syntax_Syntax.lbname
                                in
                             FStar_Syntax_Print.fv_to_string uu____6073  in
                           FStar_Util.print1
                             "Yes, Decided to unfold recursive definition %s\n"
                             uu____6071);
                      (let uu____6075 =
                         FStar_Util.first_N
                           (FStar_List.length lb.FStar_Syntax_Syntax.lbunivs)
                           args1
                          in
                       match uu____6075 with
                       | (univs,rest) ->
                           let uu____6122 =
                             let uu____6123 =
                               let uu____6126 =
                                 FStar_List.map FStar_Pervasives_Native.fst
                                   univs
                                  in
                               FStar_List.rev uu____6126  in
                             translate cfg uu____6123
                               lb.FStar_Syntax_Syntax.lbdef
                              in
                           iapp cfg uu____6122 rest)))
            else
              FStar_All.pipe_left mk
                (FStar_TypeChecker_NBETerm.TopLevelRec
                   (lb, arity, decreases_list, args1))
        | FStar_TypeChecker_NBETerm.LocalLetRec
            (i,lb,mutual_lbs,local_env,acc_args,remaining_arity,decreases_list)
            ->
            if remaining_arity = Prims.int_zero
            then
              FStar_All.pipe_left mk
                (FStar_TypeChecker_NBETerm.LocalLetRec
                   (i, lb, mutual_lbs, local_env,
                     (FStar_List.append acc_args args), remaining_arity,
                     decreases_list))
            else
              (let n_args = FStar_List.length args  in
               if n_args < remaining_arity
               then
                 FStar_All.pipe_left mk
                   (FStar_TypeChecker_NBETerm.LocalLetRec
                      (i, lb, mutual_lbs, local_env,
                        (FStar_List.append acc_args args),
                        (remaining_arity - n_args), decreases_list))
               else
                 (let args1 = FStar_List.append acc_args args  in
                  let uu____6244 =
                    should_reduce_recursive_definition args1 decreases_list
                     in
                  match uu____6244 with
                  | (should_reduce,uu____6253,uu____6254) ->
                      if Prims.op_Negation should_reduce
                      then
                        FStar_All.pipe_left mk
                          (FStar_TypeChecker_NBETerm.LocalLetRec
                             (i, lb, mutual_lbs, local_env, args1,
                               Prims.int_zero, decreases_list))
                      else
                        (let env = make_rec_env mutual_lbs local_env  in
                         debug cfg
                           (fun uu____6283  ->
                              (let uu____6285 =
                                 let uu____6287 =
                                   FStar_List.map
                                     FStar_TypeChecker_NBETerm.t_to_string
                                     env
                                    in
                                 FStar_String.concat ",\n\t " uu____6287  in
                               FStar_Util.print1
                                 "LocalLetRec Env = {\n\t%s\n}\n" uu____6285);
                              (let uu____6294 =
                                 let uu____6296 =
                                   FStar_List.map
                                     (fun uu____6308  ->
                                        match uu____6308 with
                                        | (t,uu____6315) ->
                                            FStar_TypeChecker_NBETerm.t_to_string
                                              t) args1
                                    in
                                 FStar_String.concat ",\n\t " uu____6296  in
                               FStar_Util.print1
                                 "LocalLetRec Args = {\n\t%s\n}\n" uu____6294));
                         (let uu____6318 =
                            translate cfg env lb.FStar_Syntax_Syntax.lbdef
                             in
                          iapp cfg uu____6318 args1))))
        | FStar_TypeChecker_NBETerm.Constant
            (FStar_TypeChecker_NBETerm.SConst (FStar_Const.Const_range_of ))
            ->
            (match args with
             | (a,uu____6320)::[] ->
                 mk_rt a.FStar_TypeChecker_NBETerm.nbe_r
                   (FStar_TypeChecker_NBETerm.Constant
                      (FStar_TypeChecker_NBETerm.Range
                         (a.FStar_TypeChecker_NBETerm.nbe_r)))
             | uu____6329 ->
                 let uu____6330 =
                   let uu____6332 = FStar_TypeChecker_NBETerm.t_to_string f
                      in
                   Prims.op_Hat "NBE ill-typed application: " uu____6332  in
                 failwith uu____6330)
        | FStar_TypeChecker_NBETerm.Constant
            (FStar_TypeChecker_NBETerm.SConst (FStar_Const.Const_set_range_of
            )) ->
            (match args with
             | (t,uu____6336)::({
                                  FStar_TypeChecker_NBETerm.nbe_t =
                                    FStar_TypeChecker_NBETerm.Constant
                                    (FStar_TypeChecker_NBETerm.Range r);
                                  FStar_TypeChecker_NBETerm.nbe_r =
                                    uu____6338;_},uu____6339)::[]
                 ->
                 let uu___934_6352 = t  in
                 {
                   FStar_TypeChecker_NBETerm.nbe_t =
                     (uu___934_6352.FStar_TypeChecker_NBETerm.nbe_t);
                   FStar_TypeChecker_NBETerm.nbe_r = r
                 }
             | uu____6353 ->
                 let uu____6354 =
                   let uu____6356 = FStar_TypeChecker_NBETerm.t_to_string f
                      in
                   Prims.op_Hat "NBE ill-typed application: " uu____6356  in
                 failwith uu____6354)
        | uu____6359 ->
            let uu____6360 =
              let uu____6362 = FStar_TypeChecker_NBETerm.t_to_string f  in
              Prims.op_Hat "NBE ill-typed application: " uu____6362  in
            failwith uu____6360

and (translate_fv :
  config ->
    FStar_TypeChecker_NBETerm.t Prims.list ->
      FStar_Syntax_Syntax.fv -> FStar_TypeChecker_NBETerm.t)
  =
  fun cfg  ->
    fun bs  ->
      fun fvar  ->
        let debug1 = debug cfg  in
        let qninfo =
          let uu____6379 = FStar_TypeChecker_Cfg.cfg_env cfg.core_cfg  in
          let uu____6380 = FStar_Syntax_Syntax.lid_of_fv fvar  in
          FStar_TypeChecker_Env.lookup_qname uu____6379 uu____6380  in
        let uu____6381 = (is_constr qninfo) || (is_constr_fv fvar)  in
        if uu____6381
        then FStar_TypeChecker_NBETerm.mkConstruct fvar [] []
        else
          (let uu____6390 =
             FStar_TypeChecker_Normalize.should_unfold cfg.core_cfg
               (fun uu____6392  ->
                  (cfg.core_cfg).FStar_TypeChecker_Cfg.reifying) fvar qninfo
              in
           match uu____6390 with
           | FStar_TypeChecker_Normalize.Should_unfold_fully  ->
               failwith "Not yet handled"
           | FStar_TypeChecker_Normalize.Should_unfold_no  ->
               (debug1
                  (fun uu____6399  ->
                     let uu____6400 = FStar_Syntax_Print.fv_to_string fvar
                        in
                     FStar_Util.print1 "(1) Decided to not unfold %s\n"
                       uu____6400);
                (let uu____6403 =
                   FStar_TypeChecker_Cfg.find_prim_step cfg.core_cfg fvar  in
                 match uu____6403 with
                 | FStar_Pervasives_Native.Some prim_step when
                     prim_step.FStar_TypeChecker_Cfg.strong_reduction_ok ->
                     let arity =
                       prim_step.FStar_TypeChecker_Cfg.arity +
                         prim_step.FStar_TypeChecker_Cfg.univ_arity
                        in
                     (debug1
                        (fun uu____6414  ->
                           let uu____6415 =
                             FStar_Syntax_Print.fv_to_string fvar  in
                           FStar_Util.print1 "Found a primop %s\n" uu____6415);
                      (let uu____6418 =
                         let uu____6419 =
                           let uu____6452 =
                             let f uu____6485 =
                               let uu____6487 =
                                 FStar_Syntax_Syntax.new_bv
                                   FStar_Pervasives_Native.None
                                   FStar_Syntax_Syntax.t_unit
                                  in
                               (uu____6487, FStar_Pervasives_Native.None)  in
                             let uu____6490 =
                               let uu____6501 = FStar_Common.tabulate arity f
                                  in
                               ([], uu____6501, FStar_Pervasives_Native.None)
                                in
                             FStar_Util.Inl uu____6490  in
                           ((fun args_rev  ->
                               let args' =
                                 map_rev FStar_TypeChecker_NBETerm.as_arg
                                   args_rev
                                  in
                               let callbacks =
                                 {
                                   FStar_TypeChecker_NBETerm.iapp =
                                     (iapp cfg);
                                   FStar_TypeChecker_NBETerm.translate =
                                     (translate cfg bs)
                                 }  in
                               let uu____6575 =
                                 prim_step.FStar_TypeChecker_Cfg.interpretation_nbe
                                   callbacks args'
                                  in
                               match uu____6575 with
                               | FStar_Pervasives_Native.Some x ->
                                   (debug1
                                      (fun uu____6586  ->
                                         let uu____6587 =
                                           FStar_Syntax_Print.fv_to_string
                                             fvar
                                            in
                                         let uu____6589 =
                                           FStar_TypeChecker_NBETerm.t_to_string
                                             x
                                            in
                                         FStar_Util.print2
                                           "Primitive operator %s returned %s\n"
                                           uu____6587 uu____6589);
                                    x)
                               | FStar_Pervasives_Native.None  ->
                                   (debug1
                                      (fun uu____6597  ->
                                         let uu____6598 =
                                           FStar_Syntax_Print.fv_to_string
                                             fvar
                                            in
                                         FStar_Util.print1
                                           "Primitive operator %s failed\n"
                                           uu____6598);
                                    (let uu____6601 =
                                       FStar_TypeChecker_NBETerm.mkFV fvar []
                                         []
                                        in
                                     iapp cfg uu____6601 args'))),
                             uu____6452, arity)
                            in
                         FStar_TypeChecker_NBETerm.Lam uu____6419  in
                       FStar_All.pipe_left mk_t uu____6418))
                 | FStar_Pervasives_Native.Some uu____6606 ->
                     (debug1
                        (fun uu____6612  ->
                           let uu____6613 =
                             FStar_Syntax_Print.fv_to_string fvar  in
                           FStar_Util.print1 "(2) Decided to not unfold %s\n"
                             uu____6613);
                      FStar_TypeChecker_NBETerm.mkFV fvar [] [])
                 | uu____6620 ->
                     (debug1
                        (fun uu____6628  ->
                           let uu____6629 =
                             FStar_Syntax_Print.fv_to_string fvar  in
                           FStar_Util.print1 "(3) Decided to not unfold %s\n"
                             uu____6629);
                      FStar_TypeChecker_NBETerm.mkFV fvar [] [])))
           | FStar_TypeChecker_Normalize.Should_unfold_reify  ->
               let t =
                 let is_qninfo_visible =
                   let uu____6639 =
                     FStar_TypeChecker_Env.lookup_definition_qninfo
                       (cfg.core_cfg).FStar_TypeChecker_Cfg.delta_level
                       (fvar.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                       qninfo
                      in
                   FStar_Option.isSome uu____6639  in
                 if is_qninfo_visible
                 then
                   match qninfo with
                   | FStar_Pervasives_Native.Some
                       (FStar_Util.Inr
                        ({
                           FStar_Syntax_Syntax.sigel =
                             FStar_Syntax_Syntax.Sig_let ((is_rec,lbs),names);
                           FStar_Syntax_Syntax.sigrng = uu____6654;
                           FStar_Syntax_Syntax.sigquals = uu____6655;
                           FStar_Syntax_Syntax.sigmeta = uu____6656;
                           FStar_Syntax_Syntax.sigattrs = uu____6657;
                           FStar_Syntax_Syntax.sigopts = uu____6658;_},_us_opt),_rng)
                       ->
                       (debug1
                          (fun uu____6728  ->
                             let uu____6729 =
                               FStar_Syntax_Print.fv_to_string fvar  in
                             FStar_Util.print1 "(1) Decided to unfold %s\n"
                               uu____6729);
                        (let lbm = find_let lbs fvar  in
                         match lbm with
                         | FStar_Pervasives_Native.Some lb ->
                             if
                               is_rec &&
                                 ((cfg.core_cfg).FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta
                             then
                               let uu____6737 = let_rec_arity lb  in
                               (match uu____6737 with
                                | (ar,lst) ->
                                    let uu____6756 =
                                      let uu____6761 =
                                        FStar_Syntax_Syntax.range_of_fv fvar
                                         in
                                      mk_rt uu____6761  in
                                    FStar_All.pipe_left uu____6756
                                      (FStar_TypeChecker_NBETerm.TopLevelRec
                                         (lb, ar, lst, [])))
                             else translate_letbinding cfg bs lb
                         | FStar_Pervasives_Native.None  ->
                             failwith "Could not find let binding"))
                   | uu____6779 ->
                       (debug1
                          (fun uu____6785  ->
                             let uu____6786 =
                               FStar_Syntax_Print.fv_to_string fvar  in
                             FStar_Util.print1
                               "(1) qninfo is None for (%s)\n" uu____6786);
                        FStar_TypeChecker_NBETerm.mkFV fvar [] [])
                 else
                   (debug1
                      (fun uu____6800  ->
                         let uu____6801 =
                           FStar_Syntax_Print.fv_to_string fvar  in
                         FStar_Util.print1
                           "(1) qninfo is not visible at this level (%s)\n"
                           uu____6801);
                    FStar_TypeChecker_NBETerm.mkFV fvar [] [])
                  in
               (cache_add cfg fvar t; t)
           | FStar_TypeChecker_Normalize.Should_unfold_yes  ->
               let t =
                 let is_qninfo_visible =
                   let uu____6812 =
                     FStar_TypeChecker_Env.lookup_definition_qninfo
                       (cfg.core_cfg).FStar_TypeChecker_Cfg.delta_level
                       (fvar.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                       qninfo
                      in
                   FStar_Option.isSome uu____6812  in
                 if is_qninfo_visible
                 then
                   match qninfo with
                   | FStar_Pervasives_Native.Some
                       (FStar_Util.Inr
                        ({
                           FStar_Syntax_Syntax.sigel =
                             FStar_Syntax_Syntax.Sig_let ((is_rec,lbs),names);
                           FStar_Syntax_Syntax.sigrng = uu____6827;
                           FStar_Syntax_Syntax.sigquals = uu____6828;
                           FStar_Syntax_Syntax.sigmeta = uu____6829;
                           FStar_Syntax_Syntax.sigattrs = uu____6830;
                           FStar_Syntax_Syntax.sigopts = uu____6831;_},_us_opt),_rng)
                       ->
                       (debug1
                          (fun uu____6901  ->
                             let uu____6902 =
                               FStar_Syntax_Print.fv_to_string fvar  in
                             FStar_Util.print1 "(1) Decided to unfold %s\n"
                               uu____6902);
                        (let lbm = find_let lbs fvar  in
                         match lbm with
                         | FStar_Pervasives_Native.Some lb ->
                             if
                               is_rec &&
                                 ((cfg.core_cfg).FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta
                             then
                               let uu____6910 = let_rec_arity lb  in
                               (match uu____6910 with
                                | (ar,lst) ->
                                    let uu____6929 =
                                      let uu____6934 =
                                        FStar_Syntax_Syntax.range_of_fv fvar
                                         in
                                      mk_rt uu____6934  in
                                    FStar_All.pipe_left uu____6929
                                      (FStar_TypeChecker_NBETerm.TopLevelRec
                                         (lb, ar, lst, [])))
                             else translate_letbinding cfg bs lb
                         | FStar_Pervasives_Native.None  ->
                             failwith "Could not find let binding"))
                   | uu____6952 ->
                       (debug1
                          (fun uu____6958  ->
                             let uu____6959 =
                               FStar_Syntax_Print.fv_to_string fvar  in
                             FStar_Util.print1
                               "(1) qninfo is None for (%s)\n" uu____6959);
                        FStar_TypeChecker_NBETerm.mkFV fvar [] [])
                 else
                   (debug1
                      (fun uu____6973  ->
                         let uu____6974 =
                           FStar_Syntax_Print.fv_to_string fvar  in
                         FStar_Util.print1
                           "(1) qninfo is not visible at this level (%s)\n"
                           uu____6974);
                    FStar_TypeChecker_NBETerm.mkFV fvar [] [])
                  in
               (cache_add cfg fvar t; t))

and (translate_letbinding :
  config ->
    FStar_TypeChecker_NBETerm.t Prims.list ->
      FStar_Syntax_Syntax.letbinding -> FStar_TypeChecker_NBETerm.t)
  =
  fun cfg  ->
    fun bs  ->
      fun lb  ->
        let debug1 = debug cfg  in
        let us = lb.FStar_Syntax_Syntax.lbunivs  in
        let uu____6998 =
          FStar_Syntax_Util.arrow_formals lb.FStar_Syntax_Syntax.lbtyp  in
        match uu____6998 with
        | (formals,uu____7006) ->
            let arity = (FStar_List.length us) + (FStar_List.length formals)
               in
            if arity = Prims.int_zero
            then translate cfg bs lb.FStar_Syntax_Syntax.lbdef
            else
              (let uu____7024 =
                 FStar_Util.is_right lb.FStar_Syntax_Syntax.lbname  in
               if uu____7024
               then
                 (debug1
                    (fun uu____7034  ->
                       let uu____7035 =
                         FStar_Syntax_Print.lbname_to_string
                           lb.FStar_Syntax_Syntax.lbname
                          in
                       let uu____7037 = FStar_Util.string_of_int arity  in
                       FStar_Util.print2
                         "Making TopLevelLet for %s with arity %s\n"
                         uu____7035 uu____7037);
                  (let uu____7040 =
                     let uu____7045 =
                       FStar_Syntax_Syntax.range_of_lbname
                         lb.FStar_Syntax_Syntax.lbname
                        in
                     mk_rt uu____7045  in
                   FStar_All.pipe_left uu____7040
                     (FStar_TypeChecker_NBETerm.TopLevelLet (lb, arity, []))))
               else translate cfg bs lb.FStar_Syntax_Syntax.lbdef)

and (mkRec :
  Prims.int ->
    FStar_Syntax_Syntax.letbinding ->
      FStar_Syntax_Syntax.letbinding Prims.list ->
        FStar_TypeChecker_NBETerm.t Prims.list -> FStar_TypeChecker_NBETerm.t)
  =
  fun i  ->
    fun b  ->
      fun bs  ->
        fun env  ->
          let uu____7068 = let_rec_arity b  in
          match uu____7068 with
          | (ar,ar_lst) ->
              FStar_All.pipe_left mk_t
                (FStar_TypeChecker_NBETerm.LocalLetRec
                   (i, b, bs, env, [], ar, ar_lst))

and (make_rec_env :
  FStar_Syntax_Syntax.letbinding Prims.list ->
    FStar_TypeChecker_NBETerm.t Prims.list ->
      FStar_TypeChecker_NBETerm.t Prims.list)
  =
  fun all_lbs  ->
    fun all_outer_bs  ->
      let rec_bindings =
        FStar_List.mapi
          (fun i  -> fun lb  -> mkRec i lb all_lbs all_outer_bs) all_lbs
         in
      FStar_List.rev_append rec_bindings all_outer_bs

and (translate_constant :
  FStar_Syntax_Syntax.sconst -> FStar_TypeChecker_NBETerm.constant) =
  fun c  ->
    match c with
    | FStar_Const.Const_unit  -> FStar_TypeChecker_NBETerm.Unit
    | FStar_Const.Const_bool b -> FStar_TypeChecker_NBETerm.Bool b
    | FStar_Const.Const_int (s,FStar_Pervasives_Native.None ) ->
        let uu____7138 = FStar_BigInt.big_int_of_string s  in
        FStar_TypeChecker_NBETerm.Int uu____7138
    | FStar_Const.Const_string (s,r) ->
        FStar_TypeChecker_NBETerm.String (s, r)
    | FStar_Const.Const_char c1 -> FStar_TypeChecker_NBETerm.Char c1
    | FStar_Const.Const_range r -> FStar_TypeChecker_NBETerm.Range r
    | uu____7147 -> FStar_TypeChecker_NBETerm.SConst c

and (readback_comp :
  config -> FStar_TypeChecker_NBETerm.comp -> FStar_Syntax_Syntax.comp) =
  fun cfg  ->
    fun c  ->
      let c' =
        match c with
        | FStar_TypeChecker_NBETerm.Tot (typ,u) ->
            let uu____7157 =
              let uu____7166 = readback cfg typ  in (uu____7166, u)  in
            FStar_Syntax_Syntax.Total uu____7157
        | FStar_TypeChecker_NBETerm.GTot (typ,u) ->
            let uu____7179 =
              let uu____7188 = readback cfg typ  in (uu____7188, u)  in
            FStar_Syntax_Syntax.GTotal uu____7179
        | FStar_TypeChecker_NBETerm.Comp ctyp ->
            let uu____7196 = readback_comp_typ cfg ctyp  in
            FStar_Syntax_Syntax.Comp uu____7196
         in
      FStar_Syntax_Syntax.mk c' FStar_Range.dummyRange

and (translate_comp_typ :
  config ->
    FStar_TypeChecker_NBETerm.t Prims.list ->
      FStar_Syntax_Syntax.comp_typ -> FStar_TypeChecker_NBETerm.comp_typ)
  =
  fun cfg  ->
    fun bs  ->
      fun c  ->
        let uu____7202 = c  in
        match uu____7202 with
        | { FStar_Syntax_Syntax.comp_univs = comp_univs;
            FStar_Syntax_Syntax.effect_name = effect_name;
            FStar_Syntax_Syntax.result_typ = result_typ;
            FStar_Syntax_Syntax.effect_args = effect_args;
            FStar_Syntax_Syntax.flags = flags;_} ->
            let uu____7222 =
              FStar_List.map (translate_univ cfg bs) comp_univs  in
            let uu____7223 = translate cfg bs result_typ  in
            let uu____7224 =
              FStar_List.map
                (fun x  ->
                   let uu____7252 =
                     translate cfg bs (FStar_Pervasives_Native.fst x)  in
                   (uu____7252, (FStar_Pervasives_Native.snd x))) effect_args
               in
            let uu____7259 = FStar_List.map (translate_flag cfg bs) flags  in
            {
              FStar_TypeChecker_NBETerm.comp_univs = uu____7222;
              FStar_TypeChecker_NBETerm.effect_name = effect_name;
              FStar_TypeChecker_NBETerm.result_typ = uu____7223;
              FStar_TypeChecker_NBETerm.effect_args = uu____7224;
              FStar_TypeChecker_NBETerm.flags = uu____7259
            }

and (readback_comp_typ :
  config ->
    FStar_TypeChecker_NBETerm.comp_typ -> FStar_Syntax_Syntax.comp_typ)
  =
  fun cfg  ->
    fun c  ->
      let uu____7264 = readback cfg c.FStar_TypeChecker_NBETerm.result_typ
         in
      let uu____7267 =
        FStar_List.map
          (fun x  ->
             let uu____7293 = readback cfg (FStar_Pervasives_Native.fst x)
                in
             (uu____7293, (FStar_Pervasives_Native.snd x)))
          c.FStar_TypeChecker_NBETerm.effect_args
         in
      let uu____7294 =
        FStar_List.map (readback_flag cfg) c.FStar_TypeChecker_NBETerm.flags
         in
      {
        FStar_Syntax_Syntax.comp_univs =
          (c.FStar_TypeChecker_NBETerm.comp_univs);
        FStar_Syntax_Syntax.effect_name =
          (c.FStar_TypeChecker_NBETerm.effect_name);
        FStar_Syntax_Syntax.result_typ = uu____7264;
        FStar_Syntax_Syntax.effect_args = uu____7267;
        FStar_Syntax_Syntax.flags = uu____7294
      }

and (translate_residual_comp :
  config ->
    FStar_TypeChecker_NBETerm.t Prims.list ->
      FStar_Syntax_Syntax.residual_comp ->
        FStar_TypeChecker_NBETerm.residual_comp)
  =
  fun cfg  ->
    fun bs  ->
      fun c  ->
        let uu____7302 = c  in
        match uu____7302 with
        | { FStar_Syntax_Syntax.residual_effect = residual_effect;
            FStar_Syntax_Syntax.residual_typ = residual_typ;
            FStar_Syntax_Syntax.residual_flags = residual_flags;_} ->
            let uu____7312 =
              if
                ((cfg.core_cfg).FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.for_extraction
              then FStar_Pervasives_Native.None
              else FStar_Util.map_opt residual_typ (translate cfg bs)  in
            let uu____7322 =
              FStar_List.map (translate_flag cfg bs) residual_flags  in
            {
              FStar_TypeChecker_NBETerm.residual_effect = residual_effect;
              FStar_TypeChecker_NBETerm.residual_typ = uu____7312;
              FStar_TypeChecker_NBETerm.residual_flags = uu____7322
            }

and (readback_residual_comp :
  config ->
    FStar_TypeChecker_NBETerm.residual_comp ->
      FStar_Syntax_Syntax.residual_comp)
  =
  fun cfg  ->
    fun c  ->
      let uu____7327 =
        FStar_Util.map_opt c.FStar_TypeChecker_NBETerm.residual_typ
          (fun x  ->
             debug cfg
               (fun uu____7338  ->
                  let uu____7339 = FStar_TypeChecker_NBETerm.t_to_string x
                     in
                  FStar_Util.print1 "Reading back residualtype %s\n"
                    uu____7339);
             readback cfg x)
         in
      let uu____7342 =
        FStar_List.map (readback_flag cfg)
          c.FStar_TypeChecker_NBETerm.residual_flags
         in
      {
        FStar_Syntax_Syntax.residual_effect =
          (c.FStar_TypeChecker_NBETerm.residual_effect);
        FStar_Syntax_Syntax.residual_typ = uu____7327;
        FStar_Syntax_Syntax.residual_flags = uu____7342
      }

and (translate_flag :
  config ->
    FStar_TypeChecker_NBETerm.t Prims.list ->
      FStar_Syntax_Syntax.cflag -> FStar_TypeChecker_NBETerm.cflag)
  =
  fun cfg  ->
    fun bs  ->
      fun f  ->
        match f with
        | FStar_Syntax_Syntax.TOTAL  -> FStar_TypeChecker_NBETerm.TOTAL
        | FStar_Syntax_Syntax.MLEFFECT  -> FStar_TypeChecker_NBETerm.MLEFFECT
        | FStar_Syntax_Syntax.RETURN  -> FStar_TypeChecker_NBETerm.RETURN
        | FStar_Syntax_Syntax.PARTIAL_RETURN  ->
            FStar_TypeChecker_NBETerm.PARTIAL_RETURN
        | FStar_Syntax_Syntax.SOMETRIVIAL  ->
            FStar_TypeChecker_NBETerm.SOMETRIVIAL
        | FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION  ->
            FStar_TypeChecker_NBETerm.TRIVIAL_POSTCONDITION
        | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  ->
            FStar_TypeChecker_NBETerm.SHOULD_NOT_INLINE
        | FStar_Syntax_Syntax.LEMMA  -> FStar_TypeChecker_NBETerm.LEMMA
        | FStar_Syntax_Syntax.CPS  -> FStar_TypeChecker_NBETerm.CPS
        | FStar_Syntax_Syntax.DECREASES tm ->
            let uu____7353 = translate cfg bs tm  in
            FStar_TypeChecker_NBETerm.DECREASES uu____7353

and (readback_flag :
  config -> FStar_TypeChecker_NBETerm.cflag -> FStar_Syntax_Syntax.cflag) =
  fun cfg  ->
    fun f  ->
      match f with
      | FStar_TypeChecker_NBETerm.TOTAL  -> FStar_Syntax_Syntax.TOTAL
      | FStar_TypeChecker_NBETerm.MLEFFECT  -> FStar_Syntax_Syntax.MLEFFECT
      | FStar_TypeChecker_NBETerm.RETURN  -> FStar_Syntax_Syntax.RETURN
      | FStar_TypeChecker_NBETerm.PARTIAL_RETURN  ->
          FStar_Syntax_Syntax.PARTIAL_RETURN
      | FStar_TypeChecker_NBETerm.SOMETRIVIAL  ->
          FStar_Syntax_Syntax.SOMETRIVIAL
      | FStar_TypeChecker_NBETerm.TRIVIAL_POSTCONDITION  ->
          FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION
      | FStar_TypeChecker_NBETerm.SHOULD_NOT_INLINE  ->
          FStar_Syntax_Syntax.SHOULD_NOT_INLINE
      | FStar_TypeChecker_NBETerm.LEMMA  -> FStar_Syntax_Syntax.LEMMA
      | FStar_TypeChecker_NBETerm.CPS  -> FStar_Syntax_Syntax.CPS
      | FStar_TypeChecker_NBETerm.DECREASES t ->
          let uu____7357 = readback cfg t  in
          FStar_Syntax_Syntax.DECREASES uu____7357

and (translate_monadic :
  (FStar_Syntax_Syntax.monad_name * FStar_Syntax_Syntax.term'
    FStar_Syntax_Syntax.syntax) ->
    config ->
      FStar_TypeChecker_NBETerm.t Prims.list ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
          FStar_TypeChecker_NBETerm.t)
  =
  fun uu____7360  ->
    fun cfg  ->
      fun bs  ->
        fun e  ->
          match uu____7360 with
          | (m,ty) ->
              let e1 = FStar_Syntax_Util.unascribe e  in
              (match e1.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                   let uu____7398 =
                     let uu____7407 =
                       FStar_TypeChecker_Env.norm_eff_name
                         (cfg.core_cfg).FStar_TypeChecker_Cfg.tcenv m
                        in
                     FStar_TypeChecker_Env.effect_decl_opt
                       (cfg.core_cfg).FStar_TypeChecker_Cfg.tcenv uu____7407
                      in
                   (match uu____7398 with
                    | FStar_Pervasives_Native.None  ->
                        let uu____7414 =
                          let uu____7416 = FStar_Ident.string_of_lid m  in
                          FStar_Util.format1
                            "Effect declaration not found: %s" uu____7416
                           in
                        failwith uu____7414
                    | FStar_Pervasives_Native.Some (ed,q) ->
                        let cfg' = reifying_false cfg  in
                        let body_lam =
                          let body_rc =
                            {
                              FStar_Syntax_Syntax.residual_effect = m;
                              FStar_Syntax_Syntax.residual_typ =
                                (FStar_Pervasives_Native.Some ty);
                              FStar_Syntax_Syntax.residual_flags = []
                            }  in
                          let uu____7438 =
                            let uu____7439 =
                              let uu____7458 =
                                let uu____7467 =
                                  let uu____7474 =
                                    FStar_Util.left
                                      lb.FStar_Syntax_Syntax.lbname
                                     in
                                  (uu____7474, FStar_Pervasives_Native.None)
                                   in
                                [uu____7467]  in
                              (uu____7458, body,
                                (FStar_Pervasives_Native.Some body_rc))
                               in
                            FStar_Syntax_Syntax.Tm_abs uu____7439  in
                          FStar_Syntax_Syntax.mk uu____7438
                            body.FStar_Syntax_Syntax.pos
                           in
                        let maybe_range_arg =
                          let uu____7508 =
                            FStar_Util.for_some
                              (FStar_Syntax_Util.attr_eq
                                 FStar_Syntax_Util.dm4f_bind_range_attr)
                              ed.FStar_Syntax_Syntax.eff_attrs
                             in
                          if uu____7508
                          then
                            let uu____7517 =
                              let uu____7522 =
                                let uu____7523 =
                                  FStar_TypeChecker_Cfg.embed_simple
                                    FStar_Syntax_Embeddings.e_range
                                    lb.FStar_Syntax_Syntax.lbpos
                                    lb.FStar_Syntax_Syntax.lbpos
                                   in
                                translate cfg [] uu____7523  in
                              (uu____7522, FStar_Pervasives_Native.None)  in
                            let uu____7524 =
                              let uu____7531 =
                                let uu____7536 =
                                  let uu____7537 =
                                    FStar_TypeChecker_Cfg.embed_simple
                                      FStar_Syntax_Embeddings.e_range
                                      body.FStar_Syntax_Syntax.pos
                                      body.FStar_Syntax_Syntax.pos
                                     in
                                  translate cfg [] uu____7537  in
                                (uu____7536, FStar_Pervasives_Native.None)
                                 in
                              [uu____7531]  in
                            uu____7517 :: uu____7524
                          else []  in
                        let t =
                          let uu____7557 =
                            let uu____7558 =
                              let uu____7559 =
                                let uu____7560 =
                                  let uu____7561 =
                                    let uu____7568 =
                                      FStar_All.pipe_right ed
                                        FStar_Syntax_Util.get_bind_repr
                                       in
                                    FStar_All.pipe_right uu____7568
                                      FStar_Util.must
                                     in
                                  FStar_All.pipe_right uu____7561
                                    FStar_Pervasives_Native.snd
                                   in
                                FStar_Syntax_Util.un_uinst uu____7560  in
                              translate cfg' [] uu____7559  in
                            let uu____7589 =
                              let uu____7590 =
                                let uu____7595 =
                                  FStar_All.pipe_left mk_t
                                    (FStar_TypeChecker_NBETerm.Univ
                                       FStar_Syntax_Syntax.U_unknown)
                                   in
                                (uu____7595, FStar_Pervasives_Native.None)
                                 in
                              let uu____7596 =
                                let uu____7603 =
                                  let uu____7608 =
                                    FStar_All.pipe_left mk_t
                                      (FStar_TypeChecker_NBETerm.Univ
                                         FStar_Syntax_Syntax.U_unknown)
                                     in
                                  (uu____7608, FStar_Pervasives_Native.None)
                                   in
                                [uu____7603]  in
                              uu____7590 :: uu____7596  in
                            iapp cfg uu____7558 uu____7589  in
                          let uu____7621 =
                            let uu____7622 =
                              let uu____7629 =
                                let uu____7634 =
                                  translate cfg' bs
                                    lb.FStar_Syntax_Syntax.lbtyp
                                   in
                                (uu____7634, FStar_Pervasives_Native.None)
                                 in
                              let uu____7635 =
                                let uu____7642 =
                                  let uu____7647 = translate cfg' bs ty  in
                                  (uu____7647, FStar_Pervasives_Native.None)
                                   in
                                [uu____7642]  in
                              uu____7629 :: uu____7635  in
                            let uu____7660 =
                              let uu____7667 =
                                let uu____7674 =
                                  let uu____7681 =
                                    let uu____7686 =
                                      translate cfg bs
                                        lb.FStar_Syntax_Syntax.lbdef
                                       in
                                    (uu____7686,
                                      FStar_Pervasives_Native.None)
                                     in
                                  let uu____7687 =
                                    let uu____7694 =
                                      let uu____7701 =
                                        let uu____7706 =
                                          translate cfg bs body_lam  in
                                        (uu____7706,
                                          FStar_Pervasives_Native.None)
                                         in
                                      [uu____7701]  in
                                    ((mk_t FStar_TypeChecker_NBETerm.Unknown),
                                      FStar_Pervasives_Native.None) ::
                                      uu____7694
                                     in
                                  uu____7681 :: uu____7687  in
                                ((mk_t FStar_TypeChecker_NBETerm.Unknown),
                                  FStar_Pervasives_Native.None) :: uu____7674
                                 in
                              FStar_List.append maybe_range_arg uu____7667
                               in
                            FStar_List.append uu____7622 uu____7660  in
                          iapp cfg uu____7557 uu____7621  in
                        (debug cfg
                           (fun uu____7738  ->
                              let uu____7739 =
                                FStar_TypeChecker_NBETerm.t_to_string t  in
                              FStar_Util.print1 "translate_monadic: %s\n"
                                uu____7739);
                         t))
               | FStar_Syntax_Syntax.Tm_app
                   ({
                      FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                        (FStar_Const.Const_reflect uu____7742);
                      FStar_Syntax_Syntax.pos = uu____7743;
                      FStar_Syntax_Syntax.vars = uu____7744;_},(e2,uu____7746)::[])
                   ->
                   let uu____7785 = reifying_false cfg  in
                   translate uu____7785 bs e2
               | FStar_Syntax_Syntax.Tm_app (head,args) ->
                   (debug cfg
                      (fun uu____7816  ->
                         let uu____7817 =
                           FStar_Syntax_Print.term_to_string head  in
                         let uu____7819 =
                           FStar_Syntax_Print.args_to_string args  in
                         FStar_Util.print2
                           "translate_monadic app (%s) @ (%s)\n" uu____7817
                           uu____7819);
                    (let fallback1 uu____7827 = translate cfg bs e1  in
                     let fallback2 uu____7833 =
                       let uu____7834 = reifying_false cfg  in
                       let uu____7835 =
                         FStar_Syntax_Syntax.mk
                           (FStar_Syntax_Syntax.Tm_meta
                              (e1,
                                (FStar_Syntax_Syntax.Meta_monadic (m, ty))))
                           e1.FStar_Syntax_Syntax.pos
                          in
                       translate uu____7834 bs uu____7835  in
                     let uu____7840 =
                       let uu____7841 = FStar_Syntax_Util.un_uinst head  in
                       uu____7841.FStar_Syntax_Syntax.n  in
                     match uu____7840 with
                     | FStar_Syntax_Syntax.Tm_fvar fv ->
                         let lid = FStar_Syntax_Syntax.lid_of_fv fv  in
                         let qninfo =
                           FStar_TypeChecker_Env.lookup_qname
                             (cfg.core_cfg).FStar_TypeChecker_Cfg.tcenv lid
                            in
                         let uu____7847 =
                           let uu____7849 =
                             FStar_TypeChecker_Env.is_action
                               (cfg.core_cfg).FStar_TypeChecker_Cfg.tcenv lid
                              in
                           Prims.op_Negation uu____7849  in
                         if uu____7847
                         then fallback1 ()
                         else
                           (let uu____7854 =
                              let uu____7856 =
                                FStar_TypeChecker_Env.lookup_definition_qninfo
                                  (cfg.core_cfg).FStar_TypeChecker_Cfg.delta_level
                                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                  qninfo
                                 in
                              FStar_Option.isNone uu____7856  in
                            if uu____7854
                            then fallback2 ()
                            else
                              (let e2 =
                                 let uu____7871 =
                                   FStar_Syntax_Util.mk_reify head  in
                                 FStar_Syntax_Syntax.mk_Tm_app uu____7871
                                   args e1.FStar_Syntax_Syntax.pos
                                  in
                               let uu____7872 = reifying_false cfg  in
                               translate uu____7872 bs e2))
                     | uu____7873 -> fallback1 ()))
               | FStar_Syntax_Syntax.Tm_match (sc,branches) ->
                   let branches1 =
                     FStar_All.pipe_right branches
                       (FStar_List.map
                          (fun uu____7994  ->
                             match uu____7994 with
                             | (pat,wopt,tm) ->
                                 let uu____8042 =
                                   FStar_Syntax_Util.mk_reify tm  in
                                 (pat, wopt, uu____8042)))
                      in
                   let tm =
                     FStar_Syntax_Syntax.mk
                       (FStar_Syntax_Syntax.Tm_match (sc, branches1))
                       e1.FStar_Syntax_Syntax.pos
                      in
                   let uu____8074 = reifying_false cfg  in
                   translate uu____8074 bs tm
               | FStar_Syntax_Syntax.Tm_meta
                   (t,FStar_Syntax_Syntax.Meta_monadic uu____8076) ->
                   translate_monadic (m, ty) cfg bs e1
               | FStar_Syntax_Syntax.Tm_meta
                   (t,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,ty'))
                   -> translate_monadic_lift (msrc, mtgt, ty') cfg bs e1
               | uu____8103 ->
                   let uu____8104 =
                     let uu____8106 = FStar_Syntax_Print.tag_of_term e1  in
                     FStar_Util.format1
                       "Unexpected case in translate_monadic: %s" uu____8106
                      in
                   failwith uu____8104)

and (translate_monadic_lift :
  (FStar_Syntax_Syntax.monad_name * FStar_Syntax_Syntax.monad_name *
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax) ->
    config ->
      FStar_TypeChecker_NBETerm.t Prims.list ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
          FStar_TypeChecker_NBETerm.t)
  =
  fun uu____8109  ->
    fun cfg  ->
      fun bs  ->
        fun e  ->
          match uu____8109 with
          | (msrc,mtgt,ty) ->
              let e1 = FStar_Syntax_Util.unascribe e  in
              let uu____8133 =
                (FStar_Syntax_Util.is_pure_effect msrc) ||
                  (FStar_Syntax_Util.is_div_effect msrc)
                 in
              if uu____8133
              then
                let ed =
                  let uu____8137 =
                    FStar_TypeChecker_Env.norm_eff_name
                      (cfg.core_cfg).FStar_TypeChecker_Cfg.tcenv mtgt
                     in
                  FStar_TypeChecker_Env.get_effect_decl
                    (cfg.core_cfg).FStar_TypeChecker_Cfg.tcenv uu____8137
                   in
                let ret =
                  let uu____8139 =
                    let uu____8140 =
                      let uu____8143 =
                        let uu____8144 =
                          let uu____8151 =
                            FStar_All.pipe_right ed
                              FStar_Syntax_Util.get_return_repr
                             in
                          FStar_All.pipe_right uu____8151 FStar_Util.must  in
                        FStar_All.pipe_right uu____8144
                          FStar_Pervasives_Native.snd
                         in
                      FStar_Syntax_Subst.compress uu____8143  in
                    uu____8140.FStar_Syntax_Syntax.n  in
                  match uu____8139 with
                  | FStar_Syntax_Syntax.Tm_uinst (ret,uu____8197::[]) ->
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_uinst
                           (ret, [FStar_Syntax_Syntax.U_unknown]))
                        e1.FStar_Syntax_Syntax.pos
                  | uu____8204 ->
                      failwith "NYI: Reification of indexed effect (NBE)"
                   in
                let cfg' = reifying_false cfg  in
                let t =
                  let uu____8208 =
                    let uu____8209 = translate cfg' [] ret  in
                    let uu____8210 =
                      let uu____8211 =
                        let uu____8216 =
                          FStar_All.pipe_left mk_t
                            (FStar_TypeChecker_NBETerm.Univ
                               FStar_Syntax_Syntax.U_unknown)
                           in
                        (uu____8216, FStar_Pervasives_Native.None)  in
                      [uu____8211]  in
                    iapp cfg' uu____8209 uu____8210  in
                  let uu____8225 =
                    let uu____8226 =
                      let uu____8231 = translate cfg' bs ty  in
                      (uu____8231, FStar_Pervasives_Native.None)  in
                    let uu____8232 =
                      let uu____8239 =
                        let uu____8244 = translate cfg' bs e1  in
                        (uu____8244, FStar_Pervasives_Native.None)  in
                      [uu____8239]  in
                    uu____8226 :: uu____8232  in
                  iapp cfg' uu____8208 uu____8225  in
                (debug cfg
                   (fun uu____8260  ->
                      let uu____8261 =
                        FStar_TypeChecker_NBETerm.t_to_string t  in
                      FStar_Util.print1 "translate_monadic_lift(1): %s\n"
                        uu____8261);
                 t)
              else
                (let uu____8266 =
                   FStar_TypeChecker_Env.monad_leq
                     (cfg.core_cfg).FStar_TypeChecker_Cfg.tcenv msrc mtgt
                    in
                 match uu____8266 with
                 | FStar_Pervasives_Native.None  ->
                     let uu____8269 =
                       let uu____8271 = FStar_Ident.string_of_lid msrc  in
                       let uu____8273 = FStar_Ident.string_of_lid mtgt  in
                       FStar_Util.format2
                         "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                         uu____8271 uu____8273
                        in
                     failwith uu____8269
                 | FStar_Pervasives_Native.Some
                     { FStar_TypeChecker_Env.msource = uu____8276;
                       FStar_TypeChecker_Env.mtarget = uu____8277;
                       FStar_TypeChecker_Env.mlift =
                         { FStar_TypeChecker_Env.mlift_wp = uu____8278;
                           FStar_TypeChecker_Env.mlift_term =
                             FStar_Pervasives_Native.None ;_};_}
                     ->
                     let uu____8298 =
                       let uu____8300 = FStar_Ident.string_of_lid msrc  in
                       let uu____8302 = FStar_Ident.string_of_lid mtgt  in
                       FStar_Util.format2
                         "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
                         uu____8300 uu____8302
                        in
                     failwith uu____8298
                 | FStar_Pervasives_Native.Some
                     { FStar_TypeChecker_Env.msource = uu____8305;
                       FStar_TypeChecker_Env.mtarget = uu____8306;
                       FStar_TypeChecker_Env.mlift =
                         { FStar_TypeChecker_Env.mlift_wp = uu____8307;
                           FStar_TypeChecker_Env.mlift_term =
                             FStar_Pervasives_Native.Some lift;_};_}
                     ->
                     let lift_lam =
                       let x =
                         FStar_Syntax_Syntax.new_bv
                           FStar_Pervasives_Native.None
                           FStar_Syntax_Syntax.tun
                          in
                       let uu____8341 =
                         let uu____8344 = FStar_Syntax_Syntax.bv_to_name x
                            in
                         lift FStar_Syntax_Syntax.U_unknown ty uu____8344  in
                       FStar_Syntax_Util.abs
                         [(x, FStar_Pervasives_Native.None)] uu____8341
                         FStar_Pervasives_Native.None
                        in
                     let cfg' = reifying_false cfg  in
                     let t =
                       let uu____8361 = translate cfg' [] lift_lam  in
                       let uu____8362 =
                         let uu____8363 =
                           let uu____8368 = translate cfg bs e1  in
                           (uu____8368, FStar_Pervasives_Native.None)  in
                         [uu____8363]  in
                       iapp cfg uu____8361 uu____8362  in
                     (debug cfg
                        (fun uu____8380  ->
                           let uu____8381 =
                             FStar_TypeChecker_NBETerm.t_to_string t  in
                           FStar_Util.print1
                             "translate_monadic_lift(2): %s\n" uu____8381);
                      t))

and (readback :
  config -> FStar_TypeChecker_NBETerm.t -> FStar_Syntax_Syntax.term) =
  fun cfg  ->
    fun x  ->
      let debug1 = debug cfg  in
      let readback_args cfg1 args =
        map_rev
          (fun uu____8435  ->
             match uu____8435 with
             | (x1,q) ->
                 let uu____8446 = readback cfg1 x1  in (uu____8446, q)) args
         in
      let with_range t =
        let uu___1255_8459 = t  in
        {
          FStar_Syntax_Syntax.n = (uu___1255_8459.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = (x.FStar_TypeChecker_NBETerm.nbe_r);
          FStar_Syntax_Syntax.vars =
            (uu___1255_8459.FStar_Syntax_Syntax.vars)
        }  in
      let mk t = FStar_Syntax_Syntax.mk t x.FStar_TypeChecker_NBETerm.nbe_r
         in
      debug1
        (fun uu____8475  ->
           let uu____8476 = FStar_TypeChecker_NBETerm.t_to_string x  in
           FStar_Util.print1 "Readback: %s\n" uu____8476);
      (match x.FStar_TypeChecker_NBETerm.nbe_t with
       | FStar_TypeChecker_NBETerm.Univ u ->
           failwith "Readback of universes should not occur"
       | FStar_TypeChecker_NBETerm.Unknown  ->
           FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
             x.FStar_TypeChecker_NBETerm.nbe_r
       | FStar_TypeChecker_NBETerm.Constant (FStar_TypeChecker_NBETerm.Unit )
           -> with_range FStar_Syntax_Syntax.unit_const
       | FStar_TypeChecker_NBETerm.Constant (FStar_TypeChecker_NBETerm.Bool
           (true )) -> with_range FStar_Syntax_Util.exp_true_bool
       | FStar_TypeChecker_NBETerm.Constant (FStar_TypeChecker_NBETerm.Bool
           (false )) -> with_range FStar_Syntax_Util.exp_false_bool
       | FStar_TypeChecker_NBETerm.Constant (FStar_TypeChecker_NBETerm.Int i)
           ->
           let uu____8484 =
             let uu____8487 = FStar_BigInt.string_of_big_int i  in
             FStar_Syntax_Util.exp_int uu____8487  in
           with_range uu____8484
       | FStar_TypeChecker_NBETerm.Constant (FStar_TypeChecker_NBETerm.String
           (s,r)) ->
           mk
             (FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_string (s, r)))
       | FStar_TypeChecker_NBETerm.Constant (FStar_TypeChecker_NBETerm.Char
           c) ->
           let uu____8496 = FStar_Syntax_Util.exp_char c  in
           with_range uu____8496
       | FStar_TypeChecker_NBETerm.Constant (FStar_TypeChecker_NBETerm.Range
           r) ->
           FStar_TypeChecker_Cfg.embed_simple FStar_Syntax_Embeddings.e_range
             x.FStar_TypeChecker_NBETerm.nbe_r r
       | FStar_TypeChecker_NBETerm.Constant (FStar_TypeChecker_NBETerm.SConst
           c) -> mk (FStar_Syntax_Syntax.Tm_constant c)
       | FStar_TypeChecker_NBETerm.Meta (t,m) ->
           let uu____8507 =
             let uu____8508 =
               let uu____8515 = readback cfg t  in
               let uu____8518 = FStar_Thunk.force m  in
               (uu____8515, uu____8518)  in
             FStar_Syntax_Syntax.Tm_meta uu____8508  in
           mk uu____8507
       | FStar_TypeChecker_NBETerm.Type_t u ->
           mk (FStar_Syntax_Syntax.Tm_type u)
       | FStar_TypeChecker_NBETerm.Lam (f,binders,arity) ->
           let uu____8577 =
             match binders with
             | FStar_Util.Inl (ctx,binders1,rc) ->
                 let uu____8625 =
                   FStar_List.fold_left
                     (fun uu____8679  ->
                        fun uu____8680  ->
                          match (uu____8679, uu____8680) with
                          | ((ctx1,binders_rev,accus_rev),(x1,q)) ->
                              let tnorm =
                                let uu____8805 =
                                  translate cfg ctx1
                                    x1.FStar_Syntax_Syntax.sort
                                   in
                                readback cfg uu____8805  in
                              let x2 =
                                let uu___1313_8807 =
                                  FStar_Syntax_Syntax.freshen_bv x1  in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___1313_8807.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___1313_8807.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = tnorm
                                }  in
                              let ax = FStar_TypeChecker_NBETerm.mkAccuVar x2
                                 in
                              let ctx2 = ax :: ctx1  in
                              (ctx2, ((x2, q) :: binders_rev), (ax ::
                                accus_rev))) (ctx, [], []) binders1
                    in
                 (match uu____8625 with
                  | (ctx1,binders_rev,accus_rev) ->
                      let rc1 =
                        match rc with
                        | FStar_Pervasives_Native.None  ->
                            FStar_Pervasives_Native.None
                        | FStar_Pervasives_Native.Some rc1 ->
                            let uu____8893 =
                              let uu____8894 =
                                translate_residual_comp cfg ctx1 rc1  in
                              readback_residual_comp cfg uu____8894  in
                            FStar_Pervasives_Native.Some uu____8893
                         in
                      ((FStar_List.rev binders_rev), accus_rev, rc1))
             | FStar_Util.Inr args ->
                 let uu____8928 =
                   FStar_List.fold_right
                     (fun uu____8969  ->
                        fun uu____8970  ->
                          match (uu____8969, uu____8970) with
                          | ((t,uu____9022),(binders1,accus)) ->
                              let x1 =
                                let uu____9064 = readback cfg t  in
                                FStar_Syntax_Syntax.new_bv
                                  FStar_Pervasives_Native.None uu____9064
                                 in
                              let uu____9065 =
                                let uu____9068 =
                                  FStar_TypeChecker_NBETerm.mkAccuVar x1  in
                                uu____9068 :: accus  in
                              (((x1, FStar_Pervasives_Native.None) ::
                                binders1), uu____9065)) args ([], [])
                    in
                 (match uu____8928 with
                  | (binders1,accus) ->
                      (binders1, (FStar_List.rev accus),
                        FStar_Pervasives_Native.None))
              in
           (match uu____8577 with
            | (binders1,accus_rev,rc) ->
                let body =
                  let uu____9151 = f accus_rev  in readback cfg uu____9151
                   in
                let uu____9152 = FStar_Syntax_Util.abs binders1 body rc  in
                with_range uu____9152)
       | FStar_TypeChecker_NBETerm.Refinement (f,targ) ->
           if
             ((cfg.core_cfg).FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.for_extraction
           then
             let uu____9178 =
               let uu____9179 = targ ()  in
               FStar_Pervasives_Native.fst uu____9179  in
             readback cfg uu____9178
           else
             (let x1 =
                let uu____9187 =
                  let uu____9188 =
                    let uu____9189 = targ ()  in
                    FStar_Pervasives_Native.fst uu____9189  in
                  readback cfg uu____9188  in
                FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                  uu____9187
                 in
              let body =
                let uu____9195 =
                  let uu____9196 = FStar_TypeChecker_NBETerm.mkAccuVar x1  in
                  f uu____9196  in
                readback cfg uu____9195  in
              let refinement = FStar_Syntax_Util.refine x1 body  in
              let uu____9200 =
                if
                  ((cfg.core_cfg).FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.simplify
                then
                  FStar_TypeChecker_Common.simplify
                    ((cfg.core_cfg).FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                    refinement
                else refinement  in
              with_range uu____9200)
       | FStar_TypeChecker_NBETerm.Reflect t ->
           let tm = readback cfg t  in
           let uu____9210 = FStar_Syntax_Util.mk_reflect tm  in
           with_range uu____9210
       | FStar_TypeChecker_NBETerm.Arrow (FStar_Util.Inl f) ->
           let uu____9228 = FStar_Thunk.force f  in with_range uu____9228
       | FStar_TypeChecker_NBETerm.Arrow (FStar_Util.Inr (args,c)) ->
           let binders =
             FStar_List.map
               (fun uu____9277  ->
                  match uu____9277 with
                  | (t,q) ->
                      let t1 = readback cfg t  in
                      let x1 =
                        FStar_Syntax_Syntax.new_bv
                          FStar_Pervasives_Native.None t1
                         in
                      (x1, q)) args
              in
           let c1 = readback_comp cfg c  in
           let uu____9291 = FStar_Syntax_Util.arrow binders c1  in
           with_range uu____9291
       | FStar_TypeChecker_NBETerm.Construct (fv,us,args) ->
           let args1 =
             map_rev
               (fun uu____9332  ->
                  match uu____9332 with
                  | (x1,q) ->
                      let uu____9343 = readback cfg x1  in (uu____9343, q))
               args
              in
           let fv1 =
             let uu____9347 = FStar_Syntax_Syntax.range_of_fv fv  in
             FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
               uu____9347
              in
           let app =
             let uu____9351 =
               FStar_Syntax_Syntax.mk_Tm_uinst fv1 (FStar_List.rev us)  in
             FStar_Syntax_Util.mk_app uu____9351 args1  in
           with_range app
       | FStar_TypeChecker_NBETerm.FV (fv,us,args) ->
           let args1 =
             map_rev
               (fun uu____9392  ->
                  match uu____9392 with
                  | (x1,q) ->
                      let uu____9403 = readback cfg x1  in (uu____9403, q))
               args
              in
           let fv1 =
             FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
               FStar_Range.dummyRange
              in
           let app =
             let uu____9410 =
               FStar_Syntax_Syntax.mk_Tm_uinst fv1 (FStar_List.rev us)  in
             FStar_Syntax_Util.mk_app uu____9410 args1  in
           let uu____9413 =
             if
               ((cfg.core_cfg).FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.simplify
             then
               FStar_TypeChecker_Common.simplify
                 ((cfg.core_cfg).FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                 app
             else app  in
           with_range uu____9413
       | FStar_TypeChecker_NBETerm.Accu (FStar_TypeChecker_NBETerm.Var bv,[])
           ->
           let uu____9432 = FStar_Syntax_Syntax.bv_to_name bv  in
           with_range uu____9432
       | FStar_TypeChecker_NBETerm.Accu
           (FStar_TypeChecker_NBETerm.Var bv,args) ->
           let args1 = readback_args cfg args  in
           let app =
             let uu____9459 = FStar_Syntax_Syntax.bv_to_name bv  in
             FStar_Syntax_Util.mk_app uu____9459 args1  in
           let uu____9462 =
             if
               ((cfg.core_cfg).FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.simplify
             then
               FStar_TypeChecker_Common.simplify
                 ((cfg.core_cfg).FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                 app
             else app  in
           with_range uu____9462
       | FStar_TypeChecker_NBETerm.Accu
           (FStar_TypeChecker_NBETerm.Match (scrut,make_branches),args) ->
           let args1 = readback_args cfg args  in
           let head =
             let scrut_new = readback cfg scrut  in
             let branches_new = make_branches ()  in
             FStar_Syntax_Syntax.mk
               (FStar_Syntax_Syntax.Tm_match (scrut_new, branches_new))
               scrut.FStar_TypeChecker_NBETerm.nbe_r
              in
           let app = FStar_Syntax_Util.mk_app head args1  in
           let uu____9530 =
             if
               ((cfg.core_cfg).FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.simplify
             then
               FStar_TypeChecker_Common.simplify
                 ((cfg.core_cfg).FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                 app
             else app  in
           with_range uu____9530
       | FStar_TypeChecker_NBETerm.Accu
           (FStar_TypeChecker_NBETerm.UnreducedLet
            (var,typ,defn,body,lb),args)
           ->
           let typ1 =
             let uu____9569 = FStar_Thunk.force typ  in
             readback cfg uu____9569  in
           let defn1 =
             let uu____9571 = FStar_Thunk.force defn  in
             readback cfg uu____9571  in
           let body1 =
             let uu____9573 =
               let uu____9574 = FStar_Thunk.force body  in
               readback cfg uu____9574  in
             FStar_Syntax_Subst.close [(var, FStar_Pervasives_Native.None)]
               uu____9573
              in
           let lbname =
             let uu____9594 =
               let uu___1432_9595 =
                 FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
               {
                 FStar_Syntax_Syntax.ppname =
                   (uu___1432_9595.FStar_Syntax_Syntax.ppname);
                 FStar_Syntax_Syntax.index =
                   (uu___1432_9595.FStar_Syntax_Syntax.index);
                 FStar_Syntax_Syntax.sort = typ1
               }  in
             FStar_Util.Inl uu____9594  in
           let lb1 =
             let uu___1435_9597 = lb  in
             {
               FStar_Syntax_Syntax.lbname = lbname;
               FStar_Syntax_Syntax.lbunivs =
                 (uu___1435_9597.FStar_Syntax_Syntax.lbunivs);
               FStar_Syntax_Syntax.lbtyp = typ1;
               FStar_Syntax_Syntax.lbeff =
                 (uu___1435_9597.FStar_Syntax_Syntax.lbeff);
               FStar_Syntax_Syntax.lbdef = defn1;
               FStar_Syntax_Syntax.lbattrs =
                 (uu___1435_9597.FStar_Syntax_Syntax.lbattrs);
               FStar_Syntax_Syntax.lbpos =
                 (uu___1435_9597.FStar_Syntax_Syntax.lbpos)
             }  in
           let hd =
             FStar_Syntax_Syntax.mk
               (FStar_Syntax_Syntax.Tm_let ((false, [lb1]), body1))
               FStar_Range.dummyRange
              in
           let args1 = readback_args cfg args  in
           let uu____9621 = FStar_Syntax_Util.mk_app hd args1  in
           with_range uu____9621
       | FStar_TypeChecker_NBETerm.Accu
           (FStar_TypeChecker_NBETerm.UnreducedLetRec
            (vars_typs_defns,body,lbs),args)
           ->
           let lbs1 =
             FStar_List.map2
               (fun uu____9678  ->
                  fun lb  ->
                    match uu____9678 with
                    | (v,t,d) ->
                        let t1 = readback cfg t  in
                        let def = readback cfg d  in
                        let v1 =
                          let uu___1455_9692 = v  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___1455_9692.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___1455_9692.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t1
                          }  in
                        let uu___1458_9693 = lb  in
                        {
                          FStar_Syntax_Syntax.lbname = (FStar_Util.Inl v1);
                          FStar_Syntax_Syntax.lbunivs =
                            (uu___1458_9693.FStar_Syntax_Syntax.lbunivs);
                          FStar_Syntax_Syntax.lbtyp = t1;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___1458_9693.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = def;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___1458_9693.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___1458_9693.FStar_Syntax_Syntax.lbpos)
                        }) vars_typs_defns lbs
              in
           let body1 = readback cfg body  in
           let uu____9695 = FStar_Syntax_Subst.close_let_rec lbs1 body1  in
           (match uu____9695 with
            | (lbs2,body2) ->
                let hd =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_let ((true, lbs2), body2))
                    FStar_Range.dummyRange
                   in
                let args1 = readback_args cfg args  in
                let uu____9731 = FStar_Syntax_Util.mk_app hd args1  in
                with_range uu____9731)
       | FStar_TypeChecker_NBETerm.Accu
           (FStar_TypeChecker_NBETerm.UVar f,args) ->
           let hd = FStar_Thunk.force f  in
           let args1 = readback_args cfg args  in
           let uu____9758 = FStar_Syntax_Util.mk_app hd args1  in
           with_range uu____9758
       | FStar_TypeChecker_NBETerm.TopLevelLet (lb,arity,args_rev) ->
           let n_univs = FStar_List.length lb.FStar_Syntax_Syntax.lbunivs  in
           let n_args = FStar_List.length args_rev  in
           let uu____9784 = FStar_Util.first_N (n_args - n_univs) args_rev
              in
           (match uu____9784 with
            | (args_rev1,univs) ->
                let uu____9831 =
                  let uu____9832 =
                    let uu____9833 =
                      FStar_List.map FStar_Pervasives_Native.fst univs  in
                    translate cfg uu____9833 lb.FStar_Syntax_Syntax.lbdef  in
                  iapp cfg uu____9832 (FStar_List.rev args_rev1)  in
                readback cfg uu____9831)
       | FStar_TypeChecker_NBETerm.TopLevelRec
           (lb,uu____9845,uu____9846,args) ->
           let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
           let head =
             FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
               FStar_Range.dummyRange
              in
           let args1 =
             FStar_List.map
               (fun uu____9891  ->
                  match uu____9891 with
                  | (t,q) ->
                      let uu____9902 = readback cfg t  in (uu____9902, q))
               args
              in
           let uu____9903 = FStar_Syntax_Util.mk_app head args1  in
           with_range uu____9903
       | FStar_TypeChecker_NBETerm.LocalLetRec
           (i,uu____9907,lbs,bs,args,_ar,_ar_lst) ->
           let lbnames =
             FStar_List.map
               (fun lb  ->
                  let uu____9949 =
                    let uu____9951 =
                      let uu____9952 =
                        FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                      uu____9952.FStar_Syntax_Syntax.ppname  in
                    FStar_Ident.string_of_id uu____9951  in
                  FStar_Syntax_Syntax.gen_bv uu____9949
                    FStar_Pervasives_Native.None lb.FStar_Syntax_Syntax.lbtyp)
               lbs
              in
           let let_rec_env =
             let uu____9956 =
               FStar_List.map
                 (fun x1  ->
                    let uu____9962 = FStar_Syntax_Syntax.range_of_bv x1  in
                    mk_rt uu____9962
                      (FStar_TypeChecker_NBETerm.Accu
                         ((FStar_TypeChecker_NBETerm.Var x1), []))) lbnames
                in
             FStar_List.rev_append uu____9956 bs  in
           let lbs1 =
             FStar_List.map2
               (fun lb  ->
                  fun lbname  ->
                    let lbdef =
                      let uu____9984 =
                        translate cfg let_rec_env
                          lb.FStar_Syntax_Syntax.lbdef
                         in
                      readback cfg uu____9984  in
                    let lbtyp =
                      let uu____9986 =
                        translate cfg bs lb.FStar_Syntax_Syntax.lbtyp  in
                      readback cfg uu____9986  in
                    let uu___1513_9987 = lb  in
                    {
                      FStar_Syntax_Syntax.lbname = (FStar_Util.Inl lbname);
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___1513_9987.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = lbtyp;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___1513_9987.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = lbdef;
                      FStar_Syntax_Syntax.lbattrs =
                        (uu___1513_9987.FStar_Syntax_Syntax.lbattrs);
                      FStar_Syntax_Syntax.lbpos =
                        (uu___1513_9987.FStar_Syntax_Syntax.lbpos)
                    }) lbs lbnames
              in
           let body =
             let uu____9989 = FStar_List.nth lbnames i  in
             FStar_Syntax_Syntax.bv_to_name uu____9989  in
           let uu____9990 = FStar_Syntax_Subst.close_let_rec lbs1 body  in
           (match uu____9990 with
            | (lbs2,body1) ->
                let head =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_let ((true, lbs2), body1))
                    FStar_Range.dummyRange
                   in
                let args1 =
                  FStar_List.map
                    (fun uu____10038  ->
                       match uu____10038 with
                       | (x1,q) ->
                           let uu____10049 = readback cfg x1  in
                           (uu____10049, q)) args
                   in
                let uu____10050 = FStar_Syntax_Util.mk_app head args1  in
                with_range uu____10050)
       | FStar_TypeChecker_NBETerm.Quote (qt,qi) ->
           mk (FStar_Syntax_Syntax.Tm_quoted (qt, qi))
       | FStar_TypeChecker_NBETerm.Lazy (FStar_Util.Inl li,uu____10058) ->
           mk (FStar_Syntax_Syntax.Tm_lazy li)
       | FStar_TypeChecker_NBETerm.Lazy (uu____10075,thunk) ->
           let uu____10097 = FStar_Thunk.force thunk  in
           readback cfg uu____10097)

type step =
  | Primops 
  | UnfoldUntil of FStar_Syntax_Syntax.delta_depth 
  | UnfoldOnly of FStar_Ident.lid Prims.list 
  | UnfoldAttr of FStar_Ident.lid Prims.list 
  | UnfoldTac 
  | Reify 
let (uu___is_Primops : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Primops  -> true | uu____10126 -> false
  
let (uu___is_UnfoldUntil : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldUntil _0 -> true | uu____10138 -> false
  
let (__proj__UnfoldUntil__item___0 : step -> FStar_Syntax_Syntax.delta_depth)
  = fun projectee  -> match projectee with | UnfoldUntil _0 -> _0 
let (uu___is_UnfoldOnly : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldOnly _0 -> true | uu____10159 -> false
  
let (__proj__UnfoldOnly__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldOnly _0 -> _0 
let (uu___is_UnfoldAttr : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldAttr _0 -> true | uu____10186 -> false
  
let (__proj__UnfoldAttr__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldAttr _0 -> _0 
let (uu___is_UnfoldTac : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldTac  -> true | uu____10210 -> false
  
let (uu___is_Reify : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reify  -> true | uu____10221 -> false
  
let (step_as_normalizer_step : step -> FStar_TypeChecker_Env.step) =
  fun uu___2_10228  ->
    match uu___2_10228 with
    | Primops  -> FStar_TypeChecker_Env.Primops
    | UnfoldUntil d -> FStar_TypeChecker_Env.UnfoldUntil d
    | UnfoldOnly lids -> FStar_TypeChecker_Env.UnfoldOnly lids
    | UnfoldAttr lids -> FStar_TypeChecker_Env.UnfoldAttr lids
    | UnfoldTac  -> FStar_TypeChecker_Env.UnfoldTac
    | Reify  -> FStar_TypeChecker_Env.Reify
  
let (reduce_application :
  FStar_TypeChecker_Cfg.cfg ->
    FStar_TypeChecker_NBETerm.t ->
      FStar_TypeChecker_NBETerm.args -> FStar_TypeChecker_NBETerm.t)
  =
  fun cfg  ->
    fun t  ->
      fun args  ->
        let uu____10252 = new_config cfg  in iapp uu____10252 t args
  
let (normalize :
  FStar_TypeChecker_Cfg.primitive_step Prims.list ->
    FStar_TypeChecker_Env.step Prims.list ->
      FStar_TypeChecker_Env.env ->
        FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun psteps  ->
    fun steps  ->
      fun env  ->
        fun e  ->
          let cfg = FStar_TypeChecker_Cfg.config' psteps steps env  in
          let cfg1 =
            let uu___1559_10284 = cfg  in
            {
              FStar_TypeChecker_Cfg.steps =
                (let uu___1561_10287 = cfg.FStar_TypeChecker_Cfg.steps  in
                 {
                   FStar_TypeChecker_Cfg.beta =
                     (uu___1561_10287.FStar_TypeChecker_Cfg.beta);
                   FStar_TypeChecker_Cfg.iota =
                     (uu___1561_10287.FStar_TypeChecker_Cfg.iota);
                   FStar_TypeChecker_Cfg.zeta =
                     (uu___1561_10287.FStar_TypeChecker_Cfg.zeta);
                   FStar_TypeChecker_Cfg.zeta_full =
                     (uu___1561_10287.FStar_TypeChecker_Cfg.zeta_full);
                   FStar_TypeChecker_Cfg.weak =
                     (uu___1561_10287.FStar_TypeChecker_Cfg.weak);
                   FStar_TypeChecker_Cfg.hnf =
                     (uu___1561_10287.FStar_TypeChecker_Cfg.hnf);
                   FStar_TypeChecker_Cfg.primops =
                     (uu___1561_10287.FStar_TypeChecker_Cfg.primops);
                   FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                     (uu___1561_10287.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                   FStar_TypeChecker_Cfg.unfold_until =
                     (uu___1561_10287.FStar_TypeChecker_Cfg.unfold_until);
                   FStar_TypeChecker_Cfg.unfold_only =
                     (uu___1561_10287.FStar_TypeChecker_Cfg.unfold_only);
                   FStar_TypeChecker_Cfg.unfold_fully =
                     (uu___1561_10287.FStar_TypeChecker_Cfg.unfold_fully);
                   FStar_TypeChecker_Cfg.unfold_attr =
                     (uu___1561_10287.FStar_TypeChecker_Cfg.unfold_attr);
                   FStar_TypeChecker_Cfg.unfold_tac =
                     (uu___1561_10287.FStar_TypeChecker_Cfg.unfold_tac);
                   FStar_TypeChecker_Cfg.pure_subterms_within_computations =
                     (uu___1561_10287.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                   FStar_TypeChecker_Cfg.simplify =
                     (uu___1561_10287.FStar_TypeChecker_Cfg.simplify);
                   FStar_TypeChecker_Cfg.erase_universes =
                     (uu___1561_10287.FStar_TypeChecker_Cfg.erase_universes);
                   FStar_TypeChecker_Cfg.allow_unbound_universes =
                     (uu___1561_10287.FStar_TypeChecker_Cfg.allow_unbound_universes);
                   FStar_TypeChecker_Cfg.reify_ = true;
                   FStar_TypeChecker_Cfg.compress_uvars =
                     (uu___1561_10287.FStar_TypeChecker_Cfg.compress_uvars);
                   FStar_TypeChecker_Cfg.no_full_norm =
                     (uu___1561_10287.FStar_TypeChecker_Cfg.no_full_norm);
                   FStar_TypeChecker_Cfg.check_no_uvars =
                     (uu___1561_10287.FStar_TypeChecker_Cfg.check_no_uvars);
                   FStar_TypeChecker_Cfg.unmeta =
                     (uu___1561_10287.FStar_TypeChecker_Cfg.unmeta);
                   FStar_TypeChecker_Cfg.unascribe =
                     (uu___1561_10287.FStar_TypeChecker_Cfg.unascribe);
                   FStar_TypeChecker_Cfg.in_full_norm_request =
                     (uu___1561_10287.FStar_TypeChecker_Cfg.in_full_norm_request);
                   FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                     (uu___1561_10287.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                   FStar_TypeChecker_Cfg.nbe_step =
                     (uu___1561_10287.FStar_TypeChecker_Cfg.nbe_step);
                   FStar_TypeChecker_Cfg.for_extraction =
                     (uu___1561_10287.FStar_TypeChecker_Cfg.for_extraction)
                 });
              FStar_TypeChecker_Cfg.tcenv =
                (uu___1559_10284.FStar_TypeChecker_Cfg.tcenv);
              FStar_TypeChecker_Cfg.debug =
                (uu___1559_10284.FStar_TypeChecker_Cfg.debug);
              FStar_TypeChecker_Cfg.delta_level =
                (uu___1559_10284.FStar_TypeChecker_Cfg.delta_level);
              FStar_TypeChecker_Cfg.primitive_steps =
                (uu___1559_10284.FStar_TypeChecker_Cfg.primitive_steps);
              FStar_TypeChecker_Cfg.strong =
                (uu___1559_10284.FStar_TypeChecker_Cfg.strong);
              FStar_TypeChecker_Cfg.memoize_lazy =
                (uu___1559_10284.FStar_TypeChecker_Cfg.memoize_lazy);
              FStar_TypeChecker_Cfg.normalize_pure_lets =
                (uu___1559_10284.FStar_TypeChecker_Cfg.normalize_pure_lets);
              FStar_TypeChecker_Cfg.reifying =
                (uu___1559_10284.FStar_TypeChecker_Cfg.reifying)
            }  in
          (let uu____10290 =
             (FStar_TypeChecker_Env.debug env (FStar_Options.Other "NBETop"))
               ||
               (FStar_TypeChecker_Env.debug env (FStar_Options.Other "NBE"))
              in
           if uu____10290
           then
             let uu____10295 = FStar_Syntax_Print.term_to_string e  in
             FStar_Util.print1 "Calling NBE with (%s) {\n" uu____10295
           else ());
          (let cfg2 = new_config cfg1  in
           let r =
             let uu____10302 = translate cfg2 [] e  in
             readback cfg2 uu____10302  in
           (let uu____10304 =
              (FStar_TypeChecker_Env.debug env (FStar_Options.Other "NBETop"))
                ||
                (FStar_TypeChecker_Env.debug env (FStar_Options.Other "NBE"))
               in
            if uu____10304
            then
              let uu____10309 = FStar_Syntax_Print.term_to_string r  in
              FStar_Util.print1 "}\nNBE returned (%s)\n" uu____10309
            else ());
           r)
  
let (normalize_for_unit_test :
  FStar_TypeChecker_Env.step Prims.list ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun steps  ->
    fun env  ->
      fun e  ->
        let cfg = FStar_TypeChecker_Cfg.config steps env  in
        let cfg1 =
          let uu___1577_10336 = cfg  in
          {
            FStar_TypeChecker_Cfg.steps =
              (let uu___1579_10339 = cfg.FStar_TypeChecker_Cfg.steps  in
               {
                 FStar_TypeChecker_Cfg.beta =
                   (uu___1579_10339.FStar_TypeChecker_Cfg.beta);
                 FStar_TypeChecker_Cfg.iota =
                   (uu___1579_10339.FStar_TypeChecker_Cfg.iota);
                 FStar_TypeChecker_Cfg.zeta =
                   (uu___1579_10339.FStar_TypeChecker_Cfg.zeta);
                 FStar_TypeChecker_Cfg.zeta_full =
                   (uu___1579_10339.FStar_TypeChecker_Cfg.zeta_full);
                 FStar_TypeChecker_Cfg.weak =
                   (uu___1579_10339.FStar_TypeChecker_Cfg.weak);
                 FStar_TypeChecker_Cfg.hnf =
                   (uu___1579_10339.FStar_TypeChecker_Cfg.hnf);
                 FStar_TypeChecker_Cfg.primops =
                   (uu___1579_10339.FStar_TypeChecker_Cfg.primops);
                 FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                   (uu___1579_10339.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                 FStar_TypeChecker_Cfg.unfold_until =
                   (uu___1579_10339.FStar_TypeChecker_Cfg.unfold_until);
                 FStar_TypeChecker_Cfg.unfold_only =
                   (uu___1579_10339.FStar_TypeChecker_Cfg.unfold_only);
                 FStar_TypeChecker_Cfg.unfold_fully =
                   (uu___1579_10339.FStar_TypeChecker_Cfg.unfold_fully);
                 FStar_TypeChecker_Cfg.unfold_attr =
                   (uu___1579_10339.FStar_TypeChecker_Cfg.unfold_attr);
                 FStar_TypeChecker_Cfg.unfold_tac =
                   (uu___1579_10339.FStar_TypeChecker_Cfg.unfold_tac);
                 FStar_TypeChecker_Cfg.pure_subterms_within_computations =
                   (uu___1579_10339.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                 FStar_TypeChecker_Cfg.simplify =
                   (uu___1579_10339.FStar_TypeChecker_Cfg.simplify);
                 FStar_TypeChecker_Cfg.erase_universes =
                   (uu___1579_10339.FStar_TypeChecker_Cfg.erase_universes);
                 FStar_TypeChecker_Cfg.allow_unbound_universes =
                   (uu___1579_10339.FStar_TypeChecker_Cfg.allow_unbound_universes);
                 FStar_TypeChecker_Cfg.reify_ = true;
                 FStar_TypeChecker_Cfg.compress_uvars =
                   (uu___1579_10339.FStar_TypeChecker_Cfg.compress_uvars);
                 FStar_TypeChecker_Cfg.no_full_norm =
                   (uu___1579_10339.FStar_TypeChecker_Cfg.no_full_norm);
                 FStar_TypeChecker_Cfg.check_no_uvars =
                   (uu___1579_10339.FStar_TypeChecker_Cfg.check_no_uvars);
                 FStar_TypeChecker_Cfg.unmeta =
                   (uu___1579_10339.FStar_TypeChecker_Cfg.unmeta);
                 FStar_TypeChecker_Cfg.unascribe =
                   (uu___1579_10339.FStar_TypeChecker_Cfg.unascribe);
                 FStar_TypeChecker_Cfg.in_full_norm_request =
                   (uu___1579_10339.FStar_TypeChecker_Cfg.in_full_norm_request);
                 FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                   (uu___1579_10339.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                 FStar_TypeChecker_Cfg.nbe_step =
                   (uu___1579_10339.FStar_TypeChecker_Cfg.nbe_step);
                 FStar_TypeChecker_Cfg.for_extraction =
                   (uu___1579_10339.FStar_TypeChecker_Cfg.for_extraction)
               });
            FStar_TypeChecker_Cfg.tcenv =
              (uu___1577_10336.FStar_TypeChecker_Cfg.tcenv);
            FStar_TypeChecker_Cfg.debug =
              (uu___1577_10336.FStar_TypeChecker_Cfg.debug);
            FStar_TypeChecker_Cfg.delta_level =
              (uu___1577_10336.FStar_TypeChecker_Cfg.delta_level);
            FStar_TypeChecker_Cfg.primitive_steps =
              (uu___1577_10336.FStar_TypeChecker_Cfg.primitive_steps);
            FStar_TypeChecker_Cfg.strong =
              (uu___1577_10336.FStar_TypeChecker_Cfg.strong);
            FStar_TypeChecker_Cfg.memoize_lazy =
              (uu___1577_10336.FStar_TypeChecker_Cfg.memoize_lazy);
            FStar_TypeChecker_Cfg.normalize_pure_lets =
              (uu___1577_10336.FStar_TypeChecker_Cfg.normalize_pure_lets);
            FStar_TypeChecker_Cfg.reifying =
              (uu___1577_10336.FStar_TypeChecker_Cfg.reifying)
          }  in
        let cfg2 = new_config cfg1  in
        debug cfg2
          (fun uu____10345  ->
             let uu____10346 = FStar_Syntax_Print.term_to_string e  in
             FStar_Util.print1 "Calling NBE with (%s) {\n" uu____10346);
        (let r =
           let uu____10350 = translate cfg2 [] e  in
           readback cfg2 uu____10350  in
         debug cfg2
           (fun uu____10354  ->
              let uu____10355 = FStar_Syntax_Print.term_to_string r  in
              FStar_Util.print1 "}\nNBE returned (%s)\n" uu____10355);
         r)
  