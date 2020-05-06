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
    let uu____416 = FStar_Syntax_Util.let_rec_arity b  in
    match uu____416 with
    | (ar,maybe_lst) ->
        (match maybe_lst with
         | FStar_Pervasives_Native.None  ->
             let uu____460 =
               FStar_Common.tabulate ar (fun uu____466  -> true)  in
             (ar, uu____460)
         | FStar_Pervasives_Native.Some lst -> (ar, lst))
  
let (debug_term : FStar_Syntax_Syntax.term -> unit) =
  fun t  ->
    let uu____490 = FStar_Syntax_Print.term_to_string t  in
    FStar_Util.print1 "%s\n" uu____490
  
let (debug_sigmap : FStar_Syntax_Syntax.sigelt FStar_Util.smap -> unit) =
  fun m  ->
    FStar_Util.smap_fold m
      (fun k  ->
         fun v  ->
           fun u  ->
             let uu____511 = FStar_Syntax_Print.sigelt_to_string_short v  in
             FStar_Util.print2 "%s -> %%s\n" k uu____511) ()
  
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
    let uu____556 = FStar_Util.smap_create (Prims.of_int (51))  in
    { core_cfg = cfg; fv_cache = uu____556 }
  
let (reifying_false : config -> config) =
  fun cfg  ->
    if (cfg.core_cfg).FStar_TypeChecker_Cfg.reifying
    then
      new_config
        (let uu___92_569 = cfg.core_cfg  in
         {
           FStar_TypeChecker_Cfg.steps =
             (uu___92_569.FStar_TypeChecker_Cfg.steps);
           FStar_TypeChecker_Cfg.tcenv =
             (uu___92_569.FStar_TypeChecker_Cfg.tcenv);
           FStar_TypeChecker_Cfg.debug =
             (uu___92_569.FStar_TypeChecker_Cfg.debug);
           FStar_TypeChecker_Cfg.delta_level =
             (uu___92_569.FStar_TypeChecker_Cfg.delta_level);
           FStar_TypeChecker_Cfg.primitive_steps =
             (uu___92_569.FStar_TypeChecker_Cfg.primitive_steps);
           FStar_TypeChecker_Cfg.strong =
             (uu___92_569.FStar_TypeChecker_Cfg.strong);
           FStar_TypeChecker_Cfg.memoize_lazy =
             (uu___92_569.FStar_TypeChecker_Cfg.memoize_lazy);
           FStar_TypeChecker_Cfg.normalize_pure_lets =
             (uu___92_569.FStar_TypeChecker_Cfg.normalize_pure_lets);
           FStar_TypeChecker_Cfg.reifying = false
         })
    else cfg
  
let (reifying_true : config -> config) =
  fun cfg  ->
    if Prims.op_Negation (cfg.core_cfg).FStar_TypeChecker_Cfg.reifying
    then
      new_config
        (let uu___96_582 = cfg.core_cfg  in
         {
           FStar_TypeChecker_Cfg.steps =
             (uu___96_582.FStar_TypeChecker_Cfg.steps);
           FStar_TypeChecker_Cfg.tcenv =
             (uu___96_582.FStar_TypeChecker_Cfg.tcenv);
           FStar_TypeChecker_Cfg.debug =
             (uu___96_582.FStar_TypeChecker_Cfg.debug);
           FStar_TypeChecker_Cfg.delta_level =
             (uu___96_582.FStar_TypeChecker_Cfg.delta_level);
           FStar_TypeChecker_Cfg.primitive_steps =
             (uu___96_582.FStar_TypeChecker_Cfg.primitive_steps);
           FStar_TypeChecker_Cfg.strong =
             (uu___96_582.FStar_TypeChecker_Cfg.strong);
           FStar_TypeChecker_Cfg.memoize_lazy =
             (uu___96_582.FStar_TypeChecker_Cfg.memoize_lazy);
           FStar_TypeChecker_Cfg.normalize_pure_lets =
             (uu___96_582.FStar_TypeChecker_Cfg.normalize_pure_lets);
           FStar_TypeChecker_Cfg.reifying = true
         })
    else cfg
  
let (zeta_false : config -> config) =
  fun cfg  ->
    let cfg_core = cfg.core_cfg  in
    if (cfg_core.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta
    then
      let cfg_core' =
        let uu___101_595 = cfg_core  in
        {
          FStar_TypeChecker_Cfg.steps =
            (let uu___103_598 = cfg_core.FStar_TypeChecker_Cfg.steps  in
             {
               FStar_TypeChecker_Cfg.beta =
                 (uu___103_598.FStar_TypeChecker_Cfg.beta);
               FStar_TypeChecker_Cfg.iota =
                 (uu___103_598.FStar_TypeChecker_Cfg.iota);
               FStar_TypeChecker_Cfg.zeta = false;
               FStar_TypeChecker_Cfg.zeta_full =
                 (uu___103_598.FStar_TypeChecker_Cfg.zeta_full);
               FStar_TypeChecker_Cfg.weak =
                 (uu___103_598.FStar_TypeChecker_Cfg.weak);
               FStar_TypeChecker_Cfg.hnf =
                 (uu___103_598.FStar_TypeChecker_Cfg.hnf);
               FStar_TypeChecker_Cfg.primops =
                 (uu___103_598.FStar_TypeChecker_Cfg.primops);
               FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                 (uu___103_598.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
               FStar_TypeChecker_Cfg.unfold_until =
                 (uu___103_598.FStar_TypeChecker_Cfg.unfold_until);
               FStar_TypeChecker_Cfg.unfold_only =
                 (uu___103_598.FStar_TypeChecker_Cfg.unfold_only);
               FStar_TypeChecker_Cfg.unfold_fully =
                 (uu___103_598.FStar_TypeChecker_Cfg.unfold_fully);
               FStar_TypeChecker_Cfg.unfold_attr =
                 (uu___103_598.FStar_TypeChecker_Cfg.unfold_attr);
               FStar_TypeChecker_Cfg.unfold_tac =
                 (uu___103_598.FStar_TypeChecker_Cfg.unfold_tac);
               FStar_TypeChecker_Cfg.pure_subterms_within_computations =
                 (uu___103_598.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
               FStar_TypeChecker_Cfg.simplify =
                 (uu___103_598.FStar_TypeChecker_Cfg.simplify);
               FStar_TypeChecker_Cfg.erase_universes =
                 (uu___103_598.FStar_TypeChecker_Cfg.erase_universes);
               FStar_TypeChecker_Cfg.allow_unbound_universes =
                 (uu___103_598.FStar_TypeChecker_Cfg.allow_unbound_universes);
               FStar_TypeChecker_Cfg.reify_ =
                 (uu___103_598.FStar_TypeChecker_Cfg.reify_);
               FStar_TypeChecker_Cfg.compress_uvars =
                 (uu___103_598.FStar_TypeChecker_Cfg.compress_uvars);
               FStar_TypeChecker_Cfg.no_full_norm =
                 (uu___103_598.FStar_TypeChecker_Cfg.no_full_norm);
               FStar_TypeChecker_Cfg.check_no_uvars =
                 (uu___103_598.FStar_TypeChecker_Cfg.check_no_uvars);
               FStar_TypeChecker_Cfg.unmeta =
                 (uu___103_598.FStar_TypeChecker_Cfg.unmeta);
               FStar_TypeChecker_Cfg.unascribe =
                 (uu___103_598.FStar_TypeChecker_Cfg.unascribe);
               FStar_TypeChecker_Cfg.in_full_norm_request =
                 (uu___103_598.FStar_TypeChecker_Cfg.in_full_norm_request);
               FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                 (uu___103_598.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
               FStar_TypeChecker_Cfg.nbe_step =
                 (uu___103_598.FStar_TypeChecker_Cfg.nbe_step);
               FStar_TypeChecker_Cfg.for_extraction =
                 (uu___103_598.FStar_TypeChecker_Cfg.for_extraction)
             });
          FStar_TypeChecker_Cfg.tcenv =
            (uu___101_595.FStar_TypeChecker_Cfg.tcenv);
          FStar_TypeChecker_Cfg.debug =
            (uu___101_595.FStar_TypeChecker_Cfg.debug);
          FStar_TypeChecker_Cfg.delta_level =
            (uu___101_595.FStar_TypeChecker_Cfg.delta_level);
          FStar_TypeChecker_Cfg.primitive_steps =
            (uu___101_595.FStar_TypeChecker_Cfg.primitive_steps);
          FStar_TypeChecker_Cfg.strong =
            (uu___101_595.FStar_TypeChecker_Cfg.strong);
          FStar_TypeChecker_Cfg.memoize_lazy =
            (uu___101_595.FStar_TypeChecker_Cfg.memoize_lazy);
          FStar_TypeChecker_Cfg.normalize_pure_lets =
            (uu___101_595.FStar_TypeChecker_Cfg.normalize_pure_lets);
          FStar_TypeChecker_Cfg.reifying =
            (uu___101_595.FStar_TypeChecker_Cfg.reifying)
        }  in
      new_config cfg_core'
    else cfg
  
let (cache_add :
  config -> FStar_Syntax_Syntax.fv -> FStar_TypeChecker_NBETerm.t -> unit) =
  fun cfg  ->
    fun fv  ->
      fun v  ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
        let uu____619 = FStar_Ident.string_of_lid lid  in
        FStar_Util.smap_add cfg.fv_cache uu____619 v
  
let (try_in_cache :
  config ->
    FStar_Syntax_Syntax.fv ->
      FStar_TypeChecker_NBETerm.t FStar_Pervasives_Native.option)
  =
  fun cfg  ->
    fun fv  ->
      let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
      let uu____637 = FStar_Ident.string_of_lid lid  in
      FStar_Util.smap_try_find cfg.fv_cache uu____637
  
let (debug : config -> (unit -> unit) -> unit) =
  fun cfg  -> fun f  -> FStar_TypeChecker_Cfg.log_nbe cfg.core_cfg f 
let rec (unlazy_unmeta :
  FStar_TypeChecker_NBETerm.t -> FStar_TypeChecker_NBETerm.t) =
  fun t  ->
    match t.FStar_TypeChecker_NBETerm.nbe_t with
    | FStar_TypeChecker_NBETerm.Lazy (uu____661,t1) ->
        let uu____683 = FStar_Thunk.force t1  in unlazy_unmeta uu____683
    | FStar_TypeChecker_NBETerm.Meta (t0,m) ->
        let uu____690 = FStar_Thunk.force m  in
        (match uu____690 with
         | FStar_Syntax_Syntax.Meta_monadic (uu____691,uu____692) -> t
         | FStar_Syntax_Syntax.Meta_monadic_lift
             (uu____697,uu____698,uu____699) -> t
         | uu____704 -> unlazy_unmeta t0)
    | uu____705 -> t
  
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
              (fun uu____814  ->
                 let uu____815 =
                   FStar_TypeChecker_NBETerm.t_to_string scrutinee0  in
                 let uu____817 = FStar_Syntax_Print.pat_to_string p  in
                 FStar_Util.print2 "matches_pat (%s, %s)\n" uu____815
                   uu____817);
            (let scrutinee = unlazy_unmeta scrutinee0  in
             let r =
               match p.FStar_Syntax_Syntax.v with
               | FStar_Syntax_Syntax.Pat_var bv ->
                   FStar_Util.Inl [scrutinee0]
               | FStar_Syntax_Syntax.Pat_wild bv ->
                   FStar_Util.Inl [scrutinee0]
               | FStar_Syntax_Syntax.Pat_dot_term uu____844 ->
                   FStar_Util.Inl []
               | FStar_Syntax_Syntax.Pat_constant s ->
                   let matches_const c s1 =
                     debug cfg
                       (fun uu____871  ->
                          let uu____872 =
                            FStar_TypeChecker_NBETerm.t_to_string c  in
                          let uu____874 =
                            FStar_Syntax_Print.const_to_string s1  in
                          FStar_Util.print2
                            "Testing term %s against pattern %s\n" uu____872
                            uu____874);
                     (match c.FStar_TypeChecker_NBETerm.nbe_t with
                      | FStar_TypeChecker_NBETerm.Constant
                          (FStar_TypeChecker_NBETerm.Unit ) ->
                          s1 = FStar_Const.Const_unit
                      | FStar_TypeChecker_NBETerm.Constant
                          (FStar_TypeChecker_NBETerm.Bool b) ->
                          (match s1 with
                           | FStar_Const.Const_bool p1 -> b = p1
                           | uu____884 -> false)
                      | FStar_TypeChecker_NBETerm.Constant
                          (FStar_TypeChecker_NBETerm.Int i) ->
                          (match s1 with
                           | FStar_Const.Const_int
                               (p1,FStar_Pervasives_Native.None ) ->
                               let uu____901 =
                                 FStar_BigInt.big_int_of_string p1  in
                               i = uu____901
                           | uu____902 -> false)
                      | FStar_TypeChecker_NBETerm.Constant
                          (FStar_TypeChecker_NBETerm.String (st,uu____905))
                          ->
                          (match s1 with
                           | FStar_Const.Const_string (p1,uu____910) ->
                               st = p1
                           | uu____914 -> false)
                      | FStar_TypeChecker_NBETerm.Constant
                          (FStar_TypeChecker_NBETerm.Char c1) ->
                          (match s1 with
                           | FStar_Const.Const_char p1 -> c1 = p1
                           | uu____922 -> false)
                      | uu____924 -> false)
                      in
                   let uu____926 = matches_const scrutinee s  in
                   if uu____926
                   then FStar_Util.Inl []
                   else FStar_Util.Inr false
               | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                   let rec matches_args out a p1 =
                     match (a, p1) with
                     | ([],[]) -> FStar_Util.Inl out
                     | ((t,uu____1064)::rest_a,(p2,uu____1067)::rest_p) ->
                         let uu____1106 = matches_pat t p2  in
                         (match uu____1106 with
                          | FStar_Util.Inl s ->
                              matches_args (FStar_List.append out s) rest_a
                                rest_p
                          | m -> m)
                     | uu____1135 -> FStar_Util.Inr false  in
                   (match scrutinee.FStar_TypeChecker_NBETerm.nbe_t with
                    | FStar_TypeChecker_NBETerm.Construct (fv',_us,args_rev)
                        ->
                        let uu____1183 = FStar_Syntax_Syntax.fv_eq fv fv'  in
                        if uu____1183
                        then
                          matches_args [] (FStar_List.rev args_rev) arg_pats
                        else FStar_Util.Inr false
                    | uu____1203 -> FStar_Util.Inr true)
                in
             let res_to_string uu___0_1221 =
               match uu___0_1221 with
               | FStar_Util.Inr b ->
                   let uu____1235 = FStar_Util.string_of_bool b  in
                   Prims.op_Hat "Inr " uu____1235
               | FStar_Util.Inl bs ->
                   let uu____1244 =
                     FStar_Util.string_of_int (FStar_List.length bs)  in
                   Prims.op_Hat "Inl " uu____1244
                in
             debug cfg
               (fun uu____1252  ->
                  let uu____1253 =
                    FStar_TypeChecker_NBETerm.t_to_string scrutinee  in
                  let uu____1255 = FStar_Syntax_Print.pat_to_string p  in
                  let uu____1257 = res_to_string r  in
                  FStar_Util.print3 "matches_pat (%s, %s) = %s\n" uu____1253
                    uu____1255 uu____1257);
             r)
             in
          match branches1 with
          | [] -> FStar_Pervasives_Native.None
          | (p,_wopt,e)::branches2 ->
              let uu____1296 = matches_pat scrut1 p  in
              (match uu____1296 with
               | FStar_Util.Inl matches ->
                   (debug cfg
                      (fun uu____1321  ->
                         let uu____1322 = FStar_Syntax_Print.pat_to_string p
                            in
                         FStar_Util.print1 "Pattern %s matches\n" uu____1322);
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
        | (uu____1471,[]) -> (true, acc, ts)
        | ([],uu____1502::uu____1503) -> (false, acc, [])
        | (t::ts1,in_decreases_clause::bs) ->
            let uu____1572 =
              in_decreases_clause &&
                (FStar_TypeChecker_NBETerm.isAccu
                   (FStar_Pervasives_Native.fst t))
               in
            if uu____1572
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
        let mapper uu____1671 =
          match uu____1671 with
          | (lr,rng) ->
              (match lr with
               | FStar_Util.Inr (elt,FStar_Pervasives_Native.None ) ->
                   FStar_Pervasives_Native.Some elt
               | FStar_Util.Inr (elt,FStar_Pervasives_Native.Some us) ->
                   (debug cfg
                      (fun uu____1754  ->
                         let uu____1755 =
                           FStar_Syntax_Print.univs_to_string us  in
                         FStar_Util.print1
                           "Universes in local declaration: %s\n" uu____1755);
                    FStar_Pervasives_Native.Some elt)
               | uu____1758 -> FStar_Pervasives_Native.None)
           in
        let uu____1773 = FStar_TypeChecker_Env.lookup_qname env lid  in
        FStar_Util.bind_opt uu____1773 mapper
  
let (is_univ : FStar_TypeChecker_NBETerm.t -> Prims.bool) =
  fun tm  ->
    match tm.FStar_TypeChecker_NBETerm.nbe_t with
    | FStar_TypeChecker_NBETerm.Univ uu____1820 -> true
    | uu____1822 -> false
  
let (un_univ : FStar_TypeChecker_NBETerm.t -> FStar_Syntax_Syntax.universe) =
  fun tm  ->
    match tm.FStar_TypeChecker_NBETerm.nbe_t with
    | FStar_TypeChecker_NBETerm.Univ u -> u
    | uu____1831 ->
        let uu____1832 =
          let uu____1834 = FStar_TypeChecker_NBETerm.t_to_string tm  in
          Prims.op_Hat "Not a universe: " uu____1834  in
        failwith uu____1832
  
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
              (uu____1856,uu____1857,uu____1858,uu____1859,uu____1860,uu____1861);
            FStar_Syntax_Syntax.sigrng = uu____1862;
            FStar_Syntax_Syntax.sigquals = uu____1863;
            FStar_Syntax_Syntax.sigmeta = uu____1864;
            FStar_Syntax_Syntax.sigattrs = uu____1865;
            FStar_Syntax_Syntax.sigopts = uu____1866;_},uu____1867),uu____1868)
        -> true
    | uu____1928 -> false
  
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
              let uu____1968 = aux u3  in
              FStar_Syntax_Syntax.U_succ uu____1968
          | FStar_Syntax_Syntax.U_max us ->
              let uu____1972 = FStar_List.map aux us  in
              FStar_Syntax_Syntax.U_max uu____1972
          | FStar_Syntax_Syntax.U_unknown  -> u2
          | FStar_Syntax_Syntax.U_name uu____1975 -> u2
          | FStar_Syntax_Syntax.U_unif uu____1976 -> u2
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
           | FStar_Util.Inl uu____2009 -> failwith "find_let : impossible"
           | FStar_Util.Inr name ->
               let uu____2014 = FStar_Syntax_Syntax.fv_eq name fvar  in
               if uu____2014
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
          (fun uu____2308  ->
             let uu____2309 =
               let uu____2311 = FStar_Syntax_Subst.compress e  in
               FStar_Syntax_Print.tag_of_term uu____2311  in
             let uu____2312 =
               let uu____2314 = FStar_Syntax_Subst.compress e  in
               FStar_Syntax_Print.term_to_string uu____2314  in
             FStar_Util.print2 "Term: %s - %s\n" uu____2309 uu____2312);
        (let uu____2316 =
           let uu____2317 = FStar_Syntax_Subst.compress e  in
           uu____2317.FStar_Syntax_Syntax.n  in
         match uu____2316 with
         | FStar_Syntax_Syntax.Tm_delayed (uu____2320,uu____2321) ->
             failwith "Tm_delayed: Impossible"
         | FStar_Syntax_Syntax.Tm_unknown  ->
             mk_t1 FStar_TypeChecker_NBETerm.Unknown
         | FStar_Syntax_Syntax.Tm_constant c ->
             let uu____2344 =
               let uu____2345 = translate_constant c  in
               FStar_TypeChecker_NBETerm.Constant uu____2345  in
             FStar_All.pipe_left mk_t1 uu____2344
         | FStar_Syntax_Syntax.Tm_bvar db ->
             if db.FStar_Syntax_Syntax.index < (FStar_List.length bs)
             then
               let t = FStar_List.nth bs db.FStar_Syntax_Syntax.index  in
               (debug1
                  (fun uu____2356  ->
                     let uu____2357 = FStar_TypeChecker_NBETerm.t_to_string t
                        in
                     let uu____2359 =
                       let uu____2361 =
                         FStar_List.map FStar_TypeChecker_NBETerm.t_to_string
                           bs
                          in
                       FStar_All.pipe_right uu____2361
                         (FStar_String.concat "; ")
                        in
                     FStar_Util.print2
                       "Resolved bvar to %s\n\tcontext is [%s]\n" uu____2357
                       uu____2359);
                t)
             else failwith "de Bruijn index out of bounds"
         | FStar_Syntax_Syntax.Tm_uinst (t,us) ->
             (debug1
                (fun uu____2388  ->
                   let uu____2389 = FStar_Syntax_Print.term_to_string t  in
                   let uu____2391 =
                     let uu____2393 =
                       FStar_List.map FStar_Syntax_Print.univ_to_string us
                        in
                     FStar_All.pipe_right uu____2393
                       (FStar_String.concat ", ")
                      in
                   FStar_Util.print2 "Uinst term : %s\nUnivs : %s\n"
                     uu____2389 uu____2391);
              (let uu____2404 = translate cfg bs t  in
               let uu____2405 =
                 FStar_List.map
                   (fun x  ->
                      let uu____2409 =
                        let uu____2410 =
                          let uu____2411 = translate_univ cfg bs x  in
                          FStar_TypeChecker_NBETerm.Univ uu____2411  in
                        FStar_All.pipe_left mk_t1 uu____2410  in
                      FStar_TypeChecker_NBETerm.as_arg uu____2409) us
                  in
               iapp cfg uu____2404 uu____2405))
         | FStar_Syntax_Syntax.Tm_type u ->
             let uu____2413 =
               let uu____2414 = translate_univ cfg bs u  in
               FStar_TypeChecker_NBETerm.Type_t uu____2414  in
             FStar_All.pipe_left mk_t1 uu____2413
         | FStar_Syntax_Syntax.Tm_arrow (xs,c) ->
             let norm uu____2444 =
               let uu____2445 =
                 FStar_List.fold_left
                   (fun uu____2489  ->
                      fun uu____2490  ->
                        match (uu____2489, uu____2490) with
                        | ((ctx,binders_rev),(x,q)) ->
                            let t =
                              let uu____2594 =
                                translate cfg ctx x.FStar_Syntax_Syntax.sort
                                 in
                              readback cfg uu____2594  in
                            let x1 =
                              let uu___399_2596 =
                                FStar_Syntax_Syntax.freshen_bv x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___399_2596.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___399_2596.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t
                              }  in
                            let ctx1 =
                              let uu____2600 =
                                FStar_TypeChecker_NBETerm.mkAccuVar x1  in
                              uu____2600 :: ctx  in
                            (ctx1, ((x1, q) :: binders_rev))) (bs, []) xs
                  in
               match uu____2445 with
               | (ctx,binders_rev) ->
                   let c1 =
                     let uu____2660 = translate_comp cfg ctx c  in
                     readback_comp cfg uu____2660  in
                   FStar_Syntax_Util.arrow (FStar_List.rev binders_rev) c1
                in
             let uu____2667 =
               let uu____2668 =
                 let uu____2685 = FStar_Thunk.mk norm  in
                 FStar_Util.Inl uu____2685  in
               FStar_TypeChecker_NBETerm.Arrow uu____2668  in
             FStar_All.pipe_left mk_t1 uu____2667
         | FStar_Syntax_Syntax.Tm_refine (bv,tm) ->
             if
               ((cfg.core_cfg).FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.for_extraction
             then translate cfg bs bv.FStar_Syntax_Syntax.sort
             else
               FStar_All.pipe_left mk_t1
                 (FStar_TypeChecker_NBETerm.Refinement
                    ((fun y  -> translate cfg (y :: bs) tm),
                      (fun uu____2723  ->
                         let uu____2724 =
                           translate cfg bs bv.FStar_Syntax_Syntax.sort  in
                         FStar_TypeChecker_NBETerm.as_arg uu____2724)))
         | FStar_Syntax_Syntax.Tm_ascribed (t,uu____2726,uu____2727) ->
             translate cfg bs t
         | FStar_Syntax_Syntax.Tm_uvar (u,(subst,set_use_range)) ->
             let norm_uvar uu____2794 =
               let norm_subst_elt uu___1_2800 =
                 match uu___1_2800 with
                 | FStar_Syntax_Syntax.NT (x,t) ->
                     let uu____2807 =
                       let uu____2814 =
                         let uu____2817 = translate cfg bs t  in
                         readback cfg uu____2817  in
                       (x, uu____2814)  in
                     FStar_Syntax_Syntax.NT uu____2807
                 | FStar_Syntax_Syntax.NM (x,i) ->
                     let x_i =
                       FStar_Syntax_Syntax.bv_to_tm
                         (let uu___436_2827 = x  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___436_2827.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index = i;
                            FStar_Syntax_Syntax.sort =
                              (uu___436_2827.FStar_Syntax_Syntax.sort)
                          })
                        in
                     let t =
                       let uu____2829 = translate cfg bs x_i  in
                       readback cfg uu____2829  in
                     (match t.FStar_Syntax_Syntax.n with
                      | FStar_Syntax_Syntax.Tm_bvar x_j ->
                          FStar_Syntax_Syntax.NM
                            (x, (x_j.FStar_Syntax_Syntax.index))
                      | uu____2832 -> FStar_Syntax_Syntax.NT (x, t))
                 | uu____2835 ->
                     failwith "Impossible: subst invariant of uvar nodes"
                  in
               let subst1 =
                 FStar_List.map (FStar_List.map norm_subst_elt) subst  in
               let uu___446_2846 = e  in
               {
                 FStar_Syntax_Syntax.n =
                   (FStar_Syntax_Syntax.Tm_uvar (u, (subst1, set_use_range)));
                 FStar_Syntax_Syntax.pos =
                   (uu___446_2846.FStar_Syntax_Syntax.pos);
                 FStar_Syntax_Syntax.vars =
                   (uu___446_2846.FStar_Syntax_Syntax.vars)
               }  in
             let uu____2859 =
               let uu____2860 =
                 let uu____2871 =
                   let uu____2872 = FStar_Thunk.mk norm_uvar  in
                   FStar_TypeChecker_NBETerm.UVar uu____2872  in
                 (uu____2871, [])  in
               FStar_TypeChecker_NBETerm.Accu uu____2860  in
             FStar_All.pipe_left mk_t1 uu____2859
         | FStar_Syntax_Syntax.Tm_name x ->
             FStar_TypeChecker_NBETerm.mkAccuVar x
         | FStar_Syntax_Syntax.Tm_abs ([],uu____2886,uu____2887) ->
             failwith "Impossible: abstraction with no binders"
         | FStar_Syntax_Syntax.Tm_abs (xs,body,resc) ->
             FStar_All.pipe_left mk_t1
               (FStar_TypeChecker_NBETerm.Lam
                  ((fun ys  -> translate cfg (FStar_List.append ys bs) body),
                    (FStar_Util.Inl (bs, xs, resc)), (FStar_List.length xs)))
         | FStar_Syntax_Syntax.Tm_fvar fvar ->
             let uu____2995 = try_in_cache cfg fvar  in
             (match uu____2995 with
              | FStar_Pervasives_Native.Some t -> t
              | uu____2999 -> translate_fv cfg bs fvar)
         | FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                  (FStar_Const.Const_reify );
                FStar_Syntax_Syntax.pos = uu____3002;
                FStar_Syntax_Syntax.vars = uu____3003;_},arg::more::args)
             ->
             let uu____3063 = FStar_Syntax_Util.head_and_args e  in
             (match uu____3063 with
              | (head,uu____3081) ->
                  let head1 =
                    FStar_Syntax_Syntax.mk_Tm_app head [arg]
                      e.FStar_Syntax_Syntax.pos
                     in
                  let uu____3123 =
                    FStar_Syntax_Syntax.mk_Tm_app head1 (more :: args)
                      e.FStar_Syntax_Syntax.pos
                     in
                  translate cfg bs uu____3123)
         | FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                  (FStar_Const.Const_reflect uu____3132);
                FStar_Syntax_Syntax.pos = uu____3133;
                FStar_Syntax_Syntax.vars = uu____3134;_},arg::more::args)
             ->
             let uu____3194 = FStar_Syntax_Util.head_and_args e  in
             (match uu____3194 with
              | (head,uu____3212) ->
                  let head1 =
                    FStar_Syntax_Syntax.mk_Tm_app head [arg]
                      e.FStar_Syntax_Syntax.pos
                     in
                  let uu____3254 =
                    FStar_Syntax_Syntax.mk_Tm_app head1 (more :: args)
                      e.FStar_Syntax_Syntax.pos
                     in
                  translate cfg bs uu____3254)
         | FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                  (FStar_Const.Const_reflect uu____3263);
                FStar_Syntax_Syntax.pos = uu____3264;
                FStar_Syntax_Syntax.vars = uu____3265;_},arg::[])
             when (cfg.core_cfg).FStar_TypeChecker_Cfg.reifying ->
             let cfg1 = reifying_false cfg  in
             translate cfg1 bs (FStar_Pervasives_Native.fst arg)
         | FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                  (FStar_Const.Const_reflect uu____3310);
                FStar_Syntax_Syntax.pos = uu____3311;
                FStar_Syntax_Syntax.vars = uu____3312;_},arg::[])
             ->
             let uu____3352 =
               let uu____3353 =
                 translate cfg bs (FStar_Pervasives_Native.fst arg)  in
               FStar_TypeChecker_NBETerm.Reflect uu____3353  in
             FStar_All.pipe_left mk_t1 uu____3352
         | FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                  (FStar_Const.Const_reify );
                FStar_Syntax_Syntax.pos = uu____3358;
                FStar_Syntax_Syntax.vars = uu____3359;_},arg::[])
             when
             ((cfg.core_cfg).FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.reify_
             ->
             let cfg1 = reifying_true cfg  in
             translate cfg1 bs (FStar_Pervasives_Native.fst arg)
         | FStar_Syntax_Syntax.Tm_app (head,args) ->
             (debug1
                (fun uu____3438  ->
                   let uu____3439 = FStar_Syntax_Print.term_to_string head
                      in
                   let uu____3441 = FStar_Syntax_Print.args_to_string args
                      in
                   FStar_Util.print2 "Application: %s @ %s\n" uu____3439
                     uu____3441);
              (let uu____3444 = translate cfg bs head  in
               let uu____3445 =
                 FStar_List.map
                   (fun x  ->
                      let uu____3467 =
                        translate cfg bs (FStar_Pervasives_Native.fst x)  in
                      (uu____3467, (FStar_Pervasives_Native.snd x))) args
                  in
               iapp cfg uu____3444 uu____3445))
         | FStar_Syntax_Syntax.Tm_match (scrut,branches) ->
             let make_branches uu____3519 =
               let cfg1 = zeta_false cfg  in
               let rec process_pattern bs1 p =
                 let uu____3550 =
                   match p.FStar_Syntax_Syntax.v with
                   | FStar_Syntax_Syntax.Pat_constant c ->
                       (bs1, (FStar_Syntax_Syntax.Pat_constant c))
                   | FStar_Syntax_Syntax.Pat_cons (fvar,args) ->
                       let uu____3586 =
                         FStar_List.fold_left
                           (fun uu____3627  ->
                              fun uu____3628  ->
                                match (uu____3627, uu____3628) with
                                | ((bs2,args1),(arg,b)) ->
                                    let uu____3720 = process_pattern bs2 arg
                                       in
                                    (match uu____3720 with
                                     | (bs',arg') ->
                                         (bs', ((arg', b) :: args1))))
                           (bs1, []) args
                          in
                       (match uu____3586 with
                        | (bs',args') ->
                            (bs',
                              (FStar_Syntax_Syntax.Pat_cons
                                 (fvar, (FStar_List.rev args')))))
                   | FStar_Syntax_Syntax.Pat_var bvar ->
                       let x =
                         let uu____3819 =
                           let uu____3820 =
                             translate cfg1 bs1 bvar.FStar_Syntax_Syntax.sort
                              in
                           readback cfg1 uu____3820  in
                         FStar_Syntax_Syntax.new_bv
                           FStar_Pervasives_Native.None uu____3819
                          in
                       let uu____3821 =
                         let uu____3824 =
                           FStar_TypeChecker_NBETerm.mkAccuVar x  in
                         uu____3824 :: bs1  in
                       (uu____3821, (FStar_Syntax_Syntax.Pat_var x))
                   | FStar_Syntax_Syntax.Pat_wild bvar ->
                       let x =
                         let uu____3829 =
                           let uu____3830 =
                             translate cfg1 bs1 bvar.FStar_Syntax_Syntax.sort
                              in
                           readback cfg1 uu____3830  in
                         FStar_Syntax_Syntax.new_bv
                           FStar_Pervasives_Native.None uu____3829
                          in
                       let uu____3831 =
                         let uu____3834 =
                           FStar_TypeChecker_NBETerm.mkAccuVar x  in
                         uu____3834 :: bs1  in
                       (uu____3831, (FStar_Syntax_Syntax.Pat_wild x))
                   | FStar_Syntax_Syntax.Pat_dot_term (bvar,tm) ->
                       let x =
                         let uu____3844 =
                           let uu____3845 =
                             translate cfg1 bs1 bvar.FStar_Syntax_Syntax.sort
                              in
                           readback cfg1 uu____3845  in
                         FStar_Syntax_Syntax.new_bv
                           FStar_Pervasives_Native.None uu____3844
                          in
                       let uu____3846 =
                         let uu____3847 =
                           let uu____3854 =
                             let uu____3857 = translate cfg1 bs1 tm  in
                             readback cfg1 uu____3857  in
                           (x, uu____3854)  in
                         FStar_Syntax_Syntax.Pat_dot_term uu____3847  in
                       (bs1, uu____3846)
                    in
                 match uu____3550 with
                 | (bs2,p_new) ->
                     (bs2,
                       (let uu___573_3877 = p  in
                        {
                          FStar_Syntax_Syntax.v = p_new;
                          FStar_Syntax_Syntax.p =
                            (uu___573_3877.FStar_Syntax_Syntax.p)
                        }))
                  in
               FStar_List.map
                 (fun uu____3896  ->
                    match uu____3896 with
                    | (pat,when_clause,e1) ->
                        let uu____3918 = process_pattern bs pat  in
                        (match uu____3918 with
                         | (bs',pat') ->
                             let uu____3931 =
                               let uu____3932 =
                                 let uu____3935 = translate cfg1 bs' e1  in
                                 readback cfg1 uu____3935  in
                               (pat', when_clause, uu____3932)  in
                             FStar_Syntax_Util.branch uu____3931)) branches
                in
             let scrut1 = translate cfg bs scrut  in
             (debug1
                (fun uu____3952  ->
                   let uu____3953 =
                     FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos
                      in
                   let uu____3955 = FStar_Syntax_Print.term_to_string e  in
                   FStar_Util.print2 "%s: Translating match %s\n" uu____3953
                     uu____3955);
              (let scrut2 = unlazy_unmeta scrut1  in
               match scrut2.FStar_TypeChecker_NBETerm.nbe_t with
               | FStar_TypeChecker_NBETerm.Construct (c,us,args) ->
                   (debug1
                      (fun uu____3983  ->
                         let uu____3984 =
                           let uu____3986 =
                             FStar_All.pipe_right args
                               (FStar_List.map
                                  (fun uu____4012  ->
                                     match uu____4012 with
                                     | (x,q) ->
                                         let uu____4026 =
                                           FStar_TypeChecker_NBETerm.t_to_string
                                             x
                                            in
                                         Prims.op_Hat
                                           (if FStar_Util.is_some q
                                            then "#"
                                            else "") uu____4026))
                              in
                           FStar_All.pipe_right uu____3986
                             (FStar_String.concat "; ")
                            in
                         FStar_Util.print1 "Match args: %s\n" uu____3984);
                    (let uu____4040 = pickBranch cfg scrut2 branches  in
                     match uu____4040 with
                     | FStar_Pervasives_Native.Some (branch,args1) ->
                         let uu____4061 =
                           FStar_List.fold_left
                             (fun bs1  -> fun x  -> x :: bs1) bs args1
                            in
                         translate cfg uu____4061 branch
                     | FStar_Pervasives_Native.None  ->
                         FStar_TypeChecker_NBETerm.mkAccuMatch scrut2
                           make_branches))
               | FStar_TypeChecker_NBETerm.Constant c ->
                   (debug1
                      (fun uu____4084  ->
                         let uu____4085 =
                           FStar_TypeChecker_NBETerm.t_to_string scrut2  in
                         FStar_Util.print1 "Match constant : %s\n" uu____4085);
                    (let uu____4088 = pickBranch cfg scrut2 branches  in
                     match uu____4088 with
                     | FStar_Pervasives_Native.Some (branch,[]) ->
                         translate cfg bs branch
                     | FStar_Pervasives_Native.Some (branch,arg::[]) ->
                         translate cfg (arg :: bs) branch
                     | FStar_Pervasives_Native.None  ->
                         FStar_TypeChecker_NBETerm.mkAccuMatch scrut2
                           make_branches
                     | FStar_Pervasives_Native.Some (uu____4122,hd::tl) ->
                         failwith
                           "Impossible: Matching on constants cannot bind more than one variable"))
               | uu____4136 ->
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
             let norm_meta uu____4175 =
               let norm t =
                 let uu____4182 = translate cfg bs t  in
                 readback cfg uu____4182  in
               match meta with
               | FStar_Syntax_Syntax.Meta_named uu____4183 -> meta
               | FStar_Syntax_Syntax.Meta_labeled uu____4184 -> meta
               | FStar_Syntax_Syntax.Meta_desugared uu____4193 -> meta
               | FStar_Syntax_Syntax.Meta_pattern (ts,args) ->
                   let uu____4228 =
                     let uu____4249 = FStar_List.map norm ts  in
                     let uu____4258 =
                       FStar_List.map
                         (FStar_List.map
                            (fun uu____4307  ->
                               match uu____4307 with
                               | (t,a) ->
                                   let uu____4326 = norm t  in
                                   (uu____4326, a))) args
                        in
                     (uu____4249, uu____4258)  in
                   FStar_Syntax_Syntax.Meta_pattern uu____4228
               | FStar_Syntax_Syntax.Meta_monadic (m,t) ->
                   let uu____4351 =
                     let uu____4358 = norm t  in (m, uu____4358)  in
                   FStar_Syntax_Syntax.Meta_monadic uu____4351
               | FStar_Syntax_Syntax.Meta_monadic_lift (m0,m1,t) ->
                   let uu____4370 =
                     let uu____4379 = norm t  in (m0, m1, uu____4379)  in
                   FStar_Syntax_Syntax.Meta_monadic_lift uu____4370
                in
             let uu____4384 =
               let uu____4385 =
                 let uu____4392 = translate cfg bs e1  in
                 let uu____4393 = FStar_Thunk.mk norm_meta  in
                 (uu____4392, uu____4393)  in
               FStar_TypeChecker_NBETerm.Meta uu____4385  in
             FStar_All.pipe_left mk_t1 uu____4384
         | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
             let uu____4415 =
               FStar_TypeChecker_Cfg.should_reduce_local_let cfg.core_cfg lb
                in
             if uu____4415
             then
               let uu____4418 =
                 (((cfg.core_cfg).FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.for_extraction
                    &&
                    (FStar_Syntax_Util.is_unit lb.FStar_Syntax_Syntax.lbtyp))
                   &&
                   (FStar_Syntax_Util.is_pure_or_ghost_effect
                      lb.FStar_Syntax_Syntax.lbeff)
                  in
               (if uu____4418
                then
                  let bs1 =
                    let uu____4424 =
                      let uu____4425 =
                        FStar_Syntax_Syntax.range_of_lbname
                          lb.FStar_Syntax_Syntax.lbname
                         in
                      mk_rt uu____4425
                        (FStar_TypeChecker_NBETerm.Constant
                           FStar_TypeChecker_NBETerm.Unit)
                       in
                    uu____4424 :: bs  in
                  translate cfg bs1 body
                else
                  (let bs1 =
                     let uu____4431 = translate_letbinding cfg bs lb  in
                     uu____4431 :: bs  in
                   translate cfg bs1 body))
             else
               (let def uu____4439 =
                  let uu____4440 =
                    (((cfg.core_cfg).FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.for_extraction
                       &&
                       (FStar_Syntax_Util.is_unit
                          lb.FStar_Syntax_Syntax.lbtyp))
                      &&
                      (FStar_Syntax_Util.is_pure_or_ghost_effect
                         lb.FStar_Syntax_Syntax.lbeff)
                     in
                  if uu____4440
                  then
                    FStar_All.pipe_left mk_t1
                      (FStar_TypeChecker_NBETerm.Constant
                         FStar_TypeChecker_NBETerm.Unit)
                  else translate cfg bs lb.FStar_Syntax_Syntax.lbdef  in
                let typ uu____4450 =
                  translate cfg bs lb.FStar_Syntax_Syntax.lbtyp  in
                let name =
                  let uu____4452 =
                    FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                  FStar_Syntax_Syntax.freshen_bv uu____4452  in
                let bs1 =
                  let uu____4456 =
                    let uu____4457 = FStar_Syntax_Syntax.range_of_bv name  in
                    mk_rt uu____4457
                      (FStar_TypeChecker_NBETerm.Accu
                         ((FStar_TypeChecker_NBETerm.Var name), []))
                     in
                  uu____4456 :: bs  in
                let body1 uu____4473 = translate cfg bs1 body  in
                let uu____4474 =
                  let uu____4475 =
                    let uu____4486 =
                      let uu____4487 =
                        let uu____4504 = FStar_Thunk.mk typ  in
                        let uu____4507 = FStar_Thunk.mk def  in
                        let uu____4510 = FStar_Thunk.mk body1  in
                        (name, uu____4504, uu____4507, uu____4510, lb)  in
                      FStar_TypeChecker_NBETerm.UnreducedLet uu____4487  in
                    (uu____4486, [])  in
                  FStar_TypeChecker_NBETerm.Accu uu____4475  in
                FStar_All.pipe_left mk_t1 uu____4474)
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
                      let uu____4556 =
                        FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                      FStar_Syntax_Syntax.freshen_bv uu____4556) lbs
                  in
               let typs =
                 FStar_List.map
                   (fun lb  -> translate cfg bs lb.FStar_Syntax_Syntax.lbtyp)
                   lbs
                  in
               let rec_bs =
                 let uu____4565 =
                   FStar_List.map
                     (fun v  ->
                        let uu____4571 =
                          let uu____4576 = FStar_Syntax_Syntax.range_of_bv v
                             in
                          mk_rt uu____4576  in
                        FStar_All.pipe_left uu____4571
                          (FStar_TypeChecker_NBETerm.Accu
                             ((FStar_TypeChecker_NBETerm.Var v), []))) vars
                    in
                 FStar_List.append uu____4565 bs  in
               let defs =
                 FStar_List.map
                   (fun lb  ->
                      translate cfg rec_bs lb.FStar_Syntax_Syntax.lbdef) lbs
                  in
               let body1 = translate cfg rec_bs body  in
               let uu____4593 =
                 let uu____4594 =
                   let uu____4605 =
                     let uu____4606 =
                       let uu____4623 = FStar_List.zip3 vars typs defs  in
                       (uu____4623, body1, lbs)  in
                     FStar_TypeChecker_NBETerm.UnreducedLetRec uu____4606  in
                   (uu____4605, [])  in
                 FStar_TypeChecker_NBETerm.Accu uu____4594  in
               FStar_All.pipe_left mk_t1 uu____4593
             else
               (let uu____4654 = make_rec_env lbs bs  in
                translate cfg uu____4654 body)
         | FStar_Syntax_Syntax.Tm_quoted (qt,qi) ->
             let close t =
               let bvs =
                 FStar_List.map
                   (fun uu____4673  ->
                      FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                        FStar_Syntax_Syntax.tun) bs
                  in
               let s1 =
                 FStar_List.mapi
                   (fun i  -> fun bv  -> FStar_Syntax_Syntax.DB (i, bv)) bvs
                  in
               let s2 =
                 let uu____4686 = FStar_List.zip bvs bs  in
                 FStar_List.map
                   (fun uu____4701  ->
                      match uu____4701 with
                      | (bv,t1) ->
                          let uu____4708 =
                            let uu____4715 = readback cfg t1  in
                            (bv, uu____4715)  in
                          FStar_Syntax_Syntax.NT uu____4708) uu____4686
                  in
               let uu____4720 = FStar_Syntax_Subst.subst s1 t  in
               FStar_Syntax_Subst.subst s2 uu____4720  in
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
             let f uu____4729 =
               let t = FStar_Syntax_Util.unfold_lazy li  in
               debug1
                 (fun uu____4736  ->
                    let uu____4737 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.print1 ">> Unfolding Tm_lazy to %s\n"
                      uu____4737);
               translate cfg bs t  in
             let uu____4740 =
               let uu____4741 =
                 let uu____4756 = FStar_Thunk.mk f  in
                 ((FStar_Util.Inl li), uu____4756)  in
               FStar_TypeChecker_NBETerm.Lazy uu____4741  in
             FStar_All.pipe_left mk_t1 uu____4740)

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
            let uu____4788 =
              let uu____4795 = translate cfg bs typ  in
              let uu____4796 = fmap_opt (translate_univ cfg bs) u  in
              (uu____4795, uu____4796)  in
            FStar_TypeChecker_NBETerm.Tot uu____4788
        | FStar_Syntax_Syntax.GTotal (typ,u) ->
            let uu____4811 =
              let uu____4818 = translate cfg bs typ  in
              let uu____4819 = fmap_opt (translate_univ cfg bs) u  in
              (uu____4818, uu____4819)  in
            FStar_TypeChecker_NBETerm.GTot uu____4811
        | FStar_Syntax_Syntax.Comp ctyp ->
            let uu____4825 = translate_comp_typ cfg bs ctyp  in
            FStar_TypeChecker_NBETerm.Comp uu____4825

and (iapp :
  config ->
    FStar_TypeChecker_NBETerm.t ->
      FStar_TypeChecker_NBETerm.args -> FStar_TypeChecker_NBETerm.t)
  =
  fun cfg  ->
    fun f  ->
      fun args  ->
        let mk t = mk_rt f.FStar_TypeChecker_NBETerm.nbe_r t  in
        let uu____4835 =
          let uu____4836 = unlazy_unmeta f  in
          uu____4836.FStar_TypeChecker_NBETerm.nbe_t  in
        match uu____4835 with
        | FStar_TypeChecker_NBETerm.Lam (f1,binders,n) ->
            let m = FStar_List.length args  in
            if m < n
            then
              let arg_values_rev = map_rev FStar_Pervasives_Native.fst args
                 in
              let binders1 =
                match binders with
                | FStar_Util.Inr raw_args ->
                    let uu____4969 = FStar_List.splitAt m raw_args  in
                    (match uu____4969 with
                     | (uu____5010,raw_args1) -> FStar_Util.Inr raw_args1)
                | FStar_Util.Inl (ctx,xs,rc) ->
                    let uu____5079 = FStar_List.splitAt m xs  in
                    (match uu____5079 with
                     | (uu____5126,xs1) ->
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
                (let uu____5226 = FStar_List.splitAt n args  in
                 match uu____5226 with
                 | (args1,args') ->
                     let uu____5273 =
                       let uu____5274 =
                         map_rev FStar_Pervasives_Native.fst args1  in
                       f1 uu____5274  in
                     iapp cfg uu____5273 args')
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
                   FStar_TypeChecker_NBETerm.nbe_r = uu____5393;_},uu____5394)::args2
                  -> aux args2 (u :: us1) ts1
              | a::args2 -> aux args2 us1 (a :: ts1)
              | [] -> (us1, ts1)  in
            let uu____5438 = aux args us ts  in
            (match uu____5438 with
             | (us',ts') ->
                 FStar_All.pipe_left mk
                   (FStar_TypeChecker_NBETerm.Construct (i, us', ts')))
        | FStar_TypeChecker_NBETerm.FV (i,us,ts) ->
            let rec aux args1 us1 ts1 =
              match args1 with
              | ({
                   FStar_TypeChecker_NBETerm.nbe_t =
                     FStar_TypeChecker_NBETerm.Univ u;
                   FStar_TypeChecker_NBETerm.nbe_r = uu____5565;_},uu____5566)::args2
                  -> aux args2 (u :: us1) ts1
              | a::args2 -> aux args2 us1 (a :: ts1)
              | [] -> (us1, ts1)  in
            let uu____5610 = aux args us ts  in
            (match uu____5610 with
             | (us',ts') ->
                 FStar_All.pipe_left mk
                   (FStar_TypeChecker_NBETerm.FV (i, us', ts')))
        | FStar_TypeChecker_NBETerm.TopLevelLet (lb,arity,args_rev) ->
            let args_rev1 = FStar_List.rev_append args args_rev  in
            let n_args_rev = FStar_List.length args_rev1  in
            let n_univs = FStar_List.length lb.FStar_Syntax_Syntax.lbunivs
               in
            (debug cfg
               (fun uu____5688  ->
                  let uu____5689 =
                    FStar_Syntax_Print.lbname_to_string
                      lb.FStar_Syntax_Syntax.lbname
                     in
                  let uu____5691 = FStar_Util.string_of_int arity  in
                  let uu____5693 = FStar_Util.string_of_int n_args_rev  in
                  FStar_Util.print3
                    "Reached iapp for %s with arity %s and n_args = %s\n"
                    uu____5689 uu____5691 uu____5693);
             if n_args_rev >= arity
             then
               (let uu____5697 =
                  let uu____5710 =
                    let uu____5711 =
                      FStar_Syntax_Util.unascribe
                        lb.FStar_Syntax_Syntax.lbdef
                       in
                    uu____5711.FStar_Syntax_Syntax.n  in
                  match uu____5710 with
                  | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____5728) ->
                      (bs, body)
                  | uu____5761 -> ([], (lb.FStar_Syntax_Syntax.lbdef))  in
                match uu____5697 with
                | (bs,body) ->
                    if (n_univs + (FStar_List.length bs)) = arity
                    then
                      let uu____5802 =
                        FStar_Util.first_N (n_args_rev - arity) args_rev1  in
                      (match uu____5802 with
                       | (extra,args_rev2) ->
                           (debug cfg
                              (fun uu____5854  ->
                                 let uu____5855 =
                                   FStar_Syntax_Print.lbname_to_string
                                     lb.FStar_Syntax_Syntax.lbname
                                    in
                                 let uu____5857 =
                                   FStar_Syntax_Print.term_to_string body  in
                                 let uu____5859 =
                                   let uu____5861 =
                                     FStar_List.map
                                       (fun uu____5873  ->
                                          match uu____5873 with
                                          | (x,uu____5880) ->
                                              FStar_TypeChecker_NBETerm.t_to_string
                                                x) args_rev2
                                      in
                                   FStar_All.pipe_right uu____5861
                                     (FStar_String.concat ", ")
                                    in
                                 FStar_Util.print3
                                   "Reducing body of %s = %s,\n\twith args = %s\n"
                                   uu____5855 uu____5857 uu____5859);
                            (let t =
                               let uu____5888 =
                                 FStar_List.map FStar_Pervasives_Native.fst
                                   args_rev2
                                  in
                               translate cfg uu____5888 body  in
                             match extra with
                             | [] -> t
                             | uu____5899 ->
                                 iapp cfg t (FStar_List.rev extra))))
                    else
                      (let uu____5912 =
                         FStar_Util.first_N (n_args_rev - n_univs) args_rev1
                          in
                       match uu____5912 with
                       | (extra,univs) ->
                           let uu____5959 =
                             let uu____5960 =
                               FStar_List.map FStar_Pervasives_Native.fst
                                 univs
                                in
                             translate cfg uu____5960
                               lb.FStar_Syntax_Syntax.lbdef
                              in
                           iapp cfg uu____5959 (FStar_List.rev extra)))
             else
               FStar_All.pipe_left mk
                 (FStar_TypeChecker_NBETerm.TopLevelLet
                    (lb, arity, args_rev1)))
        | FStar_TypeChecker_NBETerm.TopLevelRec
            (lb,arity,decreases_list,args') ->
            let args1 = FStar_List.append args' args  in
            if (FStar_List.length args1) >= arity
            then
              let uu____6020 =
                should_reduce_recursive_definition args1 decreases_list  in
              (match uu____6020 with
               | (should_reduce,uu____6029,uu____6030) ->
                   if Prims.op_Negation should_reduce
                   then
                     let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname
                        in
                     (debug cfg
                        (fun uu____6038  ->
                           let uu____6039 =
                             FStar_Syntax_Print.fv_to_string fv  in
                           FStar_Util.print1
                             "Decided to not unfold recursive definition %s\n"
                             uu____6039);
                      (let uu____6042 =
                         let uu____6043 = FStar_Syntax_Syntax.range_of_fv fv
                            in
                         mk_rt uu____6043
                           (FStar_TypeChecker_NBETerm.FV (fv, [], []))
                          in
                       iapp cfg uu____6042 args1))
                   else
                     (debug cfg
                        (fun uu____6061  ->
                           let uu____6062 =
                             let uu____6064 =
                               FStar_Util.right lb.FStar_Syntax_Syntax.lbname
                                in
                             FStar_Syntax_Print.fv_to_string uu____6064  in
                           FStar_Util.print1
                             "Yes, Decided to unfold recursive definition %s\n"
                             uu____6062);
                      (let uu____6066 =
                         FStar_Util.first_N
                           (FStar_List.length lb.FStar_Syntax_Syntax.lbunivs)
                           args1
                          in
                       match uu____6066 with
                       | (univs,rest) ->
                           let uu____6113 =
                             let uu____6114 =
                               let uu____6117 =
                                 FStar_List.map FStar_Pervasives_Native.fst
                                   univs
                                  in
                               FStar_List.rev uu____6117  in
                             translate cfg uu____6114
                               lb.FStar_Syntax_Syntax.lbdef
                              in
                           iapp cfg uu____6113 rest)))
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
                  let uu____6235 =
                    should_reduce_recursive_definition args1 decreases_list
                     in
                  match uu____6235 with
                  | (should_reduce,uu____6244,uu____6245) ->
                      if Prims.op_Negation should_reduce
                      then
                        FStar_All.pipe_left mk
                          (FStar_TypeChecker_NBETerm.LocalLetRec
                             (i, lb, mutual_lbs, local_env, args1,
                               Prims.int_zero, decreases_list))
                      else
                        (let env = make_rec_env mutual_lbs local_env  in
                         debug cfg
                           (fun uu____6274  ->
                              (let uu____6276 =
                                 let uu____6278 =
                                   FStar_List.map
                                     FStar_TypeChecker_NBETerm.t_to_string
                                     env
                                    in
                                 FStar_String.concat ",\n\t " uu____6278  in
                               FStar_Util.print1
                                 "LocalLetRec Env = {\n\t%s\n}\n" uu____6276);
                              (let uu____6285 =
                                 let uu____6287 =
                                   FStar_List.map
                                     (fun uu____6299  ->
                                        match uu____6299 with
                                        | (t,uu____6306) ->
                                            FStar_TypeChecker_NBETerm.t_to_string
                                              t) args1
                                    in
                                 FStar_String.concat ",\n\t " uu____6287  in
                               FStar_Util.print1
                                 "LocalLetRec Args = {\n\t%s\n}\n" uu____6285));
                         (let uu____6309 =
                            translate cfg env lb.FStar_Syntax_Syntax.lbdef
                             in
                          iapp cfg uu____6309 args1))))
        | FStar_TypeChecker_NBETerm.Constant
            (FStar_TypeChecker_NBETerm.SConst (FStar_Const.Const_range_of ))
            ->
            (match args with
             | (a,uu____6311)::[] ->
                 mk_rt a.FStar_TypeChecker_NBETerm.nbe_r
                   (FStar_TypeChecker_NBETerm.Constant
                      (FStar_TypeChecker_NBETerm.Range
                         (a.FStar_TypeChecker_NBETerm.nbe_r)))
             | uu____6320 ->
                 let uu____6321 =
                   let uu____6323 = FStar_TypeChecker_NBETerm.t_to_string f
                      in
                   Prims.op_Hat "NBE ill-typed application: " uu____6323  in
                 failwith uu____6321)
        | FStar_TypeChecker_NBETerm.Constant
            (FStar_TypeChecker_NBETerm.SConst (FStar_Const.Const_set_range_of
            )) ->
            (match args with
             | (t,uu____6327)::({
                                  FStar_TypeChecker_NBETerm.nbe_t =
                                    FStar_TypeChecker_NBETerm.Constant
                                    (FStar_TypeChecker_NBETerm.Range r);
                                  FStar_TypeChecker_NBETerm.nbe_r =
                                    uu____6329;_},uu____6330)::[]
                 ->
                 let uu___934_6343 = t  in
                 {
                   FStar_TypeChecker_NBETerm.nbe_t =
                     (uu___934_6343.FStar_TypeChecker_NBETerm.nbe_t);
                   FStar_TypeChecker_NBETerm.nbe_r = r
                 }
             | uu____6344 ->
                 let uu____6345 =
                   let uu____6347 = FStar_TypeChecker_NBETerm.t_to_string f
                      in
                   Prims.op_Hat "NBE ill-typed application: " uu____6347  in
                 failwith uu____6345)
        | uu____6350 ->
            let uu____6351 =
              let uu____6353 = FStar_TypeChecker_NBETerm.t_to_string f  in
              Prims.op_Hat "NBE ill-typed application: " uu____6353  in
            failwith uu____6351

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
          let uu____6370 = FStar_TypeChecker_Cfg.cfg_env cfg.core_cfg  in
          let uu____6371 = FStar_Syntax_Syntax.lid_of_fv fvar  in
          FStar_TypeChecker_Env.lookup_qname uu____6370 uu____6371  in
        let uu____6372 = (is_constr qninfo) || (is_constr_fv fvar)  in
        if uu____6372
        then FStar_TypeChecker_NBETerm.mkConstruct fvar [] []
        else
          (let uu____6381 =
             FStar_TypeChecker_Normalize.should_unfold cfg.core_cfg
               (fun uu____6383  ->
                  (cfg.core_cfg).FStar_TypeChecker_Cfg.reifying) fvar qninfo
              in
           match uu____6381 with
           | FStar_TypeChecker_Normalize.Should_unfold_fully  ->
               failwith "Not yet handled"
           | FStar_TypeChecker_Normalize.Should_unfold_no  ->
               (debug1
                  (fun uu____6390  ->
                     let uu____6391 = FStar_Syntax_Print.fv_to_string fvar
                        in
                     FStar_Util.print1 "(1) Decided to not unfold %s\n"
                       uu____6391);
                (let uu____6394 =
                   FStar_TypeChecker_Cfg.find_prim_step cfg.core_cfg fvar  in
                 match uu____6394 with
                 | FStar_Pervasives_Native.Some prim_step when
                     prim_step.FStar_TypeChecker_Cfg.strong_reduction_ok ->
                     let arity =
                       prim_step.FStar_TypeChecker_Cfg.arity +
                         prim_step.FStar_TypeChecker_Cfg.univ_arity
                        in
                     (debug1
                        (fun uu____6405  ->
                           let uu____6406 =
                             FStar_Syntax_Print.fv_to_string fvar  in
                           FStar_Util.print1 "Found a primop %s\n" uu____6406);
                      (let uu____6409 =
                         let uu____6410 =
                           let uu____6443 =
                             let f uu____6476 =
                               let uu____6478 =
                                 FStar_Syntax_Syntax.new_bv
                                   FStar_Pervasives_Native.None
                                   FStar_Syntax_Syntax.t_unit
                                  in
                               (uu____6478, FStar_Pervasives_Native.None)  in
                             let uu____6481 =
                               let uu____6492 = FStar_Common.tabulate arity f
                                  in
                               ([], uu____6492, FStar_Pervasives_Native.None)
                                in
                             FStar_Util.Inl uu____6481  in
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
                               let uu____6566 =
                                 prim_step.FStar_TypeChecker_Cfg.interpretation_nbe
                                   callbacks args'
                                  in
                               match uu____6566 with
                               | FStar_Pervasives_Native.Some x ->
                                   (debug1
                                      (fun uu____6577  ->
                                         let uu____6578 =
                                           FStar_Syntax_Print.fv_to_string
                                             fvar
                                            in
                                         let uu____6580 =
                                           FStar_TypeChecker_NBETerm.t_to_string
                                             x
                                            in
                                         FStar_Util.print2
                                           "Primitive operator %s returned %s\n"
                                           uu____6578 uu____6580);
                                    x)
                               | FStar_Pervasives_Native.None  ->
                                   (debug1
                                      (fun uu____6588  ->
                                         let uu____6589 =
                                           FStar_Syntax_Print.fv_to_string
                                             fvar
                                            in
                                         FStar_Util.print1
                                           "Primitive operator %s failed\n"
                                           uu____6589);
                                    (let uu____6592 =
                                       FStar_TypeChecker_NBETerm.mkFV fvar []
                                         []
                                        in
                                     iapp cfg uu____6592 args'))),
                             uu____6443, arity)
                            in
                         FStar_TypeChecker_NBETerm.Lam uu____6410  in
                       FStar_All.pipe_left mk_t uu____6409))
                 | FStar_Pervasives_Native.Some uu____6597 ->
                     (debug1
                        (fun uu____6603  ->
                           let uu____6604 =
                             FStar_Syntax_Print.fv_to_string fvar  in
                           FStar_Util.print1 "(2) Decided to not unfold %s\n"
                             uu____6604);
                      FStar_TypeChecker_NBETerm.mkFV fvar [] [])
                 | uu____6611 ->
                     (debug1
                        (fun uu____6619  ->
                           let uu____6620 =
                             FStar_Syntax_Print.fv_to_string fvar  in
                           FStar_Util.print1 "(3) Decided to not unfold %s\n"
                             uu____6620);
                      FStar_TypeChecker_NBETerm.mkFV fvar [] [])))
           | FStar_TypeChecker_Normalize.Should_unfold_reify  ->
               let t =
                 let is_qninfo_visible =
                   let uu____6630 =
                     FStar_TypeChecker_Env.lookup_definition_qninfo
                       (cfg.core_cfg).FStar_TypeChecker_Cfg.delta_level
                       (fvar.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                       qninfo
                      in
                   FStar_Option.isSome uu____6630  in
                 if is_qninfo_visible
                 then
                   match qninfo with
                   | FStar_Pervasives_Native.Some
                       (FStar_Util.Inr
                        ({
                           FStar_Syntax_Syntax.sigel =
                             FStar_Syntax_Syntax.Sig_let ((is_rec,lbs),names);
                           FStar_Syntax_Syntax.sigrng = uu____6645;
                           FStar_Syntax_Syntax.sigquals = uu____6646;
                           FStar_Syntax_Syntax.sigmeta = uu____6647;
                           FStar_Syntax_Syntax.sigattrs = uu____6648;
                           FStar_Syntax_Syntax.sigopts = uu____6649;_},_us_opt),_rng)
                       ->
                       (debug1
                          (fun uu____6719  ->
                             let uu____6720 =
                               FStar_Syntax_Print.fv_to_string fvar  in
                             FStar_Util.print1 "(1) Decided to unfold %s\n"
                               uu____6720);
                        (let lbm = find_let lbs fvar  in
                         match lbm with
                         | FStar_Pervasives_Native.Some lb ->
                             if
                               is_rec &&
                                 ((cfg.core_cfg).FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta
                             then
                               let uu____6728 = let_rec_arity lb  in
                               (match uu____6728 with
                                | (ar,lst) ->
                                    let uu____6747 =
                                      let uu____6752 =
                                        FStar_Syntax_Syntax.range_of_fv fvar
                                         in
                                      mk_rt uu____6752  in
                                    FStar_All.pipe_left uu____6747
                                      (FStar_TypeChecker_NBETerm.TopLevelRec
                                         (lb, ar, lst, [])))
                             else translate_letbinding cfg bs lb
                         | FStar_Pervasives_Native.None  ->
                             failwith "Could not find let binding"))
                   | uu____6770 ->
                       (debug1
                          (fun uu____6776  ->
                             let uu____6777 =
                               FStar_Syntax_Print.fv_to_string fvar  in
                             FStar_Util.print1
                               "(1) qninfo is None for (%s)\n" uu____6777);
                        FStar_TypeChecker_NBETerm.mkFV fvar [] [])
                 else
                   (debug1
                      (fun uu____6791  ->
                         let uu____6792 =
                           FStar_Syntax_Print.fv_to_string fvar  in
                         FStar_Util.print1
                           "(1) qninfo is not visible at this level (%s)\n"
                           uu____6792);
                    FStar_TypeChecker_NBETerm.mkFV fvar [] [])
                  in
               (cache_add cfg fvar t; t)
           | FStar_TypeChecker_Normalize.Should_unfold_yes  ->
               let t =
                 let is_qninfo_visible =
                   let uu____6803 =
                     FStar_TypeChecker_Env.lookup_definition_qninfo
                       (cfg.core_cfg).FStar_TypeChecker_Cfg.delta_level
                       (fvar.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                       qninfo
                      in
                   FStar_Option.isSome uu____6803  in
                 if is_qninfo_visible
                 then
                   match qninfo with
                   | FStar_Pervasives_Native.Some
                       (FStar_Util.Inr
                        ({
                           FStar_Syntax_Syntax.sigel =
                             FStar_Syntax_Syntax.Sig_let ((is_rec,lbs),names);
                           FStar_Syntax_Syntax.sigrng = uu____6818;
                           FStar_Syntax_Syntax.sigquals = uu____6819;
                           FStar_Syntax_Syntax.sigmeta = uu____6820;
                           FStar_Syntax_Syntax.sigattrs = uu____6821;
                           FStar_Syntax_Syntax.sigopts = uu____6822;_},_us_opt),_rng)
                       ->
                       (debug1
                          (fun uu____6892  ->
                             let uu____6893 =
                               FStar_Syntax_Print.fv_to_string fvar  in
                             FStar_Util.print1 "(1) Decided to unfold %s\n"
                               uu____6893);
                        (let lbm = find_let lbs fvar  in
                         match lbm with
                         | FStar_Pervasives_Native.Some lb ->
                             if
                               is_rec &&
                                 ((cfg.core_cfg).FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta
                             then
                               let uu____6901 = let_rec_arity lb  in
                               (match uu____6901 with
                                | (ar,lst) ->
                                    let uu____6920 =
                                      let uu____6925 =
                                        FStar_Syntax_Syntax.range_of_fv fvar
                                         in
                                      mk_rt uu____6925  in
                                    FStar_All.pipe_left uu____6920
                                      (FStar_TypeChecker_NBETerm.TopLevelRec
                                         (lb, ar, lst, [])))
                             else translate_letbinding cfg bs lb
                         | FStar_Pervasives_Native.None  ->
                             failwith "Could not find let binding"))
                   | uu____6943 ->
                       (debug1
                          (fun uu____6949  ->
                             let uu____6950 =
                               FStar_Syntax_Print.fv_to_string fvar  in
                             FStar_Util.print1
                               "(1) qninfo is None for (%s)\n" uu____6950);
                        FStar_TypeChecker_NBETerm.mkFV fvar [] [])
                 else
                   (debug1
                      (fun uu____6964  ->
                         let uu____6965 =
                           FStar_Syntax_Print.fv_to_string fvar  in
                         FStar_Util.print1
                           "(1) qninfo is not visible at this level (%s)\n"
                           uu____6965);
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
        let uu____6989 =
          FStar_Syntax_Util.arrow_formals lb.FStar_Syntax_Syntax.lbtyp  in
        match uu____6989 with
        | (formals,uu____6997) ->
            let arity = (FStar_List.length us) + (FStar_List.length formals)
               in
            if arity = Prims.int_zero
            then translate cfg bs lb.FStar_Syntax_Syntax.lbdef
            else
              (let uu____7015 =
                 FStar_Util.is_right lb.FStar_Syntax_Syntax.lbname  in
               if uu____7015
               then
                 (debug1
                    (fun uu____7025  ->
                       let uu____7026 =
                         FStar_Syntax_Print.lbname_to_string
                           lb.FStar_Syntax_Syntax.lbname
                          in
                       let uu____7028 = FStar_Util.string_of_int arity  in
                       FStar_Util.print2
                         "Making TopLevelLet for %s with arity %s\n"
                         uu____7026 uu____7028);
                  (let uu____7031 =
                     let uu____7036 =
                       FStar_Syntax_Syntax.range_of_lbname
                         lb.FStar_Syntax_Syntax.lbname
                        in
                     mk_rt uu____7036  in
                   FStar_All.pipe_left uu____7031
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
          let uu____7059 = let_rec_arity b  in
          match uu____7059 with
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
        let uu____7129 = FStar_BigInt.big_int_of_string s  in
        FStar_TypeChecker_NBETerm.Int uu____7129
    | FStar_Const.Const_string (s,r) ->
        FStar_TypeChecker_NBETerm.String (s, r)
    | FStar_Const.Const_char c1 -> FStar_TypeChecker_NBETerm.Char c1
    | FStar_Const.Const_range r -> FStar_TypeChecker_NBETerm.Range r
    | uu____7138 -> FStar_TypeChecker_NBETerm.SConst c

and (readback_comp :
  config -> FStar_TypeChecker_NBETerm.comp -> FStar_Syntax_Syntax.comp) =
  fun cfg  ->
    fun c  ->
      let c' =
        match c with
        | FStar_TypeChecker_NBETerm.Tot (typ,u) ->
            let uu____7148 =
              let uu____7157 = readback cfg typ  in (uu____7157, u)  in
            FStar_Syntax_Syntax.Total uu____7148
        | FStar_TypeChecker_NBETerm.GTot (typ,u) ->
            let uu____7170 =
              let uu____7179 = readback cfg typ  in (uu____7179, u)  in
            FStar_Syntax_Syntax.GTotal uu____7170
        | FStar_TypeChecker_NBETerm.Comp ctyp ->
            let uu____7187 = readback_comp_typ cfg ctyp  in
            FStar_Syntax_Syntax.Comp uu____7187
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
        let uu____7193 = c  in
        match uu____7193 with
        | { FStar_Syntax_Syntax.comp_univs = comp_univs;
            FStar_Syntax_Syntax.effect_name = effect_name;
            FStar_Syntax_Syntax.result_typ = result_typ;
            FStar_Syntax_Syntax.effect_args = effect_args;
            FStar_Syntax_Syntax.flags = flags;_} ->
            let uu____7213 =
              FStar_List.map (translate_univ cfg bs) comp_univs  in
            let uu____7214 = translate cfg bs result_typ  in
            let uu____7215 =
              FStar_List.map
                (fun x  ->
                   let uu____7243 =
                     translate cfg bs (FStar_Pervasives_Native.fst x)  in
                   (uu____7243, (FStar_Pervasives_Native.snd x))) effect_args
               in
            let uu____7250 = FStar_List.map (translate_flag cfg bs) flags  in
            {
              FStar_TypeChecker_NBETerm.comp_univs = uu____7213;
              FStar_TypeChecker_NBETerm.effect_name = effect_name;
              FStar_TypeChecker_NBETerm.result_typ = uu____7214;
              FStar_TypeChecker_NBETerm.effect_args = uu____7215;
              FStar_TypeChecker_NBETerm.flags = uu____7250
            }

and (readback_comp_typ :
  config ->
    FStar_TypeChecker_NBETerm.comp_typ -> FStar_Syntax_Syntax.comp_typ)
  =
  fun cfg  ->
    fun c  ->
      let uu____7255 = readback cfg c.FStar_TypeChecker_NBETerm.result_typ
         in
      let uu____7258 =
        FStar_List.map
          (fun x  ->
             let uu____7284 = readback cfg (FStar_Pervasives_Native.fst x)
                in
             (uu____7284, (FStar_Pervasives_Native.snd x)))
          c.FStar_TypeChecker_NBETerm.effect_args
         in
      let uu____7285 =
        FStar_List.map (readback_flag cfg) c.FStar_TypeChecker_NBETerm.flags
         in
      {
        FStar_Syntax_Syntax.comp_univs =
          (c.FStar_TypeChecker_NBETerm.comp_univs);
        FStar_Syntax_Syntax.effect_name =
          (c.FStar_TypeChecker_NBETerm.effect_name);
        FStar_Syntax_Syntax.result_typ = uu____7255;
        FStar_Syntax_Syntax.effect_args = uu____7258;
        FStar_Syntax_Syntax.flags = uu____7285
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
        let uu____7293 = c  in
        match uu____7293 with
        | { FStar_Syntax_Syntax.residual_effect = residual_effect;
            FStar_Syntax_Syntax.residual_typ = residual_typ;
            FStar_Syntax_Syntax.residual_flags = residual_flags;_} ->
            let uu____7303 =
              if
                ((cfg.core_cfg).FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.for_extraction
              then FStar_Pervasives_Native.None
              else FStar_Util.map_opt residual_typ (translate cfg bs)  in
            let uu____7313 =
              FStar_List.map (translate_flag cfg bs) residual_flags  in
            {
              FStar_TypeChecker_NBETerm.residual_effect = residual_effect;
              FStar_TypeChecker_NBETerm.residual_typ = uu____7303;
              FStar_TypeChecker_NBETerm.residual_flags = uu____7313
            }

and (readback_residual_comp :
  config ->
    FStar_TypeChecker_NBETerm.residual_comp ->
      FStar_Syntax_Syntax.residual_comp)
  =
  fun cfg  ->
    fun c  ->
      let uu____7318 =
        FStar_Util.map_opt c.FStar_TypeChecker_NBETerm.residual_typ
          (fun x  ->
             debug cfg
               (fun uu____7329  ->
                  let uu____7330 = FStar_TypeChecker_NBETerm.t_to_string x
                     in
                  FStar_Util.print1 "Reading back residualtype %s\n"
                    uu____7330);
             readback cfg x)
         in
      let uu____7333 =
        FStar_List.map (readback_flag cfg)
          c.FStar_TypeChecker_NBETerm.residual_flags
         in
      {
        FStar_Syntax_Syntax.residual_effect =
          (c.FStar_TypeChecker_NBETerm.residual_effect);
        FStar_Syntax_Syntax.residual_typ = uu____7318;
        FStar_Syntax_Syntax.residual_flags = uu____7333
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
            let uu____7344 = translate cfg bs tm  in
            FStar_TypeChecker_NBETerm.DECREASES uu____7344

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
          let uu____7348 = readback cfg t  in
          FStar_Syntax_Syntax.DECREASES uu____7348

and (translate_monadic :
  (FStar_Syntax_Syntax.monad_name * FStar_Syntax_Syntax.term'
    FStar_Syntax_Syntax.syntax) ->
    config ->
      FStar_TypeChecker_NBETerm.t Prims.list ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
          FStar_TypeChecker_NBETerm.t)
  =
  fun uu____7351  ->
    fun cfg  ->
      fun bs  ->
        fun e  ->
          match uu____7351 with
          | (m,ty) ->
              let e1 = FStar_Syntax_Util.unascribe e  in
              (match e1.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                   let uu____7389 =
                     let uu____7398 =
                       FStar_TypeChecker_Env.norm_eff_name
                         (cfg.core_cfg).FStar_TypeChecker_Cfg.tcenv m
                        in
                     FStar_TypeChecker_Env.effect_decl_opt
                       (cfg.core_cfg).FStar_TypeChecker_Cfg.tcenv uu____7398
                      in
                   (match uu____7389 with
                    | FStar_Pervasives_Native.None  ->
                        let uu____7405 =
                          let uu____7407 = FStar_Ident.string_of_lid m  in
                          FStar_Util.format1
                            "Effect declaration not found: %s" uu____7407
                           in
                        failwith uu____7405
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
                          let uu____7429 =
                            let uu____7430 =
                              let uu____7449 =
                                let uu____7458 =
                                  let uu____7465 =
                                    FStar_Util.left
                                      lb.FStar_Syntax_Syntax.lbname
                                     in
                                  (uu____7465, FStar_Pervasives_Native.None)
                                   in
                                [uu____7458]  in
                              (uu____7449, body,
                                (FStar_Pervasives_Native.Some body_rc))
                               in
                            FStar_Syntax_Syntax.Tm_abs uu____7430  in
                          FStar_Syntax_Syntax.mk uu____7429
                            body.FStar_Syntax_Syntax.pos
                           in
                        let maybe_range_arg =
                          let uu____7499 =
                            FStar_Util.for_some
                              (FStar_Syntax_Util.attr_eq
                                 FStar_Syntax_Util.dm4f_bind_range_attr)
                              ed.FStar_Syntax_Syntax.eff_attrs
                             in
                          if uu____7499
                          then
                            let uu____7508 =
                              let uu____7513 =
                                let uu____7514 =
                                  FStar_TypeChecker_Cfg.embed_simple
                                    FStar_Syntax_Embeddings.e_range
                                    lb.FStar_Syntax_Syntax.lbpos
                                    lb.FStar_Syntax_Syntax.lbpos
                                   in
                                translate cfg [] uu____7514  in
                              (uu____7513, FStar_Pervasives_Native.None)  in
                            let uu____7515 =
                              let uu____7522 =
                                let uu____7527 =
                                  let uu____7528 =
                                    FStar_TypeChecker_Cfg.embed_simple
                                      FStar_Syntax_Embeddings.e_range
                                      body.FStar_Syntax_Syntax.pos
                                      body.FStar_Syntax_Syntax.pos
                                     in
                                  translate cfg [] uu____7528  in
                                (uu____7527, FStar_Pervasives_Native.None)
                                 in
                              [uu____7522]  in
                            uu____7508 :: uu____7515
                          else []  in
                        let t =
                          let uu____7548 =
                            let uu____7549 =
                              let uu____7550 =
                                let uu____7551 =
                                  let uu____7552 =
                                    let uu____7559 =
                                      FStar_All.pipe_right ed
                                        FStar_Syntax_Util.get_bind_repr
                                       in
                                    FStar_All.pipe_right uu____7559
                                      FStar_Util.must
                                     in
                                  FStar_All.pipe_right uu____7552
                                    FStar_Pervasives_Native.snd
                                   in
                                FStar_Syntax_Util.un_uinst uu____7551  in
                              translate cfg' [] uu____7550  in
                            let uu____7580 =
                              let uu____7581 =
                                let uu____7586 =
                                  FStar_All.pipe_left mk_t
                                    (FStar_TypeChecker_NBETerm.Univ
                                       FStar_Syntax_Syntax.U_unknown)
                                   in
                                (uu____7586, FStar_Pervasives_Native.None)
                                 in
                              let uu____7587 =
                                let uu____7594 =
                                  let uu____7599 =
                                    FStar_All.pipe_left mk_t
                                      (FStar_TypeChecker_NBETerm.Univ
                                         FStar_Syntax_Syntax.U_unknown)
                                     in
                                  (uu____7599, FStar_Pervasives_Native.None)
                                   in
                                [uu____7594]  in
                              uu____7581 :: uu____7587  in
                            iapp cfg uu____7549 uu____7580  in
                          let uu____7612 =
                            let uu____7613 =
                              let uu____7620 =
                                let uu____7625 =
                                  translate cfg' bs
                                    lb.FStar_Syntax_Syntax.lbtyp
                                   in
                                (uu____7625, FStar_Pervasives_Native.None)
                                 in
                              let uu____7626 =
                                let uu____7633 =
                                  let uu____7638 = translate cfg' bs ty  in
                                  (uu____7638, FStar_Pervasives_Native.None)
                                   in
                                [uu____7633]  in
                              uu____7620 :: uu____7626  in
                            let uu____7651 =
                              let uu____7658 =
                                let uu____7665 =
                                  let uu____7672 =
                                    let uu____7677 =
                                      translate cfg bs
                                        lb.FStar_Syntax_Syntax.lbdef
                                       in
                                    (uu____7677,
                                      FStar_Pervasives_Native.None)
                                     in
                                  let uu____7678 =
                                    let uu____7685 =
                                      let uu____7692 =
                                        let uu____7697 =
                                          translate cfg bs body_lam  in
                                        (uu____7697,
                                          FStar_Pervasives_Native.None)
                                         in
                                      [uu____7692]  in
                                    ((mk_t FStar_TypeChecker_NBETerm.Unknown),
                                      FStar_Pervasives_Native.None) ::
                                      uu____7685
                                     in
                                  uu____7672 :: uu____7678  in
                                ((mk_t FStar_TypeChecker_NBETerm.Unknown),
                                  FStar_Pervasives_Native.None) :: uu____7665
                                 in
                              FStar_List.append maybe_range_arg uu____7658
                               in
                            FStar_List.append uu____7613 uu____7651  in
                          iapp cfg uu____7548 uu____7612  in
                        (debug cfg
                           (fun uu____7729  ->
                              let uu____7730 =
                                FStar_TypeChecker_NBETerm.t_to_string t  in
                              FStar_Util.print1 "translate_monadic: %s\n"
                                uu____7730);
                         t))
               | FStar_Syntax_Syntax.Tm_app
                   ({
                      FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                        (FStar_Const.Const_reflect uu____7733);
                      FStar_Syntax_Syntax.pos = uu____7734;
                      FStar_Syntax_Syntax.vars = uu____7735;_},(e2,uu____7737)::[])
                   ->
                   let uu____7776 = reifying_false cfg  in
                   translate uu____7776 bs e2
               | FStar_Syntax_Syntax.Tm_app (head,args) ->
                   (debug cfg
                      (fun uu____7807  ->
                         let uu____7808 =
                           FStar_Syntax_Print.term_to_string head  in
                         let uu____7810 =
                           FStar_Syntax_Print.args_to_string args  in
                         FStar_Util.print2
                           "translate_monadic app (%s) @ (%s)\n" uu____7808
                           uu____7810);
                    (let fallback1 uu____7818 = translate cfg bs e1  in
                     let fallback2 uu____7824 =
                       let uu____7825 = reifying_false cfg  in
                       let uu____7826 =
                         FStar_Syntax_Syntax.mk
                           (FStar_Syntax_Syntax.Tm_meta
                              (e1,
                                (FStar_Syntax_Syntax.Meta_monadic (m, ty))))
                           e1.FStar_Syntax_Syntax.pos
                          in
                       translate uu____7825 bs uu____7826  in
                     let uu____7831 =
                       let uu____7832 = FStar_Syntax_Util.un_uinst head  in
                       uu____7832.FStar_Syntax_Syntax.n  in
                     match uu____7831 with
                     | FStar_Syntax_Syntax.Tm_fvar fv ->
                         let lid = FStar_Syntax_Syntax.lid_of_fv fv  in
                         let qninfo =
                           FStar_TypeChecker_Env.lookup_qname
                             (cfg.core_cfg).FStar_TypeChecker_Cfg.tcenv lid
                            in
                         let uu____7838 =
                           let uu____7840 =
                             FStar_TypeChecker_Env.is_action
                               (cfg.core_cfg).FStar_TypeChecker_Cfg.tcenv lid
                              in
                           Prims.op_Negation uu____7840  in
                         if uu____7838
                         then fallback1 ()
                         else
                           (let uu____7845 =
                              let uu____7847 =
                                FStar_TypeChecker_Env.lookup_definition_qninfo
                                  (cfg.core_cfg).FStar_TypeChecker_Cfg.delta_level
                                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                  qninfo
                                 in
                              FStar_Option.isNone uu____7847  in
                            if uu____7845
                            then fallback2 ()
                            else
                              (let e2 =
                                 let uu____7862 =
                                   FStar_Syntax_Util.mk_reify head  in
                                 FStar_Syntax_Syntax.mk_Tm_app uu____7862
                                   args e1.FStar_Syntax_Syntax.pos
                                  in
                               let uu____7863 = reifying_false cfg  in
                               translate uu____7863 bs e2))
                     | uu____7864 -> fallback1 ()))
               | FStar_Syntax_Syntax.Tm_match (sc,branches) ->
                   let branches1 =
                     FStar_All.pipe_right branches
                       (FStar_List.map
                          (fun uu____7985  ->
                             match uu____7985 with
                             | (pat,wopt,tm) ->
                                 let uu____8033 =
                                   FStar_Syntax_Util.mk_reify tm  in
                                 (pat, wopt, uu____8033)))
                      in
                   let tm =
                     FStar_Syntax_Syntax.mk
                       (FStar_Syntax_Syntax.Tm_match (sc, branches1))
                       e1.FStar_Syntax_Syntax.pos
                      in
                   let uu____8065 = reifying_false cfg  in
                   translate uu____8065 bs tm
               | FStar_Syntax_Syntax.Tm_meta
                   (t,FStar_Syntax_Syntax.Meta_monadic uu____8067) ->
                   translate_monadic (m, ty) cfg bs e1
               | FStar_Syntax_Syntax.Tm_meta
                   (t,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,ty'))
                   -> translate_monadic_lift (msrc, mtgt, ty') cfg bs e1
               | uu____8094 ->
                   let uu____8095 =
                     let uu____8097 = FStar_Syntax_Print.tag_of_term e1  in
                     FStar_Util.format1
                       "Unexpected case in translate_monadic: %s" uu____8097
                      in
                   failwith uu____8095)

and (translate_monadic_lift :
  (FStar_Syntax_Syntax.monad_name * FStar_Syntax_Syntax.monad_name *
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax) ->
    config ->
      FStar_TypeChecker_NBETerm.t Prims.list ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
          FStar_TypeChecker_NBETerm.t)
  =
  fun uu____8100  ->
    fun cfg  ->
      fun bs  ->
        fun e  ->
          match uu____8100 with
          | (msrc,mtgt,ty) ->
              let e1 = FStar_Syntax_Util.unascribe e  in
              let uu____8124 =
                (FStar_Syntax_Util.is_pure_effect msrc) ||
                  (FStar_Syntax_Util.is_div_effect msrc)
                 in
              if uu____8124
              then
                let ed =
                  let uu____8128 =
                    FStar_TypeChecker_Env.norm_eff_name
                      (cfg.core_cfg).FStar_TypeChecker_Cfg.tcenv mtgt
                     in
                  FStar_TypeChecker_Env.get_effect_decl
                    (cfg.core_cfg).FStar_TypeChecker_Cfg.tcenv uu____8128
                   in
                let ret =
                  let uu____8130 =
                    let uu____8131 =
                      let uu____8134 =
                        let uu____8135 =
                          let uu____8142 =
                            FStar_All.pipe_right ed
                              FStar_Syntax_Util.get_return_repr
                             in
                          FStar_All.pipe_right uu____8142 FStar_Util.must  in
                        FStar_All.pipe_right uu____8135
                          FStar_Pervasives_Native.snd
                         in
                      FStar_Syntax_Subst.compress uu____8134  in
                    uu____8131.FStar_Syntax_Syntax.n  in
                  match uu____8130 with
                  | FStar_Syntax_Syntax.Tm_uinst (ret,uu____8188::[]) ->
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_uinst
                           (ret, [FStar_Syntax_Syntax.U_unknown]))
                        e1.FStar_Syntax_Syntax.pos
                  | uu____8195 ->
                      failwith "NYI: Reification of indexed effect (NBE)"
                   in
                let cfg' = reifying_false cfg  in
                let t =
                  let uu____8199 =
                    let uu____8200 = translate cfg' [] ret  in
                    let uu____8201 =
                      let uu____8202 =
                        let uu____8207 =
                          FStar_All.pipe_left mk_t
                            (FStar_TypeChecker_NBETerm.Univ
                               FStar_Syntax_Syntax.U_unknown)
                           in
                        (uu____8207, FStar_Pervasives_Native.None)  in
                      [uu____8202]  in
                    iapp cfg' uu____8200 uu____8201  in
                  let uu____8216 =
                    let uu____8217 =
                      let uu____8222 = translate cfg' bs ty  in
                      (uu____8222, FStar_Pervasives_Native.None)  in
                    let uu____8223 =
                      let uu____8230 =
                        let uu____8235 = translate cfg' bs e1  in
                        (uu____8235, FStar_Pervasives_Native.None)  in
                      [uu____8230]  in
                    uu____8217 :: uu____8223  in
                  iapp cfg' uu____8199 uu____8216  in
                (debug cfg
                   (fun uu____8251  ->
                      let uu____8252 =
                        FStar_TypeChecker_NBETerm.t_to_string t  in
                      FStar_Util.print1 "translate_monadic_lift(1): %s\n"
                        uu____8252);
                 t)
              else
                (let uu____8257 =
                   FStar_TypeChecker_Env.monad_leq
                     (cfg.core_cfg).FStar_TypeChecker_Cfg.tcenv msrc mtgt
                    in
                 match uu____8257 with
                 | FStar_Pervasives_Native.None  ->
                     let uu____8260 =
                       let uu____8262 = FStar_Ident.string_of_lid msrc  in
                       let uu____8264 = FStar_Ident.string_of_lid mtgt  in
                       FStar_Util.format2
                         "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                         uu____8262 uu____8264
                        in
                     failwith uu____8260
                 | FStar_Pervasives_Native.Some
                     { FStar_TypeChecker_Env.msource = uu____8267;
                       FStar_TypeChecker_Env.mtarget = uu____8268;
                       FStar_TypeChecker_Env.mlift =
                         { FStar_TypeChecker_Env.mlift_wp = uu____8269;
                           FStar_TypeChecker_Env.mlift_term =
                             FStar_Pervasives_Native.None ;_};_}
                     ->
                     let uu____8289 =
                       let uu____8291 = FStar_Ident.string_of_lid msrc  in
                       let uu____8293 = FStar_Ident.string_of_lid mtgt  in
                       FStar_Util.format2
                         "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
                         uu____8291 uu____8293
                        in
                     failwith uu____8289
                 | FStar_Pervasives_Native.Some
                     { FStar_TypeChecker_Env.msource = uu____8296;
                       FStar_TypeChecker_Env.mtarget = uu____8297;
                       FStar_TypeChecker_Env.mlift =
                         { FStar_TypeChecker_Env.mlift_wp = uu____8298;
                           FStar_TypeChecker_Env.mlift_term =
                             FStar_Pervasives_Native.Some lift;_};_}
                     ->
                     let lift_lam =
                       let x =
                         FStar_Syntax_Syntax.new_bv
                           FStar_Pervasives_Native.None
                           FStar_Syntax_Syntax.tun
                          in
                       let uu____8332 =
                         let uu____8335 = FStar_Syntax_Syntax.bv_to_name x
                            in
                         lift FStar_Syntax_Syntax.U_unknown ty uu____8335  in
                       FStar_Syntax_Util.abs
                         [(x, FStar_Pervasives_Native.None)] uu____8332
                         FStar_Pervasives_Native.None
                        in
                     let cfg' = reifying_false cfg  in
                     let t =
                       let uu____8352 = translate cfg' [] lift_lam  in
                       let uu____8353 =
                         let uu____8354 =
                           let uu____8359 = translate cfg bs e1  in
                           (uu____8359, FStar_Pervasives_Native.None)  in
                         [uu____8354]  in
                       iapp cfg uu____8352 uu____8353  in
                     (debug cfg
                        (fun uu____8371  ->
                           let uu____8372 =
                             FStar_TypeChecker_NBETerm.t_to_string t  in
                           FStar_Util.print1
                             "translate_monadic_lift(2): %s\n" uu____8372);
                      t))

and (readback :
  config -> FStar_TypeChecker_NBETerm.t -> FStar_Syntax_Syntax.term) =
  fun cfg  ->
    fun x  ->
      let debug1 = debug cfg  in
      let readback_args cfg1 args =
        map_rev
          (fun uu____8426  ->
             match uu____8426 with
             | (x1,q) ->
                 let uu____8437 = readback cfg1 x1  in (uu____8437, q)) args
         in
      let with_range t =
        let uu___1255_8450 = t  in
        {
          FStar_Syntax_Syntax.n = (uu___1255_8450.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = (x.FStar_TypeChecker_NBETerm.nbe_r);
          FStar_Syntax_Syntax.vars =
            (uu___1255_8450.FStar_Syntax_Syntax.vars)
        }  in
      let mk t = FStar_Syntax_Syntax.mk t x.FStar_TypeChecker_NBETerm.nbe_r
         in
      debug1
        (fun uu____8466  ->
           let uu____8467 = FStar_TypeChecker_NBETerm.t_to_string x  in
           FStar_Util.print1 "Readback: %s\n" uu____8467);
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
           let uu____8475 =
             let uu____8478 = FStar_BigInt.string_of_big_int i  in
             FStar_Syntax_Util.exp_int uu____8478  in
           with_range uu____8475
       | FStar_TypeChecker_NBETerm.Constant (FStar_TypeChecker_NBETerm.String
           (s,r)) ->
           mk
             (FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_string (s, r)))
       | FStar_TypeChecker_NBETerm.Constant (FStar_TypeChecker_NBETerm.Char
           c) ->
           let uu____8487 = FStar_Syntax_Util.exp_char c  in
           with_range uu____8487
       | FStar_TypeChecker_NBETerm.Constant (FStar_TypeChecker_NBETerm.Range
           r) ->
           FStar_TypeChecker_Cfg.embed_simple FStar_Syntax_Embeddings.e_range
             x.FStar_TypeChecker_NBETerm.nbe_r r
       | FStar_TypeChecker_NBETerm.Constant (FStar_TypeChecker_NBETerm.SConst
           c) -> mk (FStar_Syntax_Syntax.Tm_constant c)
       | FStar_TypeChecker_NBETerm.Meta (t,m) ->
           let uu____8498 =
             let uu____8499 =
               let uu____8506 = readback cfg t  in
               let uu____8509 = FStar_Thunk.force m  in
               (uu____8506, uu____8509)  in
             FStar_Syntax_Syntax.Tm_meta uu____8499  in
           mk uu____8498
       | FStar_TypeChecker_NBETerm.Type_t u ->
           mk (FStar_Syntax_Syntax.Tm_type u)
       | FStar_TypeChecker_NBETerm.Lam (f,binders,arity) ->
           let uu____8568 =
             match binders with
             | FStar_Util.Inl (ctx,binders1,rc) ->
                 let uu____8616 =
                   FStar_List.fold_left
                     (fun uu____8670  ->
                        fun uu____8671  ->
                          match (uu____8670, uu____8671) with
                          | ((ctx1,binders_rev,accus_rev),(x1,q)) ->
                              let tnorm =
                                let uu____8796 =
                                  translate cfg ctx1
                                    x1.FStar_Syntax_Syntax.sort
                                   in
                                readback cfg uu____8796  in
                              let x2 =
                                let uu___1313_8798 =
                                  FStar_Syntax_Syntax.freshen_bv x1  in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___1313_8798.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___1313_8798.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = tnorm
                                }  in
                              let ax = FStar_TypeChecker_NBETerm.mkAccuVar x2
                                 in
                              let ctx2 = ax :: ctx1  in
                              (ctx2, ((x2, q) :: binders_rev), (ax ::
                                accus_rev))) (ctx, [], []) binders1
                    in
                 (match uu____8616 with
                  | (ctx1,binders_rev,accus_rev) ->
                      let rc1 =
                        match rc with
                        | FStar_Pervasives_Native.None  ->
                            FStar_Pervasives_Native.None
                        | FStar_Pervasives_Native.Some rc1 ->
                            let uu____8884 =
                              let uu____8885 =
                                translate_residual_comp cfg ctx1 rc1  in
                              readback_residual_comp cfg uu____8885  in
                            FStar_Pervasives_Native.Some uu____8884
                         in
                      ((FStar_List.rev binders_rev), accus_rev, rc1))
             | FStar_Util.Inr args ->
                 let uu____8919 =
                   FStar_List.fold_right
                     (fun uu____8960  ->
                        fun uu____8961  ->
                          match (uu____8960, uu____8961) with
                          | ((t,uu____9013),(binders1,accus)) ->
                              let x1 =
                                let uu____9055 = readback cfg t  in
                                FStar_Syntax_Syntax.new_bv
                                  FStar_Pervasives_Native.None uu____9055
                                 in
                              let uu____9056 =
                                let uu____9059 =
                                  FStar_TypeChecker_NBETerm.mkAccuVar x1  in
                                uu____9059 :: accus  in
                              (((x1, FStar_Pervasives_Native.None) ::
                                binders1), uu____9056)) args ([], [])
                    in
                 (match uu____8919 with
                  | (binders1,accus) ->
                      (binders1, (FStar_List.rev accus),
                        FStar_Pervasives_Native.None))
              in
           (match uu____8568 with
            | (binders1,accus_rev,rc) ->
                let body =
                  let uu____9142 = f accus_rev  in readback cfg uu____9142
                   in
                let uu____9143 = FStar_Syntax_Util.abs binders1 body rc  in
                with_range uu____9143)
       | FStar_TypeChecker_NBETerm.Refinement (f,targ) ->
           if
             ((cfg.core_cfg).FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.for_extraction
           then
             let uu____9169 =
               let uu____9170 = targ ()  in
               FStar_Pervasives_Native.fst uu____9170  in
             readback cfg uu____9169
           else
             (let x1 =
                let uu____9178 =
                  let uu____9179 =
                    let uu____9180 = targ ()  in
                    FStar_Pervasives_Native.fst uu____9180  in
                  readback cfg uu____9179  in
                FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                  uu____9178
                 in
              let body =
                let uu____9186 =
                  let uu____9187 = FStar_TypeChecker_NBETerm.mkAccuVar x1  in
                  f uu____9187  in
                readback cfg uu____9186  in
              let refinement = FStar_Syntax_Util.refine x1 body  in
              let uu____9191 =
                if
                  ((cfg.core_cfg).FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.simplify
                then
                  FStar_TypeChecker_Common.simplify
                    ((cfg.core_cfg).FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                    refinement
                else refinement  in
              with_range uu____9191)
       | FStar_TypeChecker_NBETerm.Reflect t ->
           let tm = readback cfg t  in
           let uu____9201 = FStar_Syntax_Util.mk_reflect tm  in
           with_range uu____9201
       | FStar_TypeChecker_NBETerm.Arrow (FStar_Util.Inl f) ->
           let uu____9219 = FStar_Thunk.force f  in with_range uu____9219
       | FStar_TypeChecker_NBETerm.Arrow (FStar_Util.Inr (args,c)) ->
           let binders =
             FStar_List.map
               (fun uu____9268  ->
                  match uu____9268 with
                  | (t,q) ->
                      let t1 = readback cfg t  in
                      let x1 =
                        FStar_Syntax_Syntax.new_bv
                          FStar_Pervasives_Native.None t1
                         in
                      (x1, q)) args
              in
           let c1 = readback_comp cfg c  in
           let uu____9282 = FStar_Syntax_Util.arrow binders c1  in
           with_range uu____9282
       | FStar_TypeChecker_NBETerm.Construct (fv,us,args) ->
           let args1 =
             map_rev
               (fun uu____9323  ->
                  match uu____9323 with
                  | (x1,q) ->
                      let uu____9334 = readback cfg x1  in (uu____9334, q))
               args
              in
           let fv1 =
             let uu____9338 = FStar_Syntax_Syntax.range_of_fv fv  in
             FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
               uu____9338
              in
           let app =
             let uu____9342 =
               FStar_Syntax_Syntax.mk_Tm_uinst fv1 (FStar_List.rev us)  in
             FStar_Syntax_Util.mk_app uu____9342 args1  in
           with_range app
       | FStar_TypeChecker_NBETerm.FV (fv,us,args) ->
           let args1 =
             map_rev
               (fun uu____9383  ->
                  match uu____9383 with
                  | (x1,q) ->
                      let uu____9394 = readback cfg x1  in (uu____9394, q))
               args
              in
           let fv1 =
             FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
               FStar_Range.dummyRange
              in
           let app =
             let uu____9401 =
               FStar_Syntax_Syntax.mk_Tm_uinst fv1 (FStar_List.rev us)  in
             FStar_Syntax_Util.mk_app uu____9401 args1  in
           let uu____9404 =
             if
               ((cfg.core_cfg).FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.simplify
             then
               FStar_TypeChecker_Common.simplify
                 ((cfg.core_cfg).FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                 app
             else app  in
           with_range uu____9404
       | FStar_TypeChecker_NBETerm.Accu (FStar_TypeChecker_NBETerm.Var bv,[])
           ->
           let uu____9423 = FStar_Syntax_Syntax.bv_to_name bv  in
           with_range uu____9423
       | FStar_TypeChecker_NBETerm.Accu
           (FStar_TypeChecker_NBETerm.Var bv,args) ->
           let args1 = readback_args cfg args  in
           let app =
             let uu____9450 = FStar_Syntax_Syntax.bv_to_name bv  in
             FStar_Syntax_Util.mk_app uu____9450 args1  in
           let uu____9453 =
             if
               ((cfg.core_cfg).FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.simplify
             then
               FStar_TypeChecker_Common.simplify
                 ((cfg.core_cfg).FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                 app
             else app  in
           with_range uu____9453
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
           let uu____9521 =
             if
               ((cfg.core_cfg).FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.simplify
             then
               FStar_TypeChecker_Common.simplify
                 ((cfg.core_cfg).FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                 app
             else app  in
           with_range uu____9521
       | FStar_TypeChecker_NBETerm.Accu
           (FStar_TypeChecker_NBETerm.UnreducedLet
            (var,typ,defn,body,lb),args)
           ->
           let typ1 =
             let uu____9560 = FStar_Thunk.force typ  in
             readback cfg uu____9560  in
           let defn1 =
             let uu____9562 = FStar_Thunk.force defn  in
             readback cfg uu____9562  in
           let body1 =
             let uu____9564 =
               let uu____9565 = FStar_Thunk.force body  in
               readback cfg uu____9565  in
             FStar_Syntax_Subst.close [(var, FStar_Pervasives_Native.None)]
               uu____9564
              in
           let lbname =
             let uu____9585 =
               let uu___1432_9586 =
                 FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
               {
                 FStar_Syntax_Syntax.ppname =
                   (uu___1432_9586.FStar_Syntax_Syntax.ppname);
                 FStar_Syntax_Syntax.index =
                   (uu___1432_9586.FStar_Syntax_Syntax.index);
                 FStar_Syntax_Syntax.sort = typ1
               }  in
             FStar_Util.Inl uu____9585  in
           let lb1 =
             let uu___1435_9588 = lb  in
             {
               FStar_Syntax_Syntax.lbname = lbname;
               FStar_Syntax_Syntax.lbunivs =
                 (uu___1435_9588.FStar_Syntax_Syntax.lbunivs);
               FStar_Syntax_Syntax.lbtyp = typ1;
               FStar_Syntax_Syntax.lbeff =
                 (uu___1435_9588.FStar_Syntax_Syntax.lbeff);
               FStar_Syntax_Syntax.lbdef = defn1;
               FStar_Syntax_Syntax.lbattrs =
                 (uu___1435_9588.FStar_Syntax_Syntax.lbattrs);
               FStar_Syntax_Syntax.lbpos =
                 (uu___1435_9588.FStar_Syntax_Syntax.lbpos)
             }  in
           let hd =
             FStar_Syntax_Syntax.mk
               (FStar_Syntax_Syntax.Tm_let ((false, [lb1]), body1))
               FStar_Range.dummyRange
              in
           let args1 = readback_args cfg args  in
           let uu____9612 = FStar_Syntax_Util.mk_app hd args1  in
           with_range uu____9612
       | FStar_TypeChecker_NBETerm.Accu
           (FStar_TypeChecker_NBETerm.UnreducedLetRec
            (vars_typs_defns,body,lbs),args)
           ->
           let lbs1 =
             FStar_List.map2
               (fun uu____9669  ->
                  fun lb  ->
                    match uu____9669 with
                    | (v,t,d) ->
                        let t1 = readback cfg t  in
                        let def = readback cfg d  in
                        let v1 =
                          let uu___1455_9683 = v  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___1455_9683.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___1455_9683.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t1
                          }  in
                        let uu___1458_9684 = lb  in
                        {
                          FStar_Syntax_Syntax.lbname = (FStar_Util.Inl v1);
                          FStar_Syntax_Syntax.lbunivs =
                            (uu___1458_9684.FStar_Syntax_Syntax.lbunivs);
                          FStar_Syntax_Syntax.lbtyp = t1;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___1458_9684.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = def;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___1458_9684.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___1458_9684.FStar_Syntax_Syntax.lbpos)
                        }) vars_typs_defns lbs
              in
           let body1 = readback cfg body  in
           let uu____9686 = FStar_Syntax_Subst.close_let_rec lbs1 body1  in
           (match uu____9686 with
            | (lbs2,body2) ->
                let hd =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_let ((true, lbs2), body2))
                    FStar_Range.dummyRange
                   in
                let args1 = readback_args cfg args  in
                let uu____9722 = FStar_Syntax_Util.mk_app hd args1  in
                with_range uu____9722)
       | FStar_TypeChecker_NBETerm.Accu
           (FStar_TypeChecker_NBETerm.UVar f,args) ->
           let hd = FStar_Thunk.force f  in
           let args1 = readback_args cfg args  in
           let uu____9749 = FStar_Syntax_Util.mk_app hd args1  in
           with_range uu____9749
       | FStar_TypeChecker_NBETerm.TopLevelLet (lb,arity,args_rev) ->
           let n_univs = FStar_List.length lb.FStar_Syntax_Syntax.lbunivs  in
           let n_args = FStar_List.length args_rev  in
           let uu____9775 = FStar_Util.first_N (n_args - n_univs) args_rev
              in
           (match uu____9775 with
            | (args_rev1,univs) ->
                let uu____9822 =
                  let uu____9823 =
                    let uu____9824 =
                      FStar_List.map FStar_Pervasives_Native.fst univs  in
                    translate cfg uu____9824 lb.FStar_Syntax_Syntax.lbdef  in
                  iapp cfg uu____9823 (FStar_List.rev args_rev1)  in
                readback cfg uu____9822)
       | FStar_TypeChecker_NBETerm.TopLevelRec
           (lb,uu____9836,uu____9837,args) ->
           let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
           let head =
             FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
               FStar_Range.dummyRange
              in
           let args1 =
             FStar_List.map
               (fun uu____9882  ->
                  match uu____9882 with
                  | (t,q) ->
                      let uu____9893 = readback cfg t  in (uu____9893, q))
               args
              in
           let uu____9894 = FStar_Syntax_Util.mk_app head args1  in
           with_range uu____9894
       | FStar_TypeChecker_NBETerm.LocalLetRec
           (i,uu____9898,lbs,bs,args,_ar,_ar_lst) ->
           let lbnames =
             FStar_List.map
               (fun lb  ->
                  let uu____9940 =
                    let uu____9942 =
                      let uu____9943 =
                        FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                      uu____9943.FStar_Syntax_Syntax.ppname  in
                    FStar_Ident.string_of_id uu____9942  in
                  FStar_Syntax_Syntax.gen_bv uu____9940
                    FStar_Pervasives_Native.None lb.FStar_Syntax_Syntax.lbtyp)
               lbs
              in
           let let_rec_env =
             let uu____9947 =
               FStar_List.map
                 (fun x1  ->
                    let uu____9953 = FStar_Syntax_Syntax.range_of_bv x1  in
                    mk_rt uu____9953
                      (FStar_TypeChecker_NBETerm.Accu
                         ((FStar_TypeChecker_NBETerm.Var x1), []))) lbnames
                in
             FStar_List.rev_append uu____9947 bs  in
           let lbs1 =
             FStar_List.map2
               (fun lb  ->
                  fun lbname  ->
                    let lbdef =
                      let uu____9975 =
                        translate cfg let_rec_env
                          lb.FStar_Syntax_Syntax.lbdef
                         in
                      readback cfg uu____9975  in
                    let lbtyp =
                      let uu____9977 =
                        translate cfg bs lb.FStar_Syntax_Syntax.lbtyp  in
                      readback cfg uu____9977  in
                    let uu___1513_9978 = lb  in
                    {
                      FStar_Syntax_Syntax.lbname = (FStar_Util.Inl lbname);
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___1513_9978.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = lbtyp;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___1513_9978.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = lbdef;
                      FStar_Syntax_Syntax.lbattrs =
                        (uu___1513_9978.FStar_Syntax_Syntax.lbattrs);
                      FStar_Syntax_Syntax.lbpos =
                        (uu___1513_9978.FStar_Syntax_Syntax.lbpos)
                    }) lbs lbnames
              in
           let body =
             let uu____9980 = FStar_List.nth lbnames i  in
             FStar_Syntax_Syntax.bv_to_name uu____9980  in
           let uu____9981 = FStar_Syntax_Subst.close_let_rec lbs1 body  in
           (match uu____9981 with
            | (lbs2,body1) ->
                let head =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_let ((true, lbs2), body1))
                    FStar_Range.dummyRange
                   in
                let args1 =
                  FStar_List.map
                    (fun uu____10029  ->
                       match uu____10029 with
                       | (x1,q) ->
                           let uu____10040 = readback cfg x1  in
                           (uu____10040, q)) args
                   in
                let uu____10041 = FStar_Syntax_Util.mk_app head args1  in
                with_range uu____10041)
       | FStar_TypeChecker_NBETerm.Quote (qt,qi) ->
           mk (FStar_Syntax_Syntax.Tm_quoted (qt, qi))
       | FStar_TypeChecker_NBETerm.Lazy (FStar_Util.Inl li,uu____10049) ->
           mk (FStar_Syntax_Syntax.Tm_lazy li)
       | FStar_TypeChecker_NBETerm.Lazy (uu____10066,thunk) ->
           let uu____10088 = FStar_Thunk.force thunk  in
           readback cfg uu____10088)

type step =
  | Primops 
  | UnfoldUntil of FStar_Syntax_Syntax.delta_depth 
  | UnfoldOnly of FStar_Ident.lid Prims.list 
  | UnfoldAttr of FStar_Ident.lid Prims.list 
  | UnfoldTac 
  | Reify 
let (uu___is_Primops : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Primops  -> true | uu____10117 -> false
  
let (uu___is_UnfoldUntil : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldUntil _0 -> true | uu____10129 -> false
  
let (__proj__UnfoldUntil__item___0 : step -> FStar_Syntax_Syntax.delta_depth)
  = fun projectee  -> match projectee with | UnfoldUntil _0 -> _0 
let (uu___is_UnfoldOnly : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldOnly _0 -> true | uu____10150 -> false
  
let (__proj__UnfoldOnly__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldOnly _0 -> _0 
let (uu___is_UnfoldAttr : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldAttr _0 -> true | uu____10177 -> false
  
let (__proj__UnfoldAttr__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldAttr _0 -> _0 
let (uu___is_UnfoldTac : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldTac  -> true | uu____10201 -> false
  
let (uu___is_Reify : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reify  -> true | uu____10212 -> false
  
let (step_as_normalizer_step : step -> FStar_TypeChecker_Env.step) =
  fun uu___2_10219  ->
    match uu___2_10219 with
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
        let uu____10243 = new_config cfg  in iapp uu____10243 t args
  
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
            let uu___1559_10275 = cfg  in
            {
              FStar_TypeChecker_Cfg.steps =
                (let uu___1561_10278 = cfg.FStar_TypeChecker_Cfg.steps  in
                 {
                   FStar_TypeChecker_Cfg.beta =
                     (uu___1561_10278.FStar_TypeChecker_Cfg.beta);
                   FStar_TypeChecker_Cfg.iota =
                     (uu___1561_10278.FStar_TypeChecker_Cfg.iota);
                   FStar_TypeChecker_Cfg.zeta =
                     (uu___1561_10278.FStar_TypeChecker_Cfg.zeta);
                   FStar_TypeChecker_Cfg.zeta_full =
                     (uu___1561_10278.FStar_TypeChecker_Cfg.zeta_full);
                   FStar_TypeChecker_Cfg.weak =
                     (uu___1561_10278.FStar_TypeChecker_Cfg.weak);
                   FStar_TypeChecker_Cfg.hnf =
                     (uu___1561_10278.FStar_TypeChecker_Cfg.hnf);
                   FStar_TypeChecker_Cfg.primops =
                     (uu___1561_10278.FStar_TypeChecker_Cfg.primops);
                   FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                     (uu___1561_10278.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                   FStar_TypeChecker_Cfg.unfold_until =
                     (uu___1561_10278.FStar_TypeChecker_Cfg.unfold_until);
                   FStar_TypeChecker_Cfg.unfold_only =
                     (uu___1561_10278.FStar_TypeChecker_Cfg.unfold_only);
                   FStar_TypeChecker_Cfg.unfold_fully =
                     (uu___1561_10278.FStar_TypeChecker_Cfg.unfold_fully);
                   FStar_TypeChecker_Cfg.unfold_attr =
                     (uu___1561_10278.FStar_TypeChecker_Cfg.unfold_attr);
                   FStar_TypeChecker_Cfg.unfold_tac =
                     (uu___1561_10278.FStar_TypeChecker_Cfg.unfold_tac);
                   FStar_TypeChecker_Cfg.pure_subterms_within_computations =
                     (uu___1561_10278.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                   FStar_TypeChecker_Cfg.simplify =
                     (uu___1561_10278.FStar_TypeChecker_Cfg.simplify);
                   FStar_TypeChecker_Cfg.erase_universes =
                     (uu___1561_10278.FStar_TypeChecker_Cfg.erase_universes);
                   FStar_TypeChecker_Cfg.allow_unbound_universes =
                     (uu___1561_10278.FStar_TypeChecker_Cfg.allow_unbound_universes);
                   FStar_TypeChecker_Cfg.reify_ = true;
                   FStar_TypeChecker_Cfg.compress_uvars =
                     (uu___1561_10278.FStar_TypeChecker_Cfg.compress_uvars);
                   FStar_TypeChecker_Cfg.no_full_norm =
                     (uu___1561_10278.FStar_TypeChecker_Cfg.no_full_norm);
                   FStar_TypeChecker_Cfg.check_no_uvars =
                     (uu___1561_10278.FStar_TypeChecker_Cfg.check_no_uvars);
                   FStar_TypeChecker_Cfg.unmeta =
                     (uu___1561_10278.FStar_TypeChecker_Cfg.unmeta);
                   FStar_TypeChecker_Cfg.unascribe =
                     (uu___1561_10278.FStar_TypeChecker_Cfg.unascribe);
                   FStar_TypeChecker_Cfg.in_full_norm_request =
                     (uu___1561_10278.FStar_TypeChecker_Cfg.in_full_norm_request);
                   FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                     (uu___1561_10278.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                   FStar_TypeChecker_Cfg.nbe_step =
                     (uu___1561_10278.FStar_TypeChecker_Cfg.nbe_step);
                   FStar_TypeChecker_Cfg.for_extraction =
                     (uu___1561_10278.FStar_TypeChecker_Cfg.for_extraction)
                 });
              FStar_TypeChecker_Cfg.tcenv =
                (uu___1559_10275.FStar_TypeChecker_Cfg.tcenv);
              FStar_TypeChecker_Cfg.debug =
                (uu___1559_10275.FStar_TypeChecker_Cfg.debug);
              FStar_TypeChecker_Cfg.delta_level =
                (uu___1559_10275.FStar_TypeChecker_Cfg.delta_level);
              FStar_TypeChecker_Cfg.primitive_steps =
                (uu___1559_10275.FStar_TypeChecker_Cfg.primitive_steps);
              FStar_TypeChecker_Cfg.strong =
                (uu___1559_10275.FStar_TypeChecker_Cfg.strong);
              FStar_TypeChecker_Cfg.memoize_lazy =
                (uu___1559_10275.FStar_TypeChecker_Cfg.memoize_lazy);
              FStar_TypeChecker_Cfg.normalize_pure_lets =
                (uu___1559_10275.FStar_TypeChecker_Cfg.normalize_pure_lets);
              FStar_TypeChecker_Cfg.reifying =
                (uu___1559_10275.FStar_TypeChecker_Cfg.reifying)
            }  in
          (let uu____10281 =
             (FStar_TypeChecker_Env.debug env (FStar_Options.Other "NBETop"))
               ||
               (FStar_TypeChecker_Env.debug env (FStar_Options.Other "NBE"))
              in
           if uu____10281
           then
             let uu____10286 = FStar_Syntax_Print.term_to_string e  in
             FStar_Util.print1 "Calling NBE with (%s) {\n" uu____10286
           else ());
          (let cfg2 = new_config cfg1  in
           let r =
             let uu____10293 = translate cfg2 [] e  in
             readback cfg2 uu____10293  in
           (let uu____10295 =
              (FStar_TypeChecker_Env.debug env (FStar_Options.Other "NBETop"))
                ||
                (FStar_TypeChecker_Env.debug env (FStar_Options.Other "NBE"))
               in
            if uu____10295
            then
              let uu____10300 = FStar_Syntax_Print.term_to_string r  in
              FStar_Util.print1 "}\nNBE returned (%s)\n" uu____10300
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
          let uu___1577_10327 = cfg  in
          {
            FStar_TypeChecker_Cfg.steps =
              (let uu___1579_10330 = cfg.FStar_TypeChecker_Cfg.steps  in
               {
                 FStar_TypeChecker_Cfg.beta =
                   (uu___1579_10330.FStar_TypeChecker_Cfg.beta);
                 FStar_TypeChecker_Cfg.iota =
                   (uu___1579_10330.FStar_TypeChecker_Cfg.iota);
                 FStar_TypeChecker_Cfg.zeta =
                   (uu___1579_10330.FStar_TypeChecker_Cfg.zeta);
                 FStar_TypeChecker_Cfg.zeta_full =
                   (uu___1579_10330.FStar_TypeChecker_Cfg.zeta_full);
                 FStar_TypeChecker_Cfg.weak =
                   (uu___1579_10330.FStar_TypeChecker_Cfg.weak);
                 FStar_TypeChecker_Cfg.hnf =
                   (uu___1579_10330.FStar_TypeChecker_Cfg.hnf);
                 FStar_TypeChecker_Cfg.primops =
                   (uu___1579_10330.FStar_TypeChecker_Cfg.primops);
                 FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                   (uu___1579_10330.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                 FStar_TypeChecker_Cfg.unfold_until =
                   (uu___1579_10330.FStar_TypeChecker_Cfg.unfold_until);
                 FStar_TypeChecker_Cfg.unfold_only =
                   (uu___1579_10330.FStar_TypeChecker_Cfg.unfold_only);
                 FStar_TypeChecker_Cfg.unfold_fully =
                   (uu___1579_10330.FStar_TypeChecker_Cfg.unfold_fully);
                 FStar_TypeChecker_Cfg.unfold_attr =
                   (uu___1579_10330.FStar_TypeChecker_Cfg.unfold_attr);
                 FStar_TypeChecker_Cfg.unfold_tac =
                   (uu___1579_10330.FStar_TypeChecker_Cfg.unfold_tac);
                 FStar_TypeChecker_Cfg.pure_subterms_within_computations =
                   (uu___1579_10330.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                 FStar_TypeChecker_Cfg.simplify =
                   (uu___1579_10330.FStar_TypeChecker_Cfg.simplify);
                 FStar_TypeChecker_Cfg.erase_universes =
                   (uu___1579_10330.FStar_TypeChecker_Cfg.erase_universes);
                 FStar_TypeChecker_Cfg.allow_unbound_universes =
                   (uu___1579_10330.FStar_TypeChecker_Cfg.allow_unbound_universes);
                 FStar_TypeChecker_Cfg.reify_ = true;
                 FStar_TypeChecker_Cfg.compress_uvars =
                   (uu___1579_10330.FStar_TypeChecker_Cfg.compress_uvars);
                 FStar_TypeChecker_Cfg.no_full_norm =
                   (uu___1579_10330.FStar_TypeChecker_Cfg.no_full_norm);
                 FStar_TypeChecker_Cfg.check_no_uvars =
                   (uu___1579_10330.FStar_TypeChecker_Cfg.check_no_uvars);
                 FStar_TypeChecker_Cfg.unmeta =
                   (uu___1579_10330.FStar_TypeChecker_Cfg.unmeta);
                 FStar_TypeChecker_Cfg.unascribe =
                   (uu___1579_10330.FStar_TypeChecker_Cfg.unascribe);
                 FStar_TypeChecker_Cfg.in_full_norm_request =
                   (uu___1579_10330.FStar_TypeChecker_Cfg.in_full_norm_request);
                 FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                   (uu___1579_10330.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                 FStar_TypeChecker_Cfg.nbe_step =
                   (uu___1579_10330.FStar_TypeChecker_Cfg.nbe_step);
                 FStar_TypeChecker_Cfg.for_extraction =
                   (uu___1579_10330.FStar_TypeChecker_Cfg.for_extraction)
               });
            FStar_TypeChecker_Cfg.tcenv =
              (uu___1577_10327.FStar_TypeChecker_Cfg.tcenv);
            FStar_TypeChecker_Cfg.debug =
              (uu___1577_10327.FStar_TypeChecker_Cfg.debug);
            FStar_TypeChecker_Cfg.delta_level =
              (uu___1577_10327.FStar_TypeChecker_Cfg.delta_level);
            FStar_TypeChecker_Cfg.primitive_steps =
              (uu___1577_10327.FStar_TypeChecker_Cfg.primitive_steps);
            FStar_TypeChecker_Cfg.strong =
              (uu___1577_10327.FStar_TypeChecker_Cfg.strong);
            FStar_TypeChecker_Cfg.memoize_lazy =
              (uu___1577_10327.FStar_TypeChecker_Cfg.memoize_lazy);
            FStar_TypeChecker_Cfg.normalize_pure_lets =
              (uu___1577_10327.FStar_TypeChecker_Cfg.normalize_pure_lets);
            FStar_TypeChecker_Cfg.reifying =
              (uu___1577_10327.FStar_TypeChecker_Cfg.reifying)
          }  in
        let cfg2 = new_config cfg1  in
        debug cfg2
          (fun uu____10336  ->
             let uu____10337 = FStar_Syntax_Print.term_to_string e  in
             FStar_Util.print1 "Calling NBE with (%s) {\n" uu____10337);
        (let r =
           let uu____10341 = translate cfg2 [] e  in
           readback cfg2 uu____10341  in
         debug cfg2
           (fun uu____10345  ->
              let uu____10346 = FStar_Syntax_Print.term_to_string r  in
              FStar_Util.print1 "}\nNBE returned (%s)\n" uu____10346);
         r)
  