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
              | uu____2999 ->
                  let uu____3002 =
                    FStar_Syntax_Syntax.set_range_of_fv fvar
                      e.FStar_Syntax_Syntax.pos
                     in
                  translate_fv cfg bs uu____3002)
         | FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                  (FStar_Const.Const_reify );
                FStar_Syntax_Syntax.pos = uu____3003;
                FStar_Syntax_Syntax.vars = uu____3004;_},arg::more::args)
             ->
             let uu____3064 = FStar_Syntax_Util.head_and_args e  in
             (match uu____3064 with
              | (head,uu____3082) ->
                  let head1 =
                    FStar_Syntax_Syntax.mk_Tm_app head [arg]
                      e.FStar_Syntax_Syntax.pos
                     in
                  let uu____3124 =
                    FStar_Syntax_Syntax.mk_Tm_app head1 (more :: args)
                      e.FStar_Syntax_Syntax.pos
                     in
                  translate cfg bs uu____3124)
         | FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                  (FStar_Const.Const_reflect uu____3133);
                FStar_Syntax_Syntax.pos = uu____3134;
                FStar_Syntax_Syntax.vars = uu____3135;_},arg::more::args)
             ->
             let uu____3195 = FStar_Syntax_Util.head_and_args e  in
             (match uu____3195 with
              | (head,uu____3213) ->
                  let head1 =
                    FStar_Syntax_Syntax.mk_Tm_app head [arg]
                      e.FStar_Syntax_Syntax.pos
                     in
                  let uu____3255 =
                    FStar_Syntax_Syntax.mk_Tm_app head1 (more :: args)
                      e.FStar_Syntax_Syntax.pos
                     in
                  translate cfg bs uu____3255)
         | FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                  (FStar_Const.Const_reflect uu____3264);
                FStar_Syntax_Syntax.pos = uu____3265;
                FStar_Syntax_Syntax.vars = uu____3266;_},arg::[])
             when (cfg.core_cfg).FStar_TypeChecker_Cfg.reifying ->
             let cfg1 = reifying_false cfg  in
             translate cfg1 bs (FStar_Pervasives_Native.fst arg)
         | FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                  (FStar_Const.Const_reflect uu____3311);
                FStar_Syntax_Syntax.pos = uu____3312;
                FStar_Syntax_Syntax.vars = uu____3313;_},arg::[])
             ->
             let uu____3353 =
               let uu____3354 =
                 translate cfg bs (FStar_Pervasives_Native.fst arg)  in
               FStar_TypeChecker_NBETerm.Reflect uu____3354  in
             FStar_All.pipe_left mk_t1 uu____3353
         | FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                  (FStar_Const.Const_reify );
                FStar_Syntax_Syntax.pos = uu____3359;
                FStar_Syntax_Syntax.vars = uu____3360;_},arg::[])
             when
             ((cfg.core_cfg).FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.reify_
             ->
             let cfg1 = reifying_true cfg  in
             translate cfg1 bs (FStar_Pervasives_Native.fst arg)
         | FStar_Syntax_Syntax.Tm_app (head,args) ->
             (debug1
                (fun uu____3439  ->
                   let uu____3440 = FStar_Syntax_Print.term_to_string head
                      in
                   let uu____3442 = FStar_Syntax_Print.args_to_string args
                      in
                   FStar_Util.print2 "Application: %s @ %s\n" uu____3440
                     uu____3442);
              (let uu____3445 = translate cfg bs head  in
               let uu____3446 =
                 FStar_List.map
                   (fun x  ->
                      let uu____3468 =
                        translate cfg bs (FStar_Pervasives_Native.fst x)  in
                      (uu____3468, (FStar_Pervasives_Native.snd x))) args
                  in
               iapp cfg uu____3445 uu____3446))
         | FStar_Syntax_Syntax.Tm_match (scrut,branches) ->
             let make_branches uu____3520 =
               let cfg1 = zeta_false cfg  in
               let rec process_pattern bs1 p =
                 let uu____3551 =
                   match p.FStar_Syntax_Syntax.v with
                   | FStar_Syntax_Syntax.Pat_constant c ->
                       (bs1, (FStar_Syntax_Syntax.Pat_constant c))
                   | FStar_Syntax_Syntax.Pat_cons (fvar,args) ->
                       let uu____3587 =
                         FStar_List.fold_left
                           (fun uu____3628  ->
                              fun uu____3629  ->
                                match (uu____3628, uu____3629) with
                                | ((bs2,args1),(arg,b)) ->
                                    let uu____3721 = process_pattern bs2 arg
                                       in
                                    (match uu____3721 with
                                     | (bs',arg') ->
                                         (bs', ((arg', b) :: args1))))
                           (bs1, []) args
                          in
                       (match uu____3587 with
                        | (bs',args') ->
                            (bs',
                              (FStar_Syntax_Syntax.Pat_cons
                                 (fvar, (FStar_List.rev args')))))
                   | FStar_Syntax_Syntax.Pat_var bvar ->
                       let x =
                         let uu____3820 =
                           let uu____3821 =
                             translate cfg1 bs1 bvar.FStar_Syntax_Syntax.sort
                              in
                           readback cfg1 uu____3821  in
                         FStar_Syntax_Syntax.new_bv
                           FStar_Pervasives_Native.None uu____3820
                          in
                       let uu____3822 =
                         let uu____3825 =
                           FStar_TypeChecker_NBETerm.mkAccuVar x  in
                         uu____3825 :: bs1  in
                       (uu____3822, (FStar_Syntax_Syntax.Pat_var x))
                   | FStar_Syntax_Syntax.Pat_wild bvar ->
                       let x =
                         let uu____3830 =
                           let uu____3831 =
                             translate cfg1 bs1 bvar.FStar_Syntax_Syntax.sort
                              in
                           readback cfg1 uu____3831  in
                         FStar_Syntax_Syntax.new_bv
                           FStar_Pervasives_Native.None uu____3830
                          in
                       let uu____3832 =
                         let uu____3835 =
                           FStar_TypeChecker_NBETerm.mkAccuVar x  in
                         uu____3835 :: bs1  in
                       (uu____3832, (FStar_Syntax_Syntax.Pat_wild x))
                   | FStar_Syntax_Syntax.Pat_dot_term (bvar,tm) ->
                       let x =
                         let uu____3845 =
                           let uu____3846 =
                             translate cfg1 bs1 bvar.FStar_Syntax_Syntax.sort
                              in
                           readback cfg1 uu____3846  in
                         FStar_Syntax_Syntax.new_bv
                           FStar_Pervasives_Native.None uu____3845
                          in
                       let uu____3847 =
                         let uu____3848 =
                           let uu____3855 =
                             let uu____3858 = translate cfg1 bs1 tm  in
                             readback cfg1 uu____3858  in
                           (x, uu____3855)  in
                         FStar_Syntax_Syntax.Pat_dot_term uu____3848  in
                       (bs1, uu____3847)
                    in
                 match uu____3551 with
                 | (bs2,p_new) ->
                     (bs2,
                       (let uu___573_3878 = p  in
                        {
                          FStar_Syntax_Syntax.v = p_new;
                          FStar_Syntax_Syntax.p =
                            (uu___573_3878.FStar_Syntax_Syntax.p)
                        }))
                  in
               FStar_List.map
                 (fun uu____3897  ->
                    match uu____3897 with
                    | (pat,when_clause,e1) ->
                        let uu____3919 = process_pattern bs pat  in
                        (match uu____3919 with
                         | (bs',pat') ->
                             let uu____3932 =
                               let uu____3933 =
                                 let uu____3936 = translate cfg1 bs' e1  in
                                 readback cfg1 uu____3936  in
                               (pat', when_clause, uu____3933)  in
                             FStar_Syntax_Util.branch uu____3932)) branches
                in
             let scrut1 = translate cfg bs scrut  in
             (debug1
                (fun uu____3953  ->
                   let uu____3954 =
                     FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos
                      in
                   let uu____3956 = FStar_Syntax_Print.term_to_string e  in
                   FStar_Util.print2 "%s: Translating match %s\n" uu____3954
                     uu____3956);
              (let scrut2 = unlazy_unmeta scrut1  in
               match scrut2.FStar_TypeChecker_NBETerm.nbe_t with
               | FStar_TypeChecker_NBETerm.Construct (c,us,args) ->
                   (debug1
                      (fun uu____3984  ->
                         let uu____3985 =
                           let uu____3987 =
                             FStar_All.pipe_right args
                               (FStar_List.map
                                  (fun uu____4013  ->
                                     match uu____4013 with
                                     | (x,q) ->
                                         let uu____4027 =
                                           FStar_TypeChecker_NBETerm.t_to_string
                                             x
                                            in
                                         Prims.op_Hat
                                           (if FStar_Util.is_some q
                                            then "#"
                                            else "") uu____4027))
                              in
                           FStar_All.pipe_right uu____3987
                             (FStar_String.concat "; ")
                            in
                         FStar_Util.print1 "Match args: %s\n" uu____3985);
                    (let uu____4041 = pickBranch cfg scrut2 branches  in
                     match uu____4041 with
                     | FStar_Pervasives_Native.Some (branch,args1) ->
                         let uu____4062 =
                           FStar_List.fold_left
                             (fun bs1  -> fun x  -> x :: bs1) bs args1
                            in
                         translate cfg uu____4062 branch
                     | FStar_Pervasives_Native.None  ->
                         FStar_TypeChecker_NBETerm.mkAccuMatch scrut2
                           make_branches))
               | FStar_TypeChecker_NBETerm.Constant c ->
                   (debug1
                      (fun uu____4085  ->
                         let uu____4086 =
                           FStar_TypeChecker_NBETerm.t_to_string scrut2  in
                         FStar_Util.print1 "Match constant : %s\n" uu____4086);
                    (let uu____4089 = pickBranch cfg scrut2 branches  in
                     match uu____4089 with
                     | FStar_Pervasives_Native.Some (branch,[]) ->
                         translate cfg bs branch
                     | FStar_Pervasives_Native.Some (branch,arg::[]) ->
                         translate cfg (arg :: bs) branch
                     | FStar_Pervasives_Native.None  ->
                         FStar_TypeChecker_NBETerm.mkAccuMatch scrut2
                           make_branches
                     | FStar_Pervasives_Native.Some (uu____4123,hd::tl) ->
                         failwith
                           "Impossible: Matching on constants cannot bind more than one variable"))
               | uu____4137 ->
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
             let norm_meta uu____4176 =
               let norm t =
                 let uu____4183 = translate cfg bs t  in
                 readback cfg uu____4183  in
               match meta with
               | FStar_Syntax_Syntax.Meta_named uu____4184 -> meta
               | FStar_Syntax_Syntax.Meta_labeled uu____4185 -> meta
               | FStar_Syntax_Syntax.Meta_desugared uu____4194 -> meta
               | FStar_Syntax_Syntax.Meta_pattern (ts,args) ->
                   let uu____4229 =
                     let uu____4250 = FStar_List.map norm ts  in
                     let uu____4259 =
                       FStar_List.map
                         (FStar_List.map
                            (fun uu____4308  ->
                               match uu____4308 with
                               | (t,a) ->
                                   let uu____4327 = norm t  in
                                   (uu____4327, a))) args
                        in
                     (uu____4250, uu____4259)  in
                   FStar_Syntax_Syntax.Meta_pattern uu____4229
               | FStar_Syntax_Syntax.Meta_monadic (m,t) ->
                   let uu____4352 =
                     let uu____4359 = norm t  in (m, uu____4359)  in
                   FStar_Syntax_Syntax.Meta_monadic uu____4352
               | FStar_Syntax_Syntax.Meta_monadic_lift (m0,m1,t) ->
                   let uu____4371 =
                     let uu____4380 = norm t  in (m0, m1, uu____4380)  in
                   FStar_Syntax_Syntax.Meta_monadic_lift uu____4371
                in
             let uu____4385 =
               let uu____4386 =
                 let uu____4393 = translate cfg bs e1  in
                 let uu____4394 = FStar_Thunk.mk norm_meta  in
                 (uu____4393, uu____4394)  in
               FStar_TypeChecker_NBETerm.Meta uu____4386  in
             FStar_All.pipe_left mk_t1 uu____4385
         | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
             let uu____4416 =
               FStar_TypeChecker_Cfg.should_reduce_local_let cfg.core_cfg lb
                in
             if uu____4416
             then
               let uu____4419 =
                 (((cfg.core_cfg).FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.for_extraction
                    &&
                    (FStar_Syntax_Util.is_unit lb.FStar_Syntax_Syntax.lbtyp))
                   &&
                   (FStar_Syntax_Util.is_pure_or_ghost_effect
                      lb.FStar_Syntax_Syntax.lbeff)
                  in
               (if uu____4419
                then
                  let bs1 =
                    let uu____4425 =
                      let uu____4426 =
                        FStar_Syntax_Syntax.range_of_lbname
                          lb.FStar_Syntax_Syntax.lbname
                         in
                      mk_rt uu____4426
                        (FStar_TypeChecker_NBETerm.Constant
                           FStar_TypeChecker_NBETerm.Unit)
                       in
                    uu____4425 :: bs  in
                  translate cfg bs1 body
                else
                  (let bs1 =
                     let uu____4432 = translate_letbinding cfg bs lb  in
                     uu____4432 :: bs  in
                   translate cfg bs1 body))
             else
               (let def uu____4440 =
                  let uu____4441 =
                    (((cfg.core_cfg).FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.for_extraction
                       &&
                       (FStar_Syntax_Util.is_unit
                          lb.FStar_Syntax_Syntax.lbtyp))
                      &&
                      (FStar_Syntax_Util.is_pure_or_ghost_effect
                         lb.FStar_Syntax_Syntax.lbeff)
                     in
                  if uu____4441
                  then
                    FStar_All.pipe_left mk_t1
                      (FStar_TypeChecker_NBETerm.Constant
                         FStar_TypeChecker_NBETerm.Unit)
                  else translate cfg bs lb.FStar_Syntax_Syntax.lbdef  in
                let typ uu____4451 =
                  translate cfg bs lb.FStar_Syntax_Syntax.lbtyp  in
                let name =
                  let uu____4453 =
                    FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                  FStar_Syntax_Syntax.freshen_bv uu____4453  in
                let bs1 =
                  let uu____4457 =
                    let uu____4458 = FStar_Syntax_Syntax.range_of_bv name  in
                    mk_rt uu____4458
                      (FStar_TypeChecker_NBETerm.Accu
                         ((FStar_TypeChecker_NBETerm.Var name), []))
                     in
                  uu____4457 :: bs  in
                let body1 uu____4474 = translate cfg bs1 body  in
                let uu____4475 =
                  let uu____4476 =
                    let uu____4487 =
                      let uu____4488 =
                        let uu____4505 = FStar_Thunk.mk typ  in
                        let uu____4508 = FStar_Thunk.mk def  in
                        let uu____4511 = FStar_Thunk.mk body1  in
                        (name, uu____4505, uu____4508, uu____4511, lb)  in
                      FStar_TypeChecker_NBETerm.UnreducedLet uu____4488  in
                    (uu____4487, [])  in
                  FStar_TypeChecker_NBETerm.Accu uu____4476  in
                FStar_All.pipe_left mk_t1 uu____4475)
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
                      let uu____4557 =
                        FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                      FStar_Syntax_Syntax.freshen_bv uu____4557) lbs
                  in
               let typs =
                 FStar_List.map
                   (fun lb  -> translate cfg bs lb.FStar_Syntax_Syntax.lbtyp)
                   lbs
                  in
               let rec_bs =
                 let uu____4566 =
                   FStar_List.map
                     (fun v  ->
                        let uu____4572 =
                          let uu____4577 = FStar_Syntax_Syntax.range_of_bv v
                             in
                          mk_rt uu____4577  in
                        FStar_All.pipe_left uu____4572
                          (FStar_TypeChecker_NBETerm.Accu
                             ((FStar_TypeChecker_NBETerm.Var v), []))) vars
                    in
                 FStar_List.append uu____4566 bs  in
               let defs =
                 FStar_List.map
                   (fun lb  ->
                      translate cfg rec_bs lb.FStar_Syntax_Syntax.lbdef) lbs
                  in
               let body1 = translate cfg rec_bs body  in
               let uu____4594 =
                 let uu____4595 =
                   let uu____4606 =
                     let uu____4607 =
                       let uu____4624 = FStar_List.zip3 vars typs defs  in
                       (uu____4624, body1, lbs)  in
                     FStar_TypeChecker_NBETerm.UnreducedLetRec uu____4607  in
                   (uu____4606, [])  in
                 FStar_TypeChecker_NBETerm.Accu uu____4595  in
               FStar_All.pipe_left mk_t1 uu____4594
             else
               (let uu____4655 = make_rec_env lbs bs  in
                translate cfg uu____4655 body)
         | FStar_Syntax_Syntax.Tm_quoted (qt,qi) ->
             let close t =
               let bvs =
                 FStar_List.map
                   (fun uu____4674  ->
                      FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                        FStar_Syntax_Syntax.tun) bs
                  in
               let s1 =
                 FStar_List.mapi
                   (fun i  -> fun bv  -> FStar_Syntax_Syntax.DB (i, bv)) bvs
                  in
               let s2 =
                 let uu____4687 = FStar_List.zip bvs bs  in
                 FStar_List.map
                   (fun uu____4702  ->
                      match uu____4702 with
                      | (bv,t1) ->
                          let uu____4709 =
                            let uu____4716 = readback cfg t1  in
                            (bv, uu____4716)  in
                          FStar_Syntax_Syntax.NT uu____4709) uu____4687
                  in
               let uu____4721 = FStar_Syntax_Subst.subst s1 t  in
               FStar_Syntax_Subst.subst s2 uu____4721  in
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
             let f uu____4730 =
               let t = FStar_Syntax_Util.unfold_lazy li  in
               debug1
                 (fun uu____4737  ->
                    let uu____4738 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.print1 ">> Unfolding Tm_lazy to %s\n"
                      uu____4738);
               translate cfg bs t  in
             let uu____4741 =
               let uu____4742 =
                 let uu____4757 = FStar_Thunk.mk f  in
                 ((FStar_Util.Inl li), uu____4757)  in
               FStar_TypeChecker_NBETerm.Lazy uu____4742  in
             FStar_All.pipe_left mk_t1 uu____4741)

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
            let uu____4789 =
              let uu____4796 = translate cfg bs typ  in
              let uu____4797 = fmap_opt (translate_univ cfg bs) u  in
              (uu____4796, uu____4797)  in
            FStar_TypeChecker_NBETerm.Tot uu____4789
        | FStar_Syntax_Syntax.GTotal (typ,u) ->
            let uu____4812 =
              let uu____4819 = translate cfg bs typ  in
              let uu____4820 = fmap_opt (translate_univ cfg bs) u  in
              (uu____4819, uu____4820)  in
            FStar_TypeChecker_NBETerm.GTot uu____4812
        | FStar_Syntax_Syntax.Comp ctyp ->
            let uu____4826 = translate_comp_typ cfg bs ctyp  in
            FStar_TypeChecker_NBETerm.Comp uu____4826

and (iapp :
  config ->
    FStar_TypeChecker_NBETerm.t ->
      FStar_TypeChecker_NBETerm.args -> FStar_TypeChecker_NBETerm.t)
  =
  fun cfg  ->
    fun f  ->
      fun args  ->
        let mk t = mk_rt f.FStar_TypeChecker_NBETerm.nbe_r t  in
        let uu____4836 =
          let uu____4837 = unlazy_unmeta f  in
          uu____4837.FStar_TypeChecker_NBETerm.nbe_t  in
        match uu____4836 with
        | FStar_TypeChecker_NBETerm.Lam (f1,binders,n) ->
            let m = FStar_List.length args  in
            if m < n
            then
              let arg_values_rev = map_rev FStar_Pervasives_Native.fst args
                 in
              let binders1 =
                match binders with
                | FStar_Util.Inr raw_args ->
                    let uu____4970 = FStar_List.splitAt m raw_args  in
                    (match uu____4970 with
                     | (uu____5011,raw_args1) -> FStar_Util.Inr raw_args1)
                | FStar_Util.Inl (ctx,xs,rc) ->
                    let uu____5080 = FStar_List.splitAt m xs  in
                    (match uu____5080 with
                     | (uu____5127,xs1) ->
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
                (let uu____5227 = FStar_List.splitAt n args  in
                 match uu____5227 with
                 | (args1,args') ->
                     let uu____5274 =
                       let uu____5275 =
                         map_rev FStar_Pervasives_Native.fst args1  in
                       f1 uu____5275  in
                     iapp cfg uu____5274 args')
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
                   FStar_TypeChecker_NBETerm.nbe_r = uu____5394;_},uu____5395)::args2
                  -> aux args2 (u :: us1) ts1
              | a::args2 -> aux args2 us1 (a :: ts1)
              | [] -> (us1, ts1)  in
            let uu____5439 = aux args us ts  in
            (match uu____5439 with
             | (us',ts') ->
                 FStar_All.pipe_left mk
                   (FStar_TypeChecker_NBETerm.Construct (i, us', ts')))
        | FStar_TypeChecker_NBETerm.FV (i,us,ts) ->
            let rec aux args1 us1 ts1 =
              match args1 with
              | ({
                   FStar_TypeChecker_NBETerm.nbe_t =
                     FStar_TypeChecker_NBETerm.Univ u;
                   FStar_TypeChecker_NBETerm.nbe_r = uu____5566;_},uu____5567)::args2
                  -> aux args2 (u :: us1) ts1
              | a::args2 -> aux args2 us1 (a :: ts1)
              | [] -> (us1, ts1)  in
            let uu____5611 = aux args us ts  in
            (match uu____5611 with
             | (us',ts') ->
                 FStar_All.pipe_left mk
                   (FStar_TypeChecker_NBETerm.FV (i, us', ts')))
        | FStar_TypeChecker_NBETerm.TopLevelLet (lb,arity,args_rev) ->
            let args_rev1 = FStar_List.rev_append args args_rev  in
            let n_args_rev = FStar_List.length args_rev1  in
            let n_univs = FStar_List.length lb.FStar_Syntax_Syntax.lbunivs
               in
            (debug cfg
               (fun uu____5689  ->
                  let uu____5690 =
                    FStar_Syntax_Print.lbname_to_string
                      lb.FStar_Syntax_Syntax.lbname
                     in
                  let uu____5692 = FStar_Util.string_of_int arity  in
                  let uu____5694 = FStar_Util.string_of_int n_args_rev  in
                  FStar_Util.print3
                    "Reached iapp for %s with arity %s and n_args = %s\n"
                    uu____5690 uu____5692 uu____5694);
             if n_args_rev >= arity
             then
               (let uu____5698 =
                  let uu____5711 =
                    let uu____5712 =
                      FStar_Syntax_Util.unascribe
                        lb.FStar_Syntax_Syntax.lbdef
                       in
                    uu____5712.FStar_Syntax_Syntax.n  in
                  match uu____5711 with
                  | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____5729) ->
                      (bs, body)
                  | uu____5762 -> ([], (lb.FStar_Syntax_Syntax.lbdef))  in
                match uu____5698 with
                | (bs,body) ->
                    if (n_univs + (FStar_List.length bs)) = arity
                    then
                      let uu____5803 =
                        FStar_Util.first_N (n_args_rev - arity) args_rev1  in
                      (match uu____5803 with
                       | (extra,args_rev2) ->
                           (debug cfg
                              (fun uu____5855  ->
                                 let uu____5856 =
                                   FStar_Syntax_Print.lbname_to_string
                                     lb.FStar_Syntax_Syntax.lbname
                                    in
                                 let uu____5858 =
                                   FStar_Syntax_Print.term_to_string body  in
                                 let uu____5860 =
                                   let uu____5862 =
                                     FStar_List.map
                                       (fun uu____5874  ->
                                          match uu____5874 with
                                          | (x,uu____5881) ->
                                              FStar_TypeChecker_NBETerm.t_to_string
                                                x) args_rev2
                                      in
                                   FStar_All.pipe_right uu____5862
                                     (FStar_String.concat ", ")
                                    in
                                 FStar_Util.print3
                                   "Reducing body of %s = %s,\n\twith args = %s\n"
                                   uu____5856 uu____5858 uu____5860);
                            (let t =
                               let uu____5889 =
                                 FStar_List.map FStar_Pervasives_Native.fst
                                   args_rev2
                                  in
                               translate cfg uu____5889 body  in
                             match extra with
                             | [] -> t
                             | uu____5900 ->
                                 iapp cfg t (FStar_List.rev extra))))
                    else
                      (let uu____5913 =
                         FStar_Util.first_N (n_args_rev - n_univs) args_rev1
                          in
                       match uu____5913 with
                       | (extra,univs) ->
                           let uu____5960 =
                             let uu____5961 =
                               FStar_List.map FStar_Pervasives_Native.fst
                                 univs
                                in
                             translate cfg uu____5961
                               lb.FStar_Syntax_Syntax.lbdef
                              in
                           iapp cfg uu____5960 (FStar_List.rev extra)))
             else
               FStar_All.pipe_left mk
                 (FStar_TypeChecker_NBETerm.TopLevelLet
                    (lb, arity, args_rev1)))
        | FStar_TypeChecker_NBETerm.TopLevelRec
            (lb,arity,decreases_list,args') ->
            let args1 = FStar_List.append args' args  in
            if (FStar_List.length args1) >= arity
            then
              let uu____6021 =
                should_reduce_recursive_definition args1 decreases_list  in
              (match uu____6021 with
               | (should_reduce,uu____6030,uu____6031) ->
                   if Prims.op_Negation should_reduce
                   then
                     let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname
                        in
                     (debug cfg
                        (fun uu____6039  ->
                           let uu____6040 =
                             FStar_Syntax_Print.fv_to_string fv  in
                           FStar_Util.print1
                             "Decided to not unfold recursive definition %s\n"
                             uu____6040);
                      (let uu____6043 =
                         let uu____6044 = FStar_Syntax_Syntax.range_of_fv fv
                            in
                         mk_rt uu____6044
                           (FStar_TypeChecker_NBETerm.FV (fv, [], []))
                          in
                       iapp cfg uu____6043 args1))
                   else
                     (debug cfg
                        (fun uu____6062  ->
                           let uu____6063 =
                             let uu____6065 =
                               FStar_Util.right lb.FStar_Syntax_Syntax.lbname
                                in
                             FStar_Syntax_Print.fv_to_string uu____6065  in
                           FStar_Util.print1
                             "Yes, Decided to unfold recursive definition %s\n"
                             uu____6063);
                      (let uu____6067 =
                         FStar_Util.first_N
                           (FStar_List.length lb.FStar_Syntax_Syntax.lbunivs)
                           args1
                          in
                       match uu____6067 with
                       | (univs,rest) ->
                           let uu____6114 =
                             let uu____6115 =
                               let uu____6118 =
                                 FStar_List.map FStar_Pervasives_Native.fst
                                   univs
                                  in
                               FStar_List.rev uu____6118  in
                             translate cfg uu____6115
                               lb.FStar_Syntax_Syntax.lbdef
                              in
                           iapp cfg uu____6114 rest)))
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
                  let uu____6236 =
                    should_reduce_recursive_definition args1 decreases_list
                     in
                  match uu____6236 with
                  | (should_reduce,uu____6245,uu____6246) ->
                      if Prims.op_Negation should_reduce
                      then
                        FStar_All.pipe_left mk
                          (FStar_TypeChecker_NBETerm.LocalLetRec
                             (i, lb, mutual_lbs, local_env, args1,
                               Prims.int_zero, decreases_list))
                      else
                        (let env = make_rec_env mutual_lbs local_env  in
                         debug cfg
                           (fun uu____6275  ->
                              (let uu____6277 =
                                 let uu____6279 =
                                   FStar_List.map
                                     FStar_TypeChecker_NBETerm.t_to_string
                                     env
                                    in
                                 FStar_String.concat ",\n\t " uu____6279  in
                               FStar_Util.print1
                                 "LocalLetRec Env = {\n\t%s\n}\n" uu____6277);
                              (let uu____6286 =
                                 let uu____6288 =
                                   FStar_List.map
                                     (fun uu____6300  ->
                                        match uu____6300 with
                                        | (t,uu____6307) ->
                                            FStar_TypeChecker_NBETerm.t_to_string
                                              t) args1
                                    in
                                 FStar_String.concat ",\n\t " uu____6288  in
                               FStar_Util.print1
                                 "LocalLetRec Args = {\n\t%s\n}\n" uu____6286));
                         (let uu____6310 =
                            translate cfg env lb.FStar_Syntax_Syntax.lbdef
                             in
                          iapp cfg uu____6310 args1))))
        | FStar_TypeChecker_NBETerm.Constant
            (FStar_TypeChecker_NBETerm.SConst (FStar_Const.Const_range_of ))
            ->
            (match args with
             | (a,uu____6312)::[] ->
                 mk_rt a.FStar_TypeChecker_NBETerm.nbe_r
                   (FStar_TypeChecker_NBETerm.Constant
                      (FStar_TypeChecker_NBETerm.Range
                         (a.FStar_TypeChecker_NBETerm.nbe_r)))
             | uu____6321 ->
                 let uu____6322 =
                   let uu____6324 = FStar_TypeChecker_NBETerm.t_to_string f
                      in
                   Prims.op_Hat "NBE ill-typed application: " uu____6324  in
                 failwith uu____6322)
        | FStar_TypeChecker_NBETerm.Constant
            (FStar_TypeChecker_NBETerm.SConst (FStar_Const.Const_set_range_of
            )) ->
            (match args with
             | (t,uu____6328)::({
                                  FStar_TypeChecker_NBETerm.nbe_t =
                                    FStar_TypeChecker_NBETerm.Constant
                                    (FStar_TypeChecker_NBETerm.Range r);
                                  FStar_TypeChecker_NBETerm.nbe_r =
                                    uu____6330;_},uu____6331)::[]
                 ->
                 let uu___934_6344 = t  in
                 {
                   FStar_TypeChecker_NBETerm.nbe_t =
                     (uu___934_6344.FStar_TypeChecker_NBETerm.nbe_t);
                   FStar_TypeChecker_NBETerm.nbe_r = r
                 }
             | uu____6345 ->
                 let uu____6346 =
                   let uu____6348 = FStar_TypeChecker_NBETerm.t_to_string f
                      in
                   Prims.op_Hat "NBE ill-typed application: " uu____6348  in
                 failwith uu____6346)
        | uu____6351 ->
            let uu____6352 =
              let uu____6354 = FStar_TypeChecker_NBETerm.t_to_string f  in
              Prims.op_Hat "NBE ill-typed application: " uu____6354  in
            failwith uu____6352

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
          let uu____6371 = FStar_TypeChecker_Cfg.cfg_env cfg.core_cfg  in
          let uu____6372 = FStar_Syntax_Syntax.lid_of_fv fvar  in
          FStar_TypeChecker_Env.lookup_qname uu____6371 uu____6372  in
        let uu____6373 = (is_constr qninfo) || (is_constr_fv fvar)  in
        if uu____6373
        then FStar_TypeChecker_NBETerm.mkConstruct fvar [] []
        else
          (let uu____6382 =
             FStar_TypeChecker_Normalize.should_unfold cfg.core_cfg
               (fun uu____6384  ->
                  (cfg.core_cfg).FStar_TypeChecker_Cfg.reifying) fvar qninfo
              in
           match uu____6382 with
           | FStar_TypeChecker_Normalize.Should_unfold_fully  ->
               failwith "Not yet handled"
           | FStar_TypeChecker_Normalize.Should_unfold_no  ->
               (debug1
                  (fun uu____6391  ->
                     let uu____6392 = FStar_Syntax_Print.fv_to_string fvar
                        in
                     FStar_Util.print1 "(1) Decided to not unfold %s\n"
                       uu____6392);
                (let uu____6395 =
                   FStar_TypeChecker_Cfg.find_prim_step cfg.core_cfg fvar  in
                 match uu____6395 with
                 | FStar_Pervasives_Native.Some prim_step when
                     prim_step.FStar_TypeChecker_Cfg.strong_reduction_ok ->
                     let arity =
                       prim_step.FStar_TypeChecker_Cfg.arity +
                         prim_step.FStar_TypeChecker_Cfg.univ_arity
                        in
                     (debug1
                        (fun uu____6406  ->
                           let uu____6407 =
                             FStar_Syntax_Print.fv_to_string fvar  in
                           FStar_Util.print1 "Found a primop %s\n" uu____6407);
                      (let uu____6410 =
                         let uu____6411 =
                           let uu____6444 =
                             let f uu____6477 =
                               let uu____6479 =
                                 FStar_Syntax_Syntax.new_bv
                                   FStar_Pervasives_Native.None
                                   FStar_Syntax_Syntax.t_unit
                                  in
                               (uu____6479, FStar_Pervasives_Native.None)  in
                             let uu____6482 =
                               let uu____6493 = FStar_Common.tabulate arity f
                                  in
                               ([], uu____6493, FStar_Pervasives_Native.None)
                                in
                             FStar_Util.Inl uu____6482  in
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
                               let uu____6567 =
                                 prim_step.FStar_TypeChecker_Cfg.interpretation_nbe
                                   callbacks args'
                                  in
                               match uu____6567 with
                               | FStar_Pervasives_Native.Some x ->
                                   (debug1
                                      (fun uu____6578  ->
                                         let uu____6579 =
                                           FStar_Syntax_Print.fv_to_string
                                             fvar
                                            in
                                         let uu____6581 =
                                           FStar_TypeChecker_NBETerm.t_to_string
                                             x
                                            in
                                         FStar_Util.print2
                                           "Primitive operator %s returned %s\n"
                                           uu____6579 uu____6581);
                                    x)
                               | FStar_Pervasives_Native.None  ->
                                   (debug1
                                      (fun uu____6589  ->
                                         let uu____6590 =
                                           FStar_Syntax_Print.fv_to_string
                                             fvar
                                            in
                                         FStar_Util.print1
                                           "Primitive operator %s failed\n"
                                           uu____6590);
                                    (let uu____6593 =
                                       FStar_TypeChecker_NBETerm.mkFV fvar []
                                         []
                                        in
                                     iapp cfg uu____6593 args'))),
                             uu____6444, arity)
                            in
                         FStar_TypeChecker_NBETerm.Lam uu____6411  in
                       FStar_All.pipe_left mk_t uu____6410))
                 | FStar_Pervasives_Native.Some uu____6598 ->
                     (debug1
                        (fun uu____6604  ->
                           let uu____6605 =
                             FStar_Syntax_Print.fv_to_string fvar  in
                           FStar_Util.print1 "(2) Decided to not unfold %s\n"
                             uu____6605);
                      FStar_TypeChecker_NBETerm.mkFV fvar [] [])
                 | uu____6612 ->
                     (debug1
                        (fun uu____6620  ->
                           let uu____6621 =
                             FStar_Syntax_Print.fv_to_string fvar  in
                           FStar_Util.print1 "(3) Decided to not unfold %s\n"
                             uu____6621);
                      FStar_TypeChecker_NBETerm.mkFV fvar [] [])))
           | FStar_TypeChecker_Normalize.Should_unfold_reify  ->
               let t =
                 let is_qninfo_visible =
                   let uu____6631 =
                     FStar_TypeChecker_Env.lookup_definition_qninfo
                       (cfg.core_cfg).FStar_TypeChecker_Cfg.delta_level
                       (fvar.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                       qninfo
                      in
                   FStar_Option.isSome uu____6631  in
                 if is_qninfo_visible
                 then
                   match qninfo with
                   | FStar_Pervasives_Native.Some
                       (FStar_Util.Inr
                        ({
                           FStar_Syntax_Syntax.sigel =
                             FStar_Syntax_Syntax.Sig_let ((is_rec,lbs),names);
                           FStar_Syntax_Syntax.sigrng = uu____6646;
                           FStar_Syntax_Syntax.sigquals = uu____6647;
                           FStar_Syntax_Syntax.sigmeta = uu____6648;
                           FStar_Syntax_Syntax.sigattrs = uu____6649;
                           FStar_Syntax_Syntax.sigopts = uu____6650;_},_us_opt),_rng)
                       ->
                       (debug1
                          (fun uu____6720  ->
                             let uu____6721 =
                               FStar_Syntax_Print.fv_to_string fvar  in
                             FStar_Util.print1 "(1) Decided to unfold %s\n"
                               uu____6721);
                        (let lbm = find_let lbs fvar  in
                         match lbm with
                         | FStar_Pervasives_Native.Some lb ->
                             if
                               is_rec &&
                                 ((cfg.core_cfg).FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta
                             then
                               let uu____6729 = let_rec_arity lb  in
                               (match uu____6729 with
                                | (ar,lst) ->
                                    let uu____6748 =
                                      let uu____6753 =
                                        FStar_Syntax_Syntax.range_of_fv fvar
                                         in
                                      mk_rt uu____6753  in
                                    FStar_All.pipe_left uu____6748
                                      (FStar_TypeChecker_NBETerm.TopLevelRec
                                         (lb, ar, lst, [])))
                             else translate_letbinding cfg bs lb
                         | FStar_Pervasives_Native.None  ->
                             failwith "Could not find let binding"))
                   | uu____6771 ->
                       (debug1
                          (fun uu____6777  ->
                             let uu____6778 =
                               FStar_Syntax_Print.fv_to_string fvar  in
                             FStar_Util.print1
                               "(1) qninfo is None for (%s)\n" uu____6778);
                        FStar_TypeChecker_NBETerm.mkFV fvar [] [])
                 else
                   (debug1
                      (fun uu____6792  ->
                         let uu____6793 =
                           FStar_Syntax_Print.fv_to_string fvar  in
                         FStar_Util.print1
                           "(1) qninfo is not visible at this level (%s)\n"
                           uu____6793);
                    FStar_TypeChecker_NBETerm.mkFV fvar [] [])
                  in
               (cache_add cfg fvar t; t)
           | FStar_TypeChecker_Normalize.Should_unfold_yes  ->
               let t =
                 let is_qninfo_visible =
                   let uu____6804 =
                     FStar_TypeChecker_Env.lookup_definition_qninfo
                       (cfg.core_cfg).FStar_TypeChecker_Cfg.delta_level
                       (fvar.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                       qninfo
                      in
                   FStar_Option.isSome uu____6804  in
                 if is_qninfo_visible
                 then
                   match qninfo with
                   | FStar_Pervasives_Native.Some
                       (FStar_Util.Inr
                        ({
                           FStar_Syntax_Syntax.sigel =
                             FStar_Syntax_Syntax.Sig_let ((is_rec,lbs),names);
                           FStar_Syntax_Syntax.sigrng = uu____6819;
                           FStar_Syntax_Syntax.sigquals = uu____6820;
                           FStar_Syntax_Syntax.sigmeta = uu____6821;
                           FStar_Syntax_Syntax.sigattrs = uu____6822;
                           FStar_Syntax_Syntax.sigopts = uu____6823;_},_us_opt),_rng)
                       ->
                       (debug1
                          (fun uu____6893  ->
                             let uu____6894 =
                               FStar_Syntax_Print.fv_to_string fvar  in
                             FStar_Util.print1 "(1) Decided to unfold %s\n"
                               uu____6894);
                        (let lbm = find_let lbs fvar  in
                         match lbm with
                         | FStar_Pervasives_Native.Some lb ->
                             if
                               is_rec &&
                                 ((cfg.core_cfg).FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta
                             then
                               let uu____6902 = let_rec_arity lb  in
                               (match uu____6902 with
                                | (ar,lst) ->
                                    let uu____6921 =
                                      let uu____6926 =
                                        FStar_Syntax_Syntax.range_of_fv fvar
                                         in
                                      mk_rt uu____6926  in
                                    FStar_All.pipe_left uu____6921
                                      (FStar_TypeChecker_NBETerm.TopLevelRec
                                         (lb, ar, lst, [])))
                             else translate_letbinding cfg bs lb
                         | FStar_Pervasives_Native.None  ->
                             failwith "Could not find let binding"))
                   | uu____6944 ->
                       (debug1
                          (fun uu____6950  ->
                             let uu____6951 =
                               FStar_Syntax_Print.fv_to_string fvar  in
                             FStar_Util.print1
                               "(1) qninfo is None for (%s)\n" uu____6951);
                        FStar_TypeChecker_NBETerm.mkFV fvar [] [])
                 else
                   (debug1
                      (fun uu____6965  ->
                         let uu____6966 =
                           FStar_Syntax_Print.fv_to_string fvar  in
                         FStar_Util.print1
                           "(1) qninfo is not visible at this level (%s)\n"
                           uu____6966);
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
        let uu____6990 =
          FStar_Syntax_Util.arrow_formals lb.FStar_Syntax_Syntax.lbtyp  in
        match uu____6990 with
        | (formals,uu____6998) ->
            let arity = (FStar_List.length us) + (FStar_List.length formals)
               in
            if arity = Prims.int_zero
            then translate cfg bs lb.FStar_Syntax_Syntax.lbdef
            else
              (let uu____7016 =
                 FStar_Util.is_right lb.FStar_Syntax_Syntax.lbname  in
               if uu____7016
               then
                 (debug1
                    (fun uu____7026  ->
                       let uu____7027 =
                         FStar_Syntax_Print.lbname_to_string
                           lb.FStar_Syntax_Syntax.lbname
                          in
                       let uu____7029 = FStar_Util.string_of_int arity  in
                       FStar_Util.print2
                         "Making TopLevelLet for %s with arity %s\n"
                         uu____7027 uu____7029);
                  (let uu____7032 =
                     let uu____7037 =
                       FStar_Syntax_Syntax.range_of_lbname
                         lb.FStar_Syntax_Syntax.lbname
                        in
                     mk_rt uu____7037  in
                   FStar_All.pipe_left uu____7032
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
          let uu____7060 = let_rec_arity b  in
          match uu____7060 with
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
        let uu____7130 = FStar_BigInt.big_int_of_string s  in
        FStar_TypeChecker_NBETerm.Int uu____7130
    | FStar_Const.Const_string (s,r) ->
        FStar_TypeChecker_NBETerm.String (s, r)
    | FStar_Const.Const_char c1 -> FStar_TypeChecker_NBETerm.Char c1
    | FStar_Const.Const_range r -> FStar_TypeChecker_NBETerm.Range r
    | uu____7139 -> FStar_TypeChecker_NBETerm.SConst c

and (readback_comp :
  config -> FStar_TypeChecker_NBETerm.comp -> FStar_Syntax_Syntax.comp) =
  fun cfg  ->
    fun c  ->
      let c' =
        match c with
        | FStar_TypeChecker_NBETerm.Tot (typ,u) ->
            let uu____7149 =
              let uu____7158 = readback cfg typ  in (uu____7158, u)  in
            FStar_Syntax_Syntax.Total uu____7149
        | FStar_TypeChecker_NBETerm.GTot (typ,u) ->
            let uu____7171 =
              let uu____7180 = readback cfg typ  in (uu____7180, u)  in
            FStar_Syntax_Syntax.GTotal uu____7171
        | FStar_TypeChecker_NBETerm.Comp ctyp ->
            let uu____7188 = readback_comp_typ cfg ctyp  in
            FStar_Syntax_Syntax.Comp uu____7188
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
        let uu____7194 = c  in
        match uu____7194 with
        | { FStar_Syntax_Syntax.comp_univs = comp_univs;
            FStar_Syntax_Syntax.effect_name = effect_name;
            FStar_Syntax_Syntax.result_typ = result_typ;
            FStar_Syntax_Syntax.effect_args = effect_args;
            FStar_Syntax_Syntax.flags = flags;_} ->
            let uu____7214 =
              FStar_List.map (translate_univ cfg bs) comp_univs  in
            let uu____7215 = translate cfg bs result_typ  in
            let uu____7216 =
              FStar_List.map
                (fun x  ->
                   let uu____7244 =
                     translate cfg bs (FStar_Pervasives_Native.fst x)  in
                   (uu____7244, (FStar_Pervasives_Native.snd x))) effect_args
               in
            let uu____7251 = FStar_List.map (translate_flag cfg bs) flags  in
            {
              FStar_TypeChecker_NBETerm.comp_univs = uu____7214;
              FStar_TypeChecker_NBETerm.effect_name = effect_name;
              FStar_TypeChecker_NBETerm.result_typ = uu____7215;
              FStar_TypeChecker_NBETerm.effect_args = uu____7216;
              FStar_TypeChecker_NBETerm.flags = uu____7251
            }

and (readback_comp_typ :
  config ->
    FStar_TypeChecker_NBETerm.comp_typ -> FStar_Syntax_Syntax.comp_typ)
  =
  fun cfg  ->
    fun c  ->
      let uu____7256 = readback cfg c.FStar_TypeChecker_NBETerm.result_typ
         in
      let uu____7259 =
        FStar_List.map
          (fun x  ->
             let uu____7285 = readback cfg (FStar_Pervasives_Native.fst x)
                in
             (uu____7285, (FStar_Pervasives_Native.snd x)))
          c.FStar_TypeChecker_NBETerm.effect_args
         in
      let uu____7286 =
        FStar_List.map (readback_flag cfg) c.FStar_TypeChecker_NBETerm.flags
         in
      {
        FStar_Syntax_Syntax.comp_univs =
          (c.FStar_TypeChecker_NBETerm.comp_univs);
        FStar_Syntax_Syntax.effect_name =
          (c.FStar_TypeChecker_NBETerm.effect_name);
        FStar_Syntax_Syntax.result_typ = uu____7256;
        FStar_Syntax_Syntax.effect_args = uu____7259;
        FStar_Syntax_Syntax.flags = uu____7286
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
        let uu____7294 = c  in
        match uu____7294 with
        | { FStar_Syntax_Syntax.residual_effect = residual_effect;
            FStar_Syntax_Syntax.residual_typ = residual_typ;
            FStar_Syntax_Syntax.residual_flags = residual_flags;_} ->
            let uu____7304 =
              if
                ((cfg.core_cfg).FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.for_extraction
              then FStar_Pervasives_Native.None
              else FStar_Util.map_opt residual_typ (translate cfg bs)  in
            let uu____7314 =
              FStar_List.map (translate_flag cfg bs) residual_flags  in
            {
              FStar_TypeChecker_NBETerm.residual_effect = residual_effect;
              FStar_TypeChecker_NBETerm.residual_typ = uu____7304;
              FStar_TypeChecker_NBETerm.residual_flags = uu____7314
            }

and (readback_residual_comp :
  config ->
    FStar_TypeChecker_NBETerm.residual_comp ->
      FStar_Syntax_Syntax.residual_comp)
  =
  fun cfg  ->
    fun c  ->
      let uu____7319 =
        FStar_Util.map_opt c.FStar_TypeChecker_NBETerm.residual_typ
          (fun x  ->
             debug cfg
               (fun uu____7330  ->
                  let uu____7331 = FStar_TypeChecker_NBETerm.t_to_string x
                     in
                  FStar_Util.print1 "Reading back residualtype %s\n"
                    uu____7331);
             readback cfg x)
         in
      let uu____7334 =
        FStar_List.map (readback_flag cfg)
          c.FStar_TypeChecker_NBETerm.residual_flags
         in
      {
        FStar_Syntax_Syntax.residual_effect =
          (c.FStar_TypeChecker_NBETerm.residual_effect);
        FStar_Syntax_Syntax.residual_typ = uu____7319;
        FStar_Syntax_Syntax.residual_flags = uu____7334
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
            let uu____7345 = translate cfg bs tm  in
            FStar_TypeChecker_NBETerm.DECREASES uu____7345

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
          let uu____7349 = readback cfg t  in
          FStar_Syntax_Syntax.DECREASES uu____7349

and (translate_monadic :
  (FStar_Syntax_Syntax.monad_name * FStar_Syntax_Syntax.term'
    FStar_Syntax_Syntax.syntax) ->
    config ->
      FStar_TypeChecker_NBETerm.t Prims.list ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
          FStar_TypeChecker_NBETerm.t)
  =
  fun uu____7352  ->
    fun cfg  ->
      fun bs  ->
        fun e  ->
          match uu____7352 with
          | (m,ty) ->
              let e1 = FStar_Syntax_Util.unascribe e  in
              (match e1.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                   let uu____7390 =
                     let uu____7399 =
                       FStar_TypeChecker_Env.norm_eff_name
                         (cfg.core_cfg).FStar_TypeChecker_Cfg.tcenv m
                        in
                     FStar_TypeChecker_Env.effect_decl_opt
                       (cfg.core_cfg).FStar_TypeChecker_Cfg.tcenv uu____7399
                      in
                   (match uu____7390 with
                    | FStar_Pervasives_Native.None  ->
                        let uu____7406 =
                          let uu____7408 = FStar_Ident.string_of_lid m  in
                          FStar_Util.format1
                            "Effect declaration not found: %s" uu____7408
                           in
                        failwith uu____7406
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
                          let uu____7430 =
                            let uu____7431 =
                              let uu____7450 =
                                let uu____7459 =
                                  let uu____7466 =
                                    FStar_Util.left
                                      lb.FStar_Syntax_Syntax.lbname
                                     in
                                  (uu____7466, FStar_Pervasives_Native.None)
                                   in
                                [uu____7459]  in
                              (uu____7450, body,
                                (FStar_Pervasives_Native.Some body_rc))
                               in
                            FStar_Syntax_Syntax.Tm_abs uu____7431  in
                          FStar_Syntax_Syntax.mk uu____7430
                            body.FStar_Syntax_Syntax.pos
                           in
                        let maybe_range_arg =
                          let uu____7500 =
                            FStar_Util.for_some
                              (FStar_Syntax_Util.attr_eq
                                 FStar_Syntax_Util.dm4f_bind_range_attr)
                              ed.FStar_Syntax_Syntax.eff_attrs
                             in
                          if uu____7500
                          then
                            let uu____7509 =
                              let uu____7514 =
                                let uu____7515 =
                                  FStar_TypeChecker_Cfg.embed_simple
                                    FStar_Syntax_Embeddings.e_range
                                    lb.FStar_Syntax_Syntax.lbpos
                                    lb.FStar_Syntax_Syntax.lbpos
                                   in
                                translate cfg [] uu____7515  in
                              (uu____7514, FStar_Pervasives_Native.None)  in
                            let uu____7516 =
                              let uu____7523 =
                                let uu____7528 =
                                  let uu____7529 =
                                    FStar_TypeChecker_Cfg.embed_simple
                                      FStar_Syntax_Embeddings.e_range
                                      body.FStar_Syntax_Syntax.pos
                                      body.FStar_Syntax_Syntax.pos
                                     in
                                  translate cfg [] uu____7529  in
                                (uu____7528, FStar_Pervasives_Native.None)
                                 in
                              [uu____7523]  in
                            uu____7509 :: uu____7516
                          else []  in
                        let t =
                          let uu____7549 =
                            let uu____7550 =
                              let uu____7551 =
                                let uu____7552 =
                                  let uu____7553 =
                                    let uu____7560 =
                                      FStar_All.pipe_right ed
                                        FStar_Syntax_Util.get_bind_repr
                                       in
                                    FStar_All.pipe_right uu____7560
                                      FStar_Util.must
                                     in
                                  FStar_All.pipe_right uu____7553
                                    FStar_Pervasives_Native.snd
                                   in
                                FStar_Syntax_Util.un_uinst uu____7552  in
                              translate cfg' [] uu____7551  in
                            let uu____7581 =
                              let uu____7582 =
                                let uu____7587 =
                                  FStar_All.pipe_left mk_t
                                    (FStar_TypeChecker_NBETerm.Univ
                                       FStar_Syntax_Syntax.U_unknown)
                                   in
                                (uu____7587, FStar_Pervasives_Native.None)
                                 in
                              let uu____7588 =
                                let uu____7595 =
                                  let uu____7600 =
                                    FStar_All.pipe_left mk_t
                                      (FStar_TypeChecker_NBETerm.Univ
                                         FStar_Syntax_Syntax.U_unknown)
                                     in
                                  (uu____7600, FStar_Pervasives_Native.None)
                                   in
                                [uu____7595]  in
                              uu____7582 :: uu____7588  in
                            iapp cfg uu____7550 uu____7581  in
                          let uu____7613 =
                            let uu____7614 =
                              let uu____7621 =
                                let uu____7626 =
                                  translate cfg' bs
                                    lb.FStar_Syntax_Syntax.lbtyp
                                   in
                                (uu____7626, FStar_Pervasives_Native.None)
                                 in
                              let uu____7627 =
                                let uu____7634 =
                                  let uu____7639 = translate cfg' bs ty  in
                                  (uu____7639, FStar_Pervasives_Native.None)
                                   in
                                [uu____7634]  in
                              uu____7621 :: uu____7627  in
                            let uu____7652 =
                              let uu____7659 =
                                let uu____7666 =
                                  let uu____7673 =
                                    let uu____7678 =
                                      translate cfg bs
                                        lb.FStar_Syntax_Syntax.lbdef
                                       in
                                    (uu____7678,
                                      FStar_Pervasives_Native.None)
                                     in
                                  let uu____7679 =
                                    let uu____7686 =
                                      let uu____7693 =
                                        let uu____7698 =
                                          translate cfg bs body_lam  in
                                        (uu____7698,
                                          FStar_Pervasives_Native.None)
                                         in
                                      [uu____7693]  in
                                    ((mk_t FStar_TypeChecker_NBETerm.Unknown),
                                      FStar_Pervasives_Native.None) ::
                                      uu____7686
                                     in
                                  uu____7673 :: uu____7679  in
                                ((mk_t FStar_TypeChecker_NBETerm.Unknown),
                                  FStar_Pervasives_Native.None) :: uu____7666
                                 in
                              FStar_List.append maybe_range_arg uu____7659
                               in
                            FStar_List.append uu____7614 uu____7652  in
                          iapp cfg uu____7549 uu____7613  in
                        (debug cfg
                           (fun uu____7730  ->
                              let uu____7731 =
                                FStar_TypeChecker_NBETerm.t_to_string t  in
                              FStar_Util.print1 "translate_monadic: %s\n"
                                uu____7731);
                         t))
               | FStar_Syntax_Syntax.Tm_app
                   ({
                      FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                        (FStar_Const.Const_reflect uu____7734);
                      FStar_Syntax_Syntax.pos = uu____7735;
                      FStar_Syntax_Syntax.vars = uu____7736;_},(e2,uu____7738)::[])
                   ->
                   let uu____7777 = reifying_false cfg  in
                   translate uu____7777 bs e2
               | FStar_Syntax_Syntax.Tm_app (head,args) ->
                   (debug cfg
                      (fun uu____7808  ->
                         let uu____7809 =
                           FStar_Syntax_Print.term_to_string head  in
                         let uu____7811 =
                           FStar_Syntax_Print.args_to_string args  in
                         FStar_Util.print2
                           "translate_monadic app (%s) @ (%s)\n" uu____7809
                           uu____7811);
                    (let fallback1 uu____7819 = translate cfg bs e1  in
                     let fallback2 uu____7825 =
                       let uu____7826 = reifying_false cfg  in
                       let uu____7827 =
                         FStar_Syntax_Syntax.mk
                           (FStar_Syntax_Syntax.Tm_meta
                              (e1,
                                (FStar_Syntax_Syntax.Meta_monadic (m, ty))))
                           e1.FStar_Syntax_Syntax.pos
                          in
                       translate uu____7826 bs uu____7827  in
                     let uu____7832 =
                       let uu____7833 = FStar_Syntax_Util.un_uinst head  in
                       uu____7833.FStar_Syntax_Syntax.n  in
                     match uu____7832 with
                     | FStar_Syntax_Syntax.Tm_fvar fv ->
                         let lid = FStar_Syntax_Syntax.lid_of_fv fv  in
                         let qninfo =
                           FStar_TypeChecker_Env.lookup_qname
                             (cfg.core_cfg).FStar_TypeChecker_Cfg.tcenv lid
                            in
                         let uu____7839 =
                           let uu____7841 =
                             FStar_TypeChecker_Env.is_action
                               (cfg.core_cfg).FStar_TypeChecker_Cfg.tcenv lid
                              in
                           Prims.op_Negation uu____7841  in
                         if uu____7839
                         then fallback1 ()
                         else
                           (let uu____7846 =
                              let uu____7848 =
                                FStar_TypeChecker_Env.lookup_definition_qninfo
                                  (cfg.core_cfg).FStar_TypeChecker_Cfg.delta_level
                                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                  qninfo
                                 in
                              FStar_Option.isNone uu____7848  in
                            if uu____7846
                            then fallback2 ()
                            else
                              (let e2 =
                                 let uu____7863 =
                                   FStar_Syntax_Util.mk_reify head  in
                                 FStar_Syntax_Syntax.mk_Tm_app uu____7863
                                   args e1.FStar_Syntax_Syntax.pos
                                  in
                               let uu____7864 = reifying_false cfg  in
                               translate uu____7864 bs e2))
                     | uu____7865 -> fallback1 ()))
               | FStar_Syntax_Syntax.Tm_match (sc,branches) ->
                   let branches1 =
                     FStar_All.pipe_right branches
                       (FStar_List.map
                          (fun uu____7986  ->
                             match uu____7986 with
                             | (pat,wopt,tm) ->
                                 let uu____8034 =
                                   FStar_Syntax_Util.mk_reify tm  in
                                 (pat, wopt, uu____8034)))
                      in
                   let tm =
                     FStar_Syntax_Syntax.mk
                       (FStar_Syntax_Syntax.Tm_match (sc, branches1))
                       e1.FStar_Syntax_Syntax.pos
                      in
                   let uu____8066 = reifying_false cfg  in
                   translate uu____8066 bs tm
               | FStar_Syntax_Syntax.Tm_meta
                   (t,FStar_Syntax_Syntax.Meta_monadic uu____8068) ->
                   translate_monadic (m, ty) cfg bs e1
               | FStar_Syntax_Syntax.Tm_meta
                   (t,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,ty'))
                   -> translate_monadic_lift (msrc, mtgt, ty') cfg bs e1
               | uu____8095 ->
                   let uu____8096 =
                     let uu____8098 = FStar_Syntax_Print.tag_of_term e1  in
                     FStar_Util.format1
                       "Unexpected case in translate_monadic: %s" uu____8098
                      in
                   failwith uu____8096)

and (translate_monadic_lift :
  (FStar_Syntax_Syntax.monad_name * FStar_Syntax_Syntax.monad_name *
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax) ->
    config ->
      FStar_TypeChecker_NBETerm.t Prims.list ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
          FStar_TypeChecker_NBETerm.t)
  =
  fun uu____8101  ->
    fun cfg  ->
      fun bs  ->
        fun e  ->
          match uu____8101 with
          | (msrc,mtgt,ty) ->
              let e1 = FStar_Syntax_Util.unascribe e  in
              let uu____8125 =
                (FStar_Syntax_Util.is_pure_effect msrc) ||
                  (FStar_Syntax_Util.is_div_effect msrc)
                 in
              if uu____8125
              then
                let ed =
                  let uu____8129 =
                    FStar_TypeChecker_Env.norm_eff_name
                      (cfg.core_cfg).FStar_TypeChecker_Cfg.tcenv mtgt
                     in
                  FStar_TypeChecker_Env.get_effect_decl
                    (cfg.core_cfg).FStar_TypeChecker_Cfg.tcenv uu____8129
                   in
                let ret =
                  let uu____8131 =
                    let uu____8132 =
                      let uu____8135 =
                        let uu____8136 =
                          let uu____8143 =
                            FStar_All.pipe_right ed
                              FStar_Syntax_Util.get_return_repr
                             in
                          FStar_All.pipe_right uu____8143 FStar_Util.must  in
                        FStar_All.pipe_right uu____8136
                          FStar_Pervasives_Native.snd
                         in
                      FStar_Syntax_Subst.compress uu____8135  in
                    uu____8132.FStar_Syntax_Syntax.n  in
                  match uu____8131 with
                  | FStar_Syntax_Syntax.Tm_uinst (ret,uu____8189::[]) ->
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_uinst
                           (ret, [FStar_Syntax_Syntax.U_unknown]))
                        e1.FStar_Syntax_Syntax.pos
                  | uu____8196 ->
                      failwith "NYI: Reification of indexed effect (NBE)"
                   in
                let cfg' = reifying_false cfg  in
                let t =
                  let uu____8200 =
                    let uu____8201 = translate cfg' [] ret  in
                    let uu____8202 =
                      let uu____8203 =
                        let uu____8208 =
                          FStar_All.pipe_left mk_t
                            (FStar_TypeChecker_NBETerm.Univ
                               FStar_Syntax_Syntax.U_unknown)
                           in
                        (uu____8208, FStar_Pervasives_Native.None)  in
                      [uu____8203]  in
                    iapp cfg' uu____8201 uu____8202  in
                  let uu____8217 =
                    let uu____8218 =
                      let uu____8223 = translate cfg' bs ty  in
                      (uu____8223, FStar_Pervasives_Native.None)  in
                    let uu____8224 =
                      let uu____8231 =
                        let uu____8236 = translate cfg' bs e1  in
                        (uu____8236, FStar_Pervasives_Native.None)  in
                      [uu____8231]  in
                    uu____8218 :: uu____8224  in
                  iapp cfg' uu____8200 uu____8217  in
                (debug cfg
                   (fun uu____8252  ->
                      let uu____8253 =
                        FStar_TypeChecker_NBETerm.t_to_string t  in
                      FStar_Util.print1 "translate_monadic_lift(1): %s\n"
                        uu____8253);
                 t)
              else
                (let uu____8258 =
                   FStar_TypeChecker_Env.monad_leq
                     (cfg.core_cfg).FStar_TypeChecker_Cfg.tcenv msrc mtgt
                    in
                 match uu____8258 with
                 | FStar_Pervasives_Native.None  ->
                     let uu____8261 =
                       let uu____8263 = FStar_Ident.string_of_lid msrc  in
                       let uu____8265 = FStar_Ident.string_of_lid mtgt  in
                       FStar_Util.format2
                         "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                         uu____8263 uu____8265
                        in
                     failwith uu____8261
                 | FStar_Pervasives_Native.Some
                     { FStar_TypeChecker_Env.msource = uu____8268;
                       FStar_TypeChecker_Env.mtarget = uu____8269;
                       FStar_TypeChecker_Env.mlift =
                         { FStar_TypeChecker_Env.mlift_wp = uu____8270;
                           FStar_TypeChecker_Env.mlift_term =
                             FStar_Pervasives_Native.None ;_};_}
                     ->
                     let uu____8290 =
                       let uu____8292 = FStar_Ident.string_of_lid msrc  in
                       let uu____8294 = FStar_Ident.string_of_lid mtgt  in
                       FStar_Util.format2
                         "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
                         uu____8292 uu____8294
                        in
                     failwith uu____8290
                 | FStar_Pervasives_Native.Some
                     { FStar_TypeChecker_Env.msource = uu____8297;
                       FStar_TypeChecker_Env.mtarget = uu____8298;
                       FStar_TypeChecker_Env.mlift =
                         { FStar_TypeChecker_Env.mlift_wp = uu____8299;
                           FStar_TypeChecker_Env.mlift_term =
                             FStar_Pervasives_Native.Some lift;_};_}
                     ->
                     let lift_lam =
                       let x =
                         FStar_Syntax_Syntax.new_bv
                           FStar_Pervasives_Native.None
                           FStar_Syntax_Syntax.tun
                          in
                       let uu____8333 =
                         let uu____8336 = FStar_Syntax_Syntax.bv_to_name x
                            in
                         lift FStar_Syntax_Syntax.U_unknown ty uu____8336  in
                       FStar_Syntax_Util.abs
                         [(x, FStar_Pervasives_Native.None)] uu____8333
                         FStar_Pervasives_Native.None
                        in
                     let cfg' = reifying_false cfg  in
                     let t =
                       let uu____8353 = translate cfg' [] lift_lam  in
                       let uu____8354 =
                         let uu____8355 =
                           let uu____8360 = translate cfg bs e1  in
                           (uu____8360, FStar_Pervasives_Native.None)  in
                         [uu____8355]  in
                       iapp cfg uu____8353 uu____8354  in
                     (debug cfg
                        (fun uu____8372  ->
                           let uu____8373 =
                             FStar_TypeChecker_NBETerm.t_to_string t  in
                           FStar_Util.print1
                             "translate_monadic_lift(2): %s\n" uu____8373);
                      t))

and (readback :
  config -> FStar_TypeChecker_NBETerm.t -> FStar_Syntax_Syntax.term) =
  fun cfg  ->
    fun x  ->
      let debug1 = debug cfg  in
      let readback_args cfg1 args =
        map_rev
          (fun uu____8427  ->
             match uu____8427 with
             | (x1,q) ->
                 let uu____8438 = readback cfg1 x1  in (uu____8438, q)) args
         in
      let with_range t =
        let uu___1255_8451 = t  in
        {
          FStar_Syntax_Syntax.n = (uu___1255_8451.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = (x.FStar_TypeChecker_NBETerm.nbe_r);
          FStar_Syntax_Syntax.vars =
            (uu___1255_8451.FStar_Syntax_Syntax.vars)
        }  in
      let mk t = FStar_Syntax_Syntax.mk t x.FStar_TypeChecker_NBETerm.nbe_r
         in
      debug1
        (fun uu____8467  ->
           let uu____8468 = FStar_TypeChecker_NBETerm.t_to_string x  in
           FStar_Util.print1 "Readback: %s\n" uu____8468);
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
           let uu____8476 =
             let uu____8479 = FStar_BigInt.string_of_big_int i  in
             FStar_Syntax_Util.exp_int uu____8479  in
           with_range uu____8476
       | FStar_TypeChecker_NBETerm.Constant (FStar_TypeChecker_NBETerm.String
           (s,r)) ->
           mk
             (FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_string (s, r)))
       | FStar_TypeChecker_NBETerm.Constant (FStar_TypeChecker_NBETerm.Char
           c) ->
           let uu____8488 = FStar_Syntax_Util.exp_char c  in
           with_range uu____8488
       | FStar_TypeChecker_NBETerm.Constant (FStar_TypeChecker_NBETerm.Range
           r) ->
           FStar_TypeChecker_Cfg.embed_simple FStar_Syntax_Embeddings.e_range
             x.FStar_TypeChecker_NBETerm.nbe_r r
       | FStar_TypeChecker_NBETerm.Constant (FStar_TypeChecker_NBETerm.SConst
           c) -> mk (FStar_Syntax_Syntax.Tm_constant c)
       | FStar_TypeChecker_NBETerm.Meta (t,m) ->
           let uu____8499 =
             let uu____8500 =
               let uu____8507 = readback cfg t  in
               let uu____8510 = FStar_Thunk.force m  in
               (uu____8507, uu____8510)  in
             FStar_Syntax_Syntax.Tm_meta uu____8500  in
           mk uu____8499
       | FStar_TypeChecker_NBETerm.Type_t u ->
           mk (FStar_Syntax_Syntax.Tm_type u)
       | FStar_TypeChecker_NBETerm.Lam (f,binders,arity) ->
           let uu____8569 =
             match binders with
             | FStar_Util.Inl (ctx,binders1,rc) ->
                 let uu____8617 =
                   FStar_List.fold_left
                     (fun uu____8671  ->
                        fun uu____8672  ->
                          match (uu____8671, uu____8672) with
                          | ((ctx1,binders_rev,accus_rev),(x1,q)) ->
                              let tnorm =
                                let uu____8797 =
                                  translate cfg ctx1
                                    x1.FStar_Syntax_Syntax.sort
                                   in
                                readback cfg uu____8797  in
                              let x2 =
                                let uu___1313_8799 =
                                  FStar_Syntax_Syntax.freshen_bv x1  in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___1313_8799.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___1313_8799.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = tnorm
                                }  in
                              let ax = FStar_TypeChecker_NBETerm.mkAccuVar x2
                                 in
                              let ctx2 = ax :: ctx1  in
                              (ctx2, ((x2, q) :: binders_rev), (ax ::
                                accus_rev))) (ctx, [], []) binders1
                    in
                 (match uu____8617 with
                  | (ctx1,binders_rev,accus_rev) ->
                      let rc1 =
                        match rc with
                        | FStar_Pervasives_Native.None  ->
                            FStar_Pervasives_Native.None
                        | FStar_Pervasives_Native.Some rc1 ->
                            let uu____8885 =
                              let uu____8886 =
                                translate_residual_comp cfg ctx1 rc1  in
                              readback_residual_comp cfg uu____8886  in
                            FStar_Pervasives_Native.Some uu____8885
                         in
                      ((FStar_List.rev binders_rev), accus_rev, rc1))
             | FStar_Util.Inr args ->
                 let uu____8920 =
                   FStar_List.fold_right
                     (fun uu____8961  ->
                        fun uu____8962  ->
                          match (uu____8961, uu____8962) with
                          | ((t,uu____9014),(binders1,accus)) ->
                              let x1 =
                                let uu____9056 = readback cfg t  in
                                FStar_Syntax_Syntax.new_bv
                                  FStar_Pervasives_Native.None uu____9056
                                 in
                              let uu____9057 =
                                let uu____9060 =
                                  FStar_TypeChecker_NBETerm.mkAccuVar x1  in
                                uu____9060 :: accus  in
                              (((x1, FStar_Pervasives_Native.None) ::
                                binders1), uu____9057)) args ([], [])
                    in
                 (match uu____8920 with
                  | (binders1,accus) ->
                      (binders1, (FStar_List.rev accus),
                        FStar_Pervasives_Native.None))
              in
           (match uu____8569 with
            | (binders1,accus_rev,rc) ->
                let body =
                  let uu____9143 = f accus_rev  in readback cfg uu____9143
                   in
                let uu____9144 = FStar_Syntax_Util.abs binders1 body rc  in
                with_range uu____9144)
       | FStar_TypeChecker_NBETerm.Refinement (f,targ) ->
           if
             ((cfg.core_cfg).FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.for_extraction
           then
             let uu____9170 =
               let uu____9171 = targ ()  in
               FStar_Pervasives_Native.fst uu____9171  in
             readback cfg uu____9170
           else
             (let x1 =
                let uu____9179 =
                  let uu____9180 =
                    let uu____9181 = targ ()  in
                    FStar_Pervasives_Native.fst uu____9181  in
                  readback cfg uu____9180  in
                FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                  uu____9179
                 in
              let body =
                let uu____9187 =
                  let uu____9188 = FStar_TypeChecker_NBETerm.mkAccuVar x1  in
                  f uu____9188  in
                readback cfg uu____9187  in
              let refinement = FStar_Syntax_Util.refine x1 body  in
              let uu____9192 =
                if
                  ((cfg.core_cfg).FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.simplify
                then
                  FStar_TypeChecker_Common.simplify
                    ((cfg.core_cfg).FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                    refinement
                else refinement  in
              with_range uu____9192)
       | FStar_TypeChecker_NBETerm.Reflect t ->
           let tm = readback cfg t  in
           let uu____9202 = FStar_Syntax_Util.mk_reflect tm  in
           with_range uu____9202
       | FStar_TypeChecker_NBETerm.Arrow (FStar_Util.Inl f) ->
           let uu____9220 = FStar_Thunk.force f  in with_range uu____9220
       | FStar_TypeChecker_NBETerm.Arrow (FStar_Util.Inr (args,c)) ->
           let binders =
             FStar_List.map
               (fun uu____9269  ->
                  match uu____9269 with
                  | (t,q) ->
                      let t1 = readback cfg t  in
                      let x1 =
                        FStar_Syntax_Syntax.new_bv
                          FStar_Pervasives_Native.None t1
                         in
                      (x1, q)) args
              in
           let c1 = readback_comp cfg c  in
           let uu____9283 = FStar_Syntax_Util.arrow binders c1  in
           with_range uu____9283
       | FStar_TypeChecker_NBETerm.Construct (fv,us,args) ->
           let args1 =
             map_rev
               (fun uu____9324  ->
                  match uu____9324 with
                  | (x1,q) ->
                      let uu____9335 = readback cfg x1  in (uu____9335, q))
               args
              in
           let fv1 =
             let uu____9339 = FStar_Syntax_Syntax.range_of_fv fv  in
             FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
               uu____9339
              in
           let app =
             let uu____9343 =
               FStar_Syntax_Syntax.mk_Tm_uinst fv1 (FStar_List.rev us)  in
             FStar_Syntax_Util.mk_app uu____9343 args1  in
           with_range app
       | FStar_TypeChecker_NBETerm.FV (fv,us,args) ->
           let args1 =
             map_rev
               (fun uu____9384  ->
                  match uu____9384 with
                  | (x1,q) ->
                      let uu____9395 = readback cfg x1  in (uu____9395, q))
               args
              in
           let fv1 =
             FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
               FStar_Range.dummyRange
              in
           let app =
             let uu____9402 =
               FStar_Syntax_Syntax.mk_Tm_uinst fv1 (FStar_List.rev us)  in
             FStar_Syntax_Util.mk_app uu____9402 args1  in
           let uu____9405 =
             if
               ((cfg.core_cfg).FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.simplify
             then
               FStar_TypeChecker_Common.simplify
                 ((cfg.core_cfg).FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                 app
             else app  in
           with_range uu____9405
       | FStar_TypeChecker_NBETerm.Accu (FStar_TypeChecker_NBETerm.Var bv,[])
           ->
           let uu____9424 = FStar_Syntax_Syntax.bv_to_name bv  in
           with_range uu____9424
       | FStar_TypeChecker_NBETerm.Accu
           (FStar_TypeChecker_NBETerm.Var bv,args) ->
           let args1 = readback_args cfg args  in
           let app =
             let uu____9451 = FStar_Syntax_Syntax.bv_to_name bv  in
             FStar_Syntax_Util.mk_app uu____9451 args1  in
           let uu____9454 =
             if
               ((cfg.core_cfg).FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.simplify
             then
               FStar_TypeChecker_Common.simplify
                 ((cfg.core_cfg).FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                 app
             else app  in
           with_range uu____9454
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
           let uu____9522 =
             if
               ((cfg.core_cfg).FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.simplify
             then
               FStar_TypeChecker_Common.simplify
                 ((cfg.core_cfg).FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                 app
             else app  in
           with_range uu____9522
       | FStar_TypeChecker_NBETerm.Accu
           (FStar_TypeChecker_NBETerm.UnreducedLet
            (var,typ,defn,body,lb),args)
           ->
           let typ1 =
             let uu____9561 = FStar_Thunk.force typ  in
             readback cfg uu____9561  in
           let defn1 =
             let uu____9563 = FStar_Thunk.force defn  in
             readback cfg uu____9563  in
           let body1 =
             let uu____9565 =
               let uu____9566 = FStar_Thunk.force body  in
               readback cfg uu____9566  in
             FStar_Syntax_Subst.close [(var, FStar_Pervasives_Native.None)]
               uu____9565
              in
           let lbname =
             let uu____9586 =
               let uu___1432_9587 =
                 FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
               {
                 FStar_Syntax_Syntax.ppname =
                   (uu___1432_9587.FStar_Syntax_Syntax.ppname);
                 FStar_Syntax_Syntax.index =
                   (uu___1432_9587.FStar_Syntax_Syntax.index);
                 FStar_Syntax_Syntax.sort = typ1
               }  in
             FStar_Util.Inl uu____9586  in
           let lb1 =
             let uu___1435_9589 = lb  in
             {
               FStar_Syntax_Syntax.lbname = lbname;
               FStar_Syntax_Syntax.lbunivs =
                 (uu___1435_9589.FStar_Syntax_Syntax.lbunivs);
               FStar_Syntax_Syntax.lbtyp = typ1;
               FStar_Syntax_Syntax.lbeff =
                 (uu___1435_9589.FStar_Syntax_Syntax.lbeff);
               FStar_Syntax_Syntax.lbdef = defn1;
               FStar_Syntax_Syntax.lbattrs =
                 (uu___1435_9589.FStar_Syntax_Syntax.lbattrs);
               FStar_Syntax_Syntax.lbpos =
                 (uu___1435_9589.FStar_Syntax_Syntax.lbpos)
             }  in
           let hd =
             FStar_Syntax_Syntax.mk
               (FStar_Syntax_Syntax.Tm_let ((false, [lb1]), body1))
               FStar_Range.dummyRange
              in
           let args1 = readback_args cfg args  in
           let uu____9613 = FStar_Syntax_Util.mk_app hd args1  in
           with_range uu____9613
       | FStar_TypeChecker_NBETerm.Accu
           (FStar_TypeChecker_NBETerm.UnreducedLetRec
            (vars_typs_defns,body,lbs),args)
           ->
           let lbs1 =
             FStar_List.map2
               (fun uu____9670  ->
                  fun lb  ->
                    match uu____9670 with
                    | (v,t,d) ->
                        let t1 = readback cfg t  in
                        let def = readback cfg d  in
                        let v1 =
                          let uu___1455_9684 = v  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___1455_9684.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___1455_9684.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t1
                          }  in
                        let uu___1458_9685 = lb  in
                        {
                          FStar_Syntax_Syntax.lbname = (FStar_Util.Inl v1);
                          FStar_Syntax_Syntax.lbunivs =
                            (uu___1458_9685.FStar_Syntax_Syntax.lbunivs);
                          FStar_Syntax_Syntax.lbtyp = t1;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___1458_9685.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = def;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___1458_9685.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___1458_9685.FStar_Syntax_Syntax.lbpos)
                        }) vars_typs_defns lbs
              in
           let body1 = readback cfg body  in
           let uu____9687 = FStar_Syntax_Subst.close_let_rec lbs1 body1  in
           (match uu____9687 with
            | (lbs2,body2) ->
                let hd =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_let ((true, lbs2), body2))
                    FStar_Range.dummyRange
                   in
                let args1 = readback_args cfg args  in
                let uu____9723 = FStar_Syntax_Util.mk_app hd args1  in
                with_range uu____9723)
       | FStar_TypeChecker_NBETerm.Accu
           (FStar_TypeChecker_NBETerm.UVar f,args) ->
           let hd = FStar_Thunk.force f  in
           let args1 = readback_args cfg args  in
           let uu____9750 = FStar_Syntax_Util.mk_app hd args1  in
           with_range uu____9750
       | FStar_TypeChecker_NBETerm.TopLevelLet (lb,arity,args_rev) ->
           let n_univs = FStar_List.length lb.FStar_Syntax_Syntax.lbunivs  in
           let n_args = FStar_List.length args_rev  in
           let uu____9776 = FStar_Util.first_N (n_args - n_univs) args_rev
              in
           (match uu____9776 with
            | (args_rev1,univs) ->
                let uu____9823 =
                  let uu____9824 =
                    let uu____9825 =
                      FStar_List.map FStar_Pervasives_Native.fst univs  in
                    translate cfg uu____9825 lb.FStar_Syntax_Syntax.lbdef  in
                  iapp cfg uu____9824 (FStar_List.rev args_rev1)  in
                readback cfg uu____9823)
       | FStar_TypeChecker_NBETerm.TopLevelRec
           (lb,uu____9837,uu____9838,args) ->
           let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
           let head =
             FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
               FStar_Range.dummyRange
              in
           let args1 =
             FStar_List.map
               (fun uu____9883  ->
                  match uu____9883 with
                  | (t,q) ->
                      let uu____9894 = readback cfg t  in (uu____9894, q))
               args
              in
           let uu____9895 = FStar_Syntax_Util.mk_app head args1  in
           with_range uu____9895
       | FStar_TypeChecker_NBETerm.LocalLetRec
           (i,uu____9899,lbs,bs,args,_ar,_ar_lst) ->
           let lbnames =
             FStar_List.map
               (fun lb  ->
                  let uu____9941 =
                    let uu____9943 =
                      let uu____9944 =
                        FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                      uu____9944.FStar_Syntax_Syntax.ppname  in
                    FStar_Ident.string_of_id uu____9943  in
                  FStar_Syntax_Syntax.gen_bv uu____9941
                    FStar_Pervasives_Native.None lb.FStar_Syntax_Syntax.lbtyp)
               lbs
              in
           let let_rec_env =
             let uu____9948 =
               FStar_List.map
                 (fun x1  ->
                    let uu____9954 = FStar_Syntax_Syntax.range_of_bv x1  in
                    mk_rt uu____9954
                      (FStar_TypeChecker_NBETerm.Accu
                         ((FStar_TypeChecker_NBETerm.Var x1), []))) lbnames
                in
             FStar_List.rev_append uu____9948 bs  in
           let lbs1 =
             FStar_List.map2
               (fun lb  ->
                  fun lbname  ->
                    let lbdef =
                      let uu____9976 =
                        translate cfg let_rec_env
                          lb.FStar_Syntax_Syntax.lbdef
                         in
                      readback cfg uu____9976  in
                    let lbtyp =
                      let uu____9978 =
                        translate cfg bs lb.FStar_Syntax_Syntax.lbtyp  in
                      readback cfg uu____9978  in
                    let uu___1513_9979 = lb  in
                    {
                      FStar_Syntax_Syntax.lbname = (FStar_Util.Inl lbname);
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___1513_9979.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = lbtyp;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___1513_9979.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = lbdef;
                      FStar_Syntax_Syntax.lbattrs =
                        (uu___1513_9979.FStar_Syntax_Syntax.lbattrs);
                      FStar_Syntax_Syntax.lbpos =
                        (uu___1513_9979.FStar_Syntax_Syntax.lbpos)
                    }) lbs lbnames
              in
           let body =
             let uu____9981 = FStar_List.nth lbnames i  in
             FStar_Syntax_Syntax.bv_to_name uu____9981  in
           let uu____9982 = FStar_Syntax_Subst.close_let_rec lbs1 body  in
           (match uu____9982 with
            | (lbs2,body1) ->
                let head =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_let ((true, lbs2), body1))
                    FStar_Range.dummyRange
                   in
                let args1 =
                  FStar_List.map
                    (fun uu____10030  ->
                       match uu____10030 with
                       | (x1,q) ->
                           let uu____10041 = readback cfg x1  in
                           (uu____10041, q)) args
                   in
                let uu____10042 = FStar_Syntax_Util.mk_app head args1  in
                with_range uu____10042)
       | FStar_TypeChecker_NBETerm.Quote (qt,qi) ->
           mk (FStar_Syntax_Syntax.Tm_quoted (qt, qi))
       | FStar_TypeChecker_NBETerm.Lazy (FStar_Util.Inl li,uu____10050) ->
           mk (FStar_Syntax_Syntax.Tm_lazy li)
       | FStar_TypeChecker_NBETerm.Lazy (uu____10067,thunk) ->
           let uu____10089 = FStar_Thunk.force thunk  in
           readback cfg uu____10089)

type step =
  | Primops 
  | UnfoldUntil of FStar_Syntax_Syntax.delta_depth 
  | UnfoldOnly of FStar_Ident.lid Prims.list 
  | UnfoldAttr of FStar_Ident.lid Prims.list 
  | UnfoldTac 
  | Reify 
let (uu___is_Primops : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Primops  -> true | uu____10118 -> false
  
let (uu___is_UnfoldUntil : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldUntil _0 -> true | uu____10130 -> false
  
let (__proj__UnfoldUntil__item___0 : step -> FStar_Syntax_Syntax.delta_depth)
  = fun projectee  -> match projectee with | UnfoldUntil _0 -> _0 
let (uu___is_UnfoldOnly : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldOnly _0 -> true | uu____10151 -> false
  
let (__proj__UnfoldOnly__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldOnly _0 -> _0 
let (uu___is_UnfoldAttr : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldAttr _0 -> true | uu____10178 -> false
  
let (__proj__UnfoldAttr__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldAttr _0 -> _0 
let (uu___is_UnfoldTac : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldTac  -> true | uu____10202 -> false
  
let (uu___is_Reify : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reify  -> true | uu____10213 -> false
  
let (step_as_normalizer_step : step -> FStar_TypeChecker_Env.step) =
  fun uu___2_10220  ->
    match uu___2_10220 with
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
        let uu____10244 = new_config cfg  in iapp uu____10244 t args
  
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
            let uu___1559_10276 = cfg  in
            {
              FStar_TypeChecker_Cfg.steps =
                (let uu___1561_10279 = cfg.FStar_TypeChecker_Cfg.steps  in
                 {
                   FStar_TypeChecker_Cfg.beta =
                     (uu___1561_10279.FStar_TypeChecker_Cfg.beta);
                   FStar_TypeChecker_Cfg.iota =
                     (uu___1561_10279.FStar_TypeChecker_Cfg.iota);
                   FStar_TypeChecker_Cfg.zeta =
                     (uu___1561_10279.FStar_TypeChecker_Cfg.zeta);
                   FStar_TypeChecker_Cfg.zeta_full =
                     (uu___1561_10279.FStar_TypeChecker_Cfg.zeta_full);
                   FStar_TypeChecker_Cfg.weak =
                     (uu___1561_10279.FStar_TypeChecker_Cfg.weak);
                   FStar_TypeChecker_Cfg.hnf =
                     (uu___1561_10279.FStar_TypeChecker_Cfg.hnf);
                   FStar_TypeChecker_Cfg.primops =
                     (uu___1561_10279.FStar_TypeChecker_Cfg.primops);
                   FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                     (uu___1561_10279.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                   FStar_TypeChecker_Cfg.unfold_until =
                     (uu___1561_10279.FStar_TypeChecker_Cfg.unfold_until);
                   FStar_TypeChecker_Cfg.unfold_only =
                     (uu___1561_10279.FStar_TypeChecker_Cfg.unfold_only);
                   FStar_TypeChecker_Cfg.unfold_fully =
                     (uu___1561_10279.FStar_TypeChecker_Cfg.unfold_fully);
                   FStar_TypeChecker_Cfg.unfold_attr =
                     (uu___1561_10279.FStar_TypeChecker_Cfg.unfold_attr);
                   FStar_TypeChecker_Cfg.unfold_tac =
                     (uu___1561_10279.FStar_TypeChecker_Cfg.unfold_tac);
                   FStar_TypeChecker_Cfg.pure_subterms_within_computations =
                     (uu___1561_10279.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                   FStar_TypeChecker_Cfg.simplify =
                     (uu___1561_10279.FStar_TypeChecker_Cfg.simplify);
                   FStar_TypeChecker_Cfg.erase_universes =
                     (uu___1561_10279.FStar_TypeChecker_Cfg.erase_universes);
                   FStar_TypeChecker_Cfg.allow_unbound_universes =
                     (uu___1561_10279.FStar_TypeChecker_Cfg.allow_unbound_universes);
                   FStar_TypeChecker_Cfg.reify_ = true;
                   FStar_TypeChecker_Cfg.compress_uvars =
                     (uu___1561_10279.FStar_TypeChecker_Cfg.compress_uvars);
                   FStar_TypeChecker_Cfg.no_full_norm =
                     (uu___1561_10279.FStar_TypeChecker_Cfg.no_full_norm);
                   FStar_TypeChecker_Cfg.check_no_uvars =
                     (uu___1561_10279.FStar_TypeChecker_Cfg.check_no_uvars);
                   FStar_TypeChecker_Cfg.unmeta =
                     (uu___1561_10279.FStar_TypeChecker_Cfg.unmeta);
                   FStar_TypeChecker_Cfg.unascribe =
                     (uu___1561_10279.FStar_TypeChecker_Cfg.unascribe);
                   FStar_TypeChecker_Cfg.in_full_norm_request =
                     (uu___1561_10279.FStar_TypeChecker_Cfg.in_full_norm_request);
                   FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                     (uu___1561_10279.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                   FStar_TypeChecker_Cfg.nbe_step =
                     (uu___1561_10279.FStar_TypeChecker_Cfg.nbe_step);
                   FStar_TypeChecker_Cfg.for_extraction =
                     (uu___1561_10279.FStar_TypeChecker_Cfg.for_extraction)
                 });
              FStar_TypeChecker_Cfg.tcenv =
                (uu___1559_10276.FStar_TypeChecker_Cfg.tcenv);
              FStar_TypeChecker_Cfg.debug =
                (uu___1559_10276.FStar_TypeChecker_Cfg.debug);
              FStar_TypeChecker_Cfg.delta_level =
                (uu___1559_10276.FStar_TypeChecker_Cfg.delta_level);
              FStar_TypeChecker_Cfg.primitive_steps =
                (uu___1559_10276.FStar_TypeChecker_Cfg.primitive_steps);
              FStar_TypeChecker_Cfg.strong =
                (uu___1559_10276.FStar_TypeChecker_Cfg.strong);
              FStar_TypeChecker_Cfg.memoize_lazy =
                (uu___1559_10276.FStar_TypeChecker_Cfg.memoize_lazy);
              FStar_TypeChecker_Cfg.normalize_pure_lets =
                (uu___1559_10276.FStar_TypeChecker_Cfg.normalize_pure_lets);
              FStar_TypeChecker_Cfg.reifying =
                (uu___1559_10276.FStar_TypeChecker_Cfg.reifying)
            }  in
          (let uu____10282 =
             (FStar_TypeChecker_Env.debug env (FStar_Options.Other "NBETop"))
               ||
               (FStar_TypeChecker_Env.debug env (FStar_Options.Other "NBE"))
              in
           if uu____10282
           then
             let uu____10287 = FStar_Syntax_Print.term_to_string e  in
             FStar_Util.print1 "Calling NBE with (%s) {\n" uu____10287
           else ());
          (let cfg2 = new_config cfg1  in
           let r =
             let uu____10294 = translate cfg2 [] e  in
             readback cfg2 uu____10294  in
           (let uu____10296 =
              (FStar_TypeChecker_Env.debug env (FStar_Options.Other "NBETop"))
                ||
                (FStar_TypeChecker_Env.debug env (FStar_Options.Other "NBE"))
               in
            if uu____10296
            then
              let uu____10301 = FStar_Syntax_Print.term_to_string r  in
              FStar_Util.print1 "}\nNBE returned (%s)\n" uu____10301
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
          let uu___1577_10328 = cfg  in
          {
            FStar_TypeChecker_Cfg.steps =
              (let uu___1579_10331 = cfg.FStar_TypeChecker_Cfg.steps  in
               {
                 FStar_TypeChecker_Cfg.beta =
                   (uu___1579_10331.FStar_TypeChecker_Cfg.beta);
                 FStar_TypeChecker_Cfg.iota =
                   (uu___1579_10331.FStar_TypeChecker_Cfg.iota);
                 FStar_TypeChecker_Cfg.zeta =
                   (uu___1579_10331.FStar_TypeChecker_Cfg.zeta);
                 FStar_TypeChecker_Cfg.zeta_full =
                   (uu___1579_10331.FStar_TypeChecker_Cfg.zeta_full);
                 FStar_TypeChecker_Cfg.weak =
                   (uu___1579_10331.FStar_TypeChecker_Cfg.weak);
                 FStar_TypeChecker_Cfg.hnf =
                   (uu___1579_10331.FStar_TypeChecker_Cfg.hnf);
                 FStar_TypeChecker_Cfg.primops =
                   (uu___1579_10331.FStar_TypeChecker_Cfg.primops);
                 FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                   (uu___1579_10331.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                 FStar_TypeChecker_Cfg.unfold_until =
                   (uu___1579_10331.FStar_TypeChecker_Cfg.unfold_until);
                 FStar_TypeChecker_Cfg.unfold_only =
                   (uu___1579_10331.FStar_TypeChecker_Cfg.unfold_only);
                 FStar_TypeChecker_Cfg.unfold_fully =
                   (uu___1579_10331.FStar_TypeChecker_Cfg.unfold_fully);
                 FStar_TypeChecker_Cfg.unfold_attr =
                   (uu___1579_10331.FStar_TypeChecker_Cfg.unfold_attr);
                 FStar_TypeChecker_Cfg.unfold_tac =
                   (uu___1579_10331.FStar_TypeChecker_Cfg.unfold_tac);
                 FStar_TypeChecker_Cfg.pure_subterms_within_computations =
                   (uu___1579_10331.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                 FStar_TypeChecker_Cfg.simplify =
                   (uu___1579_10331.FStar_TypeChecker_Cfg.simplify);
                 FStar_TypeChecker_Cfg.erase_universes =
                   (uu___1579_10331.FStar_TypeChecker_Cfg.erase_universes);
                 FStar_TypeChecker_Cfg.allow_unbound_universes =
                   (uu___1579_10331.FStar_TypeChecker_Cfg.allow_unbound_universes);
                 FStar_TypeChecker_Cfg.reify_ = true;
                 FStar_TypeChecker_Cfg.compress_uvars =
                   (uu___1579_10331.FStar_TypeChecker_Cfg.compress_uvars);
                 FStar_TypeChecker_Cfg.no_full_norm =
                   (uu___1579_10331.FStar_TypeChecker_Cfg.no_full_norm);
                 FStar_TypeChecker_Cfg.check_no_uvars =
                   (uu___1579_10331.FStar_TypeChecker_Cfg.check_no_uvars);
                 FStar_TypeChecker_Cfg.unmeta =
                   (uu___1579_10331.FStar_TypeChecker_Cfg.unmeta);
                 FStar_TypeChecker_Cfg.unascribe =
                   (uu___1579_10331.FStar_TypeChecker_Cfg.unascribe);
                 FStar_TypeChecker_Cfg.in_full_norm_request =
                   (uu___1579_10331.FStar_TypeChecker_Cfg.in_full_norm_request);
                 FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                   (uu___1579_10331.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                 FStar_TypeChecker_Cfg.nbe_step =
                   (uu___1579_10331.FStar_TypeChecker_Cfg.nbe_step);
                 FStar_TypeChecker_Cfg.for_extraction =
                   (uu___1579_10331.FStar_TypeChecker_Cfg.for_extraction)
               });
            FStar_TypeChecker_Cfg.tcenv =
              (uu___1577_10328.FStar_TypeChecker_Cfg.tcenv);
            FStar_TypeChecker_Cfg.debug =
              (uu___1577_10328.FStar_TypeChecker_Cfg.debug);
            FStar_TypeChecker_Cfg.delta_level =
              (uu___1577_10328.FStar_TypeChecker_Cfg.delta_level);
            FStar_TypeChecker_Cfg.primitive_steps =
              (uu___1577_10328.FStar_TypeChecker_Cfg.primitive_steps);
            FStar_TypeChecker_Cfg.strong =
              (uu___1577_10328.FStar_TypeChecker_Cfg.strong);
            FStar_TypeChecker_Cfg.memoize_lazy =
              (uu___1577_10328.FStar_TypeChecker_Cfg.memoize_lazy);
            FStar_TypeChecker_Cfg.normalize_pure_lets =
              (uu___1577_10328.FStar_TypeChecker_Cfg.normalize_pure_lets);
            FStar_TypeChecker_Cfg.reifying =
              (uu___1577_10328.FStar_TypeChecker_Cfg.reifying)
          }  in
        let cfg2 = new_config cfg1  in
        debug cfg2
          (fun uu____10337  ->
             let uu____10338 = FStar_Syntax_Print.term_to_string e  in
             FStar_Util.print1 "Calling NBE with (%s) {\n" uu____10338);
        (let r =
           let uu____10342 = translate cfg2 [] e  in
           readback cfg2 uu____10342  in
         debug cfg2
           (fun uu____10346  ->
              let uu____10347 = FStar_Syntax_Print.term_to_string r  in
              FStar_Util.print1 "}\nNBE returned (%s)\n" uu____10347);
         r)
  