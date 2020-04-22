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
let (unlazy : FStar_TypeChecker_NBETerm.t -> FStar_TypeChecker_NBETerm.t) =
  fun t  ->
    match t with
    | FStar_TypeChecker_NBETerm.Lazy (uu____661,t1) -> FStar_Thunk.force t1
    | t1 -> t1
  
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
              (fun uu____792  ->
                 let uu____793 =
                   FStar_TypeChecker_NBETerm.t_to_string scrutinee0  in
                 let uu____795 = FStar_Syntax_Print.pat_to_string p  in
                 FStar_Util.print2 "matches_pat (%s, %s)\n" uu____793
                   uu____795);
            (let scrutinee = unlazy scrutinee0  in
             let r =
               match p.FStar_Syntax_Syntax.v with
               | FStar_Syntax_Syntax.Pat_var bv ->
                   FStar_Util.Inl [scrutinee0]
               | FStar_Syntax_Syntax.Pat_wild bv ->
                   FStar_Util.Inl [scrutinee0]
               | FStar_Syntax_Syntax.Pat_dot_term uu____822 ->
                   FStar_Util.Inl []
               | FStar_Syntax_Syntax.Pat_constant s ->
                   let matches_const c s1 =
                     debug cfg
                       (fun uu____849  ->
                          let uu____850 =
                            FStar_TypeChecker_NBETerm.t_to_string c  in
                          let uu____852 =
                            FStar_Syntax_Print.const_to_string s1  in
                          FStar_Util.print2
                            "Testing term %s against pattern %s\n" uu____850
                            uu____852);
                     (match c with
                      | FStar_TypeChecker_NBETerm.Constant
                          (FStar_TypeChecker_NBETerm.Unit ) ->
                          s1 = FStar_Const.Const_unit
                      | FStar_TypeChecker_NBETerm.Constant
                          (FStar_TypeChecker_NBETerm.Bool b) ->
                          (match s1 with
                           | FStar_Const.Const_bool p1 -> b = p1
                           | uu____862 -> false)
                      | FStar_TypeChecker_NBETerm.Constant
                          (FStar_TypeChecker_NBETerm.Int i) ->
                          (match s1 with
                           | FStar_Const.Const_int
                               (p1,FStar_Pervasives_Native.None ) ->
                               let uu____879 =
                                 FStar_BigInt.big_int_of_string p1  in
                               i = uu____879
                           | uu____880 -> false)
                      | FStar_TypeChecker_NBETerm.Constant
                          (FStar_TypeChecker_NBETerm.String (st,uu____883))
                          ->
                          (match s1 with
                           | FStar_Const.Const_string (p1,uu____888) ->
                               st = p1
                           | uu____892 -> false)
                      | FStar_TypeChecker_NBETerm.Constant
                          (FStar_TypeChecker_NBETerm.Char c1) ->
                          (match s1 with
                           | FStar_Const.Const_char p1 -> c1 = p1
                           | uu____900 -> false)
                      | uu____902 -> false)
                      in
                   let uu____904 = matches_const scrutinee s  in
                   if uu____904
                   then FStar_Util.Inl []
                   else FStar_Util.Inr false
               | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                   let rec matches_args out a p1 =
                     match (a, p1) with
                     | ([],[]) -> FStar_Util.Inl out
                     | ((t,uu____1042)::rest_a,(p2,uu____1045)::rest_p) ->
                         let uu____1084 = matches_pat t p2  in
                         (match uu____1084 with
                          | FStar_Util.Inl s ->
                              matches_args (FStar_List.append out s) rest_a
                                rest_p
                          | m -> m)
                     | uu____1113 -> FStar_Util.Inr false  in
                   (match scrutinee with
                    | FStar_TypeChecker_NBETerm.Construct (fv',_us,args_rev)
                        ->
                        let uu____1161 = FStar_Syntax_Syntax.fv_eq fv fv'  in
                        if uu____1161
                        then
                          matches_args [] (FStar_List.rev args_rev) arg_pats
                        else FStar_Util.Inr false
                    | uu____1181 -> FStar_Util.Inr true)
                in
             let res_to_string uu___0_1199 =
               match uu___0_1199 with
               | FStar_Util.Inr b ->
                   let uu____1213 = FStar_Util.string_of_bool b  in
                   Prims.op_Hat "Inr " uu____1213
               | FStar_Util.Inl bs ->
                   let uu____1222 =
                     FStar_Util.string_of_int (FStar_List.length bs)  in
                   Prims.op_Hat "Inl " uu____1222
                in
             debug cfg
               (fun uu____1230  ->
                  let uu____1231 =
                    FStar_TypeChecker_NBETerm.t_to_string scrutinee  in
                  let uu____1233 = FStar_Syntax_Print.pat_to_string p  in
                  let uu____1235 = res_to_string r  in
                  FStar_Util.print3 "matches_pat (%s, %s) = %s\n" uu____1231
                    uu____1233 uu____1235);
             r)
             in
          match branches1 with
          | [] -> FStar_Pervasives_Native.None
          | (p,_wopt,e)::branches2 ->
              let uu____1274 = matches_pat scrut1 p  in
              (match uu____1274 with
               | FStar_Util.Inl matches ->
                   (debug cfg
                      (fun uu____1299  ->
                         let uu____1300 = FStar_Syntax_Print.pat_to_string p
                            in
                         FStar_Util.print1 "Pattern %s matches\n" uu____1300);
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
        | (uu____1449,[]) -> (true, acc, ts)
        | ([],uu____1480::uu____1481) -> (false, acc, [])
        | (t::ts1,in_decreases_clause::bs) ->
            let uu____1550 =
              in_decreases_clause &&
                (FStar_TypeChecker_NBETerm.isAccu
                   (FStar_Pervasives_Native.fst t))
               in
            if uu____1550
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
        let mapper uu____1649 =
          match uu____1649 with
          | (lr,rng) ->
              (match lr with
               | FStar_Util.Inr (elt,FStar_Pervasives_Native.None ) ->
                   FStar_Pervasives_Native.Some elt
               | FStar_Util.Inr (elt,FStar_Pervasives_Native.Some us) ->
                   (debug cfg
                      (fun uu____1732  ->
                         let uu____1733 =
                           FStar_Syntax_Print.univs_to_string us  in
                         FStar_Util.print1
                           "Universes in local declaration: %s\n" uu____1733);
                    FStar_Pervasives_Native.Some elt)
               | uu____1736 -> FStar_Pervasives_Native.None)
           in
        let uu____1751 = FStar_TypeChecker_Env.lookup_qname env lid  in
        FStar_Util.bind_opt uu____1751 mapper
  
let (is_univ : FStar_TypeChecker_NBETerm.t -> Prims.bool) =
  fun tm  ->
    match tm with
    | FStar_TypeChecker_NBETerm.Univ uu____1798 -> true
    | uu____1800 -> false
  
let (un_univ : FStar_TypeChecker_NBETerm.t -> FStar_Syntax_Syntax.universe) =
  fun tm  ->
    match tm with
    | FStar_TypeChecker_NBETerm.Univ u -> u
    | t ->
        let uu____1810 =
          let uu____1812 = FStar_TypeChecker_NBETerm.t_to_string t  in
          Prims.op_Hat "Not a universe: " uu____1812  in
        failwith uu____1810
  
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
              (uu____1834,uu____1835,uu____1836,uu____1837,uu____1838,uu____1839);
            FStar_Syntax_Syntax.sigrng = uu____1840;
            FStar_Syntax_Syntax.sigquals = uu____1841;
            FStar_Syntax_Syntax.sigmeta = uu____1842;
            FStar_Syntax_Syntax.sigattrs = uu____1843;
            FStar_Syntax_Syntax.sigopts = uu____1844;_},uu____1845),uu____1846)
        -> true
    | uu____1906 -> false
  
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
              let uu____1946 = aux u3  in
              FStar_Syntax_Syntax.U_succ uu____1946
          | FStar_Syntax_Syntax.U_max us ->
              let uu____1950 = FStar_List.map aux us  in
              FStar_Syntax_Syntax.U_max uu____1950
          | FStar_Syntax_Syntax.U_unknown  -> u2
          | FStar_Syntax_Syntax.U_name uu____1953 -> u2
          | FStar_Syntax_Syntax.U_unif uu____1954 -> u2
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
           | FStar_Util.Inl uu____1987 -> failwith "find_let : impossible"
           | FStar_Util.Inr name ->
               let uu____1992 = FStar_Syntax_Syntax.fv_eq name fvar  in
               if uu____1992
               then FStar_Pervasives_Native.Some lb
               else FStar_Pervasives_Native.None)
  
let rec (translate :
  config ->
    FStar_TypeChecker_NBETerm.t Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_TypeChecker_NBETerm.t)
  =
  fun cfg  ->
    fun bs  ->
      fun e  ->
        let debug1 = debug cfg  in
        debug1
          (fun uu____2263  ->
             let uu____2264 =
               let uu____2266 = FStar_Syntax_Subst.compress e  in
               FStar_Syntax_Print.tag_of_term uu____2266  in
             let uu____2267 =
               let uu____2269 = FStar_Syntax_Subst.compress e  in
               FStar_Syntax_Print.term_to_string uu____2269  in
             FStar_Util.print2 "Term: %s - %s\n" uu____2264 uu____2267);
        (let uu____2271 =
           let uu____2272 = FStar_Syntax_Subst.compress e  in
           uu____2272.FStar_Syntax_Syntax.n  in
         match uu____2271 with
         | FStar_Syntax_Syntax.Tm_delayed (uu____2275,uu____2276) ->
             failwith "Tm_delayed: Impossible"
         | FStar_Syntax_Syntax.Tm_unknown  ->
             FStar_TypeChecker_NBETerm.Unknown
         | FStar_Syntax_Syntax.Tm_constant c ->
             let uu____2299 = translate_constant c  in
             FStar_TypeChecker_NBETerm.Constant uu____2299
         | FStar_Syntax_Syntax.Tm_bvar db ->
             if db.FStar_Syntax_Syntax.index < (FStar_List.length bs)
             then
               let t = FStar_List.nth bs db.FStar_Syntax_Syntax.index  in
               (debug1
                  (fun uu____2310  ->
                     let uu____2311 = FStar_TypeChecker_NBETerm.t_to_string t
                        in
                     let uu____2313 =
                       let uu____2315 =
                         FStar_List.map FStar_TypeChecker_NBETerm.t_to_string
                           bs
                          in
                       FStar_All.pipe_right uu____2315
                         (FStar_String.concat "; ")
                        in
                     FStar_Util.print2
                       "Resolved bvar to %s\n\tcontext is [%s]\n" uu____2311
                       uu____2313);
                t)
             else failwith "de Bruijn index out of bounds"
         | FStar_Syntax_Syntax.Tm_uinst (t,us) ->
             (debug1
                (fun uu____2342  ->
                   let uu____2343 = FStar_Syntax_Print.term_to_string t  in
                   let uu____2345 =
                     let uu____2347 =
                       FStar_List.map FStar_Syntax_Print.univ_to_string us
                        in
                     FStar_All.pipe_right uu____2347
                       (FStar_String.concat ", ")
                      in
                   FStar_Util.print2 "Uinst term : %s\nUnivs : %s\n"
                     uu____2343 uu____2345);
              (let uu____2358 = translate cfg bs t  in
               let uu____2359 =
                 FStar_List.map
                   (fun x  ->
                      let uu____2363 =
                        let uu____2364 = translate_univ cfg bs x  in
                        FStar_TypeChecker_NBETerm.Univ uu____2364  in
                      FStar_TypeChecker_NBETerm.as_arg uu____2363) us
                  in
               iapp cfg uu____2358 uu____2359))
         | FStar_Syntax_Syntax.Tm_type u ->
             let uu____2366 = translate_univ cfg bs u  in
             FStar_TypeChecker_NBETerm.Type_t uu____2366
         | FStar_Syntax_Syntax.Tm_arrow (xs,c) ->
             let norm uu____2396 =
               let uu____2397 =
                 FStar_List.fold_left
                   (fun uu____2441  ->
                      fun uu____2442  ->
                        match (uu____2441, uu____2442) with
                        | ((ctx,binders_rev),(x,q)) ->
                            let t =
                              let uu____2546 =
                                translate cfg ctx x.FStar_Syntax_Syntax.sort
                                 in
                              readback cfg uu____2546  in
                            let x1 =
                              let uu___380_2548 =
                                FStar_Syntax_Syntax.freshen_bv x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___380_2548.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___380_2548.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t
                              }  in
                            let ctx1 =
                              let uu____2552 =
                                FStar_TypeChecker_NBETerm.mkAccuVar x1  in
                              uu____2552 :: ctx  in
                            (ctx1, ((x1, q) :: binders_rev))) (bs, []) xs
                  in
               match uu____2397 with
               | (ctx,binders_rev) ->
                   let c1 =
                     let uu____2612 = translate_comp cfg ctx c  in
                     readback_comp cfg uu____2612  in
                   FStar_Syntax_Util.arrow (FStar_List.rev binders_rev) c1
                in
             let uu____2619 =
               let uu____2636 = FStar_Thunk.mk norm  in
               FStar_Util.Inl uu____2636  in
             FStar_TypeChecker_NBETerm.Arrow uu____2619
         | FStar_Syntax_Syntax.Tm_refine (bv,tm) ->
             if
               ((cfg.core_cfg).FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.for_extraction
             then translate cfg bs bv.FStar_Syntax_Syntax.sort
             else
               FStar_TypeChecker_NBETerm.Refinement
                 (((fun y  -> translate cfg (y :: bs) tm)),
                   ((fun uu____2674  ->
                       let uu____2675 =
                         translate cfg bs bv.FStar_Syntax_Syntax.sort  in
                       FStar_TypeChecker_NBETerm.as_arg uu____2675)))
         | FStar_Syntax_Syntax.Tm_ascribed (t,uu____2677,uu____2678) ->
             translate cfg bs t
         | FStar_Syntax_Syntax.Tm_uvar (u,(subst,set_use_range)) ->
             let norm_uvar uu____2745 =
               let norm_subst_elt uu___1_2751 =
                 match uu___1_2751 with
                 | FStar_Syntax_Syntax.NT (x,t) ->
                     let uu____2758 =
                       let uu____2765 =
                         let uu____2768 = translate cfg bs t  in
                         readback cfg uu____2768  in
                       (x, uu____2765)  in
                     FStar_Syntax_Syntax.NT uu____2758
                 | FStar_Syntax_Syntax.NM (x,i) ->
                     let x_i =
                       FStar_Syntax_Syntax.bv_to_tm
                         (let uu___417_2778 = x  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___417_2778.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index = i;
                            FStar_Syntax_Syntax.sort =
                              (uu___417_2778.FStar_Syntax_Syntax.sort)
                          })
                        in
                     let t =
                       let uu____2780 = translate cfg bs x_i  in
                       readback cfg uu____2780  in
                     (match t.FStar_Syntax_Syntax.n with
                      | FStar_Syntax_Syntax.Tm_bvar x_j ->
                          FStar_Syntax_Syntax.NM
                            (x, (x_j.FStar_Syntax_Syntax.index))
                      | uu____2783 -> FStar_Syntax_Syntax.NT (x, t))
                 | uu____2786 ->
                     failwith "Impossible: subst invariant of uvar nodes"
                  in
               let subst1 =
                 FStar_List.map (FStar_List.map norm_subst_elt) subst  in
               let uu___427_2797 = e  in
               {
                 FStar_Syntax_Syntax.n =
                   (FStar_Syntax_Syntax.Tm_uvar (u, (subst1, set_use_range)));
                 FStar_Syntax_Syntax.pos =
                   (uu___427_2797.FStar_Syntax_Syntax.pos);
                 FStar_Syntax_Syntax.vars =
                   (uu___427_2797.FStar_Syntax_Syntax.vars)
               }  in
             let uu____2810 =
               let uu____2821 =
                 let uu____2822 = FStar_Thunk.mk norm_uvar  in
                 FStar_TypeChecker_NBETerm.UVar uu____2822  in
               (uu____2821, [])  in
             FStar_TypeChecker_NBETerm.Accu uu____2810
         | FStar_Syntax_Syntax.Tm_name x ->
             FStar_TypeChecker_NBETerm.mkAccuVar x
         | FStar_Syntax_Syntax.Tm_abs ([],uu____2836,uu____2837) ->
             failwith "Impossible: abstraction with no binders"
         | FStar_Syntax_Syntax.Tm_abs (xs,body,resc) ->
             FStar_TypeChecker_NBETerm.Lam
               (((fun ys  -> translate cfg (FStar_List.append ys bs) body)),
                 (FStar_Util.Inl (bs, xs, resc)), (FStar_List.length xs))
         | FStar_Syntax_Syntax.Tm_fvar fvar ->
             let uu____2945 = try_in_cache cfg fvar  in
             (match uu____2945 with
              | FStar_Pervasives_Native.Some t -> t
              | uu____2949 -> translate_fv cfg bs fvar)
         | FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                  (FStar_Const.Const_reify );
                FStar_Syntax_Syntax.pos = uu____2952;
                FStar_Syntax_Syntax.vars = uu____2953;_},arg::more::args)
             ->
             let uu____3013 = FStar_Syntax_Util.head_and_args e  in
             (match uu____3013 with
              | (head,uu____3031) ->
                  let head1 =
                    FStar_Syntax_Syntax.mk_Tm_app head [arg]
                      FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
                     in
                  let uu____3075 =
                    FStar_Syntax_Syntax.mk_Tm_app head1 (more :: args)
                      FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
                     in
                  translate cfg bs uu____3075)
         | FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                  (FStar_Const.Const_reflect uu____3084);
                FStar_Syntax_Syntax.pos = uu____3085;
                FStar_Syntax_Syntax.vars = uu____3086;_},arg::more::args)
             ->
             let uu____3146 = FStar_Syntax_Util.head_and_args e  in
             (match uu____3146 with
              | (head,uu____3164) ->
                  let head1 =
                    FStar_Syntax_Syntax.mk_Tm_app head [arg]
                      FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
                     in
                  let uu____3208 =
                    FStar_Syntax_Syntax.mk_Tm_app head1 (more :: args)
                      FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
                     in
                  translate cfg bs uu____3208)
         | FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                  (FStar_Const.Const_reflect uu____3217);
                FStar_Syntax_Syntax.pos = uu____3218;
                FStar_Syntax_Syntax.vars = uu____3219;_},arg::[])
             when (cfg.core_cfg).FStar_TypeChecker_Cfg.reifying ->
             let cfg1 = reifying_false cfg  in
             translate cfg1 bs (FStar_Pervasives_Native.fst arg)
         | FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                  (FStar_Const.Const_reflect uu____3264);
                FStar_Syntax_Syntax.pos = uu____3265;
                FStar_Syntax_Syntax.vars = uu____3266;_},arg::[])
             ->
             let uu____3306 =
               translate cfg bs (FStar_Pervasives_Native.fst arg)  in
             FStar_TypeChecker_NBETerm.Reflect uu____3306
         | FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                  (FStar_Const.Const_reify );
                FStar_Syntax_Syntax.pos = uu____3311;
                FStar_Syntax_Syntax.vars = uu____3312;_},arg::[])
             when
             ((cfg.core_cfg).FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.reify_
             ->
             let cfg1 = reifying_true cfg  in
             translate cfg1 bs (FStar_Pervasives_Native.fst arg)
         | FStar_Syntax_Syntax.Tm_app (head,args) ->
             (debug1
                (fun uu____3391  ->
                   let uu____3392 = FStar_Syntax_Print.term_to_string head
                      in
                   let uu____3394 = FStar_Syntax_Print.args_to_string args
                      in
                   FStar_Util.print2 "Application: %s @ %s\n" uu____3392
                     uu____3394);
              (let uu____3397 = translate cfg bs head  in
               let uu____3398 =
                 FStar_List.map
                   (fun x  ->
                      let uu____3420 =
                        translate cfg bs (FStar_Pervasives_Native.fst x)  in
                      (uu____3420, (FStar_Pervasives_Native.snd x))) args
                  in
               iapp cfg uu____3397 uu____3398))
         | FStar_Syntax_Syntax.Tm_match (scrut,branches) ->
             let make_branches uu____3472 =
               let cfg1 = zeta_false cfg  in
               let rec process_pattern bs1 p =
                 let uu____3503 =
                   match p.FStar_Syntax_Syntax.v with
                   | FStar_Syntax_Syntax.Pat_constant c ->
                       (bs1, (FStar_Syntax_Syntax.Pat_constant c))
                   | FStar_Syntax_Syntax.Pat_cons (fvar,args) ->
                       let uu____3539 =
                         FStar_List.fold_left
                           (fun uu____3580  ->
                              fun uu____3581  ->
                                match (uu____3580, uu____3581) with
                                | ((bs2,args1),(arg,b)) ->
                                    let uu____3673 = process_pattern bs2 arg
                                       in
                                    (match uu____3673 with
                                     | (bs',arg') ->
                                         (bs', ((arg', b) :: args1))))
                           (bs1, []) args
                          in
                       (match uu____3539 with
                        | (bs',args') ->
                            (bs',
                              (FStar_Syntax_Syntax.Pat_cons
                                 (fvar, (FStar_List.rev args')))))
                   | FStar_Syntax_Syntax.Pat_var bvar ->
                       let x =
                         let uu____3772 =
                           let uu____3773 =
                             translate cfg1 bs1 bvar.FStar_Syntax_Syntax.sort
                              in
                           readback cfg1 uu____3773  in
                         FStar_Syntax_Syntax.new_bv
                           FStar_Pervasives_Native.None uu____3772
                          in
                       let uu____3774 =
                         let uu____3777 =
                           FStar_TypeChecker_NBETerm.mkAccuVar x  in
                         uu____3777 :: bs1  in
                       (uu____3774, (FStar_Syntax_Syntax.Pat_var x))
                   | FStar_Syntax_Syntax.Pat_wild bvar ->
                       let x =
                         let uu____3782 =
                           let uu____3783 =
                             translate cfg1 bs1 bvar.FStar_Syntax_Syntax.sort
                              in
                           readback cfg1 uu____3783  in
                         FStar_Syntax_Syntax.new_bv
                           FStar_Pervasives_Native.None uu____3782
                          in
                       let uu____3784 =
                         let uu____3787 =
                           FStar_TypeChecker_NBETerm.mkAccuVar x  in
                         uu____3787 :: bs1  in
                       (uu____3784, (FStar_Syntax_Syntax.Pat_wild x))
                   | FStar_Syntax_Syntax.Pat_dot_term (bvar,tm) ->
                       let x =
                         let uu____3797 =
                           let uu____3798 =
                             translate cfg1 bs1 bvar.FStar_Syntax_Syntax.sort
                              in
                           readback cfg1 uu____3798  in
                         FStar_Syntax_Syntax.new_bv
                           FStar_Pervasives_Native.None uu____3797
                          in
                       let uu____3799 =
                         let uu____3800 =
                           let uu____3807 =
                             let uu____3810 = translate cfg1 bs1 tm  in
                             readback cfg1 uu____3810  in
                           (x, uu____3807)  in
                         FStar_Syntax_Syntax.Pat_dot_term uu____3800  in
                       (bs1, uu____3799)
                    in
                 match uu____3503 with
                 | (bs2,p_new) ->
                     (bs2,
                       (let uu___554_3830 = p  in
                        {
                          FStar_Syntax_Syntax.v = p_new;
                          FStar_Syntax_Syntax.p =
                            (uu___554_3830.FStar_Syntax_Syntax.p)
                        }))
                  in
               FStar_List.map
                 (fun uu____3849  ->
                    match uu____3849 with
                    | (pat,when_clause,e1) ->
                        let uu____3871 = process_pattern bs pat  in
                        (match uu____3871 with
                         | (bs',pat') ->
                             let uu____3884 =
                               let uu____3885 =
                                 let uu____3888 = translate cfg1 bs' e1  in
                                 readback cfg1 uu____3888  in
                               (pat', when_clause, uu____3885)  in
                             FStar_Syntax_Util.branch uu____3884)) branches
                in
             let scrut1 = translate cfg bs scrut  in
             (debug1
                (fun uu____3905  ->
                   let uu____3906 =
                     FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos
                      in
                   let uu____3908 = FStar_Syntax_Print.term_to_string e  in
                   FStar_Util.print2 "%s: Translating match %s\n" uu____3906
                     uu____3908);
              (let scrut2 = unlazy scrut1  in
               match scrut2 with
               | FStar_TypeChecker_NBETerm.Construct (c,us,args) ->
                   (debug1
                      (fun uu____3936  ->
                         let uu____3937 =
                           let uu____3939 =
                             FStar_All.pipe_right args
                               (FStar_List.map
                                  (fun uu____3965  ->
                                     match uu____3965 with
                                     | (x,q) ->
                                         let uu____3979 =
                                           FStar_TypeChecker_NBETerm.t_to_string
                                             x
                                            in
                                         Prims.op_Hat
                                           (if FStar_Util.is_some q
                                            then "#"
                                            else "") uu____3979))
                              in
                           FStar_All.pipe_right uu____3939
                             (FStar_String.concat "; ")
                            in
                         FStar_Util.print1 "Match args: %s\n" uu____3937);
                    (let uu____3993 = pickBranch cfg scrut2 branches  in
                     match uu____3993 with
                     | FStar_Pervasives_Native.Some (branch,args1) ->
                         let uu____4014 =
                           FStar_List.fold_left
                             (fun bs1  -> fun x  -> x :: bs1) bs args1
                            in
                         translate cfg uu____4014 branch
                     | FStar_Pervasives_Native.None  ->
                         FStar_TypeChecker_NBETerm.mkAccuMatch scrut2
                           make_branches))
               | FStar_TypeChecker_NBETerm.Constant c ->
                   (debug1
                      (fun uu____4037  ->
                         let uu____4038 =
                           FStar_TypeChecker_NBETerm.t_to_string scrut2  in
                         FStar_Util.print1 "Match constant : %s\n" uu____4038);
                    (let uu____4041 = pickBranch cfg scrut2 branches  in
                     match uu____4041 with
                     | FStar_Pervasives_Native.Some (branch,[]) ->
                         translate cfg bs branch
                     | FStar_Pervasives_Native.Some (branch,arg::[]) ->
                         translate cfg (arg :: bs) branch
                     | FStar_Pervasives_Native.None  ->
                         FStar_TypeChecker_NBETerm.mkAccuMatch scrut2
                           make_branches
                     | FStar_Pervasives_Native.Some (uu____4075,hd::tl) ->
                         failwith
                           "Impossible: Matching on constants cannot bind more than one variable"))
               | uu____4089 ->
                   FStar_TypeChecker_NBETerm.mkAccuMatch scrut2 make_branches))
         | FStar_Syntax_Syntax.Tm_meta
             (e1,FStar_Syntax_Syntax.Meta_monadic (m,t)) when
             (cfg.core_cfg).FStar_TypeChecker_Cfg.reifying ->
             translate_monadic (m, t) cfg bs e1
         | FStar_Syntax_Syntax.Tm_meta
             (e1,FStar_Syntax_Syntax.Meta_monadic_lift (m,m',t)) when
             (cfg.core_cfg).FStar_TypeChecker_Cfg.reifying ->
             translate_monadic_lift (m, m', t) cfg bs e1
         | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
             let uu____4134 =
               FStar_TypeChecker_Cfg.should_reduce_local_let cfg.core_cfg lb
                in
             if uu____4134
             then
               let uu____4137 =
                 (((cfg.core_cfg).FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.for_extraction
                    &&
                    (FStar_Syntax_Util.is_unit lb.FStar_Syntax_Syntax.lbtyp))
                   &&
                   (FStar_Syntax_Util.is_pure_or_ghost_effect
                      lb.FStar_Syntax_Syntax.lbeff)
                  in
               (if uu____4137
                then
                  let bs1 =
                    (FStar_TypeChecker_NBETerm.Constant
                       FStar_TypeChecker_NBETerm.Unit)
                    :: bs  in
                  translate cfg bs1 body
                else
                  (let bs1 =
                     let uu____4148 = translate_letbinding cfg bs lb  in
                     uu____4148 :: bs  in
                   translate cfg bs1 body))
             else
               (let def uu____4156 =
                  let uu____4157 =
                    (((cfg.core_cfg).FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.for_extraction
                       &&
                       (FStar_Syntax_Util.is_unit
                          lb.FStar_Syntax_Syntax.lbtyp))
                      &&
                      (FStar_Syntax_Util.is_pure_or_ghost_effect
                         lb.FStar_Syntax_Syntax.lbeff)
                     in
                  if uu____4157
                  then
                    FStar_TypeChecker_NBETerm.Constant
                      FStar_TypeChecker_NBETerm.Unit
                  else translate cfg bs lb.FStar_Syntax_Syntax.lbdef  in
                let typ uu____4167 =
                  translate cfg bs lb.FStar_Syntax_Syntax.lbtyp  in
                let name =
                  let uu____4169 =
                    FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                  FStar_Syntax_Syntax.freshen_bv uu____4169  in
                let bs1 =
                  (FStar_TypeChecker_NBETerm.Accu
                     ((FStar_TypeChecker_NBETerm.Var name), []))
                  :: bs  in
                let body1 uu____4188 = translate cfg bs1 body  in
                let uu____4189 =
                  let uu____4200 =
                    let uu____4201 =
                      let uu____4218 = FStar_Thunk.mk typ  in
                      let uu____4221 = FStar_Thunk.mk def  in
                      let uu____4224 = FStar_Thunk.mk body1  in
                      (name, uu____4218, uu____4221, uu____4224, lb)  in
                    FStar_TypeChecker_NBETerm.UnreducedLet uu____4201  in
                  (uu____4200, [])  in
                FStar_TypeChecker_NBETerm.Accu uu____4189)
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
                      let uu____4270 =
                        FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                      FStar_Syntax_Syntax.freshen_bv uu____4270) lbs
                  in
               let typs =
                 FStar_List.map
                   (fun lb  -> translate cfg bs lb.FStar_Syntax_Syntax.lbtyp)
                   lbs
                  in
               let rec_bs =
                 let uu____4279 =
                   FStar_List.map
                     (fun v  ->
                        FStar_TypeChecker_NBETerm.Accu
                          ((FStar_TypeChecker_NBETerm.Var v), [])) vars
                    in
                 FStar_List.append uu____4279 bs  in
               let defs =
                 FStar_List.map
                   (fun lb  ->
                      translate cfg rec_bs lb.FStar_Syntax_Syntax.lbdef) lbs
                  in
               let body1 = translate cfg rec_bs body  in
               let uu____4300 =
                 let uu____4311 =
                   let uu____4312 =
                     let uu____4329 = FStar_List.zip3 vars typs defs  in
                     (uu____4329, body1, lbs)  in
                   FStar_TypeChecker_NBETerm.UnreducedLetRec uu____4312  in
                 (uu____4311, [])  in
               FStar_TypeChecker_NBETerm.Accu uu____4300
             else
               (let uu____4360 = make_rec_env lbs bs  in
                translate cfg uu____4360 body)
         | FStar_Syntax_Syntax.Tm_meta (e1,uu____4364) -> translate cfg bs e1
         | FStar_Syntax_Syntax.Tm_quoted (qt,qi) ->
             let close t =
               let bvs =
                 FStar_List.map
                   (fun uu____4385  ->
                      FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                        FStar_Syntax_Syntax.tun) bs
                  in
               let s1 =
                 FStar_List.mapi
                   (fun i  -> fun bv  -> FStar_Syntax_Syntax.DB (i, bv)) bvs
                  in
               let s2 =
                 let uu____4398 = FStar_List.zip bvs bs  in
                 FStar_List.map
                   (fun uu____4413  ->
                      match uu____4413 with
                      | (bv,t1) ->
                          let uu____4420 =
                            let uu____4427 = readback cfg t1  in
                            (bv, uu____4427)  in
                          FStar_Syntax_Syntax.NT uu____4420) uu____4398
                  in
               let uu____4432 = FStar_Syntax_Subst.subst s1 t  in
               FStar_Syntax_Subst.subst s2 uu____4432  in
             (match qi.FStar_Syntax_Syntax.qkind with
              | FStar_Syntax_Syntax.Quote_dynamic  ->
                  let qt1 = close qt  in
                  FStar_TypeChecker_NBETerm.Quote (qt1, qi)
              | FStar_Syntax_Syntax.Quote_static  ->
                  let qi1 = FStar_Syntax_Syntax.on_antiquoted close qi  in
                  FStar_TypeChecker_NBETerm.Quote (qt, qi1))
         | FStar_Syntax_Syntax.Tm_lazy li ->
             let f uu____4441 =
               let t = FStar_Syntax_Util.unfold_lazy li  in
               debug1
                 (fun uu____4448  ->
                    let uu____4449 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.print1 ">> Unfolding Tm_lazy to %s\n"
                      uu____4449);
               translate cfg bs t  in
             let uu____4452 =
               let uu____4467 = FStar_Thunk.mk f  in
               ((FStar_Util.Inl li), uu____4467)  in
             FStar_TypeChecker_NBETerm.Lazy uu____4452)

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
            let uu____4499 =
              let uu____4506 = translate cfg bs typ  in
              let uu____4507 = fmap_opt (translate_univ cfg bs) u  in
              (uu____4506, uu____4507)  in
            FStar_TypeChecker_NBETerm.Tot uu____4499
        | FStar_Syntax_Syntax.GTotal (typ,u) ->
            let uu____4522 =
              let uu____4529 = translate cfg bs typ  in
              let uu____4530 = fmap_opt (translate_univ cfg bs) u  in
              (uu____4529, uu____4530)  in
            FStar_TypeChecker_NBETerm.GTot uu____4522
        | FStar_Syntax_Syntax.Comp ctyp ->
            let uu____4536 = translate_comp_typ cfg bs ctyp  in
            FStar_TypeChecker_NBETerm.Comp uu____4536

and (iapp :
  config ->
    FStar_TypeChecker_NBETerm.t ->
      FStar_TypeChecker_NBETerm.args -> FStar_TypeChecker_NBETerm.t)
  =
  fun cfg  ->
    fun f  ->
      fun args  ->
        match f with
        | FStar_TypeChecker_NBETerm.Lam (f1,binders,n) ->
            let m = FStar_List.length args  in
            if m < n
            then
              let arg_values_rev = map_rev FStar_Pervasives_Native.fst args
                 in
              let binders1 =
                match binders with
                | FStar_Util.Inr raw_args ->
                    let uu____4672 = FStar_List.splitAt m raw_args  in
                    (match uu____4672 with
                     | (uu____4713,raw_args1) -> FStar_Util.Inr raw_args1)
                | FStar_Util.Inl (ctx,xs,rc) ->
                    let uu____4782 = FStar_List.splitAt m xs  in
                    (match uu____4782 with
                     | (uu____4829,xs1) ->
                         let ctx1 = FStar_List.append arg_values_rev ctx  in
                         FStar_Util.Inl (ctx1, xs1, rc))
                 in
              FStar_TypeChecker_NBETerm.Lam
                (((fun l  -> f1 (FStar_List.append l arg_values_rev))),
                  binders1, (n - m))
            else
              if m = n
              then
                (let arg_values_rev =
                   map_rev FStar_Pervasives_Native.fst args  in
                 f1 arg_values_rev)
              else
                (let uu____4929 = FStar_List.splitAt n args  in
                 match uu____4929 with
                 | (args1,args') ->
                     let uu____4976 =
                       let uu____4977 =
                         map_rev FStar_Pervasives_Native.fst args1  in
                       f1 uu____4977  in
                     iapp cfg uu____4976 args')
        | FStar_TypeChecker_NBETerm.Accu (a,ts) ->
            FStar_TypeChecker_NBETerm.Accu
              (a, (FStar_List.rev_append args ts))
        | FStar_TypeChecker_NBETerm.Construct (i,us,ts) ->
            let rec aux args1 us1 ts1 =
              match args1 with
              | (FStar_TypeChecker_NBETerm.Univ u,uu____5096)::args2 ->
                  aux args2 (u :: us1) ts1
              | a::args2 -> aux args2 us1 (a :: ts1)
              | [] -> (us1, ts1)  in
            let uu____5140 = aux args us ts  in
            (match uu____5140 with
             | (us',ts') -> FStar_TypeChecker_NBETerm.Construct (i, us', ts'))
        | FStar_TypeChecker_NBETerm.FV (i,us,ts) ->
            let rec aux args1 us1 ts1 =
              match args1 with
              | (FStar_TypeChecker_NBETerm.Univ u,uu____5267)::args2 ->
                  aux args2 (u :: us1) ts1
              | a::args2 -> aux args2 us1 (a :: ts1)
              | [] -> (us1, ts1)  in
            let uu____5311 = aux args us ts  in
            (match uu____5311 with
             | (us',ts') -> FStar_TypeChecker_NBETerm.FV (i, us', ts'))
        | FStar_TypeChecker_NBETerm.TopLevelLet (lb,arity,args_rev) ->
            let args_rev1 = FStar_List.rev_append args args_rev  in
            let n_args_rev = FStar_List.length args_rev1  in
            let n_univs = FStar_List.length lb.FStar_Syntax_Syntax.lbunivs
               in
            (debug cfg
               (fun uu____5389  ->
                  let uu____5390 =
                    FStar_Syntax_Print.lbname_to_string
                      lb.FStar_Syntax_Syntax.lbname
                     in
                  let uu____5392 = FStar_Util.string_of_int arity  in
                  let uu____5394 = FStar_Util.string_of_int n_args_rev  in
                  FStar_Util.print3
                    "Reached iapp for %s with arity %s and n_args = %s\n"
                    uu____5390 uu____5392 uu____5394);
             if n_args_rev >= arity
             then
               (let uu____5398 =
                  let uu____5411 =
                    let uu____5412 =
                      FStar_Syntax_Util.unascribe
                        lb.FStar_Syntax_Syntax.lbdef
                       in
                    uu____5412.FStar_Syntax_Syntax.n  in
                  match uu____5411 with
                  | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____5429) ->
                      (bs, body)
                  | uu____5462 -> ([], (lb.FStar_Syntax_Syntax.lbdef))  in
                match uu____5398 with
                | (bs,body) ->
                    if (n_univs + (FStar_List.length bs)) = arity
                    then
                      let uu____5503 =
                        FStar_Util.first_N (n_args_rev - arity) args_rev1  in
                      (match uu____5503 with
                       | (extra,args_rev2) ->
                           (debug cfg
                              (fun uu____5555  ->
                                 let uu____5556 =
                                   FStar_Syntax_Print.lbname_to_string
                                     lb.FStar_Syntax_Syntax.lbname
                                    in
                                 let uu____5558 =
                                   FStar_Syntax_Print.term_to_string body  in
                                 let uu____5560 =
                                   let uu____5562 =
                                     FStar_List.map
                                       (fun uu____5574  ->
                                          match uu____5574 with
                                          | (x,uu____5581) ->
                                              FStar_TypeChecker_NBETerm.t_to_string
                                                x) args_rev2
                                      in
                                   FStar_All.pipe_right uu____5562
                                     (FStar_String.concat ", ")
                                    in
                                 FStar_Util.print3
                                   "Reducing body of %s = %s,\n\twith args = %s\n"
                                   uu____5556 uu____5558 uu____5560);
                            (let t =
                               let uu____5589 =
                                 FStar_List.map FStar_Pervasives_Native.fst
                                   args_rev2
                                  in
                               translate cfg uu____5589 body  in
                             match extra with
                             | [] -> t
                             | uu____5600 ->
                                 iapp cfg t (FStar_List.rev extra))))
                    else
                      (let uu____5613 =
                         FStar_Util.first_N (n_args_rev - n_univs) args_rev1
                          in
                       match uu____5613 with
                       | (extra,univs) ->
                           let uu____5660 =
                             let uu____5661 =
                               FStar_List.map FStar_Pervasives_Native.fst
                                 univs
                                in
                             translate cfg uu____5661
                               lb.FStar_Syntax_Syntax.lbdef
                              in
                           iapp cfg uu____5660 (FStar_List.rev extra)))
             else
               FStar_TypeChecker_NBETerm.TopLevelLet (lb, arity, args_rev1))
        | FStar_TypeChecker_NBETerm.TopLevelRec
            (lb,arity,decreases_list,args') ->
            let args1 = FStar_List.append args' args  in
            if (FStar_List.length args1) >= arity
            then
              let uu____5721 =
                should_reduce_recursive_definition args1 decreases_list  in
              (match uu____5721 with
               | (should_reduce,uu____5730,uu____5731) ->
                   if Prims.op_Negation should_reduce
                   then
                     let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname
                        in
                     (debug cfg
                        (fun uu____5739  ->
                           let uu____5740 =
                             FStar_Syntax_Print.fv_to_string fv  in
                           FStar_Util.print1
                             "Decided to not unfold recursive definition %s\n"
                             uu____5740);
                      iapp cfg (FStar_TypeChecker_NBETerm.FV (fv, [], []))
                        args1)
                   else
                     (debug cfg
                        (fun uu____5760  ->
                           let uu____5761 =
                             let uu____5763 =
                               FStar_Util.right lb.FStar_Syntax_Syntax.lbname
                                in
                             FStar_Syntax_Print.fv_to_string uu____5763  in
                           FStar_Util.print1
                             "Yes, Decided to unfold recursive definition %s\n"
                             uu____5761);
                      (let uu____5765 =
                         FStar_Util.first_N
                           (FStar_List.length lb.FStar_Syntax_Syntax.lbunivs)
                           args1
                          in
                       match uu____5765 with
                       | (univs,rest) ->
                           let uu____5812 =
                             let uu____5813 =
                               let uu____5816 =
                                 FStar_List.map FStar_Pervasives_Native.fst
                                   univs
                                  in
                               FStar_List.rev uu____5816  in
                             translate cfg uu____5813
                               lb.FStar_Syntax_Syntax.lbdef
                              in
                           iapp cfg uu____5812 rest)))
            else
              FStar_TypeChecker_NBETerm.TopLevelRec
                (lb, arity, decreases_list, args1)
        | FStar_TypeChecker_NBETerm.LocalLetRec
            (i,lb,mutual_lbs,local_env,acc_args,remaining_arity,decreases_list)
            ->
            if remaining_arity = Prims.int_zero
            then
              FStar_TypeChecker_NBETerm.LocalLetRec
                (i, lb, mutual_lbs, local_env,
                  (FStar_List.append acc_args args), remaining_arity,
                  decreases_list)
            else
              (let n_args = FStar_List.length args  in
               if n_args < remaining_arity
               then
                 FStar_TypeChecker_NBETerm.LocalLetRec
                   (i, lb, mutual_lbs, local_env,
                     (FStar_List.append acc_args args),
                     (remaining_arity - n_args), decreases_list)
               else
                 (let args1 = FStar_List.append acc_args args  in
                  let uu____5934 =
                    should_reduce_recursive_definition args1 decreases_list
                     in
                  match uu____5934 with
                  | (should_reduce,uu____5943,uu____5944) ->
                      if Prims.op_Negation should_reduce
                      then
                        FStar_TypeChecker_NBETerm.LocalLetRec
                          (i, lb, mutual_lbs, local_env, args1,
                            Prims.int_zero, decreases_list)
                      else
                        (let env = make_rec_env mutual_lbs local_env  in
                         debug cfg
                           (fun uu____5973  ->
                              (let uu____5975 =
                                 let uu____5977 =
                                   FStar_List.map
                                     FStar_TypeChecker_NBETerm.t_to_string
                                     env
                                    in
                                 FStar_String.concat ",\n\t " uu____5977  in
                               FStar_Util.print1
                                 "LocalLetRec Env = {\n\t%s\n}\n" uu____5975);
                              (let uu____5984 =
                                 let uu____5986 =
                                   FStar_List.map
                                     (fun uu____5998  ->
                                        match uu____5998 with
                                        | (t,uu____6005) ->
                                            FStar_TypeChecker_NBETerm.t_to_string
                                              t) args1
                                    in
                                 FStar_String.concat ",\n\t " uu____5986  in
                               FStar_Util.print1
                                 "LocalLetRec Args = {\n\t%s\n}\n" uu____5984));
                         (let uu____6008 =
                            translate cfg env lb.FStar_Syntax_Syntax.lbdef
                             in
                          iapp cfg uu____6008 args1))))
        | uu____6009 ->
            let uu____6010 =
              let uu____6012 = FStar_TypeChecker_NBETerm.t_to_string f  in
              Prims.op_Hat "NBE ill-typed application: " uu____6012  in
            failwith uu____6010

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
          let uu____6029 = FStar_TypeChecker_Cfg.cfg_env cfg.core_cfg  in
          let uu____6030 = FStar_Syntax_Syntax.lid_of_fv fvar  in
          FStar_TypeChecker_Env.lookup_qname uu____6029 uu____6030  in
        let uu____6031 = (is_constr qninfo) || (is_constr_fv fvar)  in
        if uu____6031
        then FStar_TypeChecker_NBETerm.mkConstruct fvar [] []
        else
          (let uu____6040 =
             FStar_TypeChecker_Normalize.should_unfold cfg.core_cfg
               (fun uu____6042  ->
                  (cfg.core_cfg).FStar_TypeChecker_Cfg.reifying) fvar qninfo
              in
           match uu____6040 with
           | FStar_TypeChecker_Normalize.Should_unfold_fully  ->
               failwith "Not yet handled"
           | FStar_TypeChecker_Normalize.Should_unfold_no  ->
               (debug1
                  (fun uu____6049  ->
                     let uu____6050 = FStar_Syntax_Print.fv_to_string fvar
                        in
                     FStar_Util.print1 "(1) Decided to not unfold %s\n"
                       uu____6050);
                (let uu____6053 =
                   FStar_TypeChecker_Cfg.find_prim_step cfg.core_cfg fvar  in
                 match uu____6053 with
                 | FStar_Pervasives_Native.Some prim_step when
                     prim_step.FStar_TypeChecker_Cfg.strong_reduction_ok ->
                     let arity =
                       prim_step.FStar_TypeChecker_Cfg.arity +
                         prim_step.FStar_TypeChecker_Cfg.univ_arity
                        in
                     (debug1
                        (fun uu____6064  ->
                           let uu____6065 =
                             FStar_Syntax_Print.fv_to_string fvar  in
                           FStar_Util.print1 "Found a primop %s\n" uu____6065);
                      (let uu____6068 =
                         let uu____6101 =
                           let f uu____6134 =
                             let uu____6136 =
                               FStar_Syntax_Syntax.new_bv
                                 FStar_Pervasives_Native.None
                                 FStar_Syntax_Syntax.t_unit
                                in
                             (uu____6136, FStar_Pervasives_Native.None)  in
                           let uu____6139 =
                             let uu____6150 = FStar_Common.tabulate arity f
                                in
                             ([], uu____6150, FStar_Pervasives_Native.None)
                              in
                           FStar_Util.Inl uu____6139  in
                         ((fun args_rev  ->
                             let args' =
                               map_rev FStar_TypeChecker_NBETerm.as_arg
                                 args_rev
                                in
                             let callbacks =
                               {
                                 FStar_TypeChecker_NBETerm.iapp = (iapp cfg);
                                 FStar_TypeChecker_NBETerm.translate =
                                   (translate cfg bs)
                               }  in
                             let uu____6224 =
                               prim_step.FStar_TypeChecker_Cfg.interpretation_nbe
                                 callbacks args'
                                in
                             match uu____6224 with
                             | FStar_Pervasives_Native.Some x ->
                                 (debug1
                                    (fun uu____6235  ->
                                       let uu____6236 =
                                         FStar_Syntax_Print.fv_to_string fvar
                                          in
                                       let uu____6238 =
                                         FStar_TypeChecker_NBETerm.t_to_string
                                           x
                                          in
                                       FStar_Util.print2
                                         "Primitive operator %s returned %s\n"
                                         uu____6236 uu____6238);
                                  x)
                             | FStar_Pervasives_Native.None  ->
                                 (debug1
                                    (fun uu____6246  ->
                                       let uu____6247 =
                                         FStar_Syntax_Print.fv_to_string fvar
                                          in
                                       FStar_Util.print1
                                         "Primitive operator %s failed\n"
                                         uu____6247);
                                  (let uu____6250 =
                                     FStar_TypeChecker_NBETerm.mkFV fvar []
                                       []
                                      in
                                   iapp cfg uu____6250 args'))), uu____6101,
                           arity)
                          in
                       FStar_TypeChecker_NBETerm.Lam uu____6068))
                 | FStar_Pervasives_Native.Some uu____6255 ->
                     (debug1
                        (fun uu____6261  ->
                           let uu____6262 =
                             FStar_Syntax_Print.fv_to_string fvar  in
                           FStar_Util.print1 "(2) Decided to not unfold %s\n"
                             uu____6262);
                      FStar_TypeChecker_NBETerm.mkFV fvar [] [])
                 | uu____6269 ->
                     (debug1
                        (fun uu____6277  ->
                           let uu____6278 =
                             FStar_Syntax_Print.fv_to_string fvar  in
                           FStar_Util.print1 "(3) Decided to not unfold %s\n"
                             uu____6278);
                      FStar_TypeChecker_NBETerm.mkFV fvar [] [])))
           | FStar_TypeChecker_Normalize.Should_unfold_reify  ->
               let t =
                 let is_qninfo_visible =
                   let uu____6288 =
                     FStar_TypeChecker_Env.lookup_definition_qninfo
                       (cfg.core_cfg).FStar_TypeChecker_Cfg.delta_level
                       (fvar.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                       qninfo
                      in
                   FStar_Option.isSome uu____6288  in
                 if is_qninfo_visible
                 then
                   match qninfo with
                   | FStar_Pervasives_Native.Some
                       (FStar_Util.Inr
                        ({
                           FStar_Syntax_Syntax.sigel =
                             FStar_Syntax_Syntax.Sig_let ((is_rec,lbs),names);
                           FStar_Syntax_Syntax.sigrng = uu____6303;
                           FStar_Syntax_Syntax.sigquals = uu____6304;
                           FStar_Syntax_Syntax.sigmeta = uu____6305;
                           FStar_Syntax_Syntax.sigattrs = uu____6306;
                           FStar_Syntax_Syntax.sigopts = uu____6307;_},_us_opt),_rng)
                       ->
                       (debug1
                          (fun uu____6377  ->
                             let uu____6378 =
                               FStar_Syntax_Print.fv_to_string fvar  in
                             FStar_Util.print1 "(1) Decided to unfold %s\n"
                               uu____6378);
                        (let lbm = find_let lbs fvar  in
                         match lbm with
                         | FStar_Pervasives_Native.Some lb ->
                             if
                               is_rec &&
                                 ((cfg.core_cfg).FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta
                             then
                               let uu____6386 = let_rec_arity lb  in
                               (match uu____6386 with
                                | (ar,lst) ->
                                    FStar_TypeChecker_NBETerm.TopLevelRec
                                      (lb, ar, lst, []))
                             else translate_letbinding cfg bs lb
                         | FStar_Pervasives_Native.None  ->
                             failwith "Could not find let binding"))
                   | uu____6422 ->
                       (debug1
                          (fun uu____6428  ->
                             let uu____6429 =
                               FStar_Syntax_Print.fv_to_string fvar  in
                             FStar_Util.print1
                               "(1) qninfo is None for (%s)\n" uu____6429);
                        FStar_TypeChecker_NBETerm.mkFV fvar [] [])
                 else
                   (debug1
                      (fun uu____6443  ->
                         let uu____6444 =
                           FStar_Syntax_Print.fv_to_string fvar  in
                         FStar_Util.print1
                           "(1) qninfo is not visible at this level (%s)\n"
                           uu____6444);
                    FStar_TypeChecker_NBETerm.mkFV fvar [] [])
                  in
               (cache_add cfg fvar t; t)
           | FStar_TypeChecker_Normalize.Should_unfold_yes  ->
               let t =
                 let is_qninfo_visible =
                   let uu____6455 =
                     FStar_TypeChecker_Env.lookup_definition_qninfo
                       (cfg.core_cfg).FStar_TypeChecker_Cfg.delta_level
                       (fvar.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                       qninfo
                      in
                   FStar_Option.isSome uu____6455  in
                 if is_qninfo_visible
                 then
                   match qninfo with
                   | FStar_Pervasives_Native.Some
                       (FStar_Util.Inr
                        ({
                           FStar_Syntax_Syntax.sigel =
                             FStar_Syntax_Syntax.Sig_let ((is_rec,lbs),names);
                           FStar_Syntax_Syntax.sigrng = uu____6470;
                           FStar_Syntax_Syntax.sigquals = uu____6471;
                           FStar_Syntax_Syntax.sigmeta = uu____6472;
                           FStar_Syntax_Syntax.sigattrs = uu____6473;
                           FStar_Syntax_Syntax.sigopts = uu____6474;_},_us_opt),_rng)
                       ->
                       (debug1
                          (fun uu____6544  ->
                             let uu____6545 =
                               FStar_Syntax_Print.fv_to_string fvar  in
                             FStar_Util.print1 "(1) Decided to unfold %s\n"
                               uu____6545);
                        (let lbm = find_let lbs fvar  in
                         match lbm with
                         | FStar_Pervasives_Native.Some lb ->
                             if
                               is_rec &&
                                 ((cfg.core_cfg).FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta
                             then
                               let uu____6553 = let_rec_arity lb  in
                               (match uu____6553 with
                                | (ar,lst) ->
                                    FStar_TypeChecker_NBETerm.TopLevelRec
                                      (lb, ar, lst, []))
                             else translate_letbinding cfg bs lb
                         | FStar_Pervasives_Native.None  ->
                             failwith "Could not find let binding"))
                   | uu____6589 ->
                       (debug1
                          (fun uu____6595  ->
                             let uu____6596 =
                               FStar_Syntax_Print.fv_to_string fvar  in
                             FStar_Util.print1
                               "(1) qninfo is None for (%s)\n" uu____6596);
                        FStar_TypeChecker_NBETerm.mkFV fvar [] [])
                 else
                   (debug1
                      (fun uu____6610  ->
                         let uu____6611 =
                           FStar_Syntax_Print.fv_to_string fvar  in
                         FStar_Util.print1
                           "(1) qninfo is not visible at this level (%s)\n"
                           uu____6611);
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
        let uu____6635 =
          FStar_Syntax_Util.arrow_formals lb.FStar_Syntax_Syntax.lbtyp  in
        match uu____6635 with
        | (formals,uu____6643) ->
            let arity = (FStar_List.length us) + (FStar_List.length formals)
               in
            if arity = Prims.int_zero
            then translate cfg bs lb.FStar_Syntax_Syntax.lbdef
            else
              (let uu____6661 =
                 FStar_Util.is_right lb.FStar_Syntax_Syntax.lbname  in
               if uu____6661
               then
                 (debug1
                    (fun uu____6671  ->
                       let uu____6672 =
                         FStar_Syntax_Print.lbname_to_string
                           lb.FStar_Syntax_Syntax.lbname
                          in
                       let uu____6674 = FStar_Util.string_of_int arity  in
                       FStar_Util.print2
                         "Making TopLevelLet for %s with arity %s\n"
                         uu____6672 uu____6674);
                  FStar_TypeChecker_NBETerm.TopLevelLet (lb, arity, []))
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
          let uu____6699 = let_rec_arity b  in
          match uu____6699 with
          | (ar,ar_lst) ->
              FStar_TypeChecker_NBETerm.LocalLetRec
                (i, b, bs, env, [], ar, ar_lst)

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
        let uu____6769 = FStar_BigInt.big_int_of_string s  in
        FStar_TypeChecker_NBETerm.Int uu____6769
    | FStar_Const.Const_string (s,r) ->
        FStar_TypeChecker_NBETerm.String (s, r)
    | FStar_Const.Const_char c1 -> FStar_TypeChecker_NBETerm.Char c1
    | FStar_Const.Const_range r -> FStar_TypeChecker_NBETerm.Range r
    | uu____6778 -> FStar_TypeChecker_NBETerm.SConst c

and (readback_comp :
  config -> FStar_TypeChecker_NBETerm.comp -> FStar_Syntax_Syntax.comp) =
  fun cfg  ->
    fun c  ->
      let c' =
        match c with
        | FStar_TypeChecker_NBETerm.Tot (typ,u) ->
            let uu____6788 =
              let uu____6797 = readback cfg typ  in (uu____6797, u)  in
            FStar_Syntax_Syntax.Total uu____6788
        | FStar_TypeChecker_NBETerm.GTot (typ,u) ->
            let uu____6810 =
              let uu____6819 = readback cfg typ  in (uu____6819, u)  in
            FStar_Syntax_Syntax.GTotal uu____6810
        | FStar_TypeChecker_NBETerm.Comp ctyp ->
            let uu____6827 = readback_comp_typ cfg ctyp  in
            FStar_Syntax_Syntax.Comp uu____6827
         in
      FStar_Syntax_Syntax.mk c' FStar_Pervasives_Native.None
        FStar_Range.dummyRange

and (translate_comp_typ :
  config ->
    FStar_TypeChecker_NBETerm.t Prims.list ->
      FStar_Syntax_Syntax.comp_typ -> FStar_TypeChecker_NBETerm.comp_typ)
  =
  fun cfg  ->
    fun bs  ->
      fun c  ->
        let uu____6833 = c  in
        match uu____6833 with
        | { FStar_Syntax_Syntax.comp_univs = comp_univs;
            FStar_Syntax_Syntax.effect_name = effect_name;
            FStar_Syntax_Syntax.result_typ = result_typ;
            FStar_Syntax_Syntax.effect_args = effect_args;
            FStar_Syntax_Syntax.flags = flags;_} ->
            let uu____6853 =
              FStar_List.map (translate_univ cfg bs) comp_univs  in
            let uu____6854 = translate cfg bs result_typ  in
            let uu____6855 =
              FStar_List.map
                (fun x  ->
                   let uu____6883 =
                     translate cfg bs (FStar_Pervasives_Native.fst x)  in
                   (uu____6883, (FStar_Pervasives_Native.snd x))) effect_args
               in
            let uu____6890 = FStar_List.map (translate_flag cfg bs) flags  in
            {
              FStar_TypeChecker_NBETerm.comp_univs = uu____6853;
              FStar_TypeChecker_NBETerm.effect_name = effect_name;
              FStar_TypeChecker_NBETerm.result_typ = uu____6854;
              FStar_TypeChecker_NBETerm.effect_args = uu____6855;
              FStar_TypeChecker_NBETerm.flags = uu____6890
            }

and (readback_comp_typ :
  config ->
    FStar_TypeChecker_NBETerm.comp_typ -> FStar_Syntax_Syntax.comp_typ)
  =
  fun cfg  ->
    fun c  ->
      let uu____6895 = readback cfg c.FStar_TypeChecker_NBETerm.result_typ
         in
      let uu____6898 =
        FStar_List.map
          (fun x  ->
             let uu____6924 = readback cfg (FStar_Pervasives_Native.fst x)
                in
             (uu____6924, (FStar_Pervasives_Native.snd x)))
          c.FStar_TypeChecker_NBETerm.effect_args
         in
      let uu____6925 =
        FStar_List.map (readback_flag cfg) c.FStar_TypeChecker_NBETerm.flags
         in
      {
        FStar_Syntax_Syntax.comp_univs =
          (c.FStar_TypeChecker_NBETerm.comp_univs);
        FStar_Syntax_Syntax.effect_name =
          (c.FStar_TypeChecker_NBETerm.effect_name);
        FStar_Syntax_Syntax.result_typ = uu____6895;
        FStar_Syntax_Syntax.effect_args = uu____6898;
        FStar_Syntax_Syntax.flags = uu____6925
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
        let uu____6933 = c  in
        match uu____6933 with
        | { FStar_Syntax_Syntax.residual_effect = residual_effect;
            FStar_Syntax_Syntax.residual_typ = residual_typ;
            FStar_Syntax_Syntax.residual_flags = residual_flags;_} ->
            let uu____6943 =
              if
                ((cfg.core_cfg).FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.for_extraction
              then FStar_Pervasives_Native.None
              else FStar_Util.map_opt residual_typ (translate cfg bs)  in
            let uu____6953 =
              FStar_List.map (translate_flag cfg bs) residual_flags  in
            {
              FStar_TypeChecker_NBETerm.residual_effect = residual_effect;
              FStar_TypeChecker_NBETerm.residual_typ = uu____6943;
              FStar_TypeChecker_NBETerm.residual_flags = uu____6953
            }

and (readback_residual_comp :
  config ->
    FStar_TypeChecker_NBETerm.residual_comp ->
      FStar_Syntax_Syntax.residual_comp)
  =
  fun cfg  ->
    fun c  ->
      let uu____6958 =
        FStar_Util.map_opt c.FStar_TypeChecker_NBETerm.residual_typ
          (fun x  ->
             debug cfg
               (fun uu____6969  ->
                  let uu____6970 = FStar_TypeChecker_NBETerm.t_to_string x
                     in
                  FStar_Util.print1 "Reading back residualtype %s\n"
                    uu____6970);
             readback cfg x)
         in
      let uu____6973 =
        FStar_List.map (readback_flag cfg)
          c.FStar_TypeChecker_NBETerm.residual_flags
         in
      {
        FStar_Syntax_Syntax.residual_effect =
          (c.FStar_TypeChecker_NBETerm.residual_effect);
        FStar_Syntax_Syntax.residual_typ = uu____6958;
        FStar_Syntax_Syntax.residual_flags = uu____6973
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
            let uu____6984 = translate cfg bs tm  in
            FStar_TypeChecker_NBETerm.DECREASES uu____6984

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
          let uu____6988 = readback cfg t  in
          FStar_Syntax_Syntax.DECREASES uu____6988

and (translate_monadic :
  (FStar_Syntax_Syntax.monad_name * FStar_Syntax_Syntax.term'
    FStar_Syntax_Syntax.syntax) ->
    config ->
      FStar_TypeChecker_NBETerm.t Prims.list ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
          FStar_TypeChecker_NBETerm.t)
  =
  fun uu____6991  ->
    fun cfg  ->
      fun bs  ->
        fun e  ->
          match uu____6991 with
          | (m,ty) ->
              let e1 = FStar_Syntax_Util.unascribe e  in
              (match e1.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                   let uu____7029 =
                     let uu____7038 =
                       FStar_TypeChecker_Env.norm_eff_name
                         (cfg.core_cfg).FStar_TypeChecker_Cfg.tcenv m
                        in
                     FStar_TypeChecker_Env.effect_decl_opt
                       (cfg.core_cfg).FStar_TypeChecker_Cfg.tcenv uu____7038
                      in
                   (match uu____7029 with
                    | FStar_Pervasives_Native.None  ->
                        let uu____7045 =
                          let uu____7047 = FStar_Ident.string_of_lid m  in
                          FStar_Util.format1
                            "Effect declaration not found: %s" uu____7047
                           in
                        failwith uu____7045
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
                          let uu____7069 =
                            let uu____7076 =
                              let uu____7077 =
                                let uu____7096 =
                                  let uu____7105 =
                                    let uu____7112 =
                                      FStar_Util.left
                                        lb.FStar_Syntax_Syntax.lbname
                                       in
                                    (uu____7112,
                                      FStar_Pervasives_Native.None)
                                     in
                                  [uu____7105]  in
                                (uu____7096, body,
                                  (FStar_Pervasives_Native.Some body_rc))
                                 in
                              FStar_Syntax_Syntax.Tm_abs uu____7077  in
                            FStar_Syntax_Syntax.mk uu____7076  in
                          uu____7069 FStar_Pervasives_Native.None
                            body.FStar_Syntax_Syntax.pos
                           in
                        let maybe_range_arg =
                          let uu____7146 =
                            FStar_Util.for_some
                              (FStar_Syntax_Util.attr_eq
                                 FStar_Syntax_Util.dm4f_bind_range_attr)
                              ed.FStar_Syntax_Syntax.eff_attrs
                             in
                          if uu____7146
                          then
                            let uu____7155 =
                              let uu____7160 =
                                let uu____7161 =
                                  FStar_TypeChecker_Cfg.embed_simple
                                    FStar_Syntax_Embeddings.e_range
                                    lb.FStar_Syntax_Syntax.lbpos
                                    lb.FStar_Syntax_Syntax.lbpos
                                   in
                                translate cfg [] uu____7161  in
                              (uu____7160, FStar_Pervasives_Native.None)  in
                            let uu____7162 =
                              let uu____7169 =
                                let uu____7174 =
                                  let uu____7175 =
                                    FStar_TypeChecker_Cfg.embed_simple
                                      FStar_Syntax_Embeddings.e_range
                                      body.FStar_Syntax_Syntax.pos
                                      body.FStar_Syntax_Syntax.pos
                                     in
                                  translate cfg [] uu____7175  in
                                (uu____7174, FStar_Pervasives_Native.None)
                                 in
                              [uu____7169]  in
                            uu____7155 :: uu____7162
                          else []  in
                        let t =
                          let uu____7195 =
                            let uu____7196 =
                              let uu____7197 =
                                let uu____7198 =
                                  let uu____7199 =
                                    let uu____7206 =
                                      FStar_All.pipe_right ed
                                        FStar_Syntax_Util.get_bind_repr
                                       in
                                    FStar_All.pipe_right uu____7206
                                      FStar_Util.must
                                     in
                                  FStar_All.pipe_right uu____7199
                                    FStar_Pervasives_Native.snd
                                   in
                                FStar_Syntax_Util.un_uinst uu____7198  in
                              translate cfg' [] uu____7197  in
                            iapp cfg uu____7196
                              [((FStar_TypeChecker_NBETerm.Univ
                                   FStar_Syntax_Syntax.U_unknown),
                                 FStar_Pervasives_Native.None);
                              ((FStar_TypeChecker_NBETerm.Univ
                                  FStar_Syntax_Syntax.U_unknown),
                                FStar_Pervasives_Native.None)]
                             in
                          let uu____7239 =
                            let uu____7240 =
                              let uu____7247 =
                                let uu____7252 =
                                  translate cfg' bs
                                    lb.FStar_Syntax_Syntax.lbtyp
                                   in
                                (uu____7252, FStar_Pervasives_Native.None)
                                 in
                              let uu____7253 =
                                let uu____7260 =
                                  let uu____7265 = translate cfg' bs ty  in
                                  (uu____7265, FStar_Pervasives_Native.None)
                                   in
                                [uu____7260]  in
                              uu____7247 :: uu____7253  in
                            let uu____7278 =
                              let uu____7285 =
                                let uu____7292 =
                                  let uu____7299 =
                                    let uu____7304 =
                                      translate cfg bs
                                        lb.FStar_Syntax_Syntax.lbdef
                                       in
                                    (uu____7304,
                                      FStar_Pervasives_Native.None)
                                     in
                                  let uu____7305 =
                                    let uu____7312 =
                                      let uu____7319 =
                                        let uu____7324 =
                                          translate cfg bs body_lam  in
                                        (uu____7324,
                                          FStar_Pervasives_Native.None)
                                         in
                                      [uu____7319]  in
                                    (FStar_TypeChecker_NBETerm.Unknown,
                                      FStar_Pervasives_Native.None) ::
                                      uu____7312
                                     in
                                  uu____7299 :: uu____7305  in
                                (FStar_TypeChecker_NBETerm.Unknown,
                                  FStar_Pervasives_Native.None) :: uu____7292
                                 in
                              FStar_List.append maybe_range_arg uu____7285
                               in
                            FStar_List.append uu____7240 uu____7278  in
                          iapp cfg uu____7195 uu____7239  in
                        (debug cfg
                           (fun uu____7356  ->
                              let uu____7357 =
                                FStar_TypeChecker_NBETerm.t_to_string t  in
                              FStar_Util.print1 "translate_monadic: %s\n"
                                uu____7357);
                         t))
               | FStar_Syntax_Syntax.Tm_app
                   ({
                      FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                        (FStar_Const.Const_reflect uu____7360);
                      FStar_Syntax_Syntax.pos = uu____7361;
                      FStar_Syntax_Syntax.vars = uu____7362;_},(e2,uu____7364)::[])
                   ->
                   let uu____7403 = reifying_false cfg  in
                   translate uu____7403 bs e2
               | FStar_Syntax_Syntax.Tm_app (head,args) ->
                   (debug cfg
                      (fun uu____7434  ->
                         let uu____7435 =
                           FStar_Syntax_Print.term_to_string head  in
                         let uu____7437 =
                           FStar_Syntax_Print.args_to_string args  in
                         FStar_Util.print2
                           "translate_monadic app (%s) @ (%s)\n" uu____7435
                           uu____7437);
                    (let fallback1 uu____7445 = translate cfg bs e1  in
                     let fallback2 uu____7451 =
                       let uu____7452 = reifying_false cfg  in
                       let uu____7453 =
                         FStar_Syntax_Syntax.mk
                           (FStar_Syntax_Syntax.Tm_meta
                              (e1,
                                (FStar_Syntax_Syntax.Meta_monadic (m, ty))))
                           FStar_Pervasives_Native.None
                           e1.FStar_Syntax_Syntax.pos
                          in
                       translate uu____7452 bs uu____7453  in
                     let uu____7458 =
                       let uu____7459 = FStar_Syntax_Util.un_uinst head  in
                       uu____7459.FStar_Syntax_Syntax.n  in
                     match uu____7458 with
                     | FStar_Syntax_Syntax.Tm_fvar fv ->
                         let lid = FStar_Syntax_Syntax.lid_of_fv fv  in
                         let qninfo =
                           FStar_TypeChecker_Env.lookup_qname
                             (cfg.core_cfg).FStar_TypeChecker_Cfg.tcenv lid
                            in
                         let uu____7465 =
                           let uu____7467 =
                             FStar_TypeChecker_Env.is_action
                               (cfg.core_cfg).FStar_TypeChecker_Cfg.tcenv lid
                              in
                           Prims.op_Negation uu____7467  in
                         if uu____7465
                         then fallback1 ()
                         else
                           (let uu____7472 =
                              let uu____7474 =
                                FStar_TypeChecker_Env.lookup_definition_qninfo
                                  (cfg.core_cfg).FStar_TypeChecker_Cfg.delta_level
                                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                  qninfo
                                 in
                              FStar_Option.isNone uu____7474  in
                            if uu____7472
                            then fallback2 ()
                            else
                              (let e2 =
                                 let uu____7491 =
                                   let uu____7496 =
                                     FStar_Syntax_Util.mk_reify head  in
                                   FStar_Syntax_Syntax.mk_Tm_app uu____7496
                                     args
                                    in
                                 uu____7491 FStar_Pervasives_Native.None
                                   e1.FStar_Syntax_Syntax.pos
                                  in
                               let uu____7497 = reifying_false cfg  in
                               translate uu____7497 bs e2))
                     | uu____7498 -> fallback1 ()))
               | FStar_Syntax_Syntax.Tm_match (sc,branches) ->
                   let branches1 =
                     FStar_All.pipe_right branches
                       (FStar_List.map
                          (fun uu____7619  ->
                             match uu____7619 with
                             | (pat,wopt,tm) ->
                                 let uu____7667 =
                                   FStar_Syntax_Util.mk_reify tm  in
                                 (pat, wopt, uu____7667)))
                      in
                   let tm =
                     FStar_Syntax_Syntax.mk
                       (FStar_Syntax_Syntax.Tm_match (sc, branches1))
                       FStar_Pervasives_Native.None
                       e1.FStar_Syntax_Syntax.pos
                      in
                   let uu____7699 = reifying_false cfg  in
                   translate uu____7699 bs tm
               | FStar_Syntax_Syntax.Tm_meta
                   (t,FStar_Syntax_Syntax.Meta_monadic uu____7701) ->
                   translate_monadic (m, ty) cfg bs e1
               | FStar_Syntax_Syntax.Tm_meta
                   (t,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,ty'))
                   -> translate_monadic_lift (msrc, mtgt, ty') cfg bs e1
               | uu____7728 ->
                   let uu____7729 =
                     let uu____7731 = FStar_Syntax_Print.tag_of_term e1  in
                     FStar_Util.format1
                       "Unexpected case in translate_monadic: %s" uu____7731
                      in
                   failwith uu____7729)

and (translate_monadic_lift :
  (FStar_Syntax_Syntax.monad_name * FStar_Syntax_Syntax.monad_name *
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax) ->
    config ->
      FStar_TypeChecker_NBETerm.t Prims.list ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
          FStar_TypeChecker_NBETerm.t)
  =
  fun uu____7734  ->
    fun cfg  ->
      fun bs  ->
        fun e  ->
          match uu____7734 with
          | (msrc,mtgt,ty) ->
              let e1 = FStar_Syntax_Util.unascribe e  in
              let uu____7758 =
                (FStar_Syntax_Util.is_pure_effect msrc) ||
                  (FStar_Syntax_Util.is_div_effect msrc)
                 in
              if uu____7758
              then
                let ed =
                  let uu____7762 =
                    FStar_TypeChecker_Env.norm_eff_name
                      (cfg.core_cfg).FStar_TypeChecker_Cfg.tcenv mtgt
                     in
                  FStar_TypeChecker_Env.get_effect_decl
                    (cfg.core_cfg).FStar_TypeChecker_Cfg.tcenv uu____7762
                   in
                let ret =
                  let uu____7764 =
                    let uu____7765 =
                      let uu____7768 =
                        let uu____7769 =
                          let uu____7776 =
                            FStar_All.pipe_right ed
                              FStar_Syntax_Util.get_return_repr
                             in
                          FStar_All.pipe_right uu____7776 FStar_Util.must  in
                        FStar_All.pipe_right uu____7769
                          FStar_Pervasives_Native.snd
                         in
                      FStar_Syntax_Subst.compress uu____7768  in
                    uu____7765.FStar_Syntax_Syntax.n  in
                  match uu____7764 with
                  | FStar_Syntax_Syntax.Tm_uinst (ret,uu____7822::[]) ->
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_uinst
                           (ret, [FStar_Syntax_Syntax.U_unknown]))
                        FStar_Pervasives_Native.None
                        e1.FStar_Syntax_Syntax.pos
                  | uu____7829 ->
                      failwith "NYI: Reification of indexed effect (NBE)"
                   in
                let cfg' = reifying_false cfg  in
                let t =
                  let uu____7833 =
                    let uu____7834 = translate cfg' [] ret  in
                    iapp cfg' uu____7834
                      [((FStar_TypeChecker_NBETerm.Univ
                           FStar_Syntax_Syntax.U_unknown),
                         FStar_Pervasives_Native.None)]
                     in
                  let uu____7843 =
                    let uu____7844 =
                      let uu____7849 = translate cfg' bs ty  in
                      (uu____7849, FStar_Pervasives_Native.None)  in
                    let uu____7850 =
                      let uu____7857 =
                        let uu____7862 = translate cfg' bs e1  in
                        (uu____7862, FStar_Pervasives_Native.None)  in
                      [uu____7857]  in
                    uu____7844 :: uu____7850  in
                  iapp cfg' uu____7833 uu____7843  in
                (debug cfg
                   (fun uu____7878  ->
                      let uu____7879 =
                        FStar_TypeChecker_NBETerm.t_to_string t  in
                      FStar_Util.print1 "translate_monadic_lift(1): %s\n"
                        uu____7879);
                 t)
              else
                (let uu____7884 =
                   FStar_TypeChecker_Env.monad_leq
                     (cfg.core_cfg).FStar_TypeChecker_Cfg.tcenv msrc mtgt
                    in
                 match uu____7884 with
                 | FStar_Pervasives_Native.None  ->
                     let uu____7887 =
                       let uu____7889 = FStar_Ident.string_of_lid msrc  in
                       let uu____7891 = FStar_Ident.string_of_lid mtgt  in
                       FStar_Util.format2
                         "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                         uu____7889 uu____7891
                        in
                     failwith uu____7887
                 | FStar_Pervasives_Native.Some
                     { FStar_TypeChecker_Env.msource = uu____7894;
                       FStar_TypeChecker_Env.mtarget = uu____7895;
                       FStar_TypeChecker_Env.mlift =
                         { FStar_TypeChecker_Env.mlift_wp = uu____7896;
                           FStar_TypeChecker_Env.mlift_term =
                             FStar_Pervasives_Native.None ;_};_}
                     ->
                     let uu____7916 =
                       let uu____7918 = FStar_Ident.string_of_lid msrc  in
                       let uu____7920 = FStar_Ident.string_of_lid mtgt  in
                       FStar_Util.format2
                         "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
                         uu____7918 uu____7920
                        in
                     failwith uu____7916
                 | FStar_Pervasives_Native.Some
                     { FStar_TypeChecker_Env.msource = uu____7923;
                       FStar_TypeChecker_Env.mtarget = uu____7924;
                       FStar_TypeChecker_Env.mlift =
                         { FStar_TypeChecker_Env.mlift_wp = uu____7925;
                           FStar_TypeChecker_Env.mlift_term =
                             FStar_Pervasives_Native.Some lift;_};_}
                     ->
                     let lift_lam =
                       let x =
                         FStar_Syntax_Syntax.new_bv
                           FStar_Pervasives_Native.None
                           FStar_Syntax_Syntax.tun
                          in
                       let uu____7959 =
                         let uu____7962 = FStar_Syntax_Syntax.bv_to_name x
                            in
                         lift FStar_Syntax_Syntax.U_unknown ty uu____7962  in
                       FStar_Syntax_Util.abs
                         [(x, FStar_Pervasives_Native.None)] uu____7959
                         FStar_Pervasives_Native.None
                        in
                     let cfg' = reifying_false cfg  in
                     let t =
                       let uu____7979 = translate cfg' [] lift_lam  in
                       let uu____7980 =
                         let uu____7981 =
                           let uu____7986 = translate cfg bs e1  in
                           (uu____7986, FStar_Pervasives_Native.None)  in
                         [uu____7981]  in
                       iapp cfg uu____7979 uu____7980  in
                     (debug cfg
                        (fun uu____7998  ->
                           let uu____7999 =
                             FStar_TypeChecker_NBETerm.t_to_string t  in
                           FStar_Util.print1
                             "translate_monadic_lift(2): %s\n" uu____7999);
                      t))

and (readback :
  config -> FStar_TypeChecker_NBETerm.t -> FStar_Syntax_Syntax.term) =
  fun cfg  ->
    fun x  ->
      let debug1 = debug cfg  in
      let readback_args cfg1 args =
        map_rev
          (fun uu____8053  ->
             match uu____8053 with
             | (x1,q) ->
                 let uu____8064 = readback cfg1 x1  in (uu____8064, q)) args
         in
      debug1
        (fun uu____8070  ->
           let uu____8071 = FStar_TypeChecker_NBETerm.t_to_string x  in
           FStar_Util.print1 "Readback: %s\n" uu____8071);
      (match x with
       | FStar_TypeChecker_NBETerm.Univ u ->
           failwith "Readback of universes should not occur"
       | FStar_TypeChecker_NBETerm.Unknown  ->
           FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
             FStar_Pervasives_Native.None FStar_Range.dummyRange
       | FStar_TypeChecker_NBETerm.Constant (FStar_TypeChecker_NBETerm.Unit )
           -> FStar_Syntax_Syntax.unit_const
       | FStar_TypeChecker_NBETerm.Constant (FStar_TypeChecker_NBETerm.Bool
           (true )) -> FStar_Syntax_Util.exp_true_bool
       | FStar_TypeChecker_NBETerm.Constant (FStar_TypeChecker_NBETerm.Bool
           (false )) -> FStar_Syntax_Util.exp_false_bool
       | FStar_TypeChecker_NBETerm.Constant (FStar_TypeChecker_NBETerm.Int i)
           ->
           let uu____8079 = FStar_BigInt.string_of_big_int i  in
           FStar_All.pipe_right uu____8079 FStar_Syntax_Util.exp_int
       | FStar_TypeChecker_NBETerm.Constant (FStar_TypeChecker_NBETerm.String
           (s,r)) ->
           FStar_Syntax_Syntax.mk
             (FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_string (s, r)))
             FStar_Pervasives_Native.None FStar_Range.dummyRange
       | FStar_TypeChecker_NBETerm.Constant (FStar_TypeChecker_NBETerm.Char
           c) -> FStar_Syntax_Util.exp_char c
       | FStar_TypeChecker_NBETerm.Constant (FStar_TypeChecker_NBETerm.Range
           r) ->
           FStar_TypeChecker_Cfg.embed_simple FStar_Syntax_Embeddings.e_range
             r FStar_Range.dummyRange
       | FStar_TypeChecker_NBETerm.Constant (FStar_TypeChecker_NBETerm.SConst
           c) ->
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant c)
             FStar_Pervasives_Native.None FStar_Range.dummyRange
       | FStar_TypeChecker_NBETerm.Type_t u ->
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type u)
             FStar_Pervasives_Native.None FStar_Range.dummyRange
       | FStar_TypeChecker_NBETerm.Lam (f,binders,arity) ->
           let uu____8147 =
             match binders with
             | FStar_Util.Inl (ctx,binders1,rc) ->
                 let uu____8195 =
                   FStar_List.fold_left
                     (fun uu____8249  ->
                        fun uu____8250  ->
                          match (uu____8249, uu____8250) with
                          | ((ctx1,binders_rev,accus_rev),(x1,q)) ->
                              let tnorm =
                                let uu____8375 =
                                  translate cfg ctx1
                                    x1.FStar_Syntax_Syntax.sort
                                   in
                                readback cfg uu____8375  in
                              let x2 =
                                let uu___1227_8377 =
                                  FStar_Syntax_Syntax.freshen_bv x1  in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___1227_8377.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___1227_8377.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = tnorm
                                }  in
                              let ax = FStar_TypeChecker_NBETerm.mkAccuVar x2
                                 in
                              let ctx2 = ax :: ctx1  in
                              (ctx2, ((x2, q) :: binders_rev), (ax ::
                                accus_rev))) (ctx, [], []) binders1
                    in
                 (match uu____8195 with
                  | (ctx1,binders_rev,accus_rev) ->
                      let rc1 =
                        match rc with
                        | FStar_Pervasives_Native.None  ->
                            FStar_Pervasives_Native.None
                        | FStar_Pervasives_Native.Some rc1 ->
                            let uu____8463 =
                              let uu____8464 =
                                translate_residual_comp cfg ctx1 rc1  in
                              readback_residual_comp cfg uu____8464  in
                            FStar_Pervasives_Native.Some uu____8463
                         in
                      ((FStar_List.rev binders_rev), accus_rev, rc1))
             | FStar_Util.Inr args ->
                 let uu____8498 =
                   FStar_List.fold_right
                     (fun uu____8539  ->
                        fun uu____8540  ->
                          match (uu____8539, uu____8540) with
                          | ((t,uu____8592),(binders1,accus)) ->
                              let x1 =
                                let uu____8634 = readback cfg t  in
                                FStar_Syntax_Syntax.new_bv
                                  FStar_Pervasives_Native.None uu____8634
                                 in
                              let uu____8635 =
                                let uu____8638 =
                                  FStar_TypeChecker_NBETerm.mkAccuVar x1  in
                                uu____8638 :: accus  in
                              (((x1, FStar_Pervasives_Native.None) ::
                                binders1), uu____8635)) args ([], [])
                    in
                 (match uu____8498 with
                  | (binders1,accus) ->
                      (binders1, (FStar_List.rev accus),
                        FStar_Pervasives_Native.None))
              in
           (match uu____8147 with
            | (binders1,accus_rev,rc) ->
                let body =
                  let uu____8721 = f accus_rev  in readback cfg uu____8721
                   in
                FStar_Syntax_Util.abs binders1 body rc)
       | FStar_TypeChecker_NBETerm.Refinement (f,targ) ->
           if
             ((cfg.core_cfg).FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.for_extraction
           then
             let uu____8745 =
               let uu____8746 = targ ()  in
               FStar_Pervasives_Native.fst uu____8746  in
             readback cfg uu____8745
           else
             (let x1 =
                let uu____8754 =
                  let uu____8755 =
                    let uu____8756 = targ ()  in
                    FStar_Pervasives_Native.fst uu____8756  in
                  readback cfg uu____8755  in
                FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                  uu____8754
                 in
              let body =
                let uu____8762 =
                  let uu____8763 = FStar_TypeChecker_NBETerm.mkAccuVar x1  in
                  f uu____8763  in
                readback cfg uu____8762  in
              let refinement = FStar_Syntax_Util.refine x1 body  in
              if
                ((cfg.core_cfg).FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.simplify
              then
                FStar_TypeChecker_Common.simplify
                  ((cfg.core_cfg).FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                  refinement
              else refinement)
       | FStar_TypeChecker_NBETerm.Reflect t ->
           let tm = readback cfg t  in FStar_Syntax_Util.mk_reflect tm
       | FStar_TypeChecker_NBETerm.Arrow (FStar_Util.Inl f) ->
           FStar_Thunk.force f
       | FStar_TypeChecker_NBETerm.Arrow (FStar_Util.Inr (args,c)) ->
           let binders =
             FStar_List.map
               (fun uu____8833  ->
                  match uu____8833 with
                  | (t,q) ->
                      let t1 = readback cfg t  in
                      let x1 =
                        FStar_Syntax_Syntax.new_bv
                          FStar_Pervasives_Native.None t1
                         in
                      (x1, q)) args
              in
           let c1 = readback_comp cfg c  in
           FStar_Syntax_Util.arrow binders c1
       | FStar_TypeChecker_NBETerm.Construct (fv,us,args) ->
           let args1 =
             map_rev
               (fun uu____8885  ->
                  match uu____8885 with
                  | (x1,q) ->
                      let uu____8896 = readback cfg x1  in (uu____8896, q))
               args
              in
           let fv1 =
             FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
               FStar_Pervasives_Native.None FStar_Range.dummyRange
              in
           let app =
             let uu____8903 =
               FStar_Syntax_Syntax.mk_Tm_uinst fv1 (FStar_List.rev us)  in
             FStar_Syntax_Util.mk_app uu____8903 args1  in
           app
       | FStar_TypeChecker_NBETerm.FV (fv,us,args) ->
           let args1 =
             map_rev
               (fun uu____8944  ->
                  match uu____8944 with
                  | (x1,q) ->
                      let uu____8955 = readback cfg x1  in (uu____8955, q))
               args
              in
           let fv1 =
             FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
               FStar_Pervasives_Native.None FStar_Range.dummyRange
              in
           let app =
             let uu____8962 =
               FStar_Syntax_Syntax.mk_Tm_uinst fv1 (FStar_List.rev us)  in
             FStar_Syntax_Util.mk_app uu____8962 args1  in
           if
             ((cfg.core_cfg).FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.simplify
           then
             FStar_TypeChecker_Common.simplify
               ((cfg.core_cfg).FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
               app
           else app
       | FStar_TypeChecker_NBETerm.Accu (FStar_TypeChecker_NBETerm.Var bv,[])
           -> FStar_Syntax_Syntax.bv_to_name bv
       | FStar_TypeChecker_NBETerm.Accu
           (FStar_TypeChecker_NBETerm.Var bv,args) ->
           let args1 = readback_args cfg args  in
           let app =
             let uu____9003 = FStar_Syntax_Syntax.bv_to_name bv  in
             FStar_Syntax_Util.mk_app uu____9003 args1  in
           if
             ((cfg.core_cfg).FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.simplify
           then
             FStar_TypeChecker_Common.simplify
               ((cfg.core_cfg).FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
               app
           else app
       | FStar_TypeChecker_NBETerm.Accu
           (FStar_TypeChecker_NBETerm.Match (scrut,make_branches),args) ->
           let args1 = readback_args cfg args  in
           let head =
             let scrut_new = readback cfg scrut  in
             let branches_new = make_branches ()  in
             FStar_Syntax_Syntax.mk
               (FStar_Syntax_Syntax.Tm_match (scrut_new, branches_new))
               FStar_Pervasives_Native.None FStar_Range.dummyRange
              in
           let app = FStar_Syntax_Util.mk_app head args1  in
           if
             ((cfg.core_cfg).FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.simplify
           then
             FStar_TypeChecker_Common.simplify
               ((cfg.core_cfg).FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
               app
           else app
       | FStar_TypeChecker_NBETerm.Accu
           (FStar_TypeChecker_NBETerm.UnreducedLet
            (var,typ,defn,body,lb),args)
           ->
           let typ1 =
             let uu____9103 = FStar_Thunk.force typ  in
             readback cfg uu____9103  in
           let defn1 =
             let uu____9105 = FStar_Thunk.force defn  in
             readback cfg uu____9105  in
           let body1 =
             let uu____9107 =
               let uu____9108 = FStar_Thunk.force body  in
               readback cfg uu____9108  in
             FStar_Syntax_Subst.close [(var, FStar_Pervasives_Native.None)]
               uu____9107
              in
           let lbname =
             let uu____9128 =
               let uu___1346_9129 =
                 FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
               {
                 FStar_Syntax_Syntax.ppname =
                   (uu___1346_9129.FStar_Syntax_Syntax.ppname);
                 FStar_Syntax_Syntax.index =
                   (uu___1346_9129.FStar_Syntax_Syntax.index);
                 FStar_Syntax_Syntax.sort = typ1
               }  in
             FStar_Util.Inl uu____9128  in
           let lb1 =
             let uu___1349_9131 = lb  in
             {
               FStar_Syntax_Syntax.lbname = lbname;
               FStar_Syntax_Syntax.lbunivs =
                 (uu___1349_9131.FStar_Syntax_Syntax.lbunivs);
               FStar_Syntax_Syntax.lbtyp = typ1;
               FStar_Syntax_Syntax.lbeff =
                 (uu___1349_9131.FStar_Syntax_Syntax.lbeff);
               FStar_Syntax_Syntax.lbdef = defn1;
               FStar_Syntax_Syntax.lbattrs =
                 (uu___1349_9131.FStar_Syntax_Syntax.lbattrs);
               FStar_Syntax_Syntax.lbpos =
                 (uu___1349_9131.FStar_Syntax_Syntax.lbpos)
             }  in
           let hd =
             FStar_Syntax_Syntax.mk
               (FStar_Syntax_Syntax.Tm_let ((false, [lb1]), body1))
               FStar_Pervasives_Native.None FStar_Range.dummyRange
              in
           let args1 = readback_args cfg args  in
           FStar_Syntax_Util.mk_app hd args1
       | FStar_TypeChecker_NBETerm.Accu
           (FStar_TypeChecker_NBETerm.UnreducedLetRec
            (vars_typs_defns,body,lbs),args)
           ->
           let lbs1 =
             FStar_List.map2
               (fun uu____9209  ->
                  fun lb  ->
                    match uu____9209 with
                    | (v,t,d) ->
                        let t1 = readback cfg t  in
                        let def = readback cfg d  in
                        let v1 =
                          let uu___1369_9223 = v  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___1369_9223.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___1369_9223.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t1
                          }  in
                        let uu___1372_9224 = lb  in
                        {
                          FStar_Syntax_Syntax.lbname = (FStar_Util.Inl v1);
                          FStar_Syntax_Syntax.lbunivs =
                            (uu___1372_9224.FStar_Syntax_Syntax.lbunivs);
                          FStar_Syntax_Syntax.lbtyp = t1;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___1372_9224.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = def;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___1372_9224.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___1372_9224.FStar_Syntax_Syntax.lbpos)
                        }) vars_typs_defns lbs
              in
           let body1 = readback cfg body  in
           let uu____9226 = FStar_Syntax_Subst.close_let_rec lbs1 body1  in
           (match uu____9226 with
            | (lbs2,body2) ->
                let hd =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_let ((true, lbs2), body2))
                    FStar_Pervasives_Native.None FStar_Range.dummyRange
                   in
                let args1 = readback_args cfg args  in
                FStar_Syntax_Util.mk_app hd args1)
       | FStar_TypeChecker_NBETerm.Accu
           (FStar_TypeChecker_NBETerm.UVar f,args) ->
           let hd = FStar_Thunk.force f  in
           let args1 = readback_args cfg args  in
           FStar_Syntax_Util.mk_app hd args1
       | FStar_TypeChecker_NBETerm.TopLevelLet (lb,arity,args_rev) ->
           let n_univs = FStar_List.length lb.FStar_Syntax_Syntax.lbunivs  in
           let n_args = FStar_List.length args_rev  in
           let uu____9309 = FStar_Util.first_N (n_args - n_univs) args_rev
              in
           (match uu____9309 with
            | (args_rev1,univs) ->
                let uu____9356 =
                  let uu____9357 =
                    let uu____9358 =
                      FStar_List.map FStar_Pervasives_Native.fst univs  in
                    translate cfg uu____9358 lb.FStar_Syntax_Syntax.lbdef  in
                  iapp cfg uu____9357 (FStar_List.rev args_rev1)  in
                readback cfg uu____9356)
       | FStar_TypeChecker_NBETerm.TopLevelRec
           (lb,uu____9370,uu____9371,args) ->
           let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
           let head =
             FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
               FStar_Pervasives_Native.None FStar_Range.dummyRange
              in
           let args1 =
             FStar_List.map
               (fun uu____9416  ->
                  match uu____9416 with
                  | (t,q) ->
                      let uu____9427 = readback cfg t  in (uu____9427, q))
               args
              in
           FStar_Syntax_Util.mk_app head args1
       | FStar_TypeChecker_NBETerm.LocalLetRec
           (i,uu____9429,lbs,bs,args,_ar,_ar_lst) ->
           let lbnames =
             FStar_List.map
               (fun lb  ->
                  let uu____9471 =
                    let uu____9473 =
                      let uu____9474 =
                        FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                      uu____9474.FStar_Syntax_Syntax.ppname  in
                    FStar_Ident.text_of_id uu____9473  in
                  FStar_Syntax_Syntax.gen_bv uu____9471
                    FStar_Pervasives_Native.None lb.FStar_Syntax_Syntax.lbtyp)
               lbs
              in
           let let_rec_env =
             let uu____9478 =
               FStar_List.map
                 (fun x1  ->
                    FStar_TypeChecker_NBETerm.Accu
                      ((FStar_TypeChecker_NBETerm.Var x1), [])) lbnames
                in
             FStar_List.rev_append uu____9478 bs  in
           let lbs1 =
             FStar_List.map2
               (fun lb  ->
                  fun lbname  ->
                    let lbdef =
                      let uu____9504 =
                        translate cfg let_rec_env
                          lb.FStar_Syntax_Syntax.lbdef
                         in
                      readback cfg uu____9504  in
                    let lbtyp =
                      let uu____9506 =
                        translate cfg bs lb.FStar_Syntax_Syntax.lbtyp  in
                      readback cfg uu____9506  in
                    let uu___1427_9507 = lb  in
                    {
                      FStar_Syntax_Syntax.lbname = (FStar_Util.Inl lbname);
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___1427_9507.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = lbtyp;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___1427_9507.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = lbdef;
                      FStar_Syntax_Syntax.lbattrs =
                        (uu___1427_9507.FStar_Syntax_Syntax.lbattrs);
                      FStar_Syntax_Syntax.lbpos =
                        (uu___1427_9507.FStar_Syntax_Syntax.lbpos)
                    }) lbs lbnames
              in
           let body =
             let uu____9509 = FStar_List.nth lbnames i  in
             FStar_Syntax_Syntax.bv_to_name uu____9509  in
           let uu____9510 = FStar_Syntax_Subst.close_let_rec lbs1 body  in
           (match uu____9510 with
            | (lbs2,body1) ->
                let head =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_let ((true, lbs2), body1))
                    FStar_Pervasives_Native.None FStar_Range.dummyRange
                   in
                let args1 =
                  FStar_List.map
                    (fun uu____9558  ->
                       match uu____9558 with
                       | (x1,q) ->
                           let uu____9569 = readback cfg x1  in
                           (uu____9569, q)) args
                   in
                FStar_Syntax_Util.mk_app head args1)
       | FStar_TypeChecker_NBETerm.Quote (qt,qi) ->
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_quoted (qt, qi))
             FStar_Pervasives_Native.None FStar_Range.dummyRange
       | FStar_TypeChecker_NBETerm.Lazy (FStar_Util.Inl li,uu____9575) ->
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_lazy li)
             FStar_Pervasives_Native.None FStar_Range.dummyRange
       | FStar_TypeChecker_NBETerm.Lazy (uu____9592,thunk) ->
           let uu____9614 = FStar_Thunk.force thunk  in
           readback cfg uu____9614)

type step =
  | Primops 
  | UnfoldUntil of FStar_Syntax_Syntax.delta_depth 
  | UnfoldOnly of FStar_Ident.lid Prims.list 
  | UnfoldAttr of FStar_Ident.lid Prims.list 
  | UnfoldTac 
  | Reify 
let (uu___is_Primops : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Primops  -> true | uu____9643 -> false
  
let (uu___is_UnfoldUntil : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldUntil _0 -> true | uu____9655 -> false
  
let (__proj__UnfoldUntil__item___0 : step -> FStar_Syntax_Syntax.delta_depth)
  = fun projectee  -> match projectee with | UnfoldUntil _0 -> _0 
let (uu___is_UnfoldOnly : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldOnly _0 -> true | uu____9676 -> false
  
let (__proj__UnfoldOnly__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldOnly _0 -> _0 
let (uu___is_UnfoldAttr : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldAttr _0 -> true | uu____9703 -> false
  
let (__proj__UnfoldAttr__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldAttr _0 -> _0 
let (uu___is_UnfoldTac : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldTac  -> true | uu____9727 -> false
  
let (uu___is_Reify : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reify  -> true | uu____9738 -> false
  
let (step_as_normalizer_step : step -> FStar_TypeChecker_Env.step) =
  fun uu___2_9745  ->
    match uu___2_9745 with
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
      fun args  -> let uu____9769 = new_config cfg  in iapp uu____9769 t args
  
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
            let uu___1473_9801 = cfg  in
            {
              FStar_TypeChecker_Cfg.steps =
                (let uu___1475_9804 = cfg.FStar_TypeChecker_Cfg.steps  in
                 {
                   FStar_TypeChecker_Cfg.beta =
                     (uu___1475_9804.FStar_TypeChecker_Cfg.beta);
                   FStar_TypeChecker_Cfg.iota =
                     (uu___1475_9804.FStar_TypeChecker_Cfg.iota);
                   FStar_TypeChecker_Cfg.zeta =
                     (uu___1475_9804.FStar_TypeChecker_Cfg.zeta);
                   FStar_TypeChecker_Cfg.zeta_full =
                     (uu___1475_9804.FStar_TypeChecker_Cfg.zeta_full);
                   FStar_TypeChecker_Cfg.weak =
                     (uu___1475_9804.FStar_TypeChecker_Cfg.weak);
                   FStar_TypeChecker_Cfg.hnf =
                     (uu___1475_9804.FStar_TypeChecker_Cfg.hnf);
                   FStar_TypeChecker_Cfg.primops =
                     (uu___1475_9804.FStar_TypeChecker_Cfg.primops);
                   FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                     (uu___1475_9804.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                   FStar_TypeChecker_Cfg.unfold_until =
                     (uu___1475_9804.FStar_TypeChecker_Cfg.unfold_until);
                   FStar_TypeChecker_Cfg.unfold_only =
                     (uu___1475_9804.FStar_TypeChecker_Cfg.unfold_only);
                   FStar_TypeChecker_Cfg.unfold_fully =
                     (uu___1475_9804.FStar_TypeChecker_Cfg.unfold_fully);
                   FStar_TypeChecker_Cfg.unfold_attr =
                     (uu___1475_9804.FStar_TypeChecker_Cfg.unfold_attr);
                   FStar_TypeChecker_Cfg.unfold_tac =
                     (uu___1475_9804.FStar_TypeChecker_Cfg.unfold_tac);
                   FStar_TypeChecker_Cfg.pure_subterms_within_computations =
                     (uu___1475_9804.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                   FStar_TypeChecker_Cfg.simplify =
                     (uu___1475_9804.FStar_TypeChecker_Cfg.simplify);
                   FStar_TypeChecker_Cfg.erase_universes =
                     (uu___1475_9804.FStar_TypeChecker_Cfg.erase_universes);
                   FStar_TypeChecker_Cfg.allow_unbound_universes =
                     (uu___1475_9804.FStar_TypeChecker_Cfg.allow_unbound_universes);
                   FStar_TypeChecker_Cfg.reify_ = true;
                   FStar_TypeChecker_Cfg.compress_uvars =
                     (uu___1475_9804.FStar_TypeChecker_Cfg.compress_uvars);
                   FStar_TypeChecker_Cfg.no_full_norm =
                     (uu___1475_9804.FStar_TypeChecker_Cfg.no_full_norm);
                   FStar_TypeChecker_Cfg.check_no_uvars =
                     (uu___1475_9804.FStar_TypeChecker_Cfg.check_no_uvars);
                   FStar_TypeChecker_Cfg.unmeta =
                     (uu___1475_9804.FStar_TypeChecker_Cfg.unmeta);
                   FStar_TypeChecker_Cfg.unascribe =
                     (uu___1475_9804.FStar_TypeChecker_Cfg.unascribe);
                   FStar_TypeChecker_Cfg.in_full_norm_request =
                     (uu___1475_9804.FStar_TypeChecker_Cfg.in_full_norm_request);
                   FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                     (uu___1475_9804.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                   FStar_TypeChecker_Cfg.nbe_step =
                     (uu___1475_9804.FStar_TypeChecker_Cfg.nbe_step);
                   FStar_TypeChecker_Cfg.for_extraction =
                     (uu___1475_9804.FStar_TypeChecker_Cfg.for_extraction)
                 });
              FStar_TypeChecker_Cfg.tcenv =
                (uu___1473_9801.FStar_TypeChecker_Cfg.tcenv);
              FStar_TypeChecker_Cfg.debug =
                (uu___1473_9801.FStar_TypeChecker_Cfg.debug);
              FStar_TypeChecker_Cfg.delta_level =
                (uu___1473_9801.FStar_TypeChecker_Cfg.delta_level);
              FStar_TypeChecker_Cfg.primitive_steps =
                (uu___1473_9801.FStar_TypeChecker_Cfg.primitive_steps);
              FStar_TypeChecker_Cfg.strong =
                (uu___1473_9801.FStar_TypeChecker_Cfg.strong);
              FStar_TypeChecker_Cfg.memoize_lazy =
                (uu___1473_9801.FStar_TypeChecker_Cfg.memoize_lazy);
              FStar_TypeChecker_Cfg.normalize_pure_lets =
                (uu___1473_9801.FStar_TypeChecker_Cfg.normalize_pure_lets);
              FStar_TypeChecker_Cfg.reifying =
                (uu___1473_9801.FStar_TypeChecker_Cfg.reifying)
            }  in
          (let uu____9807 =
             (FStar_TypeChecker_Env.debug env (FStar_Options.Other "NBETop"))
               ||
               (FStar_TypeChecker_Env.debug env (FStar_Options.Other "NBE"))
              in
           if uu____9807
           then
             let uu____9812 = FStar_Syntax_Print.term_to_string e  in
             FStar_Util.print1 "Calling NBE with (%s) {\n" uu____9812
           else ());
          (let cfg2 = new_config cfg1  in
           let r =
             let uu____9819 = translate cfg2 [] e  in
             readback cfg2 uu____9819  in
           (let uu____9821 =
              (FStar_TypeChecker_Env.debug env (FStar_Options.Other "NBETop"))
                ||
                (FStar_TypeChecker_Env.debug env (FStar_Options.Other "NBE"))
               in
            if uu____9821
            then
              let uu____9826 = FStar_Syntax_Print.term_to_string r  in
              FStar_Util.print1 "}\nNBE returned (%s)\n" uu____9826
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
          let uu___1491_9853 = cfg  in
          {
            FStar_TypeChecker_Cfg.steps =
              (let uu___1493_9856 = cfg.FStar_TypeChecker_Cfg.steps  in
               {
                 FStar_TypeChecker_Cfg.beta =
                   (uu___1493_9856.FStar_TypeChecker_Cfg.beta);
                 FStar_TypeChecker_Cfg.iota =
                   (uu___1493_9856.FStar_TypeChecker_Cfg.iota);
                 FStar_TypeChecker_Cfg.zeta =
                   (uu___1493_9856.FStar_TypeChecker_Cfg.zeta);
                 FStar_TypeChecker_Cfg.zeta_full =
                   (uu___1493_9856.FStar_TypeChecker_Cfg.zeta_full);
                 FStar_TypeChecker_Cfg.weak =
                   (uu___1493_9856.FStar_TypeChecker_Cfg.weak);
                 FStar_TypeChecker_Cfg.hnf =
                   (uu___1493_9856.FStar_TypeChecker_Cfg.hnf);
                 FStar_TypeChecker_Cfg.primops =
                   (uu___1493_9856.FStar_TypeChecker_Cfg.primops);
                 FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                   (uu___1493_9856.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                 FStar_TypeChecker_Cfg.unfold_until =
                   (uu___1493_9856.FStar_TypeChecker_Cfg.unfold_until);
                 FStar_TypeChecker_Cfg.unfold_only =
                   (uu___1493_9856.FStar_TypeChecker_Cfg.unfold_only);
                 FStar_TypeChecker_Cfg.unfold_fully =
                   (uu___1493_9856.FStar_TypeChecker_Cfg.unfold_fully);
                 FStar_TypeChecker_Cfg.unfold_attr =
                   (uu___1493_9856.FStar_TypeChecker_Cfg.unfold_attr);
                 FStar_TypeChecker_Cfg.unfold_tac =
                   (uu___1493_9856.FStar_TypeChecker_Cfg.unfold_tac);
                 FStar_TypeChecker_Cfg.pure_subterms_within_computations =
                   (uu___1493_9856.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                 FStar_TypeChecker_Cfg.simplify =
                   (uu___1493_9856.FStar_TypeChecker_Cfg.simplify);
                 FStar_TypeChecker_Cfg.erase_universes =
                   (uu___1493_9856.FStar_TypeChecker_Cfg.erase_universes);
                 FStar_TypeChecker_Cfg.allow_unbound_universes =
                   (uu___1493_9856.FStar_TypeChecker_Cfg.allow_unbound_universes);
                 FStar_TypeChecker_Cfg.reify_ = true;
                 FStar_TypeChecker_Cfg.compress_uvars =
                   (uu___1493_9856.FStar_TypeChecker_Cfg.compress_uvars);
                 FStar_TypeChecker_Cfg.no_full_norm =
                   (uu___1493_9856.FStar_TypeChecker_Cfg.no_full_norm);
                 FStar_TypeChecker_Cfg.check_no_uvars =
                   (uu___1493_9856.FStar_TypeChecker_Cfg.check_no_uvars);
                 FStar_TypeChecker_Cfg.unmeta =
                   (uu___1493_9856.FStar_TypeChecker_Cfg.unmeta);
                 FStar_TypeChecker_Cfg.unascribe =
                   (uu___1493_9856.FStar_TypeChecker_Cfg.unascribe);
                 FStar_TypeChecker_Cfg.in_full_norm_request =
                   (uu___1493_9856.FStar_TypeChecker_Cfg.in_full_norm_request);
                 FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                   (uu___1493_9856.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                 FStar_TypeChecker_Cfg.nbe_step =
                   (uu___1493_9856.FStar_TypeChecker_Cfg.nbe_step);
                 FStar_TypeChecker_Cfg.for_extraction =
                   (uu___1493_9856.FStar_TypeChecker_Cfg.for_extraction)
               });
            FStar_TypeChecker_Cfg.tcenv =
              (uu___1491_9853.FStar_TypeChecker_Cfg.tcenv);
            FStar_TypeChecker_Cfg.debug =
              (uu___1491_9853.FStar_TypeChecker_Cfg.debug);
            FStar_TypeChecker_Cfg.delta_level =
              (uu___1491_9853.FStar_TypeChecker_Cfg.delta_level);
            FStar_TypeChecker_Cfg.primitive_steps =
              (uu___1491_9853.FStar_TypeChecker_Cfg.primitive_steps);
            FStar_TypeChecker_Cfg.strong =
              (uu___1491_9853.FStar_TypeChecker_Cfg.strong);
            FStar_TypeChecker_Cfg.memoize_lazy =
              (uu___1491_9853.FStar_TypeChecker_Cfg.memoize_lazy);
            FStar_TypeChecker_Cfg.normalize_pure_lets =
              (uu___1491_9853.FStar_TypeChecker_Cfg.normalize_pure_lets);
            FStar_TypeChecker_Cfg.reifying =
              (uu___1491_9853.FStar_TypeChecker_Cfg.reifying)
          }  in
        let cfg2 = new_config cfg1  in
        debug cfg2
          (fun uu____9862  ->
             let uu____9863 = FStar_Syntax_Print.term_to_string e  in
             FStar_Util.print1 "Calling NBE with (%s) {\n" uu____9863);
        (let r =
           let uu____9867 = translate cfg2 [] e  in readback cfg2 uu____9867
            in
         debug cfg2
           (fun uu____9871  ->
              let uu____9872 = FStar_Syntax_Print.term_to_string r  in
              FStar_Util.print1 "}\nNBE returned (%s)\n" uu____9872);
         r)
  