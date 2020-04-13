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
           | FStar_Util.Inl uu____1985 -> failwith "find_let : impossible"
           | FStar_Util.Inr name ->
               let uu____1990 = FStar_Syntax_Syntax.fv_eq name fvar  in
               if uu____1990
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
          (fun uu____2261  ->
             let uu____2262 =
               let uu____2264 = FStar_Syntax_Subst.compress e  in
               FStar_Syntax_Print.tag_of_term uu____2264  in
             let uu____2265 =
               let uu____2267 = FStar_Syntax_Subst.compress e  in
               FStar_Syntax_Print.term_to_string uu____2267  in
             FStar_Util.print2 "Term: %s - %s\n" uu____2262 uu____2265);
        (let uu____2269 =
           let uu____2270 = FStar_Syntax_Subst.compress e  in
           uu____2270.FStar_Syntax_Syntax.n  in
         match uu____2269 with
         | FStar_Syntax_Syntax.Tm_delayed (uu____2273,uu____2274) ->
             failwith "Tm_delayed: Impossible"
         | FStar_Syntax_Syntax.Tm_unknown  ->
             FStar_TypeChecker_NBETerm.Unknown
         | FStar_Syntax_Syntax.Tm_constant c ->
             let uu____2297 = translate_constant c  in
             FStar_TypeChecker_NBETerm.Constant uu____2297
         | FStar_Syntax_Syntax.Tm_bvar db ->
             if db.FStar_Syntax_Syntax.index < (FStar_List.length bs)
             then
               let t = FStar_List.nth bs db.FStar_Syntax_Syntax.index  in
               (debug1
                  (fun uu____2308  ->
                     let uu____2309 = FStar_TypeChecker_NBETerm.t_to_string t
                        in
                     let uu____2311 =
                       let uu____2313 =
                         FStar_List.map FStar_TypeChecker_NBETerm.t_to_string
                           bs
                          in
                       FStar_All.pipe_right uu____2313
                         (FStar_String.concat "; ")
                        in
                     FStar_Util.print2
                       "Resolved bvar to %s\n\tcontext is [%s]\n" uu____2309
                       uu____2311);
                t)
             else failwith "de Bruijn index out of bounds"
         | FStar_Syntax_Syntax.Tm_uinst (t,us) ->
             (debug1
                (fun uu____2340  ->
                   let uu____2341 = FStar_Syntax_Print.term_to_string t  in
                   let uu____2343 =
                     let uu____2345 =
                       FStar_List.map FStar_Syntax_Print.univ_to_string us
                        in
                     FStar_All.pipe_right uu____2345
                       (FStar_String.concat ", ")
                      in
                   FStar_Util.print2 "Uinst term : %s\nUnivs : %s\n"
                     uu____2341 uu____2343);
              (let uu____2356 = translate cfg bs t  in
               let uu____2357 =
                 FStar_List.map
                   (fun x  ->
                      let uu____2361 =
                        let uu____2362 = translate_univ cfg bs x  in
                        FStar_TypeChecker_NBETerm.Univ uu____2362  in
                      FStar_TypeChecker_NBETerm.as_arg uu____2361) us
                  in
               iapp cfg uu____2356 uu____2357))
         | FStar_Syntax_Syntax.Tm_type u ->
             let uu____2364 = translate_univ cfg bs u  in
             FStar_TypeChecker_NBETerm.Type_t uu____2364
         | FStar_Syntax_Syntax.Tm_arrow (xs,c) ->
             let norm uu____2394 =
               let uu____2395 =
                 FStar_List.fold_left
                   (fun uu____2439  ->
                      fun uu____2440  ->
                        match (uu____2439, uu____2440) with
                        | ((ctx,binders_rev),(x,q)) ->
                            let t =
                              let uu____2544 =
                                translate cfg ctx x.FStar_Syntax_Syntax.sort
                                 in
                              readback cfg uu____2544  in
                            let x1 =
                              let uu___380_2546 =
                                FStar_Syntax_Syntax.freshen_bv x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___380_2546.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___380_2546.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t
                              }  in
                            let ctx1 =
                              let uu____2550 =
                                FStar_TypeChecker_NBETerm.mkAccuVar x1  in
                              uu____2550 :: ctx  in
                            (ctx1, ((x1, q) :: binders_rev))) (bs, []) xs
                  in
               match uu____2395 with
               | (ctx,binders_rev) ->
                   let c1 =
                     let uu____2610 = translate_comp cfg ctx c  in
                     readback_comp cfg uu____2610  in
                   FStar_Syntax_Util.arrow (FStar_List.rev binders_rev) c1
                in
             let uu____2617 =
               let uu____2634 = FStar_Thunk.mk norm  in
               FStar_Util.Inl uu____2634  in
             FStar_TypeChecker_NBETerm.Arrow uu____2617
         | FStar_Syntax_Syntax.Tm_refine (bv,tm) ->
             if
               ((cfg.core_cfg).FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.for_extraction
             then translate cfg bs bv.FStar_Syntax_Syntax.sort
             else
               FStar_TypeChecker_NBETerm.Refinement
                 (((fun y  -> translate cfg (y :: bs) tm)),
                   ((fun uu____2672  ->
                       let uu____2673 =
                         translate cfg bs bv.FStar_Syntax_Syntax.sort  in
                       FStar_TypeChecker_NBETerm.as_arg uu____2673)))
         | FStar_Syntax_Syntax.Tm_ascribed (t,uu____2675,uu____2676) ->
             translate cfg bs t
         | FStar_Syntax_Syntax.Tm_uvar (u,(subst,set_use_range)) ->
             let norm_uvar uu____2743 =
               let norm_subst_elt uu___1_2749 =
                 match uu___1_2749 with
                 | FStar_Syntax_Syntax.NT (x,t) ->
                     let uu____2756 =
                       let uu____2763 =
                         let uu____2766 = translate cfg bs t  in
                         readback cfg uu____2766  in
                       (x, uu____2763)  in
                     FStar_Syntax_Syntax.NT uu____2756
                 | FStar_Syntax_Syntax.NM (x,i) ->
                     let x_i =
                       FStar_Syntax_Syntax.bv_to_tm
                         (let uu___417_2776 = x  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___417_2776.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index = i;
                            FStar_Syntax_Syntax.sort =
                              (uu___417_2776.FStar_Syntax_Syntax.sort)
                          })
                        in
                     let t =
                       let uu____2778 = translate cfg bs x_i  in
                       readback cfg uu____2778  in
                     (match t.FStar_Syntax_Syntax.n with
                      | FStar_Syntax_Syntax.Tm_bvar x_j ->
                          FStar_Syntax_Syntax.NM
                            (x, (x_j.FStar_Syntax_Syntax.index))
                      | uu____2781 -> FStar_Syntax_Syntax.NT (x, t))
                 | uu____2784 ->
                     failwith "Impossible: subst invariant of uvar nodes"
                  in
               let subst1 =
                 FStar_List.map (FStar_List.map norm_subst_elt) subst  in
               let uu___427_2795 = e  in
               {
                 FStar_Syntax_Syntax.n =
                   (FStar_Syntax_Syntax.Tm_uvar (u, (subst1, set_use_range)));
                 FStar_Syntax_Syntax.pos =
                   (uu___427_2795.FStar_Syntax_Syntax.pos);
                 FStar_Syntax_Syntax.vars =
                   (uu___427_2795.FStar_Syntax_Syntax.vars)
               }  in
             let uu____2808 =
               let uu____2819 =
                 let uu____2820 = FStar_Thunk.mk norm_uvar  in
                 FStar_TypeChecker_NBETerm.UVar uu____2820  in
               (uu____2819, [])  in
             FStar_TypeChecker_NBETerm.Accu uu____2808
         | FStar_Syntax_Syntax.Tm_name x ->
             FStar_TypeChecker_NBETerm.mkAccuVar x
         | FStar_Syntax_Syntax.Tm_abs ([],uu____2834,uu____2835) ->
             failwith "Impossible: abstraction with no binders"
         | FStar_Syntax_Syntax.Tm_abs (xs,body,resc) ->
             FStar_TypeChecker_NBETerm.Lam
               (((fun ys  -> translate cfg (FStar_List.append ys bs) body)),
                 (FStar_Util.Inl (bs, xs, resc)), (FStar_List.length xs))
         | FStar_Syntax_Syntax.Tm_fvar fvar ->
             let uu____2943 = try_in_cache cfg fvar  in
             (match uu____2943 with
              | FStar_Pervasives_Native.Some t -> t
              | uu____2947 -> translate_fv cfg bs fvar)
         | FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                  (FStar_Const.Const_reify );
                FStar_Syntax_Syntax.pos = uu____2950;
                FStar_Syntax_Syntax.vars = uu____2951;_},arg::more::args)
             ->
             let uu____3011 = FStar_Syntax_Util.head_and_args e  in
             (match uu____3011 with
              | (head,uu____3029) ->
                  let head1 =
                    FStar_Syntax_Syntax.mk_Tm_app head [arg]
                      FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
                     in
                  let uu____3073 =
                    FStar_Syntax_Syntax.mk_Tm_app head1 (more :: args)
                      FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
                     in
                  translate cfg bs uu____3073)
         | FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                  (FStar_Const.Const_reflect uu____3082);
                FStar_Syntax_Syntax.pos = uu____3083;
                FStar_Syntax_Syntax.vars = uu____3084;_},arg::more::args)
             ->
             let uu____3144 = FStar_Syntax_Util.head_and_args e  in
             (match uu____3144 with
              | (head,uu____3162) ->
                  let head1 =
                    FStar_Syntax_Syntax.mk_Tm_app head [arg]
                      FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
                     in
                  let uu____3206 =
                    FStar_Syntax_Syntax.mk_Tm_app head1 (more :: args)
                      FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
                     in
                  translate cfg bs uu____3206)
         | FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                  (FStar_Const.Const_reflect uu____3215);
                FStar_Syntax_Syntax.pos = uu____3216;
                FStar_Syntax_Syntax.vars = uu____3217;_},arg::[])
             when (cfg.core_cfg).FStar_TypeChecker_Cfg.reifying ->
             let cfg1 = reifying_false cfg  in
             translate cfg1 bs (FStar_Pervasives_Native.fst arg)
         | FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                  (FStar_Const.Const_reflect uu____3262);
                FStar_Syntax_Syntax.pos = uu____3263;
                FStar_Syntax_Syntax.vars = uu____3264;_},arg::[])
             ->
             let uu____3304 =
               translate cfg bs (FStar_Pervasives_Native.fst arg)  in
             FStar_TypeChecker_NBETerm.Reflect uu____3304
         | FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                  (FStar_Const.Const_reify );
                FStar_Syntax_Syntax.pos = uu____3309;
                FStar_Syntax_Syntax.vars = uu____3310;_},arg::[])
             when
             ((cfg.core_cfg).FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.reify_
             ->
             let cfg1 = reifying_true cfg  in
             translate cfg1 bs (FStar_Pervasives_Native.fst arg)
         | FStar_Syntax_Syntax.Tm_app (head,args) ->
             (debug1
                (fun uu____3389  ->
                   let uu____3390 = FStar_Syntax_Print.term_to_string head
                      in
                   let uu____3392 = FStar_Syntax_Print.args_to_string args
                      in
                   FStar_Util.print2 "Application: %s @ %s\n" uu____3390
                     uu____3392);
              (let uu____3395 = translate cfg bs head  in
               let uu____3396 =
                 FStar_List.map
                   (fun x  ->
                      let uu____3418 =
                        translate cfg bs (FStar_Pervasives_Native.fst x)  in
                      (uu____3418, (FStar_Pervasives_Native.snd x))) args
                  in
               iapp cfg uu____3395 uu____3396))
         | FStar_Syntax_Syntax.Tm_match (scrut,branches) ->
             let make_branches uu____3470 =
               let cfg1 = zeta_false cfg  in
               let rec process_pattern bs1 p =
                 let uu____3501 =
                   match p.FStar_Syntax_Syntax.v with
                   | FStar_Syntax_Syntax.Pat_constant c ->
                       (bs1, (FStar_Syntax_Syntax.Pat_constant c))
                   | FStar_Syntax_Syntax.Pat_cons (fvar,args) ->
                       let uu____3537 =
                         FStar_List.fold_left
                           (fun uu____3578  ->
                              fun uu____3579  ->
                                match (uu____3578, uu____3579) with
                                | ((bs2,args1),(arg,b)) ->
                                    let uu____3671 = process_pattern bs2 arg
                                       in
                                    (match uu____3671 with
                                     | (bs',arg') ->
                                         (bs', ((arg', b) :: args1))))
                           (bs1, []) args
                          in
                       (match uu____3537 with
                        | (bs',args') ->
                            (bs',
                              (FStar_Syntax_Syntax.Pat_cons
                                 (fvar, (FStar_List.rev args')))))
                   | FStar_Syntax_Syntax.Pat_var bvar ->
                       let x =
                         let uu____3770 =
                           let uu____3771 =
                             translate cfg1 bs1 bvar.FStar_Syntax_Syntax.sort
                              in
                           readback cfg1 uu____3771  in
                         FStar_Syntax_Syntax.new_bv
                           FStar_Pervasives_Native.None uu____3770
                          in
                       let uu____3772 =
                         let uu____3775 =
                           FStar_TypeChecker_NBETerm.mkAccuVar x  in
                         uu____3775 :: bs1  in
                       (uu____3772, (FStar_Syntax_Syntax.Pat_var x))
                   | FStar_Syntax_Syntax.Pat_wild bvar ->
                       let x =
                         let uu____3780 =
                           let uu____3781 =
                             translate cfg1 bs1 bvar.FStar_Syntax_Syntax.sort
                              in
                           readback cfg1 uu____3781  in
                         FStar_Syntax_Syntax.new_bv
                           FStar_Pervasives_Native.None uu____3780
                          in
                       let uu____3782 =
                         let uu____3785 =
                           FStar_TypeChecker_NBETerm.mkAccuVar x  in
                         uu____3785 :: bs1  in
                       (uu____3782, (FStar_Syntax_Syntax.Pat_wild x))
                   | FStar_Syntax_Syntax.Pat_dot_term (bvar,tm) ->
                       let x =
                         let uu____3795 =
                           let uu____3796 =
                             translate cfg1 bs1 bvar.FStar_Syntax_Syntax.sort
                              in
                           readback cfg1 uu____3796  in
                         FStar_Syntax_Syntax.new_bv
                           FStar_Pervasives_Native.None uu____3795
                          in
                       let uu____3797 =
                         let uu____3798 =
                           let uu____3805 =
                             let uu____3808 = translate cfg1 bs1 tm  in
                             readback cfg1 uu____3808  in
                           (x, uu____3805)  in
                         FStar_Syntax_Syntax.Pat_dot_term uu____3798  in
                       (bs1, uu____3797)
                    in
                 match uu____3501 with
                 | (bs2,p_new) ->
                     (bs2,
                       (let uu___554_3828 = p  in
                        {
                          FStar_Syntax_Syntax.v = p_new;
                          FStar_Syntax_Syntax.p =
                            (uu___554_3828.FStar_Syntax_Syntax.p)
                        }))
                  in
               FStar_List.map
                 (fun uu____3847  ->
                    match uu____3847 with
                    | (pat,when_clause,e1) ->
                        let uu____3869 = process_pattern bs pat  in
                        (match uu____3869 with
                         | (bs',pat') ->
                             let uu____3882 =
                               let uu____3883 =
                                 let uu____3886 = translate cfg1 bs' e1  in
                                 readback cfg1 uu____3886  in
                               (pat', when_clause, uu____3883)  in
                             FStar_Syntax_Util.branch uu____3882)) branches
                in
             let scrut1 = translate cfg bs scrut  in
             (debug1
                (fun uu____3903  ->
                   let uu____3904 =
                     FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos
                      in
                   let uu____3906 = FStar_Syntax_Print.term_to_string e  in
                   FStar_Util.print2 "%s: Translating match %s\n" uu____3904
                     uu____3906);
              (let scrut2 = unlazy scrut1  in
               match scrut2 with
               | FStar_TypeChecker_NBETerm.Construct (c,us,args) ->
                   (debug1
                      (fun uu____3934  ->
                         let uu____3935 =
                           let uu____3937 =
                             FStar_All.pipe_right args
                               (FStar_List.map
                                  (fun uu____3963  ->
                                     match uu____3963 with
                                     | (x,q) ->
                                         let uu____3977 =
                                           FStar_TypeChecker_NBETerm.t_to_string
                                             x
                                            in
                                         Prims.op_Hat
                                           (if FStar_Util.is_some q
                                            then "#"
                                            else "") uu____3977))
                              in
                           FStar_All.pipe_right uu____3937
                             (FStar_String.concat "; ")
                            in
                         FStar_Util.print1 "Match args: %s\n" uu____3935);
                    (let uu____3991 = pickBranch cfg scrut2 branches  in
                     match uu____3991 with
                     | FStar_Pervasives_Native.Some (branch,args1) ->
                         let uu____4012 =
                           FStar_List.fold_left
                             (fun bs1  -> fun x  -> x :: bs1) bs args1
                            in
                         translate cfg uu____4012 branch
                     | FStar_Pervasives_Native.None  ->
                         FStar_TypeChecker_NBETerm.mkAccuMatch scrut2
                           make_branches))
               | FStar_TypeChecker_NBETerm.Constant c ->
                   (debug1
                      (fun uu____4035  ->
                         let uu____4036 =
                           FStar_TypeChecker_NBETerm.t_to_string scrut2  in
                         FStar_Util.print1 "Match constant : %s\n" uu____4036);
                    (let uu____4039 = pickBranch cfg scrut2 branches  in
                     match uu____4039 with
                     | FStar_Pervasives_Native.Some (branch,[]) ->
                         translate cfg bs branch
                     | FStar_Pervasives_Native.Some (branch,arg::[]) ->
                         translate cfg (arg :: bs) branch
                     | FStar_Pervasives_Native.None  ->
                         FStar_TypeChecker_NBETerm.mkAccuMatch scrut2
                           make_branches
                     | FStar_Pervasives_Native.Some (uu____4073,hd::tl) ->
                         failwith
                           "Impossible: Matching on constants cannot bind more than one variable"))
               | uu____4087 ->
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
             let uu____4132 =
               FStar_TypeChecker_Cfg.should_reduce_local_let cfg.core_cfg lb
                in
             if uu____4132
             then
               let uu____4135 =
                 (((cfg.core_cfg).FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.for_extraction
                    &&
                    (FStar_Syntax_Util.is_unit lb.FStar_Syntax_Syntax.lbtyp))
                   &&
                   (FStar_Syntax_Util.is_pure_or_ghost_effect
                      lb.FStar_Syntax_Syntax.lbeff)
                  in
               (if uu____4135
                then
                  let bs1 =
                    (FStar_TypeChecker_NBETerm.Constant
                       FStar_TypeChecker_NBETerm.Unit)
                    :: bs  in
                  translate cfg bs1 body
                else
                  (let bs1 =
                     let uu____4146 = translate_letbinding cfg bs lb  in
                     uu____4146 :: bs  in
                   translate cfg bs1 body))
             else
               (let def uu____4154 =
                  let uu____4155 =
                    (((cfg.core_cfg).FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.for_extraction
                       &&
                       (FStar_Syntax_Util.is_unit
                          lb.FStar_Syntax_Syntax.lbtyp))
                      &&
                      (FStar_Syntax_Util.is_pure_or_ghost_effect
                         lb.FStar_Syntax_Syntax.lbeff)
                     in
                  if uu____4155
                  then
                    FStar_TypeChecker_NBETerm.Constant
                      FStar_TypeChecker_NBETerm.Unit
                  else translate cfg bs lb.FStar_Syntax_Syntax.lbdef  in
                let typ uu____4165 =
                  translate cfg bs lb.FStar_Syntax_Syntax.lbtyp  in
                let name =
                  let uu____4167 =
                    FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                  FStar_Syntax_Syntax.freshen_bv uu____4167  in
                let bs1 =
                  (FStar_TypeChecker_NBETerm.Accu
                     ((FStar_TypeChecker_NBETerm.Var name), []))
                  :: bs  in
                let body1 uu____4186 = translate cfg bs1 body  in
                let uu____4187 =
                  let uu____4198 =
                    let uu____4199 =
                      let uu____4216 = FStar_Thunk.mk typ  in
                      let uu____4219 = FStar_Thunk.mk def  in
                      let uu____4222 = FStar_Thunk.mk body1  in
                      (name, uu____4216, uu____4219, uu____4222, lb)  in
                    FStar_TypeChecker_NBETerm.UnreducedLet uu____4199  in
                  (uu____4198, [])  in
                FStar_TypeChecker_NBETerm.Accu uu____4187)
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
                      let uu____4268 =
                        FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                      FStar_Syntax_Syntax.freshen_bv uu____4268) lbs
                  in
               let typs =
                 FStar_List.map
                   (fun lb  -> translate cfg bs lb.FStar_Syntax_Syntax.lbtyp)
                   lbs
                  in
               let rec_bs =
                 let uu____4277 =
                   FStar_List.map
                     (fun v  ->
                        FStar_TypeChecker_NBETerm.Accu
                          ((FStar_TypeChecker_NBETerm.Var v), [])) vars
                    in
                 FStar_List.append uu____4277 bs  in
               let defs =
                 FStar_List.map
                   (fun lb  ->
                      translate cfg rec_bs lb.FStar_Syntax_Syntax.lbdef) lbs
                  in
               let body1 = translate cfg rec_bs body  in
               let uu____4298 =
                 let uu____4309 =
                   let uu____4310 =
                     let uu____4327 = FStar_List.zip3 vars typs defs  in
                     (uu____4327, body1, lbs)  in
                   FStar_TypeChecker_NBETerm.UnreducedLetRec uu____4310  in
                 (uu____4309, [])  in
               FStar_TypeChecker_NBETerm.Accu uu____4298
             else
               (let uu____4358 = make_rec_env lbs bs  in
                translate cfg uu____4358 body)
         | FStar_Syntax_Syntax.Tm_meta (e1,uu____4362) -> translate cfg bs e1
         | FStar_Syntax_Syntax.Tm_quoted (qt,qi) ->
             let close t =
               let bvs =
                 FStar_List.map
                   (fun uu____4383  ->
                      FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                        FStar_Syntax_Syntax.tun) bs
                  in
               let s1 =
                 FStar_List.mapi
                   (fun i  -> fun bv  -> FStar_Syntax_Syntax.DB (i, bv)) bvs
                  in
               let s2 =
                 let uu____4396 = FStar_List.zip bvs bs  in
                 FStar_List.map
                   (fun uu____4411  ->
                      match uu____4411 with
                      | (bv,t1) ->
                          let uu____4418 =
                            let uu____4425 = readback cfg t1  in
                            (bv, uu____4425)  in
                          FStar_Syntax_Syntax.NT uu____4418) uu____4396
                  in
               let uu____4430 = FStar_Syntax_Subst.subst s1 t  in
               FStar_Syntax_Subst.subst s2 uu____4430  in
             (match qi.FStar_Syntax_Syntax.qkind with
              | FStar_Syntax_Syntax.Quote_dynamic  ->
                  let qt1 = close qt  in
                  FStar_TypeChecker_NBETerm.Quote (qt1, qi)
              | FStar_Syntax_Syntax.Quote_static  ->
                  let qi1 = FStar_Syntax_Syntax.on_antiquoted close qi  in
                  FStar_TypeChecker_NBETerm.Quote (qt, qi1))
         | FStar_Syntax_Syntax.Tm_lazy li ->
             let f uu____4439 =
               let t = FStar_Syntax_Util.unfold_lazy li  in
               debug1
                 (fun uu____4446  ->
                    let uu____4447 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.print1 ">> Unfolding Tm_lazy to %s\n"
                      uu____4447);
               translate cfg bs t  in
             let uu____4450 =
               let uu____4465 = FStar_Thunk.mk f  in
               ((FStar_Util.Inl li), uu____4465)  in
             FStar_TypeChecker_NBETerm.Lazy uu____4450)

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
            let uu____4497 =
              let uu____4504 = translate cfg bs typ  in
              let uu____4505 = fmap_opt (translate_univ cfg bs) u  in
              (uu____4504, uu____4505)  in
            FStar_TypeChecker_NBETerm.Tot uu____4497
        | FStar_Syntax_Syntax.GTotal (typ,u) ->
            let uu____4520 =
              let uu____4527 = translate cfg bs typ  in
              let uu____4528 = fmap_opt (translate_univ cfg bs) u  in
              (uu____4527, uu____4528)  in
            FStar_TypeChecker_NBETerm.GTot uu____4520
        | FStar_Syntax_Syntax.Comp ctyp ->
            let uu____4534 = translate_comp_typ cfg bs ctyp  in
            FStar_TypeChecker_NBETerm.Comp uu____4534

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
                    let uu____4670 = FStar_List.splitAt m raw_args  in
                    (match uu____4670 with
                     | (uu____4711,raw_args1) -> FStar_Util.Inr raw_args1)
                | FStar_Util.Inl (ctx,xs,rc) ->
                    let uu____4780 = FStar_List.splitAt m xs  in
                    (match uu____4780 with
                     | (uu____4827,xs1) ->
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
                (let uu____4927 = FStar_List.splitAt n args  in
                 match uu____4927 with
                 | (args1,args') ->
                     let uu____4974 =
                       let uu____4975 =
                         map_rev FStar_Pervasives_Native.fst args1  in
                       f1 uu____4975  in
                     iapp cfg uu____4974 args')
        | FStar_TypeChecker_NBETerm.Accu (a,ts) ->
            FStar_TypeChecker_NBETerm.Accu
              (a, (FStar_List.rev_append args ts))
        | FStar_TypeChecker_NBETerm.Construct (i,us,ts) ->
            let rec aux args1 us1 ts1 =
              match args1 with
              | (FStar_TypeChecker_NBETerm.Univ u,uu____5094)::args2 ->
                  aux args2 (u :: us1) ts1
              | a::args2 -> aux args2 us1 (a :: ts1)
              | [] -> (us1, ts1)  in
            let uu____5138 = aux args us ts  in
            (match uu____5138 with
             | (us',ts') -> FStar_TypeChecker_NBETerm.Construct (i, us', ts'))
        | FStar_TypeChecker_NBETerm.FV (i,us,ts) ->
            let rec aux args1 us1 ts1 =
              match args1 with
              | (FStar_TypeChecker_NBETerm.Univ u,uu____5265)::args2 ->
                  aux args2 (u :: us1) ts1
              | a::args2 -> aux args2 us1 (a :: ts1)
              | [] -> (us1, ts1)  in
            let uu____5309 = aux args us ts  in
            (match uu____5309 with
             | (us',ts') -> FStar_TypeChecker_NBETerm.FV (i, us', ts'))
        | FStar_TypeChecker_NBETerm.TopLevelLet (lb,arity,args_rev) ->
            let args_rev1 = FStar_List.rev_append args args_rev  in
            let n_args_rev = FStar_List.length args_rev1  in
            let n_univs = FStar_List.length lb.FStar_Syntax_Syntax.lbunivs
               in
            (debug cfg
               (fun uu____5387  ->
                  let uu____5388 =
                    FStar_Syntax_Print.lbname_to_string
                      lb.FStar_Syntax_Syntax.lbname
                     in
                  let uu____5390 = FStar_Util.string_of_int arity  in
                  let uu____5392 = FStar_Util.string_of_int n_args_rev  in
                  FStar_Util.print3
                    "Reached iapp for %s with arity %s and n_args = %s\n"
                    uu____5388 uu____5390 uu____5392);
             if n_args_rev >= arity
             then
               (let uu____5396 =
                  let uu____5409 =
                    let uu____5410 =
                      FStar_Syntax_Util.unascribe
                        lb.FStar_Syntax_Syntax.lbdef
                       in
                    uu____5410.FStar_Syntax_Syntax.n  in
                  match uu____5409 with
                  | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____5427) ->
                      (bs, body)
                  | uu____5460 -> ([], (lb.FStar_Syntax_Syntax.lbdef))  in
                match uu____5396 with
                | (bs,body) ->
                    if (n_univs + (FStar_List.length bs)) = arity
                    then
                      let uu____5501 =
                        FStar_Util.first_N (n_args_rev - arity) args_rev1  in
                      (match uu____5501 with
                       | (extra,args_rev2) ->
                           (debug cfg
                              (fun uu____5553  ->
                                 let uu____5554 =
                                   FStar_Syntax_Print.lbname_to_string
                                     lb.FStar_Syntax_Syntax.lbname
                                    in
                                 let uu____5556 =
                                   FStar_Syntax_Print.term_to_string body  in
                                 let uu____5558 =
                                   let uu____5560 =
                                     FStar_List.map
                                       (fun uu____5572  ->
                                          match uu____5572 with
                                          | (x,uu____5579) ->
                                              FStar_TypeChecker_NBETerm.t_to_string
                                                x) args_rev2
                                      in
                                   FStar_All.pipe_right uu____5560
                                     (FStar_String.concat ", ")
                                    in
                                 FStar_Util.print3
                                   "Reducing body of %s = %s,\n\twith args = %s\n"
                                   uu____5554 uu____5556 uu____5558);
                            (let t =
                               let uu____5587 =
                                 FStar_List.map FStar_Pervasives_Native.fst
                                   args_rev2
                                  in
                               translate cfg uu____5587 body  in
                             match extra with
                             | [] -> t
                             | uu____5598 ->
                                 iapp cfg t (FStar_List.rev extra))))
                    else
                      (let uu____5611 =
                         FStar_Util.first_N (n_args_rev - n_univs) args_rev1
                          in
                       match uu____5611 with
                       | (extra,univs) ->
                           let uu____5658 =
                             let uu____5659 =
                               FStar_List.map FStar_Pervasives_Native.fst
                                 univs
                                in
                             translate cfg uu____5659
                               lb.FStar_Syntax_Syntax.lbdef
                              in
                           iapp cfg uu____5658 (FStar_List.rev extra)))
             else
               FStar_TypeChecker_NBETerm.TopLevelLet (lb, arity, args_rev1))
        | FStar_TypeChecker_NBETerm.TopLevelRec
            (lb,arity,decreases_list,args') ->
            let args1 = FStar_List.append args' args  in
            if (FStar_List.length args1) >= arity
            then
              let uu____5719 =
                should_reduce_recursive_definition args1 decreases_list  in
              (match uu____5719 with
               | (should_reduce,uu____5728,uu____5729) ->
                   if Prims.op_Negation should_reduce
                   then
                     let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname
                        in
                     (debug cfg
                        (fun uu____5737  ->
                           let uu____5738 =
                             FStar_Syntax_Print.fv_to_string fv  in
                           FStar_Util.print1
                             "Decided to not unfold recursive definition %s\n"
                             uu____5738);
                      iapp cfg (FStar_TypeChecker_NBETerm.FV (fv, [], []))
                        args1)
                   else
                     (debug cfg
                        (fun uu____5758  ->
                           let uu____5759 =
                             let uu____5761 =
                               FStar_Util.right lb.FStar_Syntax_Syntax.lbname
                                in
                             FStar_Syntax_Print.fv_to_string uu____5761  in
                           FStar_Util.print1
                             "Yes, Decided to unfold recursive definition %s\n"
                             uu____5759);
                      (let uu____5763 =
                         FStar_Util.first_N
                           (FStar_List.length lb.FStar_Syntax_Syntax.lbunivs)
                           args1
                          in
                       match uu____5763 with
                       | (univs,rest) ->
                           let uu____5810 =
                             let uu____5811 =
                               let uu____5814 =
                                 FStar_List.map FStar_Pervasives_Native.fst
                                   univs
                                  in
                               FStar_List.rev uu____5814  in
                             translate cfg uu____5811
                               lb.FStar_Syntax_Syntax.lbdef
                              in
                           iapp cfg uu____5810 rest)))
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
                  let uu____5932 =
                    should_reduce_recursive_definition args1 decreases_list
                     in
                  match uu____5932 with
                  | (should_reduce,uu____5941,uu____5942) ->
                      if Prims.op_Negation should_reduce
                      then
                        FStar_TypeChecker_NBETerm.LocalLetRec
                          (i, lb, mutual_lbs, local_env, args1,
                            Prims.int_zero, decreases_list)
                      else
                        (let env = make_rec_env mutual_lbs local_env  in
                         debug cfg
                           (fun uu____5971  ->
                              (let uu____5973 =
                                 let uu____5975 =
                                   FStar_List.map
                                     FStar_TypeChecker_NBETerm.t_to_string
                                     env
                                    in
                                 FStar_String.concat ",\n\t " uu____5975  in
                               FStar_Util.print1
                                 "LocalLetRec Env = {\n\t%s\n}\n" uu____5973);
                              (let uu____5982 =
                                 let uu____5984 =
                                   FStar_List.map
                                     (fun uu____5996  ->
                                        match uu____5996 with
                                        | (t,uu____6003) ->
                                            FStar_TypeChecker_NBETerm.t_to_string
                                              t) args1
                                    in
                                 FStar_String.concat ",\n\t " uu____5984  in
                               FStar_Util.print1
                                 "LocalLetRec Args = {\n\t%s\n}\n" uu____5982));
                         (let uu____6006 =
                            translate cfg env lb.FStar_Syntax_Syntax.lbdef
                             in
                          iapp cfg uu____6006 args1))))
        | uu____6007 ->
            let uu____6008 =
              let uu____6010 = FStar_TypeChecker_NBETerm.t_to_string f  in
              Prims.op_Hat "NBE ill-typed application: " uu____6010  in
            failwith uu____6008

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
          let uu____6027 = FStar_TypeChecker_Cfg.cfg_env cfg.core_cfg  in
          let uu____6028 = FStar_Syntax_Syntax.lid_of_fv fvar  in
          FStar_TypeChecker_Env.lookup_qname uu____6027 uu____6028  in
        let uu____6029 = (is_constr qninfo) || (is_constr_fv fvar)  in
        if uu____6029
        then FStar_TypeChecker_NBETerm.mkConstruct fvar [] []
        else
          (let uu____6038 =
             FStar_TypeChecker_Normalize.should_unfold cfg.core_cfg
               (fun uu____6040  ->
                  (cfg.core_cfg).FStar_TypeChecker_Cfg.reifying) fvar qninfo
              in
           match uu____6038 with
           | FStar_TypeChecker_Normalize.Should_unfold_fully  ->
               failwith "Not yet handled"
           | FStar_TypeChecker_Normalize.Should_unfold_no  ->
               (debug1
                  (fun uu____6047  ->
                     let uu____6048 = FStar_Syntax_Print.fv_to_string fvar
                        in
                     FStar_Util.print1 "(1) Decided to not unfold %s\n"
                       uu____6048);
                (let uu____6051 =
                   FStar_TypeChecker_Cfg.find_prim_step cfg.core_cfg fvar  in
                 match uu____6051 with
                 | FStar_Pervasives_Native.Some prim_step when
                     prim_step.FStar_TypeChecker_Cfg.strong_reduction_ok ->
                     let arity =
                       prim_step.FStar_TypeChecker_Cfg.arity +
                         prim_step.FStar_TypeChecker_Cfg.univ_arity
                        in
                     (debug1
                        (fun uu____6062  ->
                           let uu____6063 =
                             FStar_Syntax_Print.fv_to_string fvar  in
                           FStar_Util.print1 "Found a primop %s\n" uu____6063);
                      (let uu____6066 =
                         let uu____6099 =
                           let f uu____6132 =
                             let uu____6134 =
                               FStar_Syntax_Syntax.new_bv
                                 FStar_Pervasives_Native.None
                                 FStar_Syntax_Syntax.t_unit
                                in
                             (uu____6134, FStar_Pervasives_Native.None)  in
                           let uu____6137 =
                             let uu____6148 = FStar_Common.tabulate arity f
                                in
                             ([], uu____6148, FStar_Pervasives_Native.None)
                              in
                           FStar_Util.Inl uu____6137  in
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
                             let uu____6222 =
                               prim_step.FStar_TypeChecker_Cfg.interpretation_nbe
                                 callbacks args'
                                in
                             match uu____6222 with
                             | FStar_Pervasives_Native.Some x ->
                                 (debug1
                                    (fun uu____6233  ->
                                       let uu____6234 =
                                         FStar_Syntax_Print.fv_to_string fvar
                                          in
                                       let uu____6236 =
                                         FStar_TypeChecker_NBETerm.t_to_string
                                           x
                                          in
                                       FStar_Util.print2
                                         "Primitive operator %s returned %s\n"
                                         uu____6234 uu____6236);
                                  x)
                             | FStar_Pervasives_Native.None  ->
                                 (debug1
                                    (fun uu____6244  ->
                                       let uu____6245 =
                                         FStar_Syntax_Print.fv_to_string fvar
                                          in
                                       FStar_Util.print1
                                         "Primitive operator %s failed\n"
                                         uu____6245);
                                  (let uu____6248 =
                                     FStar_TypeChecker_NBETerm.mkFV fvar []
                                       []
                                      in
                                   iapp cfg uu____6248 args'))), uu____6099,
                           arity)
                          in
                       FStar_TypeChecker_NBETerm.Lam uu____6066))
                 | FStar_Pervasives_Native.Some uu____6253 ->
                     (debug1
                        (fun uu____6259  ->
                           let uu____6260 =
                             FStar_Syntax_Print.fv_to_string fvar  in
                           FStar_Util.print1 "(2) Decided to not unfold %s\n"
                             uu____6260);
                      FStar_TypeChecker_NBETerm.mkFV fvar [] [])
                 | uu____6267 ->
                     (debug1
                        (fun uu____6275  ->
                           let uu____6276 =
                             FStar_Syntax_Print.fv_to_string fvar  in
                           FStar_Util.print1 "(3) Decided to not unfold %s\n"
                             uu____6276);
                      FStar_TypeChecker_NBETerm.mkFV fvar [] [])))
           | FStar_TypeChecker_Normalize.Should_unfold_reify  ->
               let t =
                 let is_qninfo_visible =
                   let uu____6286 =
                     FStar_TypeChecker_Env.lookup_definition_qninfo
                       (cfg.core_cfg).FStar_TypeChecker_Cfg.delta_level
                       (fvar.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                       qninfo
                      in
                   FStar_Option.isSome uu____6286  in
                 if is_qninfo_visible
                 then
                   match qninfo with
                   | FStar_Pervasives_Native.Some
                       (FStar_Util.Inr
                        ({
                           FStar_Syntax_Syntax.sigel =
                             FStar_Syntax_Syntax.Sig_let ((is_rec,lbs),names);
                           FStar_Syntax_Syntax.sigrng = uu____6301;
                           FStar_Syntax_Syntax.sigquals = uu____6302;
                           FStar_Syntax_Syntax.sigmeta = uu____6303;
                           FStar_Syntax_Syntax.sigattrs = uu____6304;
                           FStar_Syntax_Syntax.sigopts = uu____6305;_},_us_opt),_rng)
                       ->
                       (debug1
                          (fun uu____6375  ->
                             let uu____6376 =
                               FStar_Syntax_Print.fv_to_string fvar  in
                             FStar_Util.print1 "(1) Decided to unfold %s\n"
                               uu____6376);
                        (let lbm = find_let lbs fvar  in
                         match lbm with
                         | FStar_Pervasives_Native.Some lb ->
                             if
                               is_rec &&
                                 ((cfg.core_cfg).FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta
                             then
                               let uu____6384 = let_rec_arity lb  in
                               (match uu____6384 with
                                | (ar,lst) ->
                                    FStar_TypeChecker_NBETerm.TopLevelRec
                                      (lb, ar, lst, []))
                             else translate_letbinding cfg bs lb
                         | FStar_Pervasives_Native.None  ->
                             failwith "Could not find let binding"))
                   | uu____6420 ->
                       (debug1
                          (fun uu____6426  ->
                             let uu____6427 =
                               FStar_Syntax_Print.fv_to_string fvar  in
                             FStar_Util.print1
                               "(1) qninfo is None for (%s)\n" uu____6427);
                        FStar_TypeChecker_NBETerm.mkFV fvar [] [])
                 else
                   (debug1
                      (fun uu____6441  ->
                         let uu____6442 =
                           FStar_Syntax_Print.fv_to_string fvar  in
                         FStar_Util.print1
                           "(1) qninfo is not visible at this level (%s)\n"
                           uu____6442);
                    FStar_TypeChecker_NBETerm.mkFV fvar [] [])
                  in
               (cache_add cfg fvar t; t)
           | FStar_TypeChecker_Normalize.Should_unfold_yes  ->
               let t =
                 let is_qninfo_visible =
                   let uu____6453 =
                     FStar_TypeChecker_Env.lookup_definition_qninfo
                       (cfg.core_cfg).FStar_TypeChecker_Cfg.delta_level
                       (fvar.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                       qninfo
                      in
                   FStar_Option.isSome uu____6453  in
                 if is_qninfo_visible
                 then
                   match qninfo with
                   | FStar_Pervasives_Native.Some
                       (FStar_Util.Inr
                        ({
                           FStar_Syntax_Syntax.sigel =
                             FStar_Syntax_Syntax.Sig_let ((is_rec,lbs),names);
                           FStar_Syntax_Syntax.sigrng = uu____6468;
                           FStar_Syntax_Syntax.sigquals = uu____6469;
                           FStar_Syntax_Syntax.sigmeta = uu____6470;
                           FStar_Syntax_Syntax.sigattrs = uu____6471;
                           FStar_Syntax_Syntax.sigopts = uu____6472;_},_us_opt),_rng)
                       ->
                       (debug1
                          (fun uu____6542  ->
                             let uu____6543 =
                               FStar_Syntax_Print.fv_to_string fvar  in
                             FStar_Util.print1 "(1) Decided to unfold %s\n"
                               uu____6543);
                        (let lbm = find_let lbs fvar  in
                         match lbm with
                         | FStar_Pervasives_Native.Some lb ->
                             if
                               is_rec &&
                                 ((cfg.core_cfg).FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta
                             then
                               let uu____6551 = let_rec_arity lb  in
                               (match uu____6551 with
                                | (ar,lst) ->
                                    FStar_TypeChecker_NBETerm.TopLevelRec
                                      (lb, ar, lst, []))
                             else translate_letbinding cfg bs lb
                         | FStar_Pervasives_Native.None  ->
                             failwith "Could not find let binding"))
                   | uu____6587 ->
                       (debug1
                          (fun uu____6593  ->
                             let uu____6594 =
                               FStar_Syntax_Print.fv_to_string fvar  in
                             FStar_Util.print1
                               "(1) qninfo is None for (%s)\n" uu____6594);
                        FStar_TypeChecker_NBETerm.mkFV fvar [] [])
                 else
                   (debug1
                      (fun uu____6608  ->
                         let uu____6609 =
                           FStar_Syntax_Print.fv_to_string fvar  in
                         FStar_Util.print1
                           "(1) qninfo is not visible at this level (%s)\n"
                           uu____6609);
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
        let uu____6633 =
          FStar_Syntax_Util.arrow_formals lb.FStar_Syntax_Syntax.lbtyp  in
        match uu____6633 with
        | (formals,uu____6641) ->
            let arity = (FStar_List.length us) + (FStar_List.length formals)
               in
            if arity = Prims.int_zero
            then translate cfg bs lb.FStar_Syntax_Syntax.lbdef
            else
              (let uu____6659 =
                 FStar_Util.is_right lb.FStar_Syntax_Syntax.lbname  in
               if uu____6659
               then
                 (debug1
                    (fun uu____6669  ->
                       let uu____6670 =
                         FStar_Syntax_Print.lbname_to_string
                           lb.FStar_Syntax_Syntax.lbname
                          in
                       let uu____6672 = FStar_Util.string_of_int arity  in
                       FStar_Util.print2
                         "Making TopLevelLet for %s with arity %s\n"
                         uu____6670 uu____6672);
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
          let uu____6697 = let_rec_arity b  in
          match uu____6697 with
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
        let uu____6767 = FStar_BigInt.big_int_of_string s  in
        FStar_TypeChecker_NBETerm.Int uu____6767
    | FStar_Const.Const_string (s,r) ->
        FStar_TypeChecker_NBETerm.String (s, r)
    | FStar_Const.Const_char c1 -> FStar_TypeChecker_NBETerm.Char c1
    | FStar_Const.Const_range r -> FStar_TypeChecker_NBETerm.Range r
    | uu____6776 -> FStar_TypeChecker_NBETerm.SConst c

and (readback_comp :
  config -> FStar_TypeChecker_NBETerm.comp -> FStar_Syntax_Syntax.comp) =
  fun cfg  ->
    fun c  ->
      let c' =
        match c with
        | FStar_TypeChecker_NBETerm.Tot (typ,u) ->
            let uu____6786 =
              let uu____6795 = readback cfg typ  in (uu____6795, u)  in
            FStar_Syntax_Syntax.Total uu____6786
        | FStar_TypeChecker_NBETerm.GTot (typ,u) ->
            let uu____6808 =
              let uu____6817 = readback cfg typ  in (uu____6817, u)  in
            FStar_Syntax_Syntax.GTotal uu____6808
        | FStar_TypeChecker_NBETerm.Comp ctyp ->
            let uu____6825 = readback_comp_typ cfg ctyp  in
            FStar_Syntax_Syntax.Comp uu____6825
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
        let uu____6831 = c  in
        match uu____6831 with
        | { FStar_Syntax_Syntax.comp_univs = comp_univs;
            FStar_Syntax_Syntax.effect_name = effect_name;
            FStar_Syntax_Syntax.result_typ = result_typ;
            FStar_Syntax_Syntax.effect_args = effect_args;
            FStar_Syntax_Syntax.flags = flags;_} ->
            let uu____6851 =
              FStar_List.map (translate_univ cfg bs) comp_univs  in
            let uu____6852 = translate cfg bs result_typ  in
            let uu____6853 =
              FStar_List.map
                (fun x  ->
                   let uu____6881 =
                     translate cfg bs (FStar_Pervasives_Native.fst x)  in
                   (uu____6881, (FStar_Pervasives_Native.snd x))) effect_args
               in
            let uu____6888 = FStar_List.map (translate_flag cfg bs) flags  in
            {
              FStar_TypeChecker_NBETerm.comp_univs = uu____6851;
              FStar_TypeChecker_NBETerm.effect_name = effect_name;
              FStar_TypeChecker_NBETerm.result_typ = uu____6852;
              FStar_TypeChecker_NBETerm.effect_args = uu____6853;
              FStar_TypeChecker_NBETerm.flags = uu____6888
            }

and (readback_comp_typ :
  config ->
    FStar_TypeChecker_NBETerm.comp_typ -> FStar_Syntax_Syntax.comp_typ)
  =
  fun cfg  ->
    fun c  ->
      let uu____6893 = readback cfg c.FStar_TypeChecker_NBETerm.result_typ
         in
      let uu____6896 =
        FStar_List.map
          (fun x  ->
             let uu____6922 = readback cfg (FStar_Pervasives_Native.fst x)
                in
             (uu____6922, (FStar_Pervasives_Native.snd x)))
          c.FStar_TypeChecker_NBETerm.effect_args
         in
      let uu____6923 =
        FStar_List.map (readback_flag cfg) c.FStar_TypeChecker_NBETerm.flags
         in
      {
        FStar_Syntax_Syntax.comp_univs =
          (c.FStar_TypeChecker_NBETerm.comp_univs);
        FStar_Syntax_Syntax.effect_name =
          (c.FStar_TypeChecker_NBETerm.effect_name);
        FStar_Syntax_Syntax.result_typ = uu____6893;
        FStar_Syntax_Syntax.effect_args = uu____6896;
        FStar_Syntax_Syntax.flags = uu____6923
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
        let uu____6931 = c  in
        match uu____6931 with
        | { FStar_Syntax_Syntax.residual_effect = residual_effect;
            FStar_Syntax_Syntax.residual_typ = residual_typ;
            FStar_Syntax_Syntax.residual_flags = residual_flags;_} ->
            let uu____6941 =
              if
                ((cfg.core_cfg).FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.for_extraction
              then FStar_Pervasives_Native.None
              else FStar_Util.map_opt residual_typ (translate cfg bs)  in
            let uu____6951 =
              FStar_List.map (translate_flag cfg bs) residual_flags  in
            {
              FStar_TypeChecker_NBETerm.residual_effect = residual_effect;
              FStar_TypeChecker_NBETerm.residual_typ = uu____6941;
              FStar_TypeChecker_NBETerm.residual_flags = uu____6951
            }

and (readback_residual_comp :
  config ->
    FStar_TypeChecker_NBETerm.residual_comp ->
      FStar_Syntax_Syntax.residual_comp)
  =
  fun cfg  ->
    fun c  ->
      let uu____6956 =
        FStar_Util.map_opt c.FStar_TypeChecker_NBETerm.residual_typ
          (fun x  ->
             debug cfg
               (fun uu____6967  ->
                  let uu____6968 = FStar_TypeChecker_NBETerm.t_to_string x
                     in
                  FStar_Util.print1 "Reading back residualtype %s\n"
                    uu____6968);
             readback cfg x)
         in
      let uu____6971 =
        FStar_List.map (readback_flag cfg)
          c.FStar_TypeChecker_NBETerm.residual_flags
         in
      {
        FStar_Syntax_Syntax.residual_effect =
          (c.FStar_TypeChecker_NBETerm.residual_effect);
        FStar_Syntax_Syntax.residual_typ = uu____6956;
        FStar_Syntax_Syntax.residual_flags = uu____6971
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
            let uu____6982 = translate cfg bs tm  in
            FStar_TypeChecker_NBETerm.DECREASES uu____6982

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
          let uu____6986 = readback cfg t  in
          FStar_Syntax_Syntax.DECREASES uu____6986

and (translate_monadic :
  (FStar_Syntax_Syntax.monad_name * FStar_Syntax_Syntax.term'
    FStar_Syntax_Syntax.syntax) ->
    config ->
      FStar_TypeChecker_NBETerm.t Prims.list ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
          FStar_TypeChecker_NBETerm.t)
  =
  fun uu____6989  ->
    fun cfg  ->
      fun bs  ->
        fun e  ->
          match uu____6989 with
          | (m,ty) ->
              let e1 = FStar_Syntax_Util.unascribe e  in
              (match e1.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                   let uu____7027 =
                     let uu____7036 =
                       FStar_TypeChecker_Env.norm_eff_name
                         (cfg.core_cfg).FStar_TypeChecker_Cfg.tcenv m
                        in
                     FStar_TypeChecker_Env.effect_decl_opt
                       (cfg.core_cfg).FStar_TypeChecker_Cfg.tcenv uu____7036
                      in
                   (match uu____7027 with
                    | FStar_Pervasives_Native.None  ->
                        let uu____7043 =
                          let uu____7045 = FStar_Ident.string_of_lid m  in
                          FStar_Util.format1
                            "Effect declaration not found: %s" uu____7045
                           in
                        failwith uu____7043
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
                          let uu____7067 =
                            let uu____7074 =
                              let uu____7075 =
                                let uu____7094 =
                                  let uu____7103 =
                                    let uu____7110 =
                                      FStar_Util.left
                                        lb.FStar_Syntax_Syntax.lbname
                                       in
                                    (uu____7110,
                                      FStar_Pervasives_Native.None)
                                     in
                                  [uu____7103]  in
                                (uu____7094, body,
                                  (FStar_Pervasives_Native.Some body_rc))
                                 in
                              FStar_Syntax_Syntax.Tm_abs uu____7075  in
                            FStar_Syntax_Syntax.mk uu____7074  in
                          uu____7067 FStar_Pervasives_Native.None
                            body.FStar_Syntax_Syntax.pos
                           in
                        let maybe_range_arg =
                          let uu____7144 =
                            FStar_Util.for_some
                              (FStar_Syntax_Util.attr_eq
                                 FStar_Syntax_Util.dm4f_bind_range_attr)
                              ed.FStar_Syntax_Syntax.eff_attrs
                             in
                          if uu____7144
                          then
                            let uu____7153 =
                              let uu____7158 =
                                let uu____7159 =
                                  FStar_TypeChecker_Cfg.embed_simple
                                    FStar_Syntax_Embeddings.e_range
                                    lb.FStar_Syntax_Syntax.lbpos
                                    lb.FStar_Syntax_Syntax.lbpos
                                   in
                                translate cfg [] uu____7159  in
                              (uu____7158, FStar_Pervasives_Native.None)  in
                            let uu____7160 =
                              let uu____7167 =
                                let uu____7172 =
                                  let uu____7173 =
                                    FStar_TypeChecker_Cfg.embed_simple
                                      FStar_Syntax_Embeddings.e_range
                                      body.FStar_Syntax_Syntax.pos
                                      body.FStar_Syntax_Syntax.pos
                                     in
                                  translate cfg [] uu____7173  in
                                (uu____7172, FStar_Pervasives_Native.None)
                                 in
                              [uu____7167]  in
                            uu____7153 :: uu____7160
                          else []  in
                        let t =
                          let uu____7193 =
                            let uu____7194 =
                              let uu____7195 =
                                let uu____7196 =
                                  let uu____7197 =
                                    let uu____7204 =
                                      FStar_All.pipe_right ed
                                        FStar_Syntax_Util.get_bind_repr
                                       in
                                    FStar_All.pipe_right uu____7204
                                      FStar_Util.must
                                     in
                                  FStar_All.pipe_right uu____7197
                                    FStar_Pervasives_Native.snd
                                   in
                                FStar_Syntax_Util.un_uinst uu____7196  in
                              translate cfg' [] uu____7195  in
                            iapp cfg uu____7194
                              [((FStar_TypeChecker_NBETerm.Univ
                                   FStar_Syntax_Syntax.U_unknown),
                                 FStar_Pervasives_Native.None);
                              ((FStar_TypeChecker_NBETerm.Univ
                                  FStar_Syntax_Syntax.U_unknown),
                                FStar_Pervasives_Native.None)]
                             in
                          let uu____7237 =
                            let uu____7238 =
                              let uu____7245 =
                                let uu____7250 =
                                  translate cfg' bs
                                    lb.FStar_Syntax_Syntax.lbtyp
                                   in
                                (uu____7250, FStar_Pervasives_Native.None)
                                 in
                              let uu____7251 =
                                let uu____7258 =
                                  let uu____7263 = translate cfg' bs ty  in
                                  (uu____7263, FStar_Pervasives_Native.None)
                                   in
                                [uu____7258]  in
                              uu____7245 :: uu____7251  in
                            let uu____7276 =
                              let uu____7283 =
                                let uu____7290 =
                                  let uu____7297 =
                                    let uu____7302 =
                                      translate cfg bs
                                        lb.FStar_Syntax_Syntax.lbdef
                                       in
                                    (uu____7302,
                                      FStar_Pervasives_Native.None)
                                     in
                                  let uu____7303 =
                                    let uu____7310 =
                                      let uu____7317 =
                                        let uu____7322 =
                                          translate cfg bs body_lam  in
                                        (uu____7322,
                                          FStar_Pervasives_Native.None)
                                         in
                                      [uu____7317]  in
                                    (FStar_TypeChecker_NBETerm.Unknown,
                                      FStar_Pervasives_Native.None) ::
                                      uu____7310
                                     in
                                  uu____7297 :: uu____7303  in
                                (FStar_TypeChecker_NBETerm.Unknown,
                                  FStar_Pervasives_Native.None) :: uu____7290
                                 in
                              FStar_List.append maybe_range_arg uu____7283
                               in
                            FStar_List.append uu____7238 uu____7276  in
                          iapp cfg uu____7193 uu____7237  in
                        (debug cfg
                           (fun uu____7354  ->
                              let uu____7355 =
                                FStar_TypeChecker_NBETerm.t_to_string t  in
                              FStar_Util.print1 "translate_monadic: %s\n"
                                uu____7355);
                         t))
               | FStar_Syntax_Syntax.Tm_app
                   ({
                      FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                        (FStar_Const.Const_reflect uu____7358);
                      FStar_Syntax_Syntax.pos = uu____7359;
                      FStar_Syntax_Syntax.vars = uu____7360;_},(e2,uu____7362)::[])
                   ->
                   let uu____7401 = reifying_false cfg  in
                   translate uu____7401 bs e2
               | FStar_Syntax_Syntax.Tm_app (head,args) ->
                   (debug cfg
                      (fun uu____7432  ->
                         let uu____7433 =
                           FStar_Syntax_Print.term_to_string head  in
                         let uu____7435 =
                           FStar_Syntax_Print.args_to_string args  in
                         FStar_Util.print2
                           "translate_monadic app (%s) @ (%s)\n" uu____7433
                           uu____7435);
                    (let fallback1 uu____7443 = translate cfg bs e1  in
                     let fallback2 uu____7449 =
                       let uu____7450 = reifying_false cfg  in
                       let uu____7451 =
                         FStar_Syntax_Syntax.mk
                           (FStar_Syntax_Syntax.Tm_meta
                              (e1,
                                (FStar_Syntax_Syntax.Meta_monadic (m, ty))))
                           FStar_Pervasives_Native.None
                           e1.FStar_Syntax_Syntax.pos
                          in
                       translate uu____7450 bs uu____7451  in
                     let uu____7456 =
                       let uu____7457 = FStar_Syntax_Util.un_uinst head  in
                       uu____7457.FStar_Syntax_Syntax.n  in
                     match uu____7456 with
                     | FStar_Syntax_Syntax.Tm_fvar fv ->
                         let lid = FStar_Syntax_Syntax.lid_of_fv fv  in
                         let qninfo =
                           FStar_TypeChecker_Env.lookup_qname
                             (cfg.core_cfg).FStar_TypeChecker_Cfg.tcenv lid
                            in
                         let uu____7463 =
                           let uu____7465 =
                             FStar_TypeChecker_Env.is_action
                               (cfg.core_cfg).FStar_TypeChecker_Cfg.tcenv lid
                              in
                           Prims.op_Negation uu____7465  in
                         if uu____7463
                         then fallback1 ()
                         else
                           (let uu____7470 =
                              let uu____7472 =
                                FStar_TypeChecker_Env.lookup_definition_qninfo
                                  (cfg.core_cfg).FStar_TypeChecker_Cfg.delta_level
                                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                  qninfo
                                 in
                              FStar_Option.isNone uu____7472  in
                            if uu____7470
                            then fallback2 ()
                            else
                              (let e2 =
                                 let uu____7489 =
                                   let uu____7494 =
                                     FStar_Syntax_Util.mk_reify head  in
                                   FStar_Syntax_Syntax.mk_Tm_app uu____7494
                                     args
                                    in
                                 uu____7489 FStar_Pervasives_Native.None
                                   e1.FStar_Syntax_Syntax.pos
                                  in
                               let uu____7495 = reifying_false cfg  in
                               translate uu____7495 bs e2))
                     | uu____7496 -> fallback1 ()))
               | FStar_Syntax_Syntax.Tm_match (sc,branches) ->
                   let branches1 =
                     FStar_All.pipe_right branches
                       (FStar_List.map
                          (fun uu____7617  ->
                             match uu____7617 with
                             | (pat,wopt,tm) ->
                                 let uu____7665 =
                                   FStar_Syntax_Util.mk_reify tm  in
                                 (pat, wopt, uu____7665)))
                      in
                   let tm =
                     FStar_Syntax_Syntax.mk
                       (FStar_Syntax_Syntax.Tm_match (sc, branches1))
                       FStar_Pervasives_Native.None
                       e1.FStar_Syntax_Syntax.pos
                      in
                   let uu____7697 = reifying_false cfg  in
                   translate uu____7697 bs tm
               | FStar_Syntax_Syntax.Tm_meta
                   (t,FStar_Syntax_Syntax.Meta_monadic uu____7699) ->
                   translate_monadic (m, ty) cfg bs e1
               | FStar_Syntax_Syntax.Tm_meta
                   (t,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,ty'))
                   -> translate_monadic_lift (msrc, mtgt, ty') cfg bs e1
               | uu____7726 ->
                   let uu____7727 =
                     let uu____7729 = FStar_Syntax_Print.tag_of_term e1  in
                     FStar_Util.format1
                       "Unexpected case in translate_monadic: %s" uu____7729
                      in
                   failwith uu____7727)

and (translate_monadic_lift :
  (FStar_Syntax_Syntax.monad_name * FStar_Syntax_Syntax.monad_name *
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax) ->
    config ->
      FStar_TypeChecker_NBETerm.t Prims.list ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
          FStar_TypeChecker_NBETerm.t)
  =
  fun uu____7732  ->
    fun cfg  ->
      fun bs  ->
        fun e  ->
          match uu____7732 with
          | (msrc,mtgt,ty) ->
              let e1 = FStar_Syntax_Util.unascribe e  in
              let uu____7756 =
                (FStar_Syntax_Util.is_pure_effect msrc) ||
                  (FStar_Syntax_Util.is_div_effect msrc)
                 in
              if uu____7756
              then
                let ed =
                  let uu____7760 =
                    FStar_TypeChecker_Env.norm_eff_name
                      (cfg.core_cfg).FStar_TypeChecker_Cfg.tcenv mtgt
                     in
                  FStar_TypeChecker_Env.get_effect_decl
                    (cfg.core_cfg).FStar_TypeChecker_Cfg.tcenv uu____7760
                   in
                let ret =
                  let uu____7762 =
                    let uu____7763 =
                      let uu____7766 =
                        let uu____7767 =
                          let uu____7774 =
                            FStar_All.pipe_right ed
                              FStar_Syntax_Util.get_return_repr
                             in
                          FStar_All.pipe_right uu____7774 FStar_Util.must  in
                        FStar_All.pipe_right uu____7767
                          FStar_Pervasives_Native.snd
                         in
                      FStar_Syntax_Subst.compress uu____7766  in
                    uu____7763.FStar_Syntax_Syntax.n  in
                  match uu____7762 with
                  | FStar_Syntax_Syntax.Tm_uinst (ret,uu____7820::[]) ->
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_uinst
                           (ret, [FStar_Syntax_Syntax.U_unknown]))
                        FStar_Pervasives_Native.None
                        e1.FStar_Syntax_Syntax.pos
                  | uu____7827 ->
                      failwith "NYI: Reification of indexed effect (NBE)"
                   in
                let cfg' = reifying_false cfg  in
                let t =
                  let uu____7831 =
                    let uu____7832 = translate cfg' [] ret  in
                    iapp cfg' uu____7832
                      [((FStar_TypeChecker_NBETerm.Univ
                           FStar_Syntax_Syntax.U_unknown),
                         FStar_Pervasives_Native.None)]
                     in
                  let uu____7841 =
                    let uu____7842 =
                      let uu____7847 = translate cfg' bs ty  in
                      (uu____7847, FStar_Pervasives_Native.None)  in
                    let uu____7848 =
                      let uu____7855 =
                        let uu____7860 = translate cfg' bs e1  in
                        (uu____7860, FStar_Pervasives_Native.None)  in
                      [uu____7855]  in
                    uu____7842 :: uu____7848  in
                  iapp cfg' uu____7831 uu____7841  in
                (debug cfg
                   (fun uu____7876  ->
                      let uu____7877 =
                        FStar_TypeChecker_NBETerm.t_to_string t  in
                      FStar_Util.print1 "translate_monadic_lift(1): %s\n"
                        uu____7877);
                 t)
              else
                (let uu____7882 =
                   FStar_TypeChecker_Env.monad_leq
                     (cfg.core_cfg).FStar_TypeChecker_Cfg.tcenv msrc mtgt
                    in
                 match uu____7882 with
                 | FStar_Pervasives_Native.None  ->
                     let uu____7885 =
                       let uu____7887 = FStar_Ident.string_of_lid msrc  in
                       let uu____7889 = FStar_Ident.string_of_lid mtgt  in
                       FStar_Util.format2
                         "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                         uu____7887 uu____7889
                        in
                     failwith uu____7885
                 | FStar_Pervasives_Native.Some
                     { FStar_TypeChecker_Env.msource = uu____7892;
                       FStar_TypeChecker_Env.mtarget = uu____7893;
                       FStar_TypeChecker_Env.mlift =
                         { FStar_TypeChecker_Env.mlift_wp = uu____7894;
                           FStar_TypeChecker_Env.mlift_term =
                             FStar_Pervasives_Native.None ;_};_}
                     ->
                     let uu____7914 =
                       let uu____7916 = FStar_Ident.string_of_lid msrc  in
                       let uu____7918 = FStar_Ident.string_of_lid mtgt  in
                       FStar_Util.format2
                         "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
                         uu____7916 uu____7918
                        in
                     failwith uu____7914
                 | FStar_Pervasives_Native.Some
                     { FStar_TypeChecker_Env.msource = uu____7921;
                       FStar_TypeChecker_Env.mtarget = uu____7922;
                       FStar_TypeChecker_Env.mlift =
                         { FStar_TypeChecker_Env.mlift_wp = uu____7923;
                           FStar_TypeChecker_Env.mlift_term =
                             FStar_Pervasives_Native.Some lift;_};_}
                     ->
                     let lift_lam =
                       let x =
                         FStar_Syntax_Syntax.new_bv
                           FStar_Pervasives_Native.None
                           FStar_Syntax_Syntax.tun
                          in
                       let uu____7957 =
                         let uu____7960 = FStar_Syntax_Syntax.bv_to_name x
                            in
                         lift FStar_Syntax_Syntax.U_unknown ty uu____7960  in
                       FStar_Syntax_Util.abs
                         [(x, FStar_Pervasives_Native.None)] uu____7957
                         FStar_Pervasives_Native.None
                        in
                     let cfg' = reifying_false cfg  in
                     let t =
                       let uu____7977 = translate cfg' [] lift_lam  in
                       let uu____7978 =
                         let uu____7979 =
                           let uu____7984 = translate cfg bs e1  in
                           (uu____7984, FStar_Pervasives_Native.None)  in
                         [uu____7979]  in
                       iapp cfg uu____7977 uu____7978  in
                     (debug cfg
                        (fun uu____7996  ->
                           let uu____7997 =
                             FStar_TypeChecker_NBETerm.t_to_string t  in
                           FStar_Util.print1
                             "translate_monadic_lift(2): %s\n" uu____7997);
                      t))

and (readback :
  config -> FStar_TypeChecker_NBETerm.t -> FStar_Syntax_Syntax.term) =
  fun cfg  ->
    fun x  ->
      let debug1 = debug cfg  in
      let readback_args cfg1 args =
        map_rev
          (fun uu____8051  ->
             match uu____8051 with
             | (x1,q) ->
                 let uu____8062 = readback cfg1 x1  in (uu____8062, q)) args
         in
      debug1
        (fun uu____8068  ->
           let uu____8069 = FStar_TypeChecker_NBETerm.t_to_string x  in
           FStar_Util.print1 "Readback: %s\n" uu____8069);
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
           let uu____8077 = FStar_BigInt.string_of_big_int i  in
           FStar_All.pipe_right uu____8077 FStar_Syntax_Util.exp_int
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
           let uu____8145 =
             match binders with
             | FStar_Util.Inl (ctx,binders1,rc) ->
                 let uu____8193 =
                   FStar_List.fold_left
                     (fun uu____8247  ->
                        fun uu____8248  ->
                          match (uu____8247, uu____8248) with
                          | ((ctx1,binders_rev,accus_rev),(x1,q)) ->
                              let tnorm =
                                let uu____8373 =
                                  translate cfg ctx1
                                    x1.FStar_Syntax_Syntax.sort
                                   in
                                readback cfg uu____8373  in
                              let x2 =
                                let uu___1227_8375 =
                                  FStar_Syntax_Syntax.freshen_bv x1  in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___1227_8375.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___1227_8375.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = tnorm
                                }  in
                              let ax = FStar_TypeChecker_NBETerm.mkAccuVar x2
                                 in
                              let ctx2 = ax :: ctx1  in
                              (ctx2, ((x2, q) :: binders_rev), (ax ::
                                accus_rev))) (ctx, [], []) binders1
                    in
                 (match uu____8193 with
                  | (ctx1,binders_rev,accus_rev) ->
                      let rc1 =
                        match rc with
                        | FStar_Pervasives_Native.None  ->
                            FStar_Pervasives_Native.None
                        | FStar_Pervasives_Native.Some rc1 ->
                            let uu____8461 =
                              let uu____8462 =
                                translate_residual_comp cfg ctx1 rc1  in
                              readback_residual_comp cfg uu____8462  in
                            FStar_Pervasives_Native.Some uu____8461
                         in
                      ((FStar_List.rev binders_rev), accus_rev, rc1))
             | FStar_Util.Inr args ->
                 let uu____8496 =
                   FStar_List.fold_right
                     (fun uu____8537  ->
                        fun uu____8538  ->
                          match (uu____8537, uu____8538) with
                          | ((t,uu____8590),(binders1,accus)) ->
                              let x1 =
                                let uu____8632 = readback cfg t  in
                                FStar_Syntax_Syntax.new_bv
                                  FStar_Pervasives_Native.None uu____8632
                                 in
                              let uu____8633 =
                                let uu____8636 =
                                  FStar_TypeChecker_NBETerm.mkAccuVar x1  in
                                uu____8636 :: accus  in
                              (((x1, FStar_Pervasives_Native.None) ::
                                binders1), uu____8633)) args ([], [])
                    in
                 (match uu____8496 with
                  | (binders1,accus) ->
                      (binders1, (FStar_List.rev accus),
                        FStar_Pervasives_Native.None))
              in
           (match uu____8145 with
            | (binders1,accus_rev,rc) ->
                let body =
                  let uu____8719 = f accus_rev  in readback cfg uu____8719
                   in
                FStar_Syntax_Util.abs binders1 body rc)
       | FStar_TypeChecker_NBETerm.Refinement (f,targ) ->
           if
             ((cfg.core_cfg).FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.for_extraction
           then
             let uu____8743 =
               let uu____8744 = targ ()  in
               FStar_Pervasives_Native.fst uu____8744  in
             readback cfg uu____8743
           else
             (let x1 =
                let uu____8752 =
                  let uu____8753 =
                    let uu____8754 = targ ()  in
                    FStar_Pervasives_Native.fst uu____8754  in
                  readback cfg uu____8753  in
                FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                  uu____8752
                 in
              let body =
                let uu____8760 =
                  let uu____8761 = FStar_TypeChecker_NBETerm.mkAccuVar x1  in
                  f uu____8761  in
                readback cfg uu____8760  in
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
               (fun uu____8831  ->
                  match uu____8831 with
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
               (fun uu____8883  ->
                  match uu____8883 with
                  | (x1,q) ->
                      let uu____8894 = readback cfg x1  in (uu____8894, q))
               args
              in
           let fv1 =
             FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
               FStar_Pervasives_Native.None FStar_Range.dummyRange
              in
           let app =
             let uu____8901 =
               FStar_Syntax_Syntax.mk_Tm_uinst fv1 (FStar_List.rev us)  in
             FStar_Syntax_Util.mk_app uu____8901 args1  in
           app
       | FStar_TypeChecker_NBETerm.FV (fv,us,args) ->
           let args1 =
             map_rev
               (fun uu____8942  ->
                  match uu____8942 with
                  | (x1,q) ->
                      let uu____8953 = readback cfg x1  in (uu____8953, q))
               args
              in
           let fv1 =
             FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
               FStar_Pervasives_Native.None FStar_Range.dummyRange
              in
           let app =
             let uu____8960 =
               FStar_Syntax_Syntax.mk_Tm_uinst fv1 (FStar_List.rev us)  in
             FStar_Syntax_Util.mk_app uu____8960 args1  in
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
             let uu____9001 = FStar_Syntax_Syntax.bv_to_name bv  in
             FStar_Syntax_Util.mk_app uu____9001 args1  in
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
             let uu____9101 = FStar_Thunk.force typ  in
             readback cfg uu____9101  in
           let defn1 =
             let uu____9103 = FStar_Thunk.force defn  in
             readback cfg uu____9103  in
           let body1 =
             let uu____9105 =
               let uu____9106 = FStar_Thunk.force body  in
               readback cfg uu____9106  in
             FStar_Syntax_Subst.close [(var, FStar_Pervasives_Native.None)]
               uu____9105
              in
           let lbname =
             let uu____9126 =
               let uu___1346_9127 =
                 FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
               {
                 FStar_Syntax_Syntax.ppname =
                   (uu___1346_9127.FStar_Syntax_Syntax.ppname);
                 FStar_Syntax_Syntax.index =
                   (uu___1346_9127.FStar_Syntax_Syntax.index);
                 FStar_Syntax_Syntax.sort = typ1
               }  in
             FStar_Util.Inl uu____9126  in
           let lb1 =
             let uu___1349_9129 = lb  in
             {
               FStar_Syntax_Syntax.lbname = lbname;
               FStar_Syntax_Syntax.lbunivs =
                 (uu___1349_9129.FStar_Syntax_Syntax.lbunivs);
               FStar_Syntax_Syntax.lbtyp = typ1;
               FStar_Syntax_Syntax.lbeff =
                 (uu___1349_9129.FStar_Syntax_Syntax.lbeff);
               FStar_Syntax_Syntax.lbdef = defn1;
               FStar_Syntax_Syntax.lbattrs =
                 (uu___1349_9129.FStar_Syntax_Syntax.lbattrs);
               FStar_Syntax_Syntax.lbpos =
                 (uu___1349_9129.FStar_Syntax_Syntax.lbpos)
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
               (fun uu____9207  ->
                  fun lb  ->
                    match uu____9207 with
                    | (v,t,d) ->
                        let t1 = readback cfg t  in
                        let def = readback cfg d  in
                        let v1 =
                          let uu___1369_9221 = v  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___1369_9221.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___1369_9221.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t1
                          }  in
                        let uu___1372_9222 = lb  in
                        {
                          FStar_Syntax_Syntax.lbname = (FStar_Util.Inl v1);
                          FStar_Syntax_Syntax.lbunivs =
                            (uu___1372_9222.FStar_Syntax_Syntax.lbunivs);
                          FStar_Syntax_Syntax.lbtyp = t1;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___1372_9222.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = def;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___1372_9222.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___1372_9222.FStar_Syntax_Syntax.lbpos)
                        }) vars_typs_defns lbs
              in
           let body1 = readback cfg body  in
           let uu____9224 = FStar_Syntax_Subst.close_let_rec lbs1 body1  in
           (match uu____9224 with
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
           let uu____9307 = FStar_Util.first_N (n_args - n_univs) args_rev
              in
           (match uu____9307 with
            | (args_rev1,univs) ->
                let uu____9354 =
                  let uu____9355 =
                    let uu____9356 =
                      FStar_List.map FStar_Pervasives_Native.fst univs  in
                    translate cfg uu____9356 lb.FStar_Syntax_Syntax.lbdef  in
                  iapp cfg uu____9355 (FStar_List.rev args_rev1)  in
                readback cfg uu____9354)
       | FStar_TypeChecker_NBETerm.TopLevelRec
           (lb,uu____9368,uu____9369,args) ->
           let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
           let head =
             FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
               FStar_Pervasives_Native.None FStar_Range.dummyRange
              in
           let args1 =
             FStar_List.map
               (fun uu____9414  ->
                  match uu____9414 with
                  | (t,q) ->
                      let uu____9425 = readback cfg t  in (uu____9425, q))
               args
              in
           FStar_Syntax_Util.mk_app head args1
       | FStar_TypeChecker_NBETerm.LocalLetRec
           (i,uu____9427,lbs,bs,args,_ar,_ar_lst) ->
           let lbnames =
             FStar_List.map
               (fun lb  ->
                  let uu____9469 =
                    let uu____9471 =
                      let uu____9472 =
                        FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                      uu____9472.FStar_Syntax_Syntax.ppname  in
                    FStar_Ident.text_of_id uu____9471  in
                  FStar_Syntax_Syntax.gen_bv uu____9469
                    FStar_Pervasives_Native.None lb.FStar_Syntax_Syntax.lbtyp)
               lbs
              in
           let let_rec_env =
             let uu____9476 =
               FStar_List.map
                 (fun x1  ->
                    FStar_TypeChecker_NBETerm.Accu
                      ((FStar_TypeChecker_NBETerm.Var x1), [])) lbnames
                in
             FStar_List.rev_append uu____9476 bs  in
           let lbs1 =
             FStar_List.map2
               (fun lb  ->
                  fun lbname  ->
                    let lbdef =
                      let uu____9502 =
                        translate cfg let_rec_env
                          lb.FStar_Syntax_Syntax.lbdef
                         in
                      readback cfg uu____9502  in
                    let lbtyp =
                      let uu____9504 =
                        translate cfg bs lb.FStar_Syntax_Syntax.lbtyp  in
                      readback cfg uu____9504  in
                    let uu___1427_9505 = lb  in
                    {
                      FStar_Syntax_Syntax.lbname = (FStar_Util.Inl lbname);
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___1427_9505.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = lbtyp;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___1427_9505.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = lbdef;
                      FStar_Syntax_Syntax.lbattrs =
                        (uu___1427_9505.FStar_Syntax_Syntax.lbattrs);
                      FStar_Syntax_Syntax.lbpos =
                        (uu___1427_9505.FStar_Syntax_Syntax.lbpos)
                    }) lbs lbnames
              in
           let body =
             let uu____9507 = FStar_List.nth lbnames i  in
             FStar_Syntax_Syntax.bv_to_name uu____9507  in
           let uu____9508 = FStar_Syntax_Subst.close_let_rec lbs1 body  in
           (match uu____9508 with
            | (lbs2,body1) ->
                let head =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_let ((true, lbs2), body1))
                    FStar_Pervasives_Native.None FStar_Range.dummyRange
                   in
                let args1 =
                  FStar_List.map
                    (fun uu____9556  ->
                       match uu____9556 with
                       | (x1,q) ->
                           let uu____9567 = readback cfg x1  in
                           (uu____9567, q)) args
                   in
                FStar_Syntax_Util.mk_app head args1)
       | FStar_TypeChecker_NBETerm.Quote (qt,qi) ->
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_quoted (qt, qi))
             FStar_Pervasives_Native.None FStar_Range.dummyRange
       | FStar_TypeChecker_NBETerm.Lazy (FStar_Util.Inl li,uu____9573) ->
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_lazy li)
             FStar_Pervasives_Native.None FStar_Range.dummyRange
       | FStar_TypeChecker_NBETerm.Lazy (uu____9590,thunk) ->
           let uu____9612 = FStar_Thunk.force thunk  in
           readback cfg uu____9612)

type step =
  | Primops 
  | UnfoldUntil of FStar_Syntax_Syntax.delta_depth 
  | UnfoldOnly of FStar_Ident.lid Prims.list 
  | UnfoldAttr of FStar_Ident.lid Prims.list 
  | UnfoldTac 
  | Reify 
let (uu___is_Primops : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Primops  -> true | uu____9641 -> false
  
let (uu___is_UnfoldUntil : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldUntil _0 -> true | uu____9653 -> false
  
let (__proj__UnfoldUntil__item___0 : step -> FStar_Syntax_Syntax.delta_depth)
  = fun projectee  -> match projectee with | UnfoldUntil _0 -> _0 
let (uu___is_UnfoldOnly : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldOnly _0 -> true | uu____9674 -> false
  
let (__proj__UnfoldOnly__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldOnly _0 -> _0 
let (uu___is_UnfoldAttr : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldAttr _0 -> true | uu____9701 -> false
  
let (__proj__UnfoldAttr__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldAttr _0 -> _0 
let (uu___is_UnfoldTac : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldTac  -> true | uu____9725 -> false
  
let (uu___is_Reify : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reify  -> true | uu____9736 -> false
  
let (step_as_normalizer_step : step -> FStar_TypeChecker_Env.step) =
  fun uu___2_9743  ->
    match uu___2_9743 with
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
      fun args  -> let uu____9767 = new_config cfg  in iapp uu____9767 t args
  
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
            let uu___1473_9799 = cfg  in
            {
              FStar_TypeChecker_Cfg.steps =
                (let uu___1475_9802 = cfg.FStar_TypeChecker_Cfg.steps  in
                 {
                   FStar_TypeChecker_Cfg.beta =
                     (uu___1475_9802.FStar_TypeChecker_Cfg.beta);
                   FStar_TypeChecker_Cfg.iota =
                     (uu___1475_9802.FStar_TypeChecker_Cfg.iota);
                   FStar_TypeChecker_Cfg.zeta =
                     (uu___1475_9802.FStar_TypeChecker_Cfg.zeta);
                   FStar_TypeChecker_Cfg.zeta_full =
                     (uu___1475_9802.FStar_TypeChecker_Cfg.zeta_full);
                   FStar_TypeChecker_Cfg.weak =
                     (uu___1475_9802.FStar_TypeChecker_Cfg.weak);
                   FStar_TypeChecker_Cfg.hnf =
                     (uu___1475_9802.FStar_TypeChecker_Cfg.hnf);
                   FStar_TypeChecker_Cfg.primops =
                     (uu___1475_9802.FStar_TypeChecker_Cfg.primops);
                   FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                     (uu___1475_9802.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                   FStar_TypeChecker_Cfg.unfold_until =
                     (uu___1475_9802.FStar_TypeChecker_Cfg.unfold_until);
                   FStar_TypeChecker_Cfg.unfold_only =
                     (uu___1475_9802.FStar_TypeChecker_Cfg.unfold_only);
                   FStar_TypeChecker_Cfg.unfold_fully =
                     (uu___1475_9802.FStar_TypeChecker_Cfg.unfold_fully);
                   FStar_TypeChecker_Cfg.unfold_attr =
                     (uu___1475_9802.FStar_TypeChecker_Cfg.unfold_attr);
                   FStar_TypeChecker_Cfg.unfold_tac =
                     (uu___1475_9802.FStar_TypeChecker_Cfg.unfold_tac);
                   FStar_TypeChecker_Cfg.pure_subterms_within_computations =
                     (uu___1475_9802.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                   FStar_TypeChecker_Cfg.simplify =
                     (uu___1475_9802.FStar_TypeChecker_Cfg.simplify);
                   FStar_TypeChecker_Cfg.erase_universes =
                     (uu___1475_9802.FStar_TypeChecker_Cfg.erase_universes);
                   FStar_TypeChecker_Cfg.allow_unbound_universes =
                     (uu___1475_9802.FStar_TypeChecker_Cfg.allow_unbound_universes);
                   FStar_TypeChecker_Cfg.reify_ = true;
                   FStar_TypeChecker_Cfg.compress_uvars =
                     (uu___1475_9802.FStar_TypeChecker_Cfg.compress_uvars);
                   FStar_TypeChecker_Cfg.no_full_norm =
                     (uu___1475_9802.FStar_TypeChecker_Cfg.no_full_norm);
                   FStar_TypeChecker_Cfg.check_no_uvars =
                     (uu___1475_9802.FStar_TypeChecker_Cfg.check_no_uvars);
                   FStar_TypeChecker_Cfg.unmeta =
                     (uu___1475_9802.FStar_TypeChecker_Cfg.unmeta);
                   FStar_TypeChecker_Cfg.unascribe =
                     (uu___1475_9802.FStar_TypeChecker_Cfg.unascribe);
                   FStar_TypeChecker_Cfg.in_full_norm_request =
                     (uu___1475_9802.FStar_TypeChecker_Cfg.in_full_norm_request);
                   FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                     (uu___1475_9802.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                   FStar_TypeChecker_Cfg.nbe_step =
                     (uu___1475_9802.FStar_TypeChecker_Cfg.nbe_step);
                   FStar_TypeChecker_Cfg.for_extraction =
                     (uu___1475_9802.FStar_TypeChecker_Cfg.for_extraction)
                 });
              FStar_TypeChecker_Cfg.tcenv =
                (uu___1473_9799.FStar_TypeChecker_Cfg.tcenv);
              FStar_TypeChecker_Cfg.debug =
                (uu___1473_9799.FStar_TypeChecker_Cfg.debug);
              FStar_TypeChecker_Cfg.delta_level =
                (uu___1473_9799.FStar_TypeChecker_Cfg.delta_level);
              FStar_TypeChecker_Cfg.primitive_steps =
                (uu___1473_9799.FStar_TypeChecker_Cfg.primitive_steps);
              FStar_TypeChecker_Cfg.strong =
                (uu___1473_9799.FStar_TypeChecker_Cfg.strong);
              FStar_TypeChecker_Cfg.memoize_lazy =
                (uu___1473_9799.FStar_TypeChecker_Cfg.memoize_lazy);
              FStar_TypeChecker_Cfg.normalize_pure_lets =
                (uu___1473_9799.FStar_TypeChecker_Cfg.normalize_pure_lets);
              FStar_TypeChecker_Cfg.reifying =
                (uu___1473_9799.FStar_TypeChecker_Cfg.reifying)
            }  in
          (let uu____9805 =
             (FStar_TypeChecker_Env.debug env (FStar_Options.Other "NBETop"))
               ||
               (FStar_TypeChecker_Env.debug env (FStar_Options.Other "NBE"))
              in
           if uu____9805
           then
             let uu____9810 = FStar_Syntax_Print.term_to_string e  in
             FStar_Util.print1 "Calling NBE with (%s) {\n" uu____9810
           else ());
          (let cfg2 = new_config cfg1  in
           let r =
             let uu____9817 = translate cfg2 [] e  in
             readback cfg2 uu____9817  in
           (let uu____9819 =
              (FStar_TypeChecker_Env.debug env (FStar_Options.Other "NBETop"))
                ||
                (FStar_TypeChecker_Env.debug env (FStar_Options.Other "NBE"))
               in
            if uu____9819
            then
              let uu____9824 = FStar_Syntax_Print.term_to_string r  in
              FStar_Util.print1 "}\nNBE returned (%s)\n" uu____9824
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
          let uu___1491_9851 = cfg  in
          {
            FStar_TypeChecker_Cfg.steps =
              (let uu___1493_9854 = cfg.FStar_TypeChecker_Cfg.steps  in
               {
                 FStar_TypeChecker_Cfg.beta =
                   (uu___1493_9854.FStar_TypeChecker_Cfg.beta);
                 FStar_TypeChecker_Cfg.iota =
                   (uu___1493_9854.FStar_TypeChecker_Cfg.iota);
                 FStar_TypeChecker_Cfg.zeta =
                   (uu___1493_9854.FStar_TypeChecker_Cfg.zeta);
                 FStar_TypeChecker_Cfg.zeta_full =
                   (uu___1493_9854.FStar_TypeChecker_Cfg.zeta_full);
                 FStar_TypeChecker_Cfg.weak =
                   (uu___1493_9854.FStar_TypeChecker_Cfg.weak);
                 FStar_TypeChecker_Cfg.hnf =
                   (uu___1493_9854.FStar_TypeChecker_Cfg.hnf);
                 FStar_TypeChecker_Cfg.primops =
                   (uu___1493_9854.FStar_TypeChecker_Cfg.primops);
                 FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                   (uu___1493_9854.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                 FStar_TypeChecker_Cfg.unfold_until =
                   (uu___1493_9854.FStar_TypeChecker_Cfg.unfold_until);
                 FStar_TypeChecker_Cfg.unfold_only =
                   (uu___1493_9854.FStar_TypeChecker_Cfg.unfold_only);
                 FStar_TypeChecker_Cfg.unfold_fully =
                   (uu___1493_9854.FStar_TypeChecker_Cfg.unfold_fully);
                 FStar_TypeChecker_Cfg.unfold_attr =
                   (uu___1493_9854.FStar_TypeChecker_Cfg.unfold_attr);
                 FStar_TypeChecker_Cfg.unfold_tac =
                   (uu___1493_9854.FStar_TypeChecker_Cfg.unfold_tac);
                 FStar_TypeChecker_Cfg.pure_subterms_within_computations =
                   (uu___1493_9854.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                 FStar_TypeChecker_Cfg.simplify =
                   (uu___1493_9854.FStar_TypeChecker_Cfg.simplify);
                 FStar_TypeChecker_Cfg.erase_universes =
                   (uu___1493_9854.FStar_TypeChecker_Cfg.erase_universes);
                 FStar_TypeChecker_Cfg.allow_unbound_universes =
                   (uu___1493_9854.FStar_TypeChecker_Cfg.allow_unbound_universes);
                 FStar_TypeChecker_Cfg.reify_ = true;
                 FStar_TypeChecker_Cfg.compress_uvars =
                   (uu___1493_9854.FStar_TypeChecker_Cfg.compress_uvars);
                 FStar_TypeChecker_Cfg.no_full_norm =
                   (uu___1493_9854.FStar_TypeChecker_Cfg.no_full_norm);
                 FStar_TypeChecker_Cfg.check_no_uvars =
                   (uu___1493_9854.FStar_TypeChecker_Cfg.check_no_uvars);
                 FStar_TypeChecker_Cfg.unmeta =
                   (uu___1493_9854.FStar_TypeChecker_Cfg.unmeta);
                 FStar_TypeChecker_Cfg.unascribe =
                   (uu___1493_9854.FStar_TypeChecker_Cfg.unascribe);
                 FStar_TypeChecker_Cfg.in_full_norm_request =
                   (uu___1493_9854.FStar_TypeChecker_Cfg.in_full_norm_request);
                 FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                   (uu___1493_9854.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                 FStar_TypeChecker_Cfg.nbe_step =
                   (uu___1493_9854.FStar_TypeChecker_Cfg.nbe_step);
                 FStar_TypeChecker_Cfg.for_extraction =
                   (uu___1493_9854.FStar_TypeChecker_Cfg.for_extraction)
               });
            FStar_TypeChecker_Cfg.tcenv =
              (uu___1491_9851.FStar_TypeChecker_Cfg.tcenv);
            FStar_TypeChecker_Cfg.debug =
              (uu___1491_9851.FStar_TypeChecker_Cfg.debug);
            FStar_TypeChecker_Cfg.delta_level =
              (uu___1491_9851.FStar_TypeChecker_Cfg.delta_level);
            FStar_TypeChecker_Cfg.primitive_steps =
              (uu___1491_9851.FStar_TypeChecker_Cfg.primitive_steps);
            FStar_TypeChecker_Cfg.strong =
              (uu___1491_9851.FStar_TypeChecker_Cfg.strong);
            FStar_TypeChecker_Cfg.memoize_lazy =
              (uu___1491_9851.FStar_TypeChecker_Cfg.memoize_lazy);
            FStar_TypeChecker_Cfg.normalize_pure_lets =
              (uu___1491_9851.FStar_TypeChecker_Cfg.normalize_pure_lets);
            FStar_TypeChecker_Cfg.reifying =
              (uu___1491_9851.FStar_TypeChecker_Cfg.reifying)
          }  in
        let cfg2 = new_config cfg1  in
        debug cfg2
          (fun uu____9860  ->
             let uu____9861 = FStar_Syntax_Print.term_to_string e  in
             FStar_Util.print1 "Calling NBE with (%s) {\n" uu____9861);
        (let r =
           let uu____9865 = translate cfg2 [] e  in readback cfg2 uu____9865
            in
         debug cfg2
           (fun uu____9869  ->
              let uu____9870 = FStar_Syntax_Print.term_to_string r  in
              FStar_Util.print1 "}\nNBE returned (%s)\n" uu____9870);
         r)
  