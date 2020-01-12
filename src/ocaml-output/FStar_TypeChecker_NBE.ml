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
         fun v1  ->
           fun u  ->
             let uu____511 = FStar_Syntax_Print.sigelt_to_string_short v1  in
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
  
let (zeta_false : config -> config) =
  fun cfg  ->
    let cfg_core = cfg.core_cfg  in
    if (cfg_core.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta
    then
      let cfg_core' =
        let uu___97_582 = cfg_core  in
        {
          FStar_TypeChecker_Cfg.steps =
            (let uu___99_585 = cfg_core.FStar_TypeChecker_Cfg.steps  in
             {
               FStar_TypeChecker_Cfg.beta =
                 (uu___99_585.FStar_TypeChecker_Cfg.beta);
               FStar_TypeChecker_Cfg.iota =
                 (uu___99_585.FStar_TypeChecker_Cfg.iota);
               FStar_TypeChecker_Cfg.zeta = false;
               FStar_TypeChecker_Cfg.weak =
                 (uu___99_585.FStar_TypeChecker_Cfg.weak);
               FStar_TypeChecker_Cfg.hnf =
                 (uu___99_585.FStar_TypeChecker_Cfg.hnf);
               FStar_TypeChecker_Cfg.primops =
                 (uu___99_585.FStar_TypeChecker_Cfg.primops);
               FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                 (uu___99_585.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
               FStar_TypeChecker_Cfg.unfold_until =
                 (uu___99_585.FStar_TypeChecker_Cfg.unfold_until);
               FStar_TypeChecker_Cfg.unfold_only =
                 (uu___99_585.FStar_TypeChecker_Cfg.unfold_only);
               FStar_TypeChecker_Cfg.unfold_fully =
                 (uu___99_585.FStar_TypeChecker_Cfg.unfold_fully);
               FStar_TypeChecker_Cfg.unfold_attr =
                 (uu___99_585.FStar_TypeChecker_Cfg.unfold_attr);
               FStar_TypeChecker_Cfg.unfold_tac =
                 (uu___99_585.FStar_TypeChecker_Cfg.unfold_tac);
               FStar_TypeChecker_Cfg.pure_subterms_within_computations =
                 (uu___99_585.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
               FStar_TypeChecker_Cfg.simplify =
                 (uu___99_585.FStar_TypeChecker_Cfg.simplify);
               FStar_TypeChecker_Cfg.erase_universes =
                 (uu___99_585.FStar_TypeChecker_Cfg.erase_universes);
               FStar_TypeChecker_Cfg.allow_unbound_universes =
                 (uu___99_585.FStar_TypeChecker_Cfg.allow_unbound_universes);
               FStar_TypeChecker_Cfg.reify_ =
                 (uu___99_585.FStar_TypeChecker_Cfg.reify_);
               FStar_TypeChecker_Cfg.compress_uvars =
                 (uu___99_585.FStar_TypeChecker_Cfg.compress_uvars);
               FStar_TypeChecker_Cfg.no_full_norm =
                 (uu___99_585.FStar_TypeChecker_Cfg.no_full_norm);
               FStar_TypeChecker_Cfg.check_no_uvars =
                 (uu___99_585.FStar_TypeChecker_Cfg.check_no_uvars);
               FStar_TypeChecker_Cfg.unmeta =
                 (uu___99_585.FStar_TypeChecker_Cfg.unmeta);
               FStar_TypeChecker_Cfg.unascribe =
                 (uu___99_585.FStar_TypeChecker_Cfg.unascribe);
               FStar_TypeChecker_Cfg.in_full_norm_request =
                 (uu___99_585.FStar_TypeChecker_Cfg.in_full_norm_request);
               FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                 (uu___99_585.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
               FStar_TypeChecker_Cfg.nbe_step =
                 (uu___99_585.FStar_TypeChecker_Cfg.nbe_step);
               FStar_TypeChecker_Cfg.for_extraction =
                 (uu___99_585.FStar_TypeChecker_Cfg.for_extraction)
             });
          FStar_TypeChecker_Cfg.tcenv =
            (uu___97_582.FStar_TypeChecker_Cfg.tcenv);
          FStar_TypeChecker_Cfg.debug =
            (uu___97_582.FStar_TypeChecker_Cfg.debug);
          FStar_TypeChecker_Cfg.delta_level =
            (uu___97_582.FStar_TypeChecker_Cfg.delta_level);
          FStar_TypeChecker_Cfg.primitive_steps =
            (uu___97_582.FStar_TypeChecker_Cfg.primitive_steps);
          FStar_TypeChecker_Cfg.strong =
            (uu___97_582.FStar_TypeChecker_Cfg.strong);
          FStar_TypeChecker_Cfg.memoize_lazy =
            (uu___97_582.FStar_TypeChecker_Cfg.memoize_lazy);
          FStar_TypeChecker_Cfg.normalize_pure_lets =
            (uu___97_582.FStar_TypeChecker_Cfg.normalize_pure_lets);
          FStar_TypeChecker_Cfg.reifying =
            (uu___97_582.FStar_TypeChecker_Cfg.reifying)
        }  in
      new_config cfg_core'
    else cfg
  
let (cache_add :
  config -> FStar_Syntax_Syntax.fv -> FStar_TypeChecker_NBETerm.t -> unit) =
  fun cfg  ->
    fun fv  ->
      fun v1  ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
        FStar_Util.smap_add cfg.fv_cache lid.FStar_Ident.str v1
  
let (try_in_cache :
  config ->
    FStar_Syntax_Syntax.fv ->
      FStar_TypeChecker_NBETerm.t FStar_Pervasives_Native.option)
  =
  fun cfg  ->
    fun fv  ->
      let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
      FStar_Util.smap_try_find cfg.fv_cache lid.FStar_Ident.str
  
let (debug : config -> (unit -> unit) -> unit) =
  fun cfg  -> fun f  -> FStar_TypeChecker_Cfg.log_nbe cfg.core_cfg f 
let (unlazy : FStar_TypeChecker_NBETerm.t -> FStar_TypeChecker_NBETerm.t) =
  fun t  ->
    match t with
    | FStar_TypeChecker_NBETerm.Lazy (uu____644,t1) -> FStar_Thunk.force t1
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
              (fun uu____775  ->
                 let uu____776 =
                   FStar_TypeChecker_NBETerm.t_to_string scrutinee0  in
                 let uu____778 = FStar_Syntax_Print.pat_to_string p  in
                 FStar_Util.print2 "matches_pat (%s, %s)\n" uu____776
                   uu____778);
            (let scrutinee = unlazy scrutinee0  in
             let r =
               match p.FStar_Syntax_Syntax.v with
               | FStar_Syntax_Syntax.Pat_var bv ->
                   FStar_Util.Inl [scrutinee0]
               | FStar_Syntax_Syntax.Pat_wild bv ->
                   FStar_Util.Inl [scrutinee0]
               | FStar_Syntax_Syntax.Pat_dot_term uu____805 ->
                   FStar_Util.Inl []
               | FStar_Syntax_Syntax.Pat_constant s ->
                   let matches_const c s1 =
                     debug cfg
                       (fun uu____832  ->
                          let uu____833 =
                            FStar_TypeChecker_NBETerm.t_to_string c  in
                          let uu____835 =
                            FStar_Syntax_Print.const_to_string s1  in
                          FStar_Util.print2
                            "Testing term %s against pattern %s\n" uu____833
                            uu____835);
                     (match c with
                      | FStar_TypeChecker_NBETerm.Constant
                          (FStar_TypeChecker_NBETerm.Unit ) ->
                          s1 = FStar_Const.Const_unit
                      | FStar_TypeChecker_NBETerm.Constant
                          (FStar_TypeChecker_NBETerm.Bool b) ->
                          (match s1 with
                           | FStar_Const.Const_bool p1 -> b = p1
                           | uu____845 -> false)
                      | FStar_TypeChecker_NBETerm.Constant
                          (FStar_TypeChecker_NBETerm.Int i) ->
                          (match s1 with
                           | FStar_Const.Const_int
                               (p1,FStar_Pervasives_Native.None ) ->
                               let uu____862 =
                                 FStar_BigInt.big_int_of_string p1  in
                               i = uu____862
                           | uu____863 -> false)
                      | FStar_TypeChecker_NBETerm.Constant
                          (FStar_TypeChecker_NBETerm.String (st,uu____866))
                          ->
                          (match s1 with
                           | FStar_Const.Const_string (p1,uu____871) ->
                               st = p1
                           | uu____875 -> false)
                      | FStar_TypeChecker_NBETerm.Constant
                          (FStar_TypeChecker_NBETerm.Char c1) ->
                          (match s1 with
                           | FStar_Const.Const_char p1 -> c1 = p1
                           | uu____883 -> false)
                      | uu____885 -> false)
                      in
                   let uu____887 = matches_const scrutinee s  in
                   if uu____887
                   then FStar_Util.Inl []
                   else FStar_Util.Inr false
               | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                   let rec matches_args out a p1 =
                     match (a, p1) with
                     | ([],[]) -> FStar_Util.Inl out
                     | ((t,uu____1025)::rest_a,(p2,uu____1028)::rest_p) ->
                         let uu____1067 = matches_pat t p2  in
                         (match uu____1067 with
                          | FStar_Util.Inl s ->
                              matches_args (FStar_List.append out s) rest_a
                                rest_p
                          | m -> m)
                     | uu____1096 -> FStar_Util.Inr false  in
                   (match scrutinee with
                    | FStar_TypeChecker_NBETerm.Construct (fv',_us,args_rev)
                        ->
                        let uu____1144 = FStar_Syntax_Syntax.fv_eq fv fv'  in
                        if uu____1144
                        then
                          matches_args [] (FStar_List.rev args_rev) arg_pats
                        else FStar_Util.Inr false
                    | uu____1164 -> FStar_Util.Inr true)
                in
             let res_to_string uu___0_1182 =
               match uu___0_1182 with
               | FStar_Util.Inr b ->
                   let uu____1196 = FStar_Util.string_of_bool b  in
                   Prims.op_Hat "Inr " uu____1196
               | FStar_Util.Inl bs ->
                   let uu____1205 =
                     FStar_Util.string_of_int (FStar_List.length bs)  in
                   Prims.op_Hat "Inl " uu____1205
                in
             debug cfg
               (fun uu____1213  ->
                  let uu____1214 =
                    FStar_TypeChecker_NBETerm.t_to_string scrutinee  in
                  let uu____1216 = FStar_Syntax_Print.pat_to_string p  in
                  let uu____1218 = res_to_string r  in
                  FStar_Util.print3 "matches_pat (%s, %s) = %s\n" uu____1214
                    uu____1216 uu____1218);
             r)
             in
          match branches1 with
          | [] -> FStar_Pervasives_Native.None
          | (p,_wopt,e)::branches2 ->
              let uu____1257 = matches_pat scrut1 p  in
              (match uu____1257 with
               | FStar_Util.Inl matches ->
                   (debug cfg
                      (fun uu____1282  ->
                         let uu____1283 = FStar_Syntax_Print.pat_to_string p
                            in
                         FStar_Util.print1 "Pattern %s matches\n" uu____1283);
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
        | (uu____1432,[]) -> (true, acc, ts)
        | ([],uu____1463::uu____1464) -> (false, acc, [])
        | (t::ts1,in_decreases_clause::bs) ->
            let uu____1533 =
              in_decreases_clause &&
                (FStar_TypeChecker_NBETerm.isAccu
                   (FStar_Pervasives_Native.fst t))
               in
            if uu____1533
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
        let mapper uu____1632 =
          match uu____1632 with
          | (lr,rng) ->
              (match lr with
               | FStar_Util.Inr (elt,FStar_Pervasives_Native.None ) ->
                   FStar_Pervasives_Native.Some elt
               | FStar_Util.Inr (elt,FStar_Pervasives_Native.Some us) ->
                   (debug cfg
                      (fun uu____1715  ->
                         let uu____1716 =
                           FStar_Syntax_Print.univs_to_string us  in
                         FStar_Util.print1
                           "Universes in local declaration: %s\n" uu____1716);
                    FStar_Pervasives_Native.Some elt)
               | uu____1719 -> FStar_Pervasives_Native.None)
           in
        let uu____1734 = FStar_TypeChecker_Env.lookup_qname env lid  in
        FStar_Util.bind_opt uu____1734 mapper
  
let (is_univ : FStar_TypeChecker_NBETerm.t -> Prims.bool) =
  fun tm  ->
    match tm with
    | FStar_TypeChecker_NBETerm.Univ uu____1781 -> true
    | uu____1783 -> false
  
let (un_univ : FStar_TypeChecker_NBETerm.t -> FStar_Syntax_Syntax.universe) =
  fun tm  ->
    match tm with
    | FStar_TypeChecker_NBETerm.Univ u -> u
    | t ->
        let uu____1793 =
          let uu____1795 = FStar_TypeChecker_NBETerm.t_to_string t  in
          Prims.op_Hat "Not a universe: " uu____1795  in
        failwith uu____1793
  
let (is_constr_fv : FStar_Syntax_Syntax.fv -> Prims.bool) =
  fun fvar1  ->
    fvar1.FStar_Syntax_Syntax.fv_qual =
      (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
  
let (is_constr : FStar_TypeChecker_Env.qninfo -> Prims.bool) =
  fun q  ->
    match q with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
              (uu____1817,uu____1818,uu____1819,uu____1820,uu____1821,uu____1822);
            FStar_Syntax_Syntax.sigrng = uu____1823;
            FStar_Syntax_Syntax.sigquals = uu____1824;
            FStar_Syntax_Syntax.sigmeta = uu____1825;
            FStar_Syntax_Syntax.sigattrs = uu____1826;
            FStar_Syntax_Syntax.sigopts = uu____1827;_},uu____1828),uu____1829)
        -> true
    | uu____1889 -> false
  
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
              let uu____1929 = aux u3  in
              FStar_Syntax_Syntax.U_succ uu____1929
          | FStar_Syntax_Syntax.U_max us ->
              let uu____1933 = FStar_List.map aux us  in
              FStar_Syntax_Syntax.U_max uu____1933
          | FStar_Syntax_Syntax.U_unknown  -> u2
          | FStar_Syntax_Syntax.U_name uu____1936 -> u2
          | FStar_Syntax_Syntax.U_unif uu____1937 -> u2
          | FStar_Syntax_Syntax.U_zero  -> u2  in
        aux u
  
let (find_let :
  FStar_Syntax_Syntax.letbinding Prims.list ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.letbinding FStar_Pervasives_Native.option)
  =
  fun lbs  ->
    fun fvar1  ->
      FStar_Util.find_map lbs
        (fun lb  ->
           match lb.FStar_Syntax_Syntax.lbname with
           | FStar_Util.Inl uu____1968 -> failwith "find_let : impossible"
           | FStar_Util.Inr name ->
               let uu____1973 = FStar_Syntax_Syntax.fv_eq name fvar1  in
               if uu____1973
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
          (fun uu____2244  ->
             let uu____2245 =
               let uu____2247 = FStar_Syntax_Subst.compress e  in
               FStar_Syntax_Print.tag_of_term uu____2247  in
             let uu____2248 =
               let uu____2250 = FStar_Syntax_Subst.compress e  in
               FStar_Syntax_Print.term_to_string uu____2250  in
             FStar_Util.print2 "Term: %s - %s\n" uu____2245 uu____2248);
        (let uu____2252 =
           let uu____2253 = FStar_Syntax_Subst.compress e  in
           uu____2253.FStar_Syntax_Syntax.n  in
         match uu____2252 with
         | FStar_Syntax_Syntax.Tm_delayed (uu____2256,uu____2257) ->
             failwith "Tm_delayed: Impossible"
         | FStar_Syntax_Syntax.Tm_unknown  ->
             FStar_TypeChecker_NBETerm.Unknown
         | FStar_Syntax_Syntax.Tm_constant c ->
             let uu____2296 = translate_constant c  in
             FStar_TypeChecker_NBETerm.Constant uu____2296
         | FStar_Syntax_Syntax.Tm_bvar db ->
             if db.FStar_Syntax_Syntax.index < (FStar_List.length bs)
             then
               let t = FStar_List.nth bs db.FStar_Syntax_Syntax.index  in
               (debug1
                  (fun uu____2307  ->
                     let uu____2308 = FStar_TypeChecker_NBETerm.t_to_string t
                        in
                     let uu____2310 =
                       let uu____2312 =
                         FStar_List.map FStar_TypeChecker_NBETerm.t_to_string
                           bs
                          in
                       FStar_All.pipe_right uu____2312
                         (FStar_String.concat "; ")
                        in
                     FStar_Util.print2
                       "Resolved bvar to %s\n\tcontext is [%s]\n" uu____2308
                       uu____2310);
                t)
             else failwith "de Bruijn index out of bounds"
         | FStar_Syntax_Syntax.Tm_uinst (t,us) ->
             (debug1
                (fun uu____2339  ->
                   let uu____2340 = FStar_Syntax_Print.term_to_string t  in
                   let uu____2342 =
                     let uu____2344 =
                       FStar_List.map FStar_Syntax_Print.univ_to_string us
                        in
                     FStar_All.pipe_right uu____2344
                       (FStar_String.concat ", ")
                      in
                   FStar_Util.print2 "Uinst term : %s\nUnivs : %s\n"
                     uu____2340 uu____2342);
              (let uu____2355 = translate cfg bs t  in
               let uu____2356 =
                 FStar_List.map
                   (fun x  ->
                      let uu____2360 =
                        let uu____2361 = translate_univ cfg bs x  in
                        FStar_TypeChecker_NBETerm.Univ uu____2361  in
                      FStar_TypeChecker_NBETerm.as_arg uu____2360) us
                  in
               iapp cfg uu____2355 uu____2356))
         | FStar_Syntax_Syntax.Tm_type u ->
             let uu____2363 = translate_univ cfg bs u  in
             FStar_TypeChecker_NBETerm.Type_t uu____2363
         | FStar_Syntax_Syntax.Tm_arrow (xs,c) ->
             let norm1 uu____2393 =
               let uu____2394 =
                 FStar_List.fold_left
                   (fun uu____2438  ->
                      fun uu____2439  ->
                        match (uu____2438, uu____2439) with
                        | ((ctx,binders_rev),(x,q)) ->
                            let t =
                              let uu____2543 =
                                translate cfg ctx x.FStar_Syntax_Syntax.sort
                                 in
                              readback cfg uu____2543  in
                            let x1 =
                              let uu___376_2545 =
                                FStar_Syntax_Syntax.freshen_bv x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___376_2545.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___376_2545.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t
                              }  in
                            let ctx1 =
                              let uu____2549 =
                                FStar_TypeChecker_NBETerm.mkAccuVar x1  in
                              uu____2549 :: ctx  in
                            (ctx1, ((x1, q) :: binders_rev))) (bs, []) xs
                  in
               match uu____2394 with
               | (ctx,binders_rev) ->
                   let c1 =
                     let uu____2609 = translate_comp cfg ctx c  in
                     readback_comp cfg uu____2609  in
                   FStar_Syntax_Util.arrow (FStar_List.rev binders_rev) c1
                in
             let uu____2616 =
               let uu____2633 = FStar_Thunk.mk norm1  in
               FStar_Util.Inl uu____2633  in
             FStar_TypeChecker_NBETerm.Arrow uu____2616
         | FStar_Syntax_Syntax.Tm_refine (bv,tm) ->
             if
               ((cfg.core_cfg).FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.for_extraction
             then translate cfg bs bv.FStar_Syntax_Syntax.sort
             else
               FStar_TypeChecker_NBETerm.Refinement
                 (((fun y  -> translate cfg (y :: bs) tm)),
                   ((fun uu____2671  ->
                       let uu____2672 =
                         translate cfg bs bv.FStar_Syntax_Syntax.sort  in
                       FStar_TypeChecker_NBETerm.as_arg uu____2672)))
         | FStar_Syntax_Syntax.Tm_ascribed (t,uu____2674,uu____2675) ->
             translate cfg bs t
         | FStar_Syntax_Syntax.Tm_uvar (u,(subst1,set_use_range1)) ->
             let norm_uvar uu____2742 =
               let norm_subst_elt uu___1_2748 =
                 match uu___1_2748 with
                 | FStar_Syntax_Syntax.NT (x,t) ->
                     let uu____2755 =
                       let uu____2762 =
                         let uu____2765 = translate cfg bs t  in
                         readback cfg uu____2765  in
                       (x, uu____2762)  in
                     FStar_Syntax_Syntax.NT uu____2755
                 | FStar_Syntax_Syntax.NM (x,i) ->
                     let x_i =
                       FStar_Syntax_Syntax.bv_to_tm
                         (let uu___413_2775 = x  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___413_2775.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index = i;
                            FStar_Syntax_Syntax.sort =
                              (uu___413_2775.FStar_Syntax_Syntax.sort)
                          })
                        in
                     let t =
                       let uu____2777 = translate cfg bs x_i  in
                       readback cfg uu____2777  in
                     (match t.FStar_Syntax_Syntax.n with
                      | FStar_Syntax_Syntax.Tm_bvar x_j ->
                          FStar_Syntax_Syntax.NM
                            (x, (x_j.FStar_Syntax_Syntax.index))
                      | uu____2780 -> FStar_Syntax_Syntax.NT (x, t))
                 | uu____2783 ->
                     failwith "Impossible: subst invariant of uvar nodes"
                  in
               let subst2 =
                 FStar_List.map (FStar_List.map norm_subst_elt) subst1  in
               let uu___423_2794 = e  in
               {
                 FStar_Syntax_Syntax.n =
                   (FStar_Syntax_Syntax.Tm_uvar (u, (subst2, set_use_range1)));
                 FStar_Syntax_Syntax.pos =
                   (uu___423_2794.FStar_Syntax_Syntax.pos);
                 FStar_Syntax_Syntax.vars =
                   (uu___423_2794.FStar_Syntax_Syntax.vars)
               }  in
             let uu____2807 =
               let uu____2818 =
                 let uu____2819 = FStar_Thunk.mk norm_uvar  in
                 FStar_TypeChecker_NBETerm.UVar uu____2819  in
               (uu____2818, [])  in
             FStar_TypeChecker_NBETerm.Accu uu____2807
         | FStar_Syntax_Syntax.Tm_name x ->
             FStar_TypeChecker_NBETerm.mkAccuVar x
         | FStar_Syntax_Syntax.Tm_abs ([],uu____2833,uu____2834) ->
             failwith "Impossible: abstraction with no binders"
         | FStar_Syntax_Syntax.Tm_abs (xs,body,resc) ->
             FStar_TypeChecker_NBETerm.Lam
               (((fun ys  -> translate cfg (FStar_List.append ys bs) body)),
                 (FStar_Util.Inl (bs, xs, resc)), (FStar_List.length xs))
         | FStar_Syntax_Syntax.Tm_fvar fvar1 ->
             let uu____2942 = try_in_cache cfg fvar1  in
             (match uu____2942 with
              | FStar_Pervasives_Native.Some t -> t
              | uu____2946 -> translate_fv cfg bs fvar1)
         | FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                  (FStar_Const.Const_reify );
                FStar_Syntax_Syntax.pos = uu____2949;
                FStar_Syntax_Syntax.vars = uu____2950;_},arg::more::args)
             ->
             let uu____3010 = FStar_Syntax_Util.head_and_args e  in
             (match uu____3010 with
              | (head1,uu____3028) ->
                  let head2 =
                    FStar_Syntax_Syntax.mk_Tm_app head1 [arg]
                      FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
                     in
                  let uu____3072 =
                    FStar_Syntax_Syntax.mk_Tm_app head2 (more :: args)
                      FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
                     in
                  translate cfg bs uu____3072)
         | FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                  (FStar_Const.Const_reflect uu____3081);
                FStar_Syntax_Syntax.pos = uu____3082;
                FStar_Syntax_Syntax.vars = uu____3083;_},arg::more::args)
             ->
             let uu____3143 = FStar_Syntax_Util.head_and_args e  in
             (match uu____3143 with
              | (head1,uu____3161) ->
                  let head2 =
                    FStar_Syntax_Syntax.mk_Tm_app head1 [arg]
                      FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
                     in
                  let uu____3205 =
                    FStar_Syntax_Syntax.mk_Tm_app head2 (more :: args)
                      FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
                     in
                  translate cfg bs uu____3205)
         | FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                  (FStar_Const.Const_reflect uu____3214);
                FStar_Syntax_Syntax.pos = uu____3215;
                FStar_Syntax_Syntax.vars = uu____3216;_},arg::[])
             when (cfg.core_cfg).FStar_TypeChecker_Cfg.reifying ->
             let cfg1 = reifying_false cfg  in
             translate cfg1 bs (FStar_Pervasives_Native.fst arg)
         | FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                  (FStar_Const.Const_reflect uu____3261);
                FStar_Syntax_Syntax.pos = uu____3262;
                FStar_Syntax_Syntax.vars = uu____3263;_},arg::[])
             ->
             let uu____3303 =
               translate cfg bs (FStar_Pervasives_Native.fst arg)  in
             FStar_TypeChecker_NBETerm.Reflect uu____3303
         | FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                  (FStar_Const.Const_reify );
                FStar_Syntax_Syntax.pos = uu____3308;
                FStar_Syntax_Syntax.vars = uu____3309;_},arg::[])
             when
             ((cfg.core_cfg).FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.reify_
             ->
             let cfg1 = reifying_false cfg  in
             translate cfg1 bs (FStar_Pervasives_Native.fst arg)
         | FStar_Syntax_Syntax.Tm_app (head1,args) ->
             (debug1
                (fun uu____3388  ->
                   let uu____3389 = FStar_Syntax_Print.term_to_string head1
                      in
                   let uu____3391 = FStar_Syntax_Print.args_to_string args
                      in
                   FStar_Util.print2 "Application: %s @ %s\n" uu____3389
                     uu____3391);
              (let uu____3394 = translate cfg bs head1  in
               let uu____3395 =
                 FStar_List.map
                   (fun x  ->
                      let uu____3417 =
                        translate cfg bs (FStar_Pervasives_Native.fst x)  in
                      (uu____3417, (FStar_Pervasives_Native.snd x))) args
                  in
               iapp cfg uu____3394 uu____3395))
         | FStar_Syntax_Syntax.Tm_match (scrut,branches) ->
             let make_branches uu____3469 =
               let cfg1 = zeta_false cfg  in
               let rec process_pattern bs1 p =
                 let uu____3500 =
                   match p.FStar_Syntax_Syntax.v with
                   | FStar_Syntax_Syntax.Pat_constant c ->
                       (bs1, (FStar_Syntax_Syntax.Pat_constant c))
                   | FStar_Syntax_Syntax.Pat_cons (fvar1,args) ->
                       let uu____3536 =
                         FStar_List.fold_left
                           (fun uu____3577  ->
                              fun uu____3578  ->
                                match (uu____3577, uu____3578) with
                                | ((bs2,args1),(arg,b)) ->
                                    let uu____3670 = process_pattern bs2 arg
                                       in
                                    (match uu____3670 with
                                     | (bs',arg') ->
                                         (bs', ((arg', b) :: args1))))
                           (bs1, []) args
                          in
                       (match uu____3536 with
                        | (bs',args') ->
                            (bs',
                              (FStar_Syntax_Syntax.Pat_cons
                                 (fvar1, (FStar_List.rev args')))))
                   | FStar_Syntax_Syntax.Pat_var bvar ->
                       let x =
                         let uu____3769 =
                           let uu____3770 =
                             translate cfg1 bs1 bvar.FStar_Syntax_Syntax.sort
                              in
                           readback cfg1 uu____3770  in
                         FStar_Syntax_Syntax.new_bv
                           FStar_Pervasives_Native.None uu____3769
                          in
                       let uu____3771 =
                         let uu____3774 =
                           FStar_TypeChecker_NBETerm.mkAccuVar x  in
                         uu____3774 :: bs1  in
                       (uu____3771, (FStar_Syntax_Syntax.Pat_var x))
                   | FStar_Syntax_Syntax.Pat_wild bvar ->
                       let x =
                         let uu____3779 =
                           let uu____3780 =
                             translate cfg1 bs1 bvar.FStar_Syntax_Syntax.sort
                              in
                           readback cfg1 uu____3780  in
                         FStar_Syntax_Syntax.new_bv
                           FStar_Pervasives_Native.None uu____3779
                          in
                       let uu____3781 =
                         let uu____3784 =
                           FStar_TypeChecker_NBETerm.mkAccuVar x  in
                         uu____3784 :: bs1  in
                       (uu____3781, (FStar_Syntax_Syntax.Pat_wild x))
                   | FStar_Syntax_Syntax.Pat_dot_term (bvar,tm) ->
                       let x =
                         let uu____3794 =
                           let uu____3795 =
                             translate cfg1 bs1 bvar.FStar_Syntax_Syntax.sort
                              in
                           readback cfg1 uu____3795  in
                         FStar_Syntax_Syntax.new_bv
                           FStar_Pervasives_Native.None uu____3794
                          in
                       let uu____3796 =
                         let uu____3797 =
                           let uu____3804 =
                             let uu____3807 = translate cfg1 bs1 tm  in
                             readback cfg1 uu____3807  in
                           (x, uu____3804)  in
                         FStar_Syntax_Syntax.Pat_dot_term uu____3797  in
                       (bs1, uu____3796)
                    in
                 match uu____3500 with
                 | (bs2,p_new) ->
                     (bs2,
                       (let uu___550_3827 = p  in
                        {
                          FStar_Syntax_Syntax.v = p_new;
                          FStar_Syntax_Syntax.p =
                            (uu___550_3827.FStar_Syntax_Syntax.p)
                        }))
                  in
               FStar_List.map
                 (fun uu____3846  ->
                    match uu____3846 with
                    | (pat,when_clause,e1) ->
                        let uu____3868 = process_pattern bs pat  in
                        (match uu____3868 with
                         | (bs',pat') ->
                             let uu____3881 =
                               let uu____3882 =
                                 let uu____3885 = translate cfg1 bs' e1  in
                                 readback cfg1 uu____3885  in
                               (pat', when_clause, uu____3882)  in
                             FStar_Syntax_Util.branch uu____3881)) branches
                in
             let scrut1 = translate cfg bs scrut  in
             (debug1
                (fun uu____3902  ->
                   let uu____3903 =
                     FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos
                      in
                   let uu____3905 = FStar_Syntax_Print.term_to_string e  in
                   FStar_Util.print2 "%s: Translating match %s\n" uu____3903
                     uu____3905);
              (let scrut2 = unlazy scrut1  in
               match scrut2 with
               | FStar_TypeChecker_NBETerm.Construct (c,us,args) ->
                   (debug1
                      (fun uu____3933  ->
                         let uu____3934 =
                           let uu____3936 =
                             FStar_All.pipe_right args
                               (FStar_List.map
                                  (fun uu____3962  ->
                                     match uu____3962 with
                                     | (x,q) ->
                                         let uu____3976 =
                                           FStar_TypeChecker_NBETerm.t_to_string
                                             x
                                            in
                                         Prims.op_Hat
                                           (if FStar_Util.is_some q
                                            then "#"
                                            else "") uu____3976))
                              in
                           FStar_All.pipe_right uu____3936
                             (FStar_String.concat "; ")
                            in
                         FStar_Util.print1 "Match args: %s\n" uu____3934);
                    (let uu____3990 = pickBranch cfg scrut2 branches  in
                     match uu____3990 with
                     | FStar_Pervasives_Native.Some (branch1,args1) ->
                         let uu____4011 =
                           FStar_List.fold_left
                             (fun bs1  -> fun x  -> x :: bs1) bs args1
                            in
                         translate cfg uu____4011 branch1
                     | FStar_Pervasives_Native.None  ->
                         FStar_TypeChecker_NBETerm.mkAccuMatch scrut2
                           make_branches))
               | FStar_TypeChecker_NBETerm.Constant c ->
                   (debug1
                      (fun uu____4034  ->
                         let uu____4035 =
                           FStar_TypeChecker_NBETerm.t_to_string scrut2  in
                         FStar_Util.print1 "Match constant : %s\n" uu____4035);
                    (let uu____4038 = pickBranch cfg scrut2 branches  in
                     match uu____4038 with
                     | FStar_Pervasives_Native.Some (branch1,[]) ->
                         translate cfg bs branch1
                     | FStar_Pervasives_Native.Some (branch1,arg::[]) ->
                         translate cfg (arg :: bs) branch1
                     | FStar_Pervasives_Native.None  ->
                         FStar_TypeChecker_NBETerm.mkAccuMatch scrut2
                           make_branches
                     | FStar_Pervasives_Native.Some (uu____4072,hd1::tl1) ->
                         failwith
                           "Impossible: Matching on constants cannot bind more than one variable"))
               | uu____4086 ->
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
             let uu____4131 =
               FStar_TypeChecker_Cfg.should_reduce_local_let cfg.core_cfg lb
                in
             if uu____4131
             then
               let uu____4134 =
                 (((cfg.core_cfg).FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.for_extraction
                    &&
                    (FStar_Syntax_Util.is_unit lb.FStar_Syntax_Syntax.lbtyp))
                   &&
                   (FStar_Syntax_Util.is_pure_or_ghost_effect
                      lb.FStar_Syntax_Syntax.lbeff)
                  in
               (if uu____4134
                then
                  let bs1 =
                    (FStar_TypeChecker_NBETerm.Constant
                       FStar_TypeChecker_NBETerm.Unit)
                    :: bs  in
                  translate cfg bs1 body
                else
                  (let bs1 =
                     let uu____4145 = translate_letbinding cfg bs lb  in
                     uu____4145 :: bs  in
                   translate cfg bs1 body))
             else
               (let def uu____4153 =
                  let uu____4154 =
                    (((cfg.core_cfg).FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.for_extraction
                       &&
                       (FStar_Syntax_Util.is_unit
                          lb.FStar_Syntax_Syntax.lbtyp))
                      &&
                      (FStar_Syntax_Util.is_pure_or_ghost_effect
                         lb.FStar_Syntax_Syntax.lbeff)
                     in
                  if uu____4154
                  then
                    FStar_TypeChecker_NBETerm.Constant
                      FStar_TypeChecker_NBETerm.Unit
                  else translate cfg bs lb.FStar_Syntax_Syntax.lbdef  in
                let typ uu____4164 =
                  translate cfg bs lb.FStar_Syntax_Syntax.lbtyp  in
                let name =
                  let uu____4166 =
                    FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                  FStar_Syntax_Syntax.freshen_bv uu____4166  in
                let bs1 =
                  (FStar_TypeChecker_NBETerm.Accu
                     ((FStar_TypeChecker_NBETerm.Var name), []))
                  :: bs  in
                let body1 uu____4185 = translate cfg bs1 body  in
                let uu____4186 =
                  let uu____4197 =
                    let uu____4198 =
                      let uu____4215 = FStar_Thunk.mk typ  in
                      let uu____4218 = FStar_Thunk.mk def  in
                      let uu____4221 = FStar_Thunk.mk body1  in
                      (name, uu____4215, uu____4218, uu____4221, lb)  in
                    FStar_TypeChecker_NBETerm.UnreducedLet uu____4198  in
                  (uu____4197, [])  in
                FStar_TypeChecker_NBETerm.Accu uu____4186)
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
                      let uu____4267 =
                        FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                      FStar_Syntax_Syntax.freshen_bv uu____4267) lbs
                  in
               let typs =
                 FStar_List.map
                   (fun lb  -> translate cfg bs lb.FStar_Syntax_Syntax.lbtyp)
                   lbs
                  in
               let rec_bs =
                 let uu____4276 =
                   FStar_List.map
                     (fun v1  ->
                        FStar_TypeChecker_NBETerm.Accu
                          ((FStar_TypeChecker_NBETerm.Var v1), [])) vars
                    in
                 FStar_List.append uu____4276 bs  in
               let defs =
                 FStar_List.map
                   (fun lb  ->
                      translate cfg rec_bs lb.FStar_Syntax_Syntax.lbdef) lbs
                  in
               let body1 = translate cfg rec_bs body  in
               let uu____4297 =
                 let uu____4308 =
                   let uu____4309 =
                     let uu____4326 = FStar_List.zip3 vars typs defs  in
                     (uu____4326, body1, lbs)  in
                   FStar_TypeChecker_NBETerm.UnreducedLetRec uu____4309  in
                 (uu____4308, [])  in
               FStar_TypeChecker_NBETerm.Accu uu____4297
             else
               (let uu____4357 = make_rec_env lbs bs  in
                translate cfg uu____4357 body)
         | FStar_Syntax_Syntax.Tm_meta (e1,uu____4361) -> translate cfg bs e1
         | FStar_Syntax_Syntax.Tm_quoted (qt,qi) ->
             let close1 t =
               let bvs =
                 FStar_List.map
                   (fun uu____4382  ->
                      FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                        FStar_Syntax_Syntax.tun) bs
                  in
               let s1 =
                 FStar_List.mapi
                   (fun i  -> fun bv  -> FStar_Syntax_Syntax.DB (i, bv)) bvs
                  in
               let s2 =
                 let uu____4395 = FStar_List.zip bvs bs  in
                 FStar_List.map
                   (fun uu____4410  ->
                      match uu____4410 with
                      | (bv,t1) ->
                          let uu____4417 =
                            let uu____4424 = readback cfg t1  in
                            (bv, uu____4424)  in
                          FStar_Syntax_Syntax.NT uu____4417) uu____4395
                  in
               let uu____4429 = FStar_Syntax_Subst.subst s1 t  in
               FStar_Syntax_Subst.subst s2 uu____4429  in
             (match qi.FStar_Syntax_Syntax.qkind with
              | FStar_Syntax_Syntax.Quote_dynamic  ->
                  let qt1 = close1 qt  in
                  FStar_TypeChecker_NBETerm.Quote (qt1, qi)
              | FStar_Syntax_Syntax.Quote_static  ->
                  let qi1 = FStar_Syntax_Syntax.on_antiquoted close1 qi  in
                  FStar_TypeChecker_NBETerm.Quote (qt, qi1))
         | FStar_Syntax_Syntax.Tm_lazy li ->
             let f uu____4438 =
               let t = FStar_Syntax_Util.unfold_lazy li  in
               debug1
                 (fun uu____4445  ->
                    let uu____4446 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.print1 ">> Unfolding Tm_lazy to %s\n"
                      uu____4446);
               translate cfg bs t  in
             let uu____4449 =
               let uu____4464 = FStar_Thunk.mk f  in
               ((FStar_Util.Inl li), uu____4464)  in
             FStar_TypeChecker_NBETerm.Lazy uu____4449)

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
            let uu____4496 =
              let uu____4503 = translate cfg bs typ  in
              let uu____4504 = fmap_opt (translate_univ cfg bs) u  in
              (uu____4503, uu____4504)  in
            FStar_TypeChecker_NBETerm.Tot uu____4496
        | FStar_Syntax_Syntax.GTotal (typ,u) ->
            let uu____4519 =
              let uu____4526 = translate cfg bs typ  in
              let uu____4527 = fmap_opt (translate_univ cfg bs) u  in
              (uu____4526, uu____4527)  in
            FStar_TypeChecker_NBETerm.GTot uu____4519
        | FStar_Syntax_Syntax.Comp ctyp ->
            let uu____4533 = translate_comp_typ cfg bs ctyp  in
            FStar_TypeChecker_NBETerm.Comp uu____4533

and (iapp :
  config ->
    FStar_TypeChecker_NBETerm.t ->
      FStar_TypeChecker_NBETerm.args -> FStar_TypeChecker_NBETerm.t)
  =
  fun cfg  ->
    fun f  ->
      fun args  ->
        match f with
        | FStar_TypeChecker_NBETerm.Lam (f1,binders,n1) ->
            let m = FStar_List.length args  in
            if m < n1
            then
              let arg_values_rev = map_rev FStar_Pervasives_Native.fst args
                 in
              let binders1 =
                match binders with
                | FStar_Util.Inr raw_args ->
                    let uu____4669 = FStar_List.splitAt m raw_args  in
                    (match uu____4669 with
                     | (uu____4710,raw_args1) -> FStar_Util.Inr raw_args1)
                | FStar_Util.Inl (ctx,xs,rc) ->
                    let uu____4779 = FStar_List.splitAt m xs  in
                    (match uu____4779 with
                     | (uu____4826,xs1) ->
                         let ctx1 = FStar_List.append arg_values_rev ctx  in
                         FStar_Util.Inl (ctx1, xs1, rc))
                 in
              FStar_TypeChecker_NBETerm.Lam
                (((fun l  -> f1 (FStar_List.append l arg_values_rev))),
                  binders1, (n1 - m))
            else
              if m = n1
              then
                (let arg_values_rev =
                   map_rev FStar_Pervasives_Native.fst args  in
                 f1 arg_values_rev)
              else
                (let uu____4926 = FStar_List.splitAt n1 args  in
                 match uu____4926 with
                 | (args1,args') ->
                     let uu____4973 =
                       let uu____4974 =
                         map_rev FStar_Pervasives_Native.fst args1  in
                       f1 uu____4974  in
                     iapp cfg uu____4973 args')
        | FStar_TypeChecker_NBETerm.Accu (a,ts) ->
            FStar_TypeChecker_NBETerm.Accu
              (a, (FStar_List.rev_append args ts))
        | FStar_TypeChecker_NBETerm.Construct (i,us,ts) ->
            let rec aux args1 us1 ts1 =
              match args1 with
              | (FStar_TypeChecker_NBETerm.Univ u,uu____5093)::args2 ->
                  aux args2 (u :: us1) ts1
              | a::args2 -> aux args2 us1 (a :: ts1)
              | [] -> (us1, ts1)  in
            let uu____5137 = aux args us ts  in
            (match uu____5137 with
             | (us',ts') -> FStar_TypeChecker_NBETerm.Construct (i, us', ts'))
        | FStar_TypeChecker_NBETerm.FV (i,us,ts) ->
            let rec aux args1 us1 ts1 =
              match args1 with
              | (FStar_TypeChecker_NBETerm.Univ u,uu____5264)::args2 ->
                  aux args2 (u :: us1) ts1
              | a::args2 -> aux args2 us1 (a :: ts1)
              | [] -> (us1, ts1)  in
            let uu____5308 = aux args us ts  in
            (match uu____5308 with
             | (us',ts') -> FStar_TypeChecker_NBETerm.FV (i, us', ts'))
        | FStar_TypeChecker_NBETerm.TopLevelLet (lb,arity,args_rev) ->
            let args_rev1 = FStar_List.rev_append args args_rev  in
            let n_args_rev = FStar_List.length args_rev1  in
            let n_univs = FStar_List.length lb.FStar_Syntax_Syntax.lbunivs
               in
            (debug cfg
               (fun uu____5386  ->
                  let uu____5387 =
                    FStar_Syntax_Print.lbname_to_string
                      lb.FStar_Syntax_Syntax.lbname
                     in
                  let uu____5389 = FStar_Util.string_of_int arity  in
                  let uu____5391 = FStar_Util.string_of_int n_args_rev  in
                  FStar_Util.print3
                    "Reached iapp for %s with arity %s and n_args = %s\n"
                    uu____5387 uu____5389 uu____5391);
             if n_args_rev >= arity
             then
               (let uu____5395 =
                  let uu____5408 =
                    let uu____5409 =
                      FStar_Syntax_Util.unascribe
                        lb.FStar_Syntax_Syntax.lbdef
                       in
                    uu____5409.FStar_Syntax_Syntax.n  in
                  match uu____5408 with
                  | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____5426) ->
                      (bs, body)
                  | uu____5459 -> ([], (lb.FStar_Syntax_Syntax.lbdef))  in
                match uu____5395 with
                | (bs,body) ->
                    if (n_univs + (FStar_List.length bs)) = arity
                    then
                      let uu____5500 =
                        FStar_Util.first_N (n_args_rev - arity) args_rev1  in
                      (match uu____5500 with
                       | (extra,args_rev2) ->
                           (debug cfg
                              (fun uu____5552  ->
                                 let uu____5553 =
                                   FStar_Syntax_Print.lbname_to_string
                                     lb.FStar_Syntax_Syntax.lbname
                                    in
                                 let uu____5555 =
                                   FStar_Syntax_Print.term_to_string body  in
                                 let uu____5557 =
                                   let uu____5559 =
                                     FStar_List.map
                                       (fun uu____5571  ->
                                          match uu____5571 with
                                          | (x,uu____5578) ->
                                              FStar_TypeChecker_NBETerm.t_to_string
                                                x) args_rev2
                                      in
                                   FStar_All.pipe_right uu____5559
                                     (FStar_String.concat ", ")
                                    in
                                 FStar_Util.print3
                                   "Reducing body of %s = %s,\n\twith args = %s\n"
                                   uu____5553 uu____5555 uu____5557);
                            (let t =
                               let uu____5586 =
                                 FStar_List.map FStar_Pervasives_Native.fst
                                   args_rev2
                                  in
                               translate cfg uu____5586 body  in
                             match extra with
                             | [] -> t
                             | uu____5597 ->
                                 iapp cfg t (FStar_List.rev extra))))
                    else
                      (let uu____5610 =
                         FStar_Util.first_N (n_args_rev - n_univs) args_rev1
                          in
                       match uu____5610 with
                       | (extra,univs1) ->
                           let uu____5657 =
                             let uu____5658 =
                               FStar_List.map FStar_Pervasives_Native.fst
                                 univs1
                                in
                             translate cfg uu____5658
                               lb.FStar_Syntax_Syntax.lbdef
                              in
                           iapp cfg uu____5657 (FStar_List.rev extra)))
             else
               FStar_TypeChecker_NBETerm.TopLevelLet (lb, arity, args_rev1))
        | FStar_TypeChecker_NBETerm.TopLevelRec
            (lb,arity,decreases_list,args') ->
            let args1 = FStar_List.append args' args  in
            if (FStar_List.length args1) >= arity
            then
              let uu____5718 =
                should_reduce_recursive_definition args1 decreases_list  in
              (match uu____5718 with
               | (should_reduce,uu____5727,uu____5728) ->
                   if Prims.op_Negation should_reduce
                   then
                     let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname
                        in
                     (debug cfg
                        (fun uu____5736  ->
                           let uu____5737 =
                             FStar_Syntax_Print.fv_to_string fv  in
                           FStar_Util.print1
                             "Decided to not unfold recursive definition %s\n"
                             uu____5737);
                      iapp cfg (FStar_TypeChecker_NBETerm.FV (fv, [], []))
                        args1)
                   else
                     (debug cfg
                        (fun uu____5757  ->
                           let uu____5758 =
                             let uu____5760 =
                               FStar_Util.right lb.FStar_Syntax_Syntax.lbname
                                in
                             FStar_Syntax_Print.fv_to_string uu____5760  in
                           FStar_Util.print1
                             "Yes, Decided to unfold recursive definition %s\n"
                             uu____5758);
                      (let uu____5762 =
                         FStar_Util.first_N
                           (FStar_List.length lb.FStar_Syntax_Syntax.lbunivs)
                           args1
                          in
                       match uu____5762 with
                       | (univs1,rest) ->
                           let uu____5809 =
                             let uu____5810 =
                               let uu____5813 =
                                 FStar_List.map FStar_Pervasives_Native.fst
                                   univs1
                                  in
                               FStar_List.rev uu____5813  in
                             translate cfg uu____5810
                               lb.FStar_Syntax_Syntax.lbdef
                              in
                           iapp cfg uu____5809 rest)))
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
                  let uu____5931 =
                    should_reduce_recursive_definition args1 decreases_list
                     in
                  match uu____5931 with
                  | (should_reduce,uu____5940,uu____5941) ->
                      if Prims.op_Negation should_reduce
                      then
                        FStar_TypeChecker_NBETerm.LocalLetRec
                          (i, lb, mutual_lbs, local_env, args1,
                            Prims.int_zero, decreases_list)
                      else
                        (let env = make_rec_env mutual_lbs local_env  in
                         debug cfg
                           (fun uu____5970  ->
                              (let uu____5972 =
                                 let uu____5974 =
                                   FStar_List.map
                                     FStar_TypeChecker_NBETerm.t_to_string
                                     env
                                    in
                                 FStar_String.concat ",\n\t " uu____5974  in
                               FStar_Util.print1
                                 "LocalLetRec Env = {\n\t%s\n}\n" uu____5972);
                              (let uu____5981 =
                                 let uu____5983 =
                                   FStar_List.map
                                     (fun uu____5995  ->
                                        match uu____5995 with
                                        | (t,uu____6002) ->
                                            FStar_TypeChecker_NBETerm.t_to_string
                                              t) args1
                                    in
                                 FStar_String.concat ",\n\t " uu____5983  in
                               FStar_Util.print1
                                 "LocalLetRec Args = {\n\t%s\n}\n" uu____5981));
                         (let uu____6005 =
                            translate cfg env lb.FStar_Syntax_Syntax.lbdef
                             in
                          iapp cfg uu____6005 args1))))
        | uu____6006 ->
            let uu____6007 =
              let uu____6009 = FStar_TypeChecker_NBETerm.t_to_string f  in
              Prims.op_Hat "NBE ill-typed application: " uu____6009  in
            failwith uu____6007

and (translate_fv :
  config ->
    FStar_TypeChecker_NBETerm.t Prims.list ->
      FStar_Syntax_Syntax.fv -> FStar_TypeChecker_NBETerm.t)
  =
  fun cfg  ->
    fun bs  ->
      fun fvar1  ->
        let debug1 = debug cfg  in
        let qninfo =
          let uu____6026 = FStar_TypeChecker_Cfg.cfg_env cfg.core_cfg  in
          let uu____6027 = FStar_Syntax_Syntax.lid_of_fv fvar1  in
          FStar_TypeChecker_Env.lookup_qname uu____6026 uu____6027  in
        let uu____6028 = (is_constr qninfo) || (is_constr_fv fvar1)  in
        if uu____6028
        then FStar_TypeChecker_NBETerm.mkConstruct fvar1 [] []
        else
          (let uu____6037 =
             FStar_TypeChecker_Normalize.should_unfold cfg.core_cfg
               (fun uu____6039  ->
                  (cfg.core_cfg).FStar_TypeChecker_Cfg.reifying) fvar1 qninfo
              in
           match uu____6037 with
           | FStar_TypeChecker_Normalize.Should_unfold_fully  ->
               failwith "Not yet handled"
           | FStar_TypeChecker_Normalize.Should_unfold_no  ->
               (debug1
                  (fun uu____6046  ->
                     let uu____6047 = FStar_Syntax_Print.fv_to_string fvar1
                        in
                     FStar_Util.print1 "(1) Decided to not unfold %s\n"
                       uu____6047);
                (let uu____6050 =
                   FStar_TypeChecker_Cfg.find_prim_step cfg.core_cfg fvar1
                    in
                 match uu____6050 with
                 | FStar_Pervasives_Native.Some prim_step when
                     prim_step.FStar_TypeChecker_Cfg.strong_reduction_ok ->
                     let arity =
                       prim_step.FStar_TypeChecker_Cfg.arity +
                         prim_step.FStar_TypeChecker_Cfg.univ_arity
                        in
                     (debug1
                        (fun uu____6061  ->
                           let uu____6062 =
                             FStar_Syntax_Print.fv_to_string fvar1  in
                           FStar_Util.print1 "Found a primop %s\n" uu____6062);
                      (let uu____6065 =
                         let uu____6098 =
                           let f uu____6131 =
                             let uu____6133 =
                               FStar_Syntax_Syntax.new_bv
                                 FStar_Pervasives_Native.None
                                 FStar_Syntax_Syntax.t_unit
                                in
                             (uu____6133, FStar_Pervasives_Native.None)  in
                           let uu____6136 =
                             let uu____6147 = FStar_Common.tabulate arity f
                                in
                             ([], uu____6147, FStar_Pervasives_Native.None)
                              in
                           FStar_Util.Inl uu____6136  in
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
                             let uu____6221 =
                               prim_step.FStar_TypeChecker_Cfg.interpretation_nbe
                                 callbacks args'
                                in
                             match uu____6221 with
                             | FStar_Pervasives_Native.Some x ->
                                 (debug1
                                    (fun uu____6232  ->
                                       let uu____6233 =
                                         FStar_Syntax_Print.fv_to_string
                                           fvar1
                                          in
                                       let uu____6235 =
                                         FStar_TypeChecker_NBETerm.t_to_string
                                           x
                                          in
                                       FStar_Util.print2
                                         "Primitive operator %s returned %s\n"
                                         uu____6233 uu____6235);
                                  x)
                             | FStar_Pervasives_Native.None  ->
                                 (debug1
                                    (fun uu____6243  ->
                                       let uu____6244 =
                                         FStar_Syntax_Print.fv_to_string
                                           fvar1
                                          in
                                       FStar_Util.print1
                                         "Primitive operator %s failed\n"
                                         uu____6244);
                                  (let uu____6247 =
                                     FStar_TypeChecker_NBETerm.mkFV fvar1 []
                                       []
                                      in
                                   iapp cfg uu____6247 args'))), uu____6098,
                           arity)
                          in
                       FStar_TypeChecker_NBETerm.Lam uu____6065))
                 | FStar_Pervasives_Native.Some uu____6252 ->
                     (debug1
                        (fun uu____6258  ->
                           let uu____6259 =
                             FStar_Syntax_Print.fv_to_string fvar1  in
                           FStar_Util.print1 "(2) Decided to not unfold %s\n"
                             uu____6259);
                      FStar_TypeChecker_NBETerm.mkFV fvar1 [] [])
                 | uu____6266 ->
                     (debug1
                        (fun uu____6274  ->
                           let uu____6275 =
                             FStar_Syntax_Print.fv_to_string fvar1  in
                           FStar_Util.print1 "(3) Decided to not unfold %s\n"
                             uu____6275);
                      FStar_TypeChecker_NBETerm.mkFV fvar1 [] [])))
           | FStar_TypeChecker_Normalize.Should_unfold_reify  ->
               let t =
                 let is_qninfo_visible =
                   let uu____6285 =
                     FStar_TypeChecker_Env.lookup_definition_qninfo
                       (cfg.core_cfg).FStar_TypeChecker_Cfg.delta_level
                       (fvar1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                       qninfo
                      in
                   FStar_Option.isSome uu____6285  in
                 if is_qninfo_visible
                 then
                   match qninfo with
                   | FStar_Pervasives_Native.Some
                       (FStar_Util.Inr
                        ({
                           FStar_Syntax_Syntax.sigel =
                             FStar_Syntax_Syntax.Sig_let
                             ((is_rec,lbs),names1);
                           FStar_Syntax_Syntax.sigrng = uu____6300;
                           FStar_Syntax_Syntax.sigquals = uu____6301;
                           FStar_Syntax_Syntax.sigmeta = uu____6302;
                           FStar_Syntax_Syntax.sigattrs = uu____6303;
                           FStar_Syntax_Syntax.sigopts = uu____6304;_},_us_opt),_rng)
                       ->
                       (debug1
                          (fun uu____6374  ->
                             let uu____6375 =
                               FStar_Syntax_Print.fv_to_string fvar1  in
                             FStar_Util.print1 "(1) Decided to unfold %s\n"
                               uu____6375);
                        (let lbm = find_let lbs fvar1  in
                         match lbm with
                         | FStar_Pervasives_Native.Some lb ->
                             if
                               is_rec &&
                                 ((cfg.core_cfg).FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta
                             then
                               let uu____6383 = let_rec_arity lb  in
                               (match uu____6383 with
                                | (ar,lst) ->
                                    FStar_TypeChecker_NBETerm.TopLevelRec
                                      (lb, ar, lst, []))
                             else translate_letbinding cfg bs lb
                         | FStar_Pervasives_Native.None  ->
                             failwith "Could not find let binding"))
                   | uu____6419 ->
                       (debug1
                          (fun uu____6425  ->
                             let uu____6426 =
                               FStar_Syntax_Print.fv_to_string fvar1  in
                             FStar_Util.print1
                               "(1) qninfo is None for (%s)\n" uu____6426);
                        FStar_TypeChecker_NBETerm.mkFV fvar1 [] [])
                 else
                   (debug1
                      (fun uu____6440  ->
                         let uu____6441 =
                           FStar_Syntax_Print.fv_to_string fvar1  in
                         FStar_Util.print1
                           "(1) qninfo is not visible at this level (%s)\n"
                           uu____6441);
                    FStar_TypeChecker_NBETerm.mkFV fvar1 [] [])
                  in
               (cache_add cfg fvar1 t; t)
           | FStar_TypeChecker_Normalize.Should_unfold_yes  ->
               let t =
                 let is_qninfo_visible =
                   let uu____6452 =
                     FStar_TypeChecker_Env.lookup_definition_qninfo
                       (cfg.core_cfg).FStar_TypeChecker_Cfg.delta_level
                       (fvar1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                       qninfo
                      in
                   FStar_Option.isSome uu____6452  in
                 if is_qninfo_visible
                 then
                   match qninfo with
                   | FStar_Pervasives_Native.Some
                       (FStar_Util.Inr
                        ({
                           FStar_Syntax_Syntax.sigel =
                             FStar_Syntax_Syntax.Sig_let
                             ((is_rec,lbs),names1);
                           FStar_Syntax_Syntax.sigrng = uu____6467;
                           FStar_Syntax_Syntax.sigquals = uu____6468;
                           FStar_Syntax_Syntax.sigmeta = uu____6469;
                           FStar_Syntax_Syntax.sigattrs = uu____6470;
                           FStar_Syntax_Syntax.sigopts = uu____6471;_},_us_opt),_rng)
                       ->
                       (debug1
                          (fun uu____6541  ->
                             let uu____6542 =
                               FStar_Syntax_Print.fv_to_string fvar1  in
                             FStar_Util.print1 "(1) Decided to unfold %s\n"
                               uu____6542);
                        (let lbm = find_let lbs fvar1  in
                         match lbm with
                         | FStar_Pervasives_Native.Some lb ->
                             if
                               is_rec &&
                                 ((cfg.core_cfg).FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta
                             then
                               let uu____6550 = let_rec_arity lb  in
                               (match uu____6550 with
                                | (ar,lst) ->
                                    FStar_TypeChecker_NBETerm.TopLevelRec
                                      (lb, ar, lst, []))
                             else translate_letbinding cfg bs lb
                         | FStar_Pervasives_Native.None  ->
                             failwith "Could not find let binding"))
                   | uu____6586 ->
                       (debug1
                          (fun uu____6592  ->
                             let uu____6593 =
                               FStar_Syntax_Print.fv_to_string fvar1  in
                             FStar_Util.print1
                               "(1) qninfo is None for (%s)\n" uu____6593);
                        FStar_TypeChecker_NBETerm.mkFV fvar1 [] [])
                 else
                   (debug1
                      (fun uu____6607  ->
                         let uu____6608 =
                           FStar_Syntax_Print.fv_to_string fvar1  in
                         FStar_Util.print1
                           "(1) qninfo is not visible at this level (%s)\n"
                           uu____6608);
                    FStar_TypeChecker_NBETerm.mkFV fvar1 [] [])
                  in
               (cache_add cfg fvar1 t; t))

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
        let uu____6632 =
          FStar_Syntax_Util.arrow_formals lb.FStar_Syntax_Syntax.lbtyp  in
        match uu____6632 with
        | (formals,uu____6648) ->
            let arity = (FStar_List.length us) + (FStar_List.length formals)
               in
            if arity = Prims.int_zero
            then translate cfg bs lb.FStar_Syntax_Syntax.lbdef
            else
              (let uu____6682 =
                 FStar_Util.is_right lb.FStar_Syntax_Syntax.lbname  in
               if uu____6682
               then
                 (debug1
                    (fun uu____6692  ->
                       let uu____6693 =
                         FStar_Syntax_Print.lbname_to_string
                           lb.FStar_Syntax_Syntax.lbname
                          in
                       let uu____6695 = FStar_Util.string_of_int arity  in
                       FStar_Util.print2
                         "Making TopLevelLet for %s with arity %s\n"
                         uu____6693 uu____6695);
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
          let uu____6720 = let_rec_arity b  in
          match uu____6720 with
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
        let uu____6790 = FStar_BigInt.big_int_of_string s  in
        FStar_TypeChecker_NBETerm.Int uu____6790
    | FStar_Const.Const_string (s,r) ->
        FStar_TypeChecker_NBETerm.String (s, r)
    | FStar_Const.Const_char c1 -> FStar_TypeChecker_NBETerm.Char c1
    | FStar_Const.Const_range r -> FStar_TypeChecker_NBETerm.Range r
    | uu____6799 ->
        let uu____6800 =
          let uu____6802 =
            let uu____6804 = FStar_Syntax_Print.const_to_string c  in
            Prims.op_Hat uu____6804 ": Not yet implemented"  in
          Prims.op_Hat "Tm_constant " uu____6802  in
        failwith uu____6800

and (readback_comp :
  config -> FStar_TypeChecker_NBETerm.comp -> FStar_Syntax_Syntax.comp) =
  fun cfg  ->
    fun c  ->
      let c' =
        match c with
        | FStar_TypeChecker_NBETerm.Tot (typ,u) ->
            let uu____6817 =
              let uu____6826 = readback cfg typ  in (uu____6826, u)  in
            FStar_Syntax_Syntax.Total uu____6817
        | FStar_TypeChecker_NBETerm.GTot (typ,u) ->
            let uu____6839 =
              let uu____6848 = readback cfg typ  in (uu____6848, u)  in
            FStar_Syntax_Syntax.GTotal uu____6839
        | FStar_TypeChecker_NBETerm.Comp ctyp ->
            let uu____6856 = readback_comp_typ cfg ctyp  in
            FStar_Syntax_Syntax.Comp uu____6856
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
        let uu____6862 = c  in
        match uu____6862 with
        | { FStar_Syntax_Syntax.comp_univs = comp_univs;
            FStar_Syntax_Syntax.effect_name = effect_name;
            FStar_Syntax_Syntax.result_typ = result_typ;
            FStar_Syntax_Syntax.effect_args = effect_args;
            FStar_Syntax_Syntax.flags = flags;_} ->
            let uu____6882 =
              FStar_List.map (translate_univ cfg bs) comp_univs  in
            let uu____6883 = translate cfg bs result_typ  in
            let uu____6884 =
              FStar_List.map
                (fun x  ->
                   let uu____6912 =
                     translate cfg bs (FStar_Pervasives_Native.fst x)  in
                   (uu____6912, (FStar_Pervasives_Native.snd x))) effect_args
               in
            let uu____6919 = FStar_List.map (translate_flag cfg bs) flags  in
            {
              FStar_TypeChecker_NBETerm.comp_univs = uu____6882;
              FStar_TypeChecker_NBETerm.effect_name = effect_name;
              FStar_TypeChecker_NBETerm.result_typ = uu____6883;
              FStar_TypeChecker_NBETerm.effect_args = uu____6884;
              FStar_TypeChecker_NBETerm.flags = uu____6919
            }

and (readback_comp_typ :
  config ->
    FStar_TypeChecker_NBETerm.comp_typ -> FStar_Syntax_Syntax.comp_typ)
  =
  fun cfg  ->
    fun c  ->
      let uu____6924 = readback cfg c.FStar_TypeChecker_NBETerm.result_typ
         in
      let uu____6927 =
        FStar_List.map
          (fun x  ->
             let uu____6953 = readback cfg (FStar_Pervasives_Native.fst x)
                in
             (uu____6953, (FStar_Pervasives_Native.snd x)))
          c.FStar_TypeChecker_NBETerm.effect_args
         in
      let uu____6954 =
        FStar_List.map (readback_flag cfg) c.FStar_TypeChecker_NBETerm.flags
         in
      {
        FStar_Syntax_Syntax.comp_univs =
          (c.FStar_TypeChecker_NBETerm.comp_univs);
        FStar_Syntax_Syntax.effect_name =
          (c.FStar_TypeChecker_NBETerm.effect_name);
        FStar_Syntax_Syntax.result_typ = uu____6924;
        FStar_Syntax_Syntax.effect_args = uu____6927;
        FStar_Syntax_Syntax.flags = uu____6954
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
        let uu____6962 = c  in
        match uu____6962 with
        | { FStar_Syntax_Syntax.residual_effect = residual_effect;
            FStar_Syntax_Syntax.residual_typ = residual_typ;
            FStar_Syntax_Syntax.residual_flags = residual_flags;_} ->
            let uu____6972 =
              if
                ((cfg.core_cfg).FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.for_extraction
              then FStar_Pervasives_Native.None
              else FStar_Util.map_opt residual_typ (translate cfg bs)  in
            let uu____6982 =
              FStar_List.map (translate_flag cfg bs) residual_flags  in
            {
              FStar_TypeChecker_NBETerm.residual_effect = residual_effect;
              FStar_TypeChecker_NBETerm.residual_typ = uu____6972;
              FStar_TypeChecker_NBETerm.residual_flags = uu____6982
            }

and (readback_residual_comp :
  config ->
    FStar_TypeChecker_NBETerm.residual_comp ->
      FStar_Syntax_Syntax.residual_comp)
  =
  fun cfg  ->
    fun c  ->
      let uu____6987 =
        FStar_Util.map_opt c.FStar_TypeChecker_NBETerm.residual_typ
          (fun x  ->
             debug cfg
               (fun uu____6998  ->
                  let uu____6999 = FStar_TypeChecker_NBETerm.t_to_string x
                     in
                  FStar_Util.print1 "Reading back residualtype %s\n"
                    uu____6999);
             readback cfg x)
         in
      let uu____7002 =
        FStar_List.map (readback_flag cfg)
          c.FStar_TypeChecker_NBETerm.residual_flags
         in
      {
        FStar_Syntax_Syntax.residual_effect =
          (c.FStar_TypeChecker_NBETerm.residual_effect);
        FStar_Syntax_Syntax.residual_typ = uu____6987;
        FStar_Syntax_Syntax.residual_flags = uu____7002
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
            let uu____7013 = translate cfg bs tm  in
            FStar_TypeChecker_NBETerm.DECREASES uu____7013

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
          let uu____7017 = readback cfg t  in
          FStar_Syntax_Syntax.DECREASES uu____7017

and (translate_monadic :
  (FStar_Syntax_Syntax.monad_name * FStar_Syntax_Syntax.term'
    FStar_Syntax_Syntax.syntax) ->
    config ->
      FStar_TypeChecker_NBETerm.t Prims.list ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
          FStar_TypeChecker_NBETerm.t)
  =
  fun uu____7020  ->
    fun cfg  ->
      fun bs  ->
        fun e  ->
          match uu____7020 with
          | (m,ty) ->
              let e1 = FStar_Syntax_Util.unascribe e  in
              (match e1.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                   let uu____7058 =
                     let uu____7067 =
                       FStar_TypeChecker_Env.norm_eff_name
                         (cfg.core_cfg).FStar_TypeChecker_Cfg.tcenv m
                        in
                     FStar_TypeChecker_Env.effect_decl_opt
                       (cfg.core_cfg).FStar_TypeChecker_Cfg.tcenv uu____7067
                      in
                   (match uu____7058 with
                    | FStar_Pervasives_Native.None  ->
                        let uu____7074 =
                          let uu____7076 = FStar_Ident.string_of_lid m  in
                          FStar_Util.format1
                            "Effect declaration not found: %s" uu____7076
                           in
                        failwith uu____7074
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
                          let uu____7098 =
                            let uu____7105 =
                              let uu____7106 =
                                let uu____7125 =
                                  let uu____7134 =
                                    let uu____7141 =
                                      FStar_Util.left
                                        lb.FStar_Syntax_Syntax.lbname
                                       in
                                    (uu____7141,
                                      FStar_Pervasives_Native.None)
                                     in
                                  [uu____7134]  in
                                (uu____7125, body,
                                  (FStar_Pervasives_Native.Some body_rc))
                                 in
                              FStar_Syntax_Syntax.Tm_abs uu____7106  in
                            FStar_Syntax_Syntax.mk uu____7105  in
                          uu____7098 FStar_Pervasives_Native.None
                            body.FStar_Syntax_Syntax.pos
                           in
                        let maybe_range_arg =
                          let uu____7175 =
                            FStar_Util.for_some
                              (FStar_Syntax_Util.attr_eq
                                 FStar_Syntax_Util.dm4f_bind_range_attr)
                              ed.FStar_Syntax_Syntax.eff_attrs
                             in
                          if uu____7175
                          then
                            let uu____7184 =
                              let uu____7189 =
                                let uu____7190 =
                                  FStar_TypeChecker_Cfg.embed_simple
                                    FStar_Syntax_Embeddings.e_range
                                    lb.FStar_Syntax_Syntax.lbpos
                                    lb.FStar_Syntax_Syntax.lbpos
                                   in
                                translate cfg [] uu____7190  in
                              (uu____7189, FStar_Pervasives_Native.None)  in
                            let uu____7191 =
                              let uu____7198 =
                                let uu____7203 =
                                  let uu____7204 =
                                    FStar_TypeChecker_Cfg.embed_simple
                                      FStar_Syntax_Embeddings.e_range
                                      body.FStar_Syntax_Syntax.pos
                                      body.FStar_Syntax_Syntax.pos
                                     in
                                  translate cfg [] uu____7204  in
                                (uu____7203, FStar_Pervasives_Native.None)
                                 in
                              [uu____7198]  in
                            uu____7184 :: uu____7191
                          else []  in
                        let t =
                          let uu____7224 =
                            let uu____7225 =
                              let uu____7226 =
                                let uu____7227 =
                                  let uu____7228 =
                                    let uu____7235 =
                                      FStar_All.pipe_right ed
                                        FStar_Syntax_Util.get_bind_repr
                                       in
                                    FStar_All.pipe_right uu____7235
                                      FStar_Util.must
                                     in
                                  FStar_All.pipe_right uu____7228
                                    FStar_Pervasives_Native.snd
                                   in
                                FStar_Syntax_Util.un_uinst uu____7227  in
                              translate cfg' [] uu____7226  in
                            iapp cfg uu____7225
                              [((FStar_TypeChecker_NBETerm.Univ
                                   FStar_Syntax_Syntax.U_unknown),
                                 FStar_Pervasives_Native.None);
                              ((FStar_TypeChecker_NBETerm.Univ
                                  FStar_Syntax_Syntax.U_unknown),
                                FStar_Pervasives_Native.None)]
                             in
                          let uu____7268 =
                            let uu____7269 =
                              let uu____7276 =
                                let uu____7281 =
                                  translate cfg' bs
                                    lb.FStar_Syntax_Syntax.lbtyp
                                   in
                                (uu____7281, FStar_Pervasives_Native.None)
                                 in
                              let uu____7282 =
                                let uu____7289 =
                                  let uu____7294 = translate cfg' bs ty  in
                                  (uu____7294, FStar_Pervasives_Native.None)
                                   in
                                [uu____7289]  in
                              uu____7276 :: uu____7282  in
                            let uu____7307 =
                              let uu____7314 =
                                let uu____7321 =
                                  let uu____7328 =
                                    let uu____7333 =
                                      translate cfg bs
                                        lb.FStar_Syntax_Syntax.lbdef
                                       in
                                    (uu____7333,
                                      FStar_Pervasives_Native.None)
                                     in
                                  let uu____7334 =
                                    let uu____7341 =
                                      let uu____7348 =
                                        let uu____7353 =
                                          translate cfg bs body_lam  in
                                        (uu____7353,
                                          FStar_Pervasives_Native.None)
                                         in
                                      [uu____7348]  in
                                    (FStar_TypeChecker_NBETerm.Unknown,
                                      FStar_Pervasives_Native.None) ::
                                      uu____7341
                                     in
                                  uu____7328 :: uu____7334  in
                                (FStar_TypeChecker_NBETerm.Unknown,
                                  FStar_Pervasives_Native.None) :: uu____7321
                                 in
                              FStar_List.append maybe_range_arg uu____7314
                               in
                            FStar_List.append uu____7269 uu____7307  in
                          iapp cfg uu____7224 uu____7268  in
                        (debug cfg
                           (fun uu____7385  ->
                              let uu____7386 =
                                FStar_TypeChecker_NBETerm.t_to_string t  in
                              FStar_Util.print1 "translate_monadic: %s\n"
                                uu____7386);
                         t))
               | FStar_Syntax_Syntax.Tm_app
                   ({
                      FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                        (FStar_Const.Const_reflect uu____7389);
                      FStar_Syntax_Syntax.pos = uu____7390;
                      FStar_Syntax_Syntax.vars = uu____7391;_},(e2,uu____7393)::[])
                   ->
                   let uu____7432 = reifying_false cfg  in
                   translate uu____7432 bs e2
               | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                   (debug cfg
                      (fun uu____7463  ->
                         let uu____7464 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____7466 =
                           FStar_Syntax_Print.args_to_string args  in
                         FStar_Util.print2
                           "translate_monadic app (%s) @ (%s)\n" uu____7464
                           uu____7466);
                    (let fallback1 uu____7474 = translate cfg bs e1  in
                     let fallback2 uu____7480 =
                       let uu____7481 = reifying_false cfg  in
                       let uu____7482 =
                         FStar_Syntax_Syntax.mk
                           (FStar_Syntax_Syntax.Tm_meta
                              (e1,
                                (FStar_Syntax_Syntax.Meta_monadic (m, ty))))
                           FStar_Pervasives_Native.None
                           e1.FStar_Syntax_Syntax.pos
                          in
                       translate uu____7481 bs uu____7482  in
                     let uu____7487 =
                       let uu____7488 = FStar_Syntax_Util.un_uinst head1  in
                       uu____7488.FStar_Syntax_Syntax.n  in
                     match uu____7487 with
                     | FStar_Syntax_Syntax.Tm_fvar fv ->
                         let lid = FStar_Syntax_Syntax.lid_of_fv fv  in
                         let qninfo =
                           FStar_TypeChecker_Env.lookup_qname
                             (cfg.core_cfg).FStar_TypeChecker_Cfg.tcenv lid
                            in
                         let uu____7494 =
                           let uu____7496 =
                             FStar_TypeChecker_Env.is_action
                               (cfg.core_cfg).FStar_TypeChecker_Cfg.tcenv lid
                              in
                           Prims.op_Negation uu____7496  in
                         if uu____7494
                         then fallback1 ()
                         else
                           (let uu____7501 =
                              let uu____7503 =
                                FStar_TypeChecker_Env.lookup_definition_qninfo
                                  (cfg.core_cfg).FStar_TypeChecker_Cfg.delta_level
                                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                  qninfo
                                 in
                              FStar_Option.isNone uu____7503  in
                            if uu____7501
                            then fallback2 ()
                            else
                              (let e2 =
                                 let uu____7520 =
                                   let uu____7525 =
                                     FStar_Syntax_Util.mk_reify head1  in
                                   FStar_Syntax_Syntax.mk_Tm_app uu____7525
                                     args
                                    in
                                 uu____7520 FStar_Pervasives_Native.None
                                   e1.FStar_Syntax_Syntax.pos
                                  in
                               let uu____7526 = reifying_false cfg  in
                               translate uu____7526 bs e2))
                     | uu____7527 -> fallback1 ()))
               | FStar_Syntax_Syntax.Tm_match (sc,branches) ->
                   let branches1 =
                     FStar_All.pipe_right branches
                       (FStar_List.map
                          (fun uu____7648  ->
                             match uu____7648 with
                             | (pat,wopt,tm) ->
                                 let uu____7696 =
                                   FStar_Syntax_Util.mk_reify tm  in
                                 (pat, wopt, uu____7696)))
                      in
                   let tm =
                     FStar_Syntax_Syntax.mk
                       (FStar_Syntax_Syntax.Tm_match (sc, branches1))
                       FStar_Pervasives_Native.None
                       e1.FStar_Syntax_Syntax.pos
                      in
                   let uu____7728 = reifying_false cfg  in
                   translate uu____7728 bs tm
               | FStar_Syntax_Syntax.Tm_meta
                   (t,FStar_Syntax_Syntax.Meta_monadic uu____7730) ->
                   translate_monadic (m, ty) cfg bs e1
               | FStar_Syntax_Syntax.Tm_meta
                   (t,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,ty'))
                   -> translate_monadic_lift (msrc, mtgt, ty') cfg bs e1
               | uu____7757 ->
                   let uu____7758 =
                     let uu____7760 = FStar_Syntax_Print.tag_of_term e1  in
                     FStar_Util.format1
                       "Unexpected case in translate_monadic: %s" uu____7760
                      in
                   failwith uu____7758)

and (translate_monadic_lift :
  (FStar_Syntax_Syntax.monad_name * FStar_Syntax_Syntax.monad_name *
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax) ->
    config ->
      FStar_TypeChecker_NBETerm.t Prims.list ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
          FStar_TypeChecker_NBETerm.t)
  =
  fun uu____7763  ->
    fun cfg  ->
      fun bs  ->
        fun e  ->
          match uu____7763 with
          | (msrc,mtgt,ty) ->
              let e1 = FStar_Syntax_Util.unascribe e  in
              let uu____7787 =
                (FStar_Syntax_Util.is_pure_effect msrc) ||
                  (FStar_Syntax_Util.is_div_effect msrc)
                 in
              if uu____7787
              then
                let ed =
                  let uu____7791 =
                    FStar_TypeChecker_Env.norm_eff_name
                      (cfg.core_cfg).FStar_TypeChecker_Cfg.tcenv mtgt
                     in
                  FStar_TypeChecker_Env.get_effect_decl
                    (cfg.core_cfg).FStar_TypeChecker_Cfg.tcenv uu____7791
                   in
                let ret1 =
                  let uu____7793 =
                    let uu____7794 =
                      let uu____7797 =
                        let uu____7798 =
                          let uu____7805 =
                            FStar_All.pipe_right ed
                              FStar_Syntax_Util.get_return_repr
                             in
                          FStar_All.pipe_right uu____7805 FStar_Util.must  in
                        FStar_All.pipe_right uu____7798
                          FStar_Pervasives_Native.snd
                         in
                      FStar_Syntax_Subst.compress uu____7797  in
                    uu____7794.FStar_Syntax_Syntax.n  in
                  match uu____7793 with
                  | FStar_Syntax_Syntax.Tm_uinst (ret1,uu____7851::[]) ->
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_uinst
                           (ret1, [FStar_Syntax_Syntax.U_unknown]))
                        FStar_Pervasives_Native.None
                        e1.FStar_Syntax_Syntax.pos
                  | uu____7858 ->
                      failwith "NYI: Reification of indexed effect (NBE)"
                   in
                let cfg' = reifying_false cfg  in
                let t =
                  let uu____7862 =
                    let uu____7863 = translate cfg' [] ret1  in
                    iapp cfg' uu____7863
                      [((FStar_TypeChecker_NBETerm.Univ
                           FStar_Syntax_Syntax.U_unknown),
                         FStar_Pervasives_Native.None)]
                     in
                  let uu____7872 =
                    let uu____7873 =
                      let uu____7878 = translate cfg' bs ty  in
                      (uu____7878, FStar_Pervasives_Native.None)  in
                    let uu____7879 =
                      let uu____7886 =
                        let uu____7891 = translate cfg' bs e1  in
                        (uu____7891, FStar_Pervasives_Native.None)  in
                      [uu____7886]  in
                    uu____7873 :: uu____7879  in
                  iapp cfg' uu____7862 uu____7872  in
                (debug cfg
                   (fun uu____7907  ->
                      let uu____7908 =
                        FStar_TypeChecker_NBETerm.t_to_string t  in
                      FStar_Util.print1 "translate_monadic_lift(1): %s\n"
                        uu____7908);
                 t)
              else
                (let uu____7913 =
                   FStar_TypeChecker_Env.monad_leq
                     (cfg.core_cfg).FStar_TypeChecker_Cfg.tcenv msrc mtgt
                    in
                 match uu____7913 with
                 | FStar_Pervasives_Native.None  ->
                     let uu____7916 =
                       let uu____7918 = FStar_Ident.text_of_lid msrc  in
                       let uu____7920 = FStar_Ident.text_of_lid mtgt  in
                       FStar_Util.format2
                         "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                         uu____7918 uu____7920
                        in
                     failwith uu____7916
                 | FStar_Pervasives_Native.Some
                     { FStar_TypeChecker_Env.msource = uu____7923;
                       FStar_TypeChecker_Env.mtarget = uu____7924;
                       FStar_TypeChecker_Env.mlift =
                         { FStar_TypeChecker_Env.mlift_wp = uu____7925;
                           FStar_TypeChecker_Env.mlift_term =
                             FStar_Pervasives_Native.None ;_};_}
                     ->
                     let uu____7945 =
                       let uu____7947 = FStar_Ident.text_of_lid msrc  in
                       let uu____7949 = FStar_Ident.text_of_lid mtgt  in
                       FStar_Util.format2
                         "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
                         uu____7947 uu____7949
                        in
                     failwith uu____7945
                 | FStar_Pervasives_Native.Some
                     { FStar_TypeChecker_Env.msource = uu____7952;
                       FStar_TypeChecker_Env.mtarget = uu____7953;
                       FStar_TypeChecker_Env.mlift =
                         { FStar_TypeChecker_Env.mlift_wp = uu____7954;
                           FStar_TypeChecker_Env.mlift_term =
                             FStar_Pervasives_Native.Some lift;_};_}
                     ->
                     let lift_lam =
                       let x =
                         FStar_Syntax_Syntax.new_bv
                           FStar_Pervasives_Native.None
                           FStar_Syntax_Syntax.tun
                          in
                       let uu____7988 =
                         let uu____7991 = FStar_Syntax_Syntax.bv_to_name x
                            in
                         lift FStar_Syntax_Syntax.U_unknown ty uu____7991  in
                       FStar_Syntax_Util.abs
                         [(x, FStar_Pervasives_Native.None)] uu____7988
                         FStar_Pervasives_Native.None
                        in
                     let cfg' = reifying_false cfg  in
                     let t =
                       let uu____8008 = translate cfg' [] lift_lam  in
                       let uu____8009 =
                         let uu____8010 =
                           let uu____8015 = translate cfg bs e1  in
                           (uu____8015, FStar_Pervasives_Native.None)  in
                         [uu____8010]  in
                       iapp cfg uu____8008 uu____8009  in
                     (debug cfg
                        (fun uu____8027  ->
                           let uu____8028 =
                             FStar_TypeChecker_NBETerm.t_to_string t  in
                           FStar_Util.print1
                             "translate_monadic_lift(2): %s\n" uu____8028);
                      t))

and (readback :
  config -> FStar_TypeChecker_NBETerm.t -> FStar_Syntax_Syntax.term) =
  fun cfg  ->
    fun x  ->
      let debug1 = debug cfg  in
      let readback_args cfg1 args =
        map_rev
          (fun uu____8082  ->
             match uu____8082 with
             | (x1,q) ->
                 let uu____8093 = readback cfg1 x1  in (uu____8093, q)) args
         in
      debug1
        (fun uu____8099  ->
           let uu____8100 = FStar_TypeChecker_NBETerm.t_to_string x  in
           FStar_Util.print1 "Readback: %s\n" uu____8100);
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
           let uu____8108 = FStar_BigInt.string_of_big_int i  in
           FStar_All.pipe_right uu____8108 FStar_Syntax_Util.exp_int
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
       | FStar_TypeChecker_NBETerm.Type_t u ->
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type u)
             FStar_Pervasives_Native.None FStar_Range.dummyRange
       | FStar_TypeChecker_NBETerm.Lam (f,binders,arity) ->
           let uu____8175 =
             match binders with
             | FStar_Util.Inl (ctx,binders1,rc) ->
                 let uu____8223 =
                   FStar_List.fold_left
                     (fun uu____8277  ->
                        fun uu____8278  ->
                          match (uu____8277, uu____8278) with
                          | ((ctx1,binders_rev,accus_rev),(x1,q)) ->
                              let tnorm =
                                let uu____8403 =
                                  translate cfg ctx1
                                    x1.FStar_Syntax_Syntax.sort
                                   in
                                readback cfg uu____8403  in
                              let x2 =
                                let uu___1220_8405 =
                                  FStar_Syntax_Syntax.freshen_bv x1  in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___1220_8405.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___1220_8405.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = tnorm
                                }  in
                              let ax = FStar_TypeChecker_NBETerm.mkAccuVar x2
                                 in
                              let ctx2 = ax :: ctx1  in
                              (ctx2, ((x2, q) :: binders_rev), (ax ::
                                accus_rev))) (ctx, [], []) binders1
                    in
                 (match uu____8223 with
                  | (ctx1,binders_rev,accus_rev) ->
                      let rc1 =
                        match rc with
                        | FStar_Pervasives_Native.None  ->
                            FStar_Pervasives_Native.None
                        | FStar_Pervasives_Native.Some rc1 ->
                            let uu____8491 =
                              let uu____8492 =
                                translate_residual_comp cfg ctx1 rc1  in
                              readback_residual_comp cfg uu____8492  in
                            FStar_Pervasives_Native.Some uu____8491
                         in
                      ((FStar_List.rev binders_rev), accus_rev, rc1))
             | FStar_Util.Inr args ->
                 let uu____8526 =
                   FStar_List.fold_right
                     (fun uu____8567  ->
                        fun uu____8568  ->
                          match (uu____8567, uu____8568) with
                          | ((t,uu____8620),(binders1,accus)) ->
                              let x1 =
                                let uu____8662 = readback cfg t  in
                                FStar_Syntax_Syntax.new_bv
                                  FStar_Pervasives_Native.None uu____8662
                                 in
                              let uu____8663 =
                                let uu____8666 =
                                  FStar_TypeChecker_NBETerm.mkAccuVar x1  in
                                uu____8666 :: accus  in
                              (((x1, FStar_Pervasives_Native.None) ::
                                binders1), uu____8663)) args ([], [])
                    in
                 (match uu____8526 with
                  | (binders1,accus) ->
                      (binders1, (FStar_List.rev accus),
                        FStar_Pervasives_Native.None))
              in
           (match uu____8175 with
            | (binders1,accus_rev,rc) ->
                let body =
                  let uu____8749 = f accus_rev  in readback cfg uu____8749
                   in
                FStar_Syntax_Util.abs binders1 body rc)
       | FStar_TypeChecker_NBETerm.Refinement (f,targ) ->
           if
             ((cfg.core_cfg).FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.for_extraction
           then
             let uu____8773 =
               let uu____8774 = targ ()  in
               FStar_Pervasives_Native.fst uu____8774  in
             readback cfg uu____8773
           else
             (let x1 =
                let uu____8782 =
                  let uu____8783 =
                    let uu____8784 = targ ()  in
                    FStar_Pervasives_Native.fst uu____8784  in
                  readback cfg uu____8783  in
                FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                  uu____8782
                 in
              let body =
                let uu____8790 =
                  let uu____8791 = FStar_TypeChecker_NBETerm.mkAccuVar x1  in
                  f uu____8791  in
                readback cfg uu____8790  in
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
               (fun uu____8861  ->
                  match uu____8861 with
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
               (fun uu____8913  ->
                  match uu____8913 with
                  | (x1,q) ->
                      let uu____8924 = readback cfg x1  in (uu____8924, q))
               args
              in
           let fv1 =
             FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
               FStar_Pervasives_Native.None FStar_Range.dummyRange
              in
           let app =
             let uu____8931 =
               FStar_Syntax_Syntax.mk_Tm_uinst fv1 (FStar_List.rev us)  in
             FStar_Syntax_Util.mk_app uu____8931 args1  in
           app
       | FStar_TypeChecker_NBETerm.FV (fv,us,args) ->
           let args1 =
             map_rev
               (fun uu____8972  ->
                  match uu____8972 with
                  | (x1,q) ->
                      let uu____8983 = readback cfg x1  in (uu____8983, q))
               args
              in
           let fv1 =
             FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
               FStar_Pervasives_Native.None FStar_Range.dummyRange
              in
           let app =
             let uu____8990 =
               FStar_Syntax_Syntax.mk_Tm_uinst fv1 (FStar_List.rev us)  in
             FStar_Syntax_Util.mk_app uu____8990 args1  in
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
             let uu____9031 = FStar_Syntax_Syntax.bv_to_name bv  in
             FStar_Syntax_Util.mk_app uu____9031 args1  in
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
           let head1 =
             let scrut_new = readback cfg scrut  in
             let branches_new = make_branches ()  in
             FStar_Syntax_Syntax.mk
               (FStar_Syntax_Syntax.Tm_match (scrut_new, branches_new))
               FStar_Pervasives_Native.None FStar_Range.dummyRange
              in
           let app = FStar_Syntax_Util.mk_app head1 args1  in
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
             let uu____9131 = FStar_Thunk.force typ  in
             readback cfg uu____9131  in
           let defn1 =
             let uu____9133 = FStar_Thunk.force defn  in
             readback cfg uu____9133  in
           let body1 =
             let uu____9135 =
               let uu____9136 = FStar_Thunk.force body  in
               readback cfg uu____9136  in
             FStar_Syntax_Subst.close [(var, FStar_Pervasives_Native.None)]
               uu____9135
              in
           let lbname =
             let uu____9156 =
               let uu___1339_9157 =
                 FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
               {
                 FStar_Syntax_Syntax.ppname =
                   (uu___1339_9157.FStar_Syntax_Syntax.ppname);
                 FStar_Syntax_Syntax.index =
                   (uu___1339_9157.FStar_Syntax_Syntax.index);
                 FStar_Syntax_Syntax.sort = typ1
               }  in
             FStar_Util.Inl uu____9156  in
           let lb1 =
             let uu___1342_9159 = lb  in
             {
               FStar_Syntax_Syntax.lbname = lbname;
               FStar_Syntax_Syntax.lbunivs =
                 (uu___1342_9159.FStar_Syntax_Syntax.lbunivs);
               FStar_Syntax_Syntax.lbtyp = typ1;
               FStar_Syntax_Syntax.lbeff =
                 (uu___1342_9159.FStar_Syntax_Syntax.lbeff);
               FStar_Syntax_Syntax.lbdef = defn1;
               FStar_Syntax_Syntax.lbattrs =
                 (uu___1342_9159.FStar_Syntax_Syntax.lbattrs);
               FStar_Syntax_Syntax.lbpos =
                 (uu___1342_9159.FStar_Syntax_Syntax.lbpos)
             }  in
           let hd1 =
             FStar_Syntax_Syntax.mk
               (FStar_Syntax_Syntax.Tm_let ((false, [lb1]), body1))
               FStar_Pervasives_Native.None FStar_Range.dummyRange
              in
           let args1 = readback_args cfg args  in
           FStar_Syntax_Util.mk_app hd1 args1
       | FStar_TypeChecker_NBETerm.Accu
           (FStar_TypeChecker_NBETerm.UnreducedLetRec
            (vars_typs_defns,body,lbs),args)
           ->
           let lbs1 =
             FStar_List.map2
               (fun uu____9237  ->
                  fun lb  ->
                    match uu____9237 with
                    | (v1,t,d) ->
                        let t1 = readback cfg t  in
                        let def = readback cfg d  in
                        let v2 =
                          let uu___1362_9251 = v1  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___1362_9251.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___1362_9251.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t1
                          }  in
                        let uu___1365_9252 = lb  in
                        {
                          FStar_Syntax_Syntax.lbname = (FStar_Util.Inl v2);
                          FStar_Syntax_Syntax.lbunivs =
                            (uu___1365_9252.FStar_Syntax_Syntax.lbunivs);
                          FStar_Syntax_Syntax.lbtyp = t1;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___1365_9252.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = def;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___1365_9252.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___1365_9252.FStar_Syntax_Syntax.lbpos)
                        }) vars_typs_defns lbs
              in
           let body1 = readback cfg body  in
           let uu____9254 = FStar_Syntax_Subst.close_let_rec lbs1 body1  in
           (match uu____9254 with
            | (lbs2,body2) ->
                let hd1 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_let ((true, lbs2), body2))
                    FStar_Pervasives_Native.None FStar_Range.dummyRange
                   in
                let args1 = readback_args cfg args  in
                FStar_Syntax_Util.mk_app hd1 args1)
       | FStar_TypeChecker_NBETerm.Accu
           (FStar_TypeChecker_NBETerm.UVar f,args) ->
           let hd1 = FStar_Thunk.force f  in
           let args1 = readback_args cfg args  in
           FStar_Syntax_Util.mk_app hd1 args1
       | FStar_TypeChecker_NBETerm.TopLevelLet (lb,arity,args_rev) ->
           let n_univs = FStar_List.length lb.FStar_Syntax_Syntax.lbunivs  in
           let n_args = FStar_List.length args_rev  in
           let uu____9337 = FStar_Util.first_N (n_args - n_univs) args_rev
              in
           (match uu____9337 with
            | (args_rev1,univs1) ->
                let uu____9384 =
                  let uu____9385 =
                    let uu____9386 =
                      FStar_List.map FStar_Pervasives_Native.fst univs1  in
                    translate cfg uu____9386 lb.FStar_Syntax_Syntax.lbdef  in
                  iapp cfg uu____9385 (FStar_List.rev args_rev1)  in
                readback cfg uu____9384)
       | FStar_TypeChecker_NBETerm.TopLevelRec
           (lb,uu____9398,uu____9399,args) ->
           let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
           let head1 =
             FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
               FStar_Pervasives_Native.None FStar_Range.dummyRange
              in
           let args1 =
             FStar_List.map
               (fun uu____9444  ->
                  match uu____9444 with
                  | (t,q) ->
                      let uu____9455 = readback cfg t  in (uu____9455, q))
               args
              in
           FStar_Syntax_Util.mk_app head1 args1
       | FStar_TypeChecker_NBETerm.LocalLetRec
           (i,uu____9457,lbs,bs,args,_ar,_ar_lst) ->
           let lbnames =
             FStar_List.map
               (fun lb  ->
                  let uu____9499 =
                    let uu____9501 =
                      let uu____9502 =
                        FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                      uu____9502.FStar_Syntax_Syntax.ppname  in
                    FStar_Ident.text_of_id uu____9501  in
                  FStar_Syntax_Syntax.gen_bv uu____9499
                    FStar_Pervasives_Native.None lb.FStar_Syntax_Syntax.lbtyp)
               lbs
              in
           let let_rec_env =
             let uu____9506 =
               FStar_List.map
                 (fun x1  ->
                    FStar_TypeChecker_NBETerm.Accu
                      ((FStar_TypeChecker_NBETerm.Var x1), [])) lbnames
                in
             FStar_List.rev_append uu____9506 bs  in
           let lbs1 =
             FStar_List.map2
               (fun lb  ->
                  fun lbname  ->
                    let lbdef =
                      let uu____9532 =
                        translate cfg let_rec_env
                          lb.FStar_Syntax_Syntax.lbdef
                         in
                      readback cfg uu____9532  in
                    let lbtyp =
                      let uu____9534 =
                        translate cfg bs lb.FStar_Syntax_Syntax.lbtyp  in
                      readback cfg uu____9534  in
                    let uu___1420_9535 = lb  in
                    {
                      FStar_Syntax_Syntax.lbname = (FStar_Util.Inl lbname);
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___1420_9535.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = lbtyp;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___1420_9535.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = lbdef;
                      FStar_Syntax_Syntax.lbattrs =
                        (uu___1420_9535.FStar_Syntax_Syntax.lbattrs);
                      FStar_Syntax_Syntax.lbpos =
                        (uu___1420_9535.FStar_Syntax_Syntax.lbpos)
                    }) lbs lbnames
              in
           let body =
             let uu____9537 = FStar_List.nth lbnames i  in
             FStar_Syntax_Syntax.bv_to_name uu____9537  in
           let uu____9538 = FStar_Syntax_Subst.close_let_rec lbs1 body  in
           (match uu____9538 with
            | (lbs2,body1) ->
                let head1 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_let ((true, lbs2), body1))
                    FStar_Pervasives_Native.None FStar_Range.dummyRange
                   in
                let args1 =
                  FStar_List.map
                    (fun uu____9586  ->
                       match uu____9586 with
                       | (x1,q) ->
                           let uu____9597 = readback cfg x1  in
                           (uu____9597, q)) args
                   in
                FStar_Syntax_Util.mk_app head1 args1)
       | FStar_TypeChecker_NBETerm.Quote (qt,qi) ->
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_quoted (qt, qi))
             FStar_Pervasives_Native.None FStar_Range.dummyRange
       | FStar_TypeChecker_NBETerm.Lazy (FStar_Util.Inl li,uu____9603) ->
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_lazy li)
             FStar_Pervasives_Native.None FStar_Range.dummyRange
       | FStar_TypeChecker_NBETerm.Lazy (uu____9620,thunk1) ->
           let uu____9642 = FStar_Thunk.force thunk1  in
           readback cfg uu____9642)

type step =
  | Primops 
  | UnfoldUntil of FStar_Syntax_Syntax.delta_depth 
  | UnfoldOnly of FStar_Ident.lid Prims.list 
  | UnfoldAttr of FStar_Ident.lid Prims.list 
  | UnfoldTac 
  | Reify 
let (uu___is_Primops : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Primops  -> true | uu____9671 -> false
  
let (uu___is_UnfoldUntil : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldUntil _0 -> true | uu____9683 -> false
  
let (__proj__UnfoldUntil__item___0 : step -> FStar_Syntax_Syntax.delta_depth)
  = fun projectee  -> match projectee with | UnfoldUntil _0 -> _0 
let (uu___is_UnfoldOnly : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldOnly _0 -> true | uu____9704 -> false
  
let (__proj__UnfoldOnly__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldOnly _0 -> _0 
let (uu___is_UnfoldAttr : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldAttr _0 -> true | uu____9731 -> false
  
let (__proj__UnfoldAttr__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldAttr _0 -> _0 
let (uu___is_UnfoldTac : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldTac  -> true | uu____9755 -> false
  
let (uu___is_Reify : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reify  -> true | uu____9766 -> false
  
let (step_as_normalizer_step : step -> FStar_TypeChecker_Env.step) =
  fun uu___2_9773  ->
    match uu___2_9773 with
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
      fun args  -> let uu____9797 = new_config cfg  in iapp uu____9797 t args
  
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
            let uu___1466_9829 = cfg  in
            {
              FStar_TypeChecker_Cfg.steps =
                (let uu___1468_9832 = cfg.FStar_TypeChecker_Cfg.steps  in
                 {
                   FStar_TypeChecker_Cfg.beta =
                     (uu___1468_9832.FStar_TypeChecker_Cfg.beta);
                   FStar_TypeChecker_Cfg.iota =
                     (uu___1468_9832.FStar_TypeChecker_Cfg.iota);
                   FStar_TypeChecker_Cfg.zeta =
                     (uu___1468_9832.FStar_TypeChecker_Cfg.zeta);
                   FStar_TypeChecker_Cfg.weak =
                     (uu___1468_9832.FStar_TypeChecker_Cfg.weak);
                   FStar_TypeChecker_Cfg.hnf =
                     (uu___1468_9832.FStar_TypeChecker_Cfg.hnf);
                   FStar_TypeChecker_Cfg.primops =
                     (uu___1468_9832.FStar_TypeChecker_Cfg.primops);
                   FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                     (uu___1468_9832.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                   FStar_TypeChecker_Cfg.unfold_until =
                     (uu___1468_9832.FStar_TypeChecker_Cfg.unfold_until);
                   FStar_TypeChecker_Cfg.unfold_only =
                     (uu___1468_9832.FStar_TypeChecker_Cfg.unfold_only);
                   FStar_TypeChecker_Cfg.unfold_fully =
                     (uu___1468_9832.FStar_TypeChecker_Cfg.unfold_fully);
                   FStar_TypeChecker_Cfg.unfold_attr =
                     (uu___1468_9832.FStar_TypeChecker_Cfg.unfold_attr);
                   FStar_TypeChecker_Cfg.unfold_tac =
                     (uu___1468_9832.FStar_TypeChecker_Cfg.unfold_tac);
                   FStar_TypeChecker_Cfg.pure_subterms_within_computations =
                     (uu___1468_9832.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                   FStar_TypeChecker_Cfg.simplify =
                     (uu___1468_9832.FStar_TypeChecker_Cfg.simplify);
                   FStar_TypeChecker_Cfg.erase_universes =
                     (uu___1468_9832.FStar_TypeChecker_Cfg.erase_universes);
                   FStar_TypeChecker_Cfg.allow_unbound_universes =
                     (uu___1468_9832.FStar_TypeChecker_Cfg.allow_unbound_universes);
                   FStar_TypeChecker_Cfg.reify_ = true;
                   FStar_TypeChecker_Cfg.compress_uvars =
                     (uu___1468_9832.FStar_TypeChecker_Cfg.compress_uvars);
                   FStar_TypeChecker_Cfg.no_full_norm =
                     (uu___1468_9832.FStar_TypeChecker_Cfg.no_full_norm);
                   FStar_TypeChecker_Cfg.check_no_uvars =
                     (uu___1468_9832.FStar_TypeChecker_Cfg.check_no_uvars);
                   FStar_TypeChecker_Cfg.unmeta =
                     (uu___1468_9832.FStar_TypeChecker_Cfg.unmeta);
                   FStar_TypeChecker_Cfg.unascribe =
                     (uu___1468_9832.FStar_TypeChecker_Cfg.unascribe);
                   FStar_TypeChecker_Cfg.in_full_norm_request =
                     (uu___1468_9832.FStar_TypeChecker_Cfg.in_full_norm_request);
                   FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                     (uu___1468_9832.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                   FStar_TypeChecker_Cfg.nbe_step =
                     (uu___1468_9832.FStar_TypeChecker_Cfg.nbe_step);
                   FStar_TypeChecker_Cfg.for_extraction =
                     (uu___1468_9832.FStar_TypeChecker_Cfg.for_extraction)
                 });
              FStar_TypeChecker_Cfg.tcenv =
                (uu___1466_9829.FStar_TypeChecker_Cfg.tcenv);
              FStar_TypeChecker_Cfg.debug =
                (uu___1466_9829.FStar_TypeChecker_Cfg.debug);
              FStar_TypeChecker_Cfg.delta_level =
                (uu___1466_9829.FStar_TypeChecker_Cfg.delta_level);
              FStar_TypeChecker_Cfg.primitive_steps =
                (uu___1466_9829.FStar_TypeChecker_Cfg.primitive_steps);
              FStar_TypeChecker_Cfg.strong =
                (uu___1466_9829.FStar_TypeChecker_Cfg.strong);
              FStar_TypeChecker_Cfg.memoize_lazy =
                (uu___1466_9829.FStar_TypeChecker_Cfg.memoize_lazy);
              FStar_TypeChecker_Cfg.normalize_pure_lets =
                (uu___1466_9829.FStar_TypeChecker_Cfg.normalize_pure_lets);
              FStar_TypeChecker_Cfg.reifying =
                (uu___1466_9829.FStar_TypeChecker_Cfg.reifying)
            }  in
          (let uu____9835 =
             (FStar_TypeChecker_Env.debug env (FStar_Options.Other "NBETop"))
               ||
               (FStar_TypeChecker_Env.debug env (FStar_Options.Other "NBE"))
              in
           if uu____9835
           then
             let uu____9840 = FStar_Syntax_Print.term_to_string e  in
             FStar_Util.print1 "Calling NBE with (%s) {\n" uu____9840
           else ());
          (let cfg2 = new_config cfg1  in
           let r =
             let uu____9847 = translate cfg2 [] e  in
             readback cfg2 uu____9847  in
           (let uu____9849 =
              (FStar_TypeChecker_Env.debug env (FStar_Options.Other "NBETop"))
                ||
                (FStar_TypeChecker_Env.debug env (FStar_Options.Other "NBE"))
               in
            if uu____9849
            then
              let uu____9854 = FStar_Syntax_Print.term_to_string r  in
              FStar_Util.print1 "}\nNBE returned (%s)\n" uu____9854
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
          let uu___1484_9881 = cfg  in
          {
            FStar_TypeChecker_Cfg.steps =
              (let uu___1486_9884 = cfg.FStar_TypeChecker_Cfg.steps  in
               {
                 FStar_TypeChecker_Cfg.beta =
                   (uu___1486_9884.FStar_TypeChecker_Cfg.beta);
                 FStar_TypeChecker_Cfg.iota =
                   (uu___1486_9884.FStar_TypeChecker_Cfg.iota);
                 FStar_TypeChecker_Cfg.zeta =
                   (uu___1486_9884.FStar_TypeChecker_Cfg.zeta);
                 FStar_TypeChecker_Cfg.weak =
                   (uu___1486_9884.FStar_TypeChecker_Cfg.weak);
                 FStar_TypeChecker_Cfg.hnf =
                   (uu___1486_9884.FStar_TypeChecker_Cfg.hnf);
                 FStar_TypeChecker_Cfg.primops =
                   (uu___1486_9884.FStar_TypeChecker_Cfg.primops);
                 FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                   (uu___1486_9884.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                 FStar_TypeChecker_Cfg.unfold_until =
                   (uu___1486_9884.FStar_TypeChecker_Cfg.unfold_until);
                 FStar_TypeChecker_Cfg.unfold_only =
                   (uu___1486_9884.FStar_TypeChecker_Cfg.unfold_only);
                 FStar_TypeChecker_Cfg.unfold_fully =
                   (uu___1486_9884.FStar_TypeChecker_Cfg.unfold_fully);
                 FStar_TypeChecker_Cfg.unfold_attr =
                   (uu___1486_9884.FStar_TypeChecker_Cfg.unfold_attr);
                 FStar_TypeChecker_Cfg.unfold_tac =
                   (uu___1486_9884.FStar_TypeChecker_Cfg.unfold_tac);
                 FStar_TypeChecker_Cfg.pure_subterms_within_computations =
                   (uu___1486_9884.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                 FStar_TypeChecker_Cfg.simplify =
                   (uu___1486_9884.FStar_TypeChecker_Cfg.simplify);
                 FStar_TypeChecker_Cfg.erase_universes =
                   (uu___1486_9884.FStar_TypeChecker_Cfg.erase_universes);
                 FStar_TypeChecker_Cfg.allow_unbound_universes =
                   (uu___1486_9884.FStar_TypeChecker_Cfg.allow_unbound_universes);
                 FStar_TypeChecker_Cfg.reify_ = true;
                 FStar_TypeChecker_Cfg.compress_uvars =
                   (uu___1486_9884.FStar_TypeChecker_Cfg.compress_uvars);
                 FStar_TypeChecker_Cfg.no_full_norm =
                   (uu___1486_9884.FStar_TypeChecker_Cfg.no_full_norm);
                 FStar_TypeChecker_Cfg.check_no_uvars =
                   (uu___1486_9884.FStar_TypeChecker_Cfg.check_no_uvars);
                 FStar_TypeChecker_Cfg.unmeta =
                   (uu___1486_9884.FStar_TypeChecker_Cfg.unmeta);
                 FStar_TypeChecker_Cfg.unascribe =
                   (uu___1486_9884.FStar_TypeChecker_Cfg.unascribe);
                 FStar_TypeChecker_Cfg.in_full_norm_request =
                   (uu___1486_9884.FStar_TypeChecker_Cfg.in_full_norm_request);
                 FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                   (uu___1486_9884.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                 FStar_TypeChecker_Cfg.nbe_step =
                   (uu___1486_9884.FStar_TypeChecker_Cfg.nbe_step);
                 FStar_TypeChecker_Cfg.for_extraction =
                   (uu___1486_9884.FStar_TypeChecker_Cfg.for_extraction)
               });
            FStar_TypeChecker_Cfg.tcenv =
              (uu___1484_9881.FStar_TypeChecker_Cfg.tcenv);
            FStar_TypeChecker_Cfg.debug =
              (uu___1484_9881.FStar_TypeChecker_Cfg.debug);
            FStar_TypeChecker_Cfg.delta_level =
              (uu___1484_9881.FStar_TypeChecker_Cfg.delta_level);
            FStar_TypeChecker_Cfg.primitive_steps =
              (uu___1484_9881.FStar_TypeChecker_Cfg.primitive_steps);
            FStar_TypeChecker_Cfg.strong =
              (uu___1484_9881.FStar_TypeChecker_Cfg.strong);
            FStar_TypeChecker_Cfg.memoize_lazy =
              (uu___1484_9881.FStar_TypeChecker_Cfg.memoize_lazy);
            FStar_TypeChecker_Cfg.normalize_pure_lets =
              (uu___1484_9881.FStar_TypeChecker_Cfg.normalize_pure_lets);
            FStar_TypeChecker_Cfg.reifying =
              (uu___1484_9881.FStar_TypeChecker_Cfg.reifying)
          }  in
        let cfg2 = new_config cfg1  in
        debug cfg2
          (fun uu____9890  ->
             let uu____9891 = FStar_Syntax_Print.term_to_string e  in
             FStar_Util.print1 "Calling NBE with (%s) {\n" uu____9891);
        (let r =
           let uu____9895 = translate cfg2 [] e  in readback cfg2 uu____9895
            in
         debug cfg2
           (fun uu____9899  ->
              let uu____9900 = FStar_Syntax_Print.term_to_string r  in
              FStar_Util.print1 "}\nNBE returned (%s)\n" uu____9900);
         r)
  