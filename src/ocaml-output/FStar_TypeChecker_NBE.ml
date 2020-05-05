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
let (unlazy : FStar_TypeChecker_NBETerm.t -> FStar_TypeChecker_NBETerm.t) =
  fun t  ->
    match t with
    | FStar_TypeChecker_NBETerm.Lazy (uu____669,t1) -> FStar_Thunk.force t1
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
              (fun uu____800  ->
                 let uu____801 =
                   FStar_TypeChecker_NBETerm.t_to_string scrutinee0  in
                 let uu____803 = FStar_Syntax_Print.pat_to_string p  in
                 FStar_Util.print2 "matches_pat (%s, %s)\n" uu____801
                   uu____803);
            (let scrutinee = unlazy scrutinee0  in
             let r =
               match p.FStar_Syntax_Syntax.v with
               | FStar_Syntax_Syntax.Pat_var bv ->
                   FStar_Util.Inl [scrutinee0]
               | FStar_Syntax_Syntax.Pat_wild bv ->
                   FStar_Util.Inl [scrutinee0]
               | FStar_Syntax_Syntax.Pat_dot_term uu____830 ->
                   FStar_Util.Inl []
               | FStar_Syntax_Syntax.Pat_constant s ->
                   let matches_const c s1 =
                     debug cfg
                       (fun uu____857  ->
                          let uu____858 =
                            FStar_TypeChecker_NBETerm.t_to_string c  in
                          let uu____860 =
                            FStar_Syntax_Print.const_to_string s1  in
                          FStar_Util.print2
                            "Testing term %s against pattern %s\n" uu____858
                            uu____860);
                     (match c with
                      | FStar_TypeChecker_NBETerm.Constant
                          (FStar_TypeChecker_NBETerm.Unit ) ->
                          s1 = FStar_Const.Const_unit
                      | FStar_TypeChecker_NBETerm.Constant
                          (FStar_TypeChecker_NBETerm.Bool b) ->
                          (match s1 with
                           | FStar_Const.Const_bool p1 -> b = p1
                           | uu____870 -> false)
                      | FStar_TypeChecker_NBETerm.Constant
                          (FStar_TypeChecker_NBETerm.Int i) ->
                          (match s1 with
                           | FStar_Const.Const_int
                               (p1,FStar_Pervasives_Native.None ) ->
                               let uu____887 =
                                 FStar_BigInt.big_int_of_string p1  in
                               i = uu____887
                           | uu____888 -> false)
                      | FStar_TypeChecker_NBETerm.Constant
                          (FStar_TypeChecker_NBETerm.String (st,uu____891))
                          ->
                          (match s1 with
                           | FStar_Const.Const_string (p1,uu____896) ->
                               st = p1
                           | uu____900 -> false)
                      | FStar_TypeChecker_NBETerm.Constant
                          (FStar_TypeChecker_NBETerm.Char c1) ->
                          (match s1 with
                           | FStar_Const.Const_char p1 -> c1 = p1
                           | uu____908 -> false)
                      | uu____910 -> false)
                      in
                   let uu____912 = matches_const scrutinee s  in
                   if uu____912
                   then FStar_Util.Inl []
                   else FStar_Util.Inr false
               | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                   let rec matches_args out a p1 =
                     match (a, p1) with
                     | ([],[]) -> FStar_Util.Inl out
                     | ((t,uu____1050)::rest_a,(p2,uu____1053)::rest_p) ->
                         let uu____1092 = matches_pat t p2  in
                         (match uu____1092 with
                          | FStar_Util.Inl s ->
                              matches_args (FStar_List.append out s) rest_a
                                rest_p
                          | m -> m)
                     | uu____1121 -> FStar_Util.Inr false  in
                   (match scrutinee with
                    | FStar_TypeChecker_NBETerm.Construct (fv',_us,args_rev)
                        ->
                        let uu____1169 = FStar_Syntax_Syntax.fv_eq fv fv'  in
                        if uu____1169
                        then
                          matches_args [] (FStar_List.rev args_rev) arg_pats
                        else FStar_Util.Inr false
                    | uu____1189 -> FStar_Util.Inr true)
                in
             let res_to_string uu___0_1207 =
               match uu___0_1207 with
               | FStar_Util.Inr b ->
                   let uu____1221 = FStar_Util.string_of_bool b  in
                   Prims.op_Hat "Inr " uu____1221
               | FStar_Util.Inl bs ->
                   let uu____1230 =
                     FStar_Util.string_of_int (FStar_List.length bs)  in
                   Prims.op_Hat "Inl " uu____1230
                in
             debug cfg
               (fun uu____1238  ->
                  let uu____1239 =
                    FStar_TypeChecker_NBETerm.t_to_string scrutinee  in
                  let uu____1241 = FStar_Syntax_Print.pat_to_string p  in
                  let uu____1243 = res_to_string r  in
                  FStar_Util.print3 "matches_pat (%s, %s) = %s\n" uu____1239
                    uu____1241 uu____1243);
             r)
             in
          match branches1 with
          | [] -> FStar_Pervasives_Native.None
          | (p,_wopt,e)::branches2 ->
              let uu____1282 = matches_pat scrut1 p  in
              (match uu____1282 with
               | FStar_Util.Inl matches ->
                   (debug cfg
                      (fun uu____1307  ->
                         let uu____1308 = FStar_Syntax_Print.pat_to_string p
                            in
                         FStar_Util.print1 "Pattern %s matches\n" uu____1308);
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
        | (uu____1457,[]) -> (true, acc, ts)
        | ([],uu____1488::uu____1489) -> (false, acc, [])
        | (t::ts1,in_decreases_clause::bs) ->
            let uu____1558 =
              in_decreases_clause &&
                (FStar_TypeChecker_NBETerm.isAccu
                   (FStar_Pervasives_Native.fst t))
               in
            if uu____1558
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
        let mapper uu____1657 =
          match uu____1657 with
          | (lr,rng) ->
              (match lr with
               | FStar_Util.Inr (elt,FStar_Pervasives_Native.None ) ->
                   FStar_Pervasives_Native.Some elt
               | FStar_Util.Inr (elt,FStar_Pervasives_Native.Some us) ->
                   (debug cfg
                      (fun uu____1740  ->
                         let uu____1741 =
                           FStar_Syntax_Print.univs_to_string us  in
                         FStar_Util.print1
                           "Universes in local declaration: %s\n" uu____1741);
                    FStar_Pervasives_Native.Some elt)
               | uu____1744 -> FStar_Pervasives_Native.None)
           in
        let uu____1759 = FStar_TypeChecker_Env.lookup_qname env lid  in
        FStar_Util.bind_opt uu____1759 mapper
  
let (is_univ : FStar_TypeChecker_NBETerm.t -> Prims.bool) =
  fun tm  ->
    match tm with
    | FStar_TypeChecker_NBETerm.Univ uu____1806 -> true
    | uu____1808 -> false
  
let (un_univ : FStar_TypeChecker_NBETerm.t -> FStar_Syntax_Syntax.universe) =
  fun tm  ->
    match tm with
    | FStar_TypeChecker_NBETerm.Univ u -> u
    | t ->
        let uu____1818 =
          let uu____1820 = FStar_TypeChecker_NBETerm.t_to_string t  in
          Prims.op_Hat "Not a universe: " uu____1820  in
        failwith uu____1818
  
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
              (uu____1842,uu____1843,uu____1844,uu____1845,uu____1846,uu____1847);
            FStar_Syntax_Syntax.sigrng = uu____1848;
            FStar_Syntax_Syntax.sigquals = uu____1849;
            FStar_Syntax_Syntax.sigmeta = uu____1850;
            FStar_Syntax_Syntax.sigattrs = uu____1851;
            FStar_Syntax_Syntax.sigopts = uu____1852;_},uu____1853),uu____1854)
        -> true
    | uu____1914 -> false
  
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
              let uu____1954 = aux u3  in
              FStar_Syntax_Syntax.U_succ uu____1954
          | FStar_Syntax_Syntax.U_max us ->
              let uu____1958 = FStar_List.map aux us  in
              FStar_Syntax_Syntax.U_max uu____1958
          | FStar_Syntax_Syntax.U_unknown  -> u2
          | FStar_Syntax_Syntax.U_name uu____1961 -> u2
          | FStar_Syntax_Syntax.U_unif uu____1962 -> u2
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
           | FStar_Util.Inl uu____1995 -> failwith "find_let : impossible"
           | FStar_Util.Inr name ->
               let uu____2000 = FStar_Syntax_Syntax.fv_eq name fvar  in
               if uu____2000
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
          (fun uu____2271  ->
             let uu____2272 =
               let uu____2274 = FStar_Syntax_Subst.compress e  in
               FStar_Syntax_Print.tag_of_term uu____2274  in
             let uu____2275 =
               let uu____2277 = FStar_Syntax_Subst.compress e  in
               FStar_Syntax_Print.term_to_string uu____2277  in
             FStar_Util.print2 "Term: %s - %s\n" uu____2272 uu____2275);
        (let uu____2279 =
           let uu____2280 = FStar_Syntax_Subst.compress e  in
           uu____2280.FStar_Syntax_Syntax.n  in
         match uu____2279 with
         | FStar_Syntax_Syntax.Tm_delayed (uu____2283,uu____2284) ->
             failwith "Tm_delayed: Impossible"
         | FStar_Syntax_Syntax.Tm_unknown  ->
             FStar_TypeChecker_NBETerm.Unknown
         | FStar_Syntax_Syntax.Tm_constant c ->
             let uu____2307 = translate_constant c  in
             FStar_TypeChecker_NBETerm.Constant uu____2307
         | FStar_Syntax_Syntax.Tm_bvar db ->
             if db.FStar_Syntax_Syntax.index < (FStar_List.length bs)
             then
               let t = FStar_List.nth bs db.FStar_Syntax_Syntax.index  in
               (debug1
                  (fun uu____2318  ->
                     let uu____2319 = FStar_TypeChecker_NBETerm.t_to_string t
                        in
                     let uu____2321 =
                       let uu____2323 =
                         FStar_List.map FStar_TypeChecker_NBETerm.t_to_string
                           bs
                          in
                       FStar_All.pipe_right uu____2323
                         (FStar_String.concat "; ")
                        in
                     FStar_Util.print2
                       "Resolved bvar to %s\n\tcontext is [%s]\n" uu____2319
                       uu____2321);
                t)
             else failwith "de Bruijn index out of bounds"
         | FStar_Syntax_Syntax.Tm_uinst (t,us) ->
             (debug1
                (fun uu____2350  ->
                   let uu____2351 = FStar_Syntax_Print.term_to_string t  in
                   let uu____2353 =
                     let uu____2355 =
                       FStar_List.map FStar_Syntax_Print.univ_to_string us
                        in
                     FStar_All.pipe_right uu____2355
                       (FStar_String.concat ", ")
                      in
                   FStar_Util.print2 "Uinst term : %s\nUnivs : %s\n"
                     uu____2351 uu____2353);
              (let uu____2366 = translate cfg bs t  in
               let uu____2367 =
                 FStar_List.map
                   (fun x  ->
                      let uu____2371 =
                        let uu____2372 = translate_univ cfg bs x  in
                        FStar_TypeChecker_NBETerm.Univ uu____2372  in
                      FStar_TypeChecker_NBETerm.as_arg uu____2371) us
                  in
               iapp cfg uu____2366 uu____2367))
         | FStar_Syntax_Syntax.Tm_type u ->
             let uu____2374 = translate_univ cfg bs u  in
             FStar_TypeChecker_NBETerm.Type_t uu____2374
         | FStar_Syntax_Syntax.Tm_arrow (xs,c) ->
             let norm uu____2404 =
               let uu____2405 =
                 FStar_List.fold_left
                   (fun uu____2449  ->
                      fun uu____2450  ->
                        match (uu____2449, uu____2450) with
                        | ((ctx,binders_rev),(x,q)) ->
                            let t =
                              let uu____2554 =
                                translate cfg ctx x.FStar_Syntax_Syntax.sort
                                 in
                              readback cfg uu____2554  in
                            let x1 =
                              let uu___380_2556 =
                                FStar_Syntax_Syntax.freshen_bv x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___380_2556.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___380_2556.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t
                              }  in
                            let ctx1 =
                              let uu____2560 =
                                FStar_TypeChecker_NBETerm.mkAccuVar x1  in
                              uu____2560 :: ctx  in
                            (ctx1, ((x1, q) :: binders_rev))) (bs, []) xs
                  in
               match uu____2405 with
               | (ctx,binders_rev) ->
                   let c1 =
                     let uu____2620 = translate_comp cfg ctx c  in
                     readback_comp cfg uu____2620  in
                   FStar_Syntax_Util.arrow (FStar_List.rev binders_rev) c1
                in
             let uu____2627 =
               let uu____2644 = FStar_Thunk.mk norm  in
               FStar_Util.Inl uu____2644  in
             FStar_TypeChecker_NBETerm.Arrow uu____2627
         | FStar_Syntax_Syntax.Tm_refine (bv,tm) ->
             if
               ((cfg.core_cfg).FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.for_extraction
             then translate cfg bs bv.FStar_Syntax_Syntax.sort
             else
               FStar_TypeChecker_NBETerm.Refinement
                 (((fun y  -> translate cfg (y :: bs) tm)),
                   ((fun uu____2682  ->
                       let uu____2683 =
                         translate cfg bs bv.FStar_Syntax_Syntax.sort  in
                       FStar_TypeChecker_NBETerm.as_arg uu____2683)))
         | FStar_Syntax_Syntax.Tm_ascribed (t,uu____2685,uu____2686) ->
             translate cfg bs t
         | FStar_Syntax_Syntax.Tm_uvar (u,(subst,set_use_range)) ->
             let norm_uvar uu____2753 =
               let norm_subst_elt uu___1_2759 =
                 match uu___1_2759 with
                 | FStar_Syntax_Syntax.NT (x,t) ->
                     let uu____2766 =
                       let uu____2773 =
                         let uu____2776 = translate cfg bs t  in
                         readback cfg uu____2776  in
                       (x, uu____2773)  in
                     FStar_Syntax_Syntax.NT uu____2766
                 | FStar_Syntax_Syntax.NM (x,i) ->
                     let x_i =
                       FStar_Syntax_Syntax.bv_to_tm
                         (let uu___417_2786 = x  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___417_2786.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index = i;
                            FStar_Syntax_Syntax.sort =
                              (uu___417_2786.FStar_Syntax_Syntax.sort)
                          })
                        in
                     let t =
                       let uu____2788 = translate cfg bs x_i  in
                       readback cfg uu____2788  in
                     (match t.FStar_Syntax_Syntax.n with
                      | FStar_Syntax_Syntax.Tm_bvar x_j ->
                          FStar_Syntax_Syntax.NM
                            (x, (x_j.FStar_Syntax_Syntax.index))
                      | uu____2791 -> FStar_Syntax_Syntax.NT (x, t))
                 | uu____2794 ->
                     failwith "Impossible: subst invariant of uvar nodes"
                  in
               let subst1 =
                 FStar_List.map (FStar_List.map norm_subst_elt) subst  in
               let uu___427_2805 = e  in
               {
                 FStar_Syntax_Syntax.n =
                   (FStar_Syntax_Syntax.Tm_uvar (u, (subst1, set_use_range)));
                 FStar_Syntax_Syntax.pos =
                   (uu___427_2805.FStar_Syntax_Syntax.pos);
                 FStar_Syntax_Syntax.vars =
                   (uu___427_2805.FStar_Syntax_Syntax.vars)
               }  in
             let uu____2818 =
               let uu____2829 =
                 let uu____2830 = FStar_Thunk.mk norm_uvar  in
                 FStar_TypeChecker_NBETerm.UVar uu____2830  in
               (uu____2829, [])  in
             FStar_TypeChecker_NBETerm.Accu uu____2818
         | FStar_Syntax_Syntax.Tm_name x ->
             FStar_TypeChecker_NBETerm.mkAccuVar x
         | FStar_Syntax_Syntax.Tm_abs ([],uu____2844,uu____2845) ->
             failwith "Impossible: abstraction with no binders"
         | FStar_Syntax_Syntax.Tm_abs (xs,body,resc) ->
             FStar_TypeChecker_NBETerm.Lam
               (((fun ys  -> translate cfg (FStar_List.append ys bs) body)),
                 (FStar_Util.Inl (bs, xs, resc)), (FStar_List.length xs))
         | FStar_Syntax_Syntax.Tm_fvar fvar ->
             let uu____2953 = try_in_cache cfg fvar  in
             (match uu____2953 with
              | FStar_Pervasives_Native.Some t -> t
              | uu____2957 -> translate_fv cfg bs fvar)
         | FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                  (FStar_Const.Const_reify );
                FStar_Syntax_Syntax.pos = uu____2960;
                FStar_Syntax_Syntax.vars = uu____2961;_},arg::more::args)
             ->
             let uu____3021 = FStar_Syntax_Util.head_and_args e  in
             (match uu____3021 with
              | (head,uu____3039) ->
                  let head1 =
                    FStar_Syntax_Syntax.mk_Tm_app head [arg]
                      e.FStar_Syntax_Syntax.pos
                     in
                  let uu____3081 =
                    FStar_Syntax_Syntax.mk_Tm_app head1 (more :: args)
                      e.FStar_Syntax_Syntax.pos
                     in
                  translate cfg bs uu____3081)
         | FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                  (FStar_Const.Const_reflect uu____3090);
                FStar_Syntax_Syntax.pos = uu____3091;
                FStar_Syntax_Syntax.vars = uu____3092;_},arg::more::args)
             ->
             let uu____3152 = FStar_Syntax_Util.head_and_args e  in
             (match uu____3152 with
              | (head,uu____3170) ->
                  let head1 =
                    FStar_Syntax_Syntax.mk_Tm_app head [arg]
                      e.FStar_Syntax_Syntax.pos
                     in
                  let uu____3212 =
                    FStar_Syntax_Syntax.mk_Tm_app head1 (more :: args)
                      e.FStar_Syntax_Syntax.pos
                     in
                  translate cfg bs uu____3212)
         | FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                  (FStar_Const.Const_reflect uu____3221);
                FStar_Syntax_Syntax.pos = uu____3222;
                FStar_Syntax_Syntax.vars = uu____3223;_},arg::[])
             when (cfg.core_cfg).FStar_TypeChecker_Cfg.reifying ->
             let cfg1 = reifying_false cfg  in
             translate cfg1 bs (FStar_Pervasives_Native.fst arg)
         | FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                  (FStar_Const.Const_reflect uu____3268);
                FStar_Syntax_Syntax.pos = uu____3269;
                FStar_Syntax_Syntax.vars = uu____3270;_},arg::[])
             ->
             let uu____3310 =
               translate cfg bs (FStar_Pervasives_Native.fst arg)  in
             FStar_TypeChecker_NBETerm.Reflect uu____3310
         | FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                  (FStar_Const.Const_reify );
                FStar_Syntax_Syntax.pos = uu____3315;
                FStar_Syntax_Syntax.vars = uu____3316;_},arg::[])
             when
             ((cfg.core_cfg).FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.reify_
             ->
             let cfg1 = reifying_true cfg  in
             translate cfg1 bs (FStar_Pervasives_Native.fst arg)
         | FStar_Syntax_Syntax.Tm_app (head,args) ->
             (debug1
                (fun uu____3395  ->
                   let uu____3396 = FStar_Syntax_Print.term_to_string head
                      in
                   let uu____3398 = FStar_Syntax_Print.args_to_string args
                      in
                   FStar_Util.print2 "Application: %s @ %s\n" uu____3396
                     uu____3398);
              (let uu____3401 = translate cfg bs head  in
               let uu____3402 =
                 FStar_List.map
                   (fun x  ->
                      let uu____3424 =
                        translate cfg bs (FStar_Pervasives_Native.fst x)  in
                      (uu____3424, (FStar_Pervasives_Native.snd x))) args
                  in
               iapp cfg uu____3401 uu____3402))
         | FStar_Syntax_Syntax.Tm_match (scrut,branches) ->
             let make_branches uu____3476 =
               let cfg1 = zeta_false cfg  in
               let rec process_pattern bs1 p =
                 let uu____3507 =
                   match p.FStar_Syntax_Syntax.v with
                   | FStar_Syntax_Syntax.Pat_constant c ->
                       (bs1, (FStar_Syntax_Syntax.Pat_constant c))
                   | FStar_Syntax_Syntax.Pat_cons (fvar,args) ->
                       let uu____3543 =
                         FStar_List.fold_left
                           (fun uu____3584  ->
                              fun uu____3585  ->
                                match (uu____3584, uu____3585) with
                                | ((bs2,args1),(arg,b)) ->
                                    let uu____3677 = process_pattern bs2 arg
                                       in
                                    (match uu____3677 with
                                     | (bs',arg') ->
                                         (bs', ((arg', b) :: args1))))
                           (bs1, []) args
                          in
                       (match uu____3543 with
                        | (bs',args') ->
                            (bs',
                              (FStar_Syntax_Syntax.Pat_cons
                                 (fvar, (FStar_List.rev args')))))
                   | FStar_Syntax_Syntax.Pat_var bvar ->
                       let x =
                         let uu____3776 =
                           let uu____3777 =
                             translate cfg1 bs1 bvar.FStar_Syntax_Syntax.sort
                              in
                           readback cfg1 uu____3777  in
                         FStar_Syntax_Syntax.new_bv
                           FStar_Pervasives_Native.None uu____3776
                          in
                       let uu____3778 =
                         let uu____3781 =
                           FStar_TypeChecker_NBETerm.mkAccuVar x  in
                         uu____3781 :: bs1  in
                       (uu____3778, (FStar_Syntax_Syntax.Pat_var x))
                   | FStar_Syntax_Syntax.Pat_wild bvar ->
                       let x =
                         let uu____3786 =
                           let uu____3787 =
                             translate cfg1 bs1 bvar.FStar_Syntax_Syntax.sort
                              in
                           readback cfg1 uu____3787  in
                         FStar_Syntax_Syntax.new_bv
                           FStar_Pervasives_Native.None uu____3786
                          in
                       let uu____3788 =
                         let uu____3791 =
                           FStar_TypeChecker_NBETerm.mkAccuVar x  in
                         uu____3791 :: bs1  in
                       (uu____3788, (FStar_Syntax_Syntax.Pat_wild x))
                   | FStar_Syntax_Syntax.Pat_dot_term (bvar,tm) ->
                       let x =
                         let uu____3801 =
                           let uu____3802 =
                             translate cfg1 bs1 bvar.FStar_Syntax_Syntax.sort
                              in
                           readback cfg1 uu____3802  in
                         FStar_Syntax_Syntax.new_bv
                           FStar_Pervasives_Native.None uu____3801
                          in
                       let uu____3803 =
                         let uu____3804 =
                           let uu____3811 =
                             let uu____3814 = translate cfg1 bs1 tm  in
                             readback cfg1 uu____3814  in
                           (x, uu____3811)  in
                         FStar_Syntax_Syntax.Pat_dot_term uu____3804  in
                       (bs1, uu____3803)
                    in
                 match uu____3507 with
                 | (bs2,p_new) ->
                     (bs2,
                       (let uu___554_3834 = p  in
                        {
                          FStar_Syntax_Syntax.v = p_new;
                          FStar_Syntax_Syntax.p =
                            (uu___554_3834.FStar_Syntax_Syntax.p)
                        }))
                  in
               FStar_List.map
                 (fun uu____3853  ->
                    match uu____3853 with
                    | (pat,when_clause,e1) ->
                        let uu____3875 = process_pattern bs pat  in
                        (match uu____3875 with
                         | (bs',pat') ->
                             let uu____3888 =
                               let uu____3889 =
                                 let uu____3892 = translate cfg1 bs' e1  in
                                 readback cfg1 uu____3892  in
                               (pat', when_clause, uu____3889)  in
                             FStar_Syntax_Util.branch uu____3888)) branches
                in
             let scrut1 = translate cfg bs scrut  in
             (debug1
                (fun uu____3909  ->
                   let uu____3910 =
                     FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos
                      in
                   let uu____3912 = FStar_Syntax_Print.term_to_string e  in
                   FStar_Util.print2 "%s: Translating match %s\n" uu____3910
                     uu____3912);
              (let scrut2 = unlazy scrut1  in
               match scrut2 with
               | FStar_TypeChecker_NBETerm.Construct (c,us,args) ->
                   (debug1
                      (fun uu____3940  ->
                         let uu____3941 =
                           let uu____3943 =
                             FStar_All.pipe_right args
                               (FStar_List.map
                                  (fun uu____3969  ->
                                     match uu____3969 with
                                     | (x,q) ->
                                         let uu____3983 =
                                           FStar_TypeChecker_NBETerm.t_to_string
                                             x
                                            in
                                         Prims.op_Hat
                                           (if FStar_Util.is_some q
                                            then "#"
                                            else "") uu____3983))
                              in
                           FStar_All.pipe_right uu____3943
                             (FStar_String.concat "; ")
                            in
                         FStar_Util.print1 "Match args: %s\n" uu____3941);
                    (let uu____3997 = pickBranch cfg scrut2 branches  in
                     match uu____3997 with
                     | FStar_Pervasives_Native.Some (branch,args1) ->
                         let uu____4018 =
                           FStar_List.fold_left
                             (fun bs1  -> fun x  -> x :: bs1) bs args1
                            in
                         translate cfg uu____4018 branch
                     | FStar_Pervasives_Native.None  ->
                         FStar_TypeChecker_NBETerm.mkAccuMatch scrut2
                           make_branches))
               | FStar_TypeChecker_NBETerm.Constant c ->
                   (debug1
                      (fun uu____4041  ->
                         let uu____4042 =
                           FStar_TypeChecker_NBETerm.t_to_string scrut2  in
                         FStar_Util.print1 "Match constant : %s\n" uu____4042);
                    (let uu____4045 = pickBranch cfg scrut2 branches  in
                     match uu____4045 with
                     | FStar_Pervasives_Native.Some (branch,[]) ->
                         translate cfg bs branch
                     | FStar_Pervasives_Native.Some (branch,arg::[]) ->
                         translate cfg (arg :: bs) branch
                     | FStar_Pervasives_Native.None  ->
                         FStar_TypeChecker_NBETerm.mkAccuMatch scrut2
                           make_branches
                     | FStar_Pervasives_Native.Some (uu____4079,hd::tl) ->
                         failwith
                           "Impossible: Matching on constants cannot bind more than one variable"))
               | uu____4093 ->
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
             let uu____4138 =
               FStar_TypeChecker_Cfg.should_reduce_local_let cfg.core_cfg lb
                in
             if uu____4138
             then
               let uu____4141 =
                 (((cfg.core_cfg).FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.for_extraction
                    &&
                    (FStar_Syntax_Util.is_unit lb.FStar_Syntax_Syntax.lbtyp))
                   &&
                   (FStar_Syntax_Util.is_pure_or_ghost_effect
                      lb.FStar_Syntax_Syntax.lbeff)
                  in
               (if uu____4141
                then
                  let bs1 =
                    (FStar_TypeChecker_NBETerm.Constant
                       FStar_TypeChecker_NBETerm.Unit)
                    :: bs  in
                  translate cfg bs1 body
                else
                  (let bs1 =
                     let uu____4152 = translate_letbinding cfg bs lb  in
                     uu____4152 :: bs  in
                   translate cfg bs1 body))
             else
               (let def uu____4160 =
                  let uu____4161 =
                    (((cfg.core_cfg).FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.for_extraction
                       &&
                       (FStar_Syntax_Util.is_unit
                          lb.FStar_Syntax_Syntax.lbtyp))
                      &&
                      (FStar_Syntax_Util.is_pure_or_ghost_effect
                         lb.FStar_Syntax_Syntax.lbeff)
                     in
                  if uu____4161
                  then
                    FStar_TypeChecker_NBETerm.Constant
                      FStar_TypeChecker_NBETerm.Unit
                  else translate cfg bs lb.FStar_Syntax_Syntax.lbdef  in
                let typ uu____4171 =
                  translate cfg bs lb.FStar_Syntax_Syntax.lbtyp  in
                let name =
                  let uu____4173 =
                    FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                  FStar_Syntax_Syntax.freshen_bv uu____4173  in
                let bs1 =
                  (FStar_TypeChecker_NBETerm.Accu
                     ((FStar_TypeChecker_NBETerm.Var name), []))
                  :: bs  in
                let body1 uu____4192 = translate cfg bs1 body  in
                let uu____4193 =
                  let uu____4204 =
                    let uu____4205 =
                      let uu____4222 = FStar_Thunk.mk typ  in
                      let uu____4225 = FStar_Thunk.mk def  in
                      let uu____4228 = FStar_Thunk.mk body1  in
                      (name, uu____4222, uu____4225, uu____4228, lb)  in
                    FStar_TypeChecker_NBETerm.UnreducedLet uu____4205  in
                  (uu____4204, [])  in
                FStar_TypeChecker_NBETerm.Accu uu____4193)
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
                      let uu____4274 =
                        FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                      FStar_Syntax_Syntax.freshen_bv uu____4274) lbs
                  in
               let typs =
                 FStar_List.map
                   (fun lb  -> translate cfg bs lb.FStar_Syntax_Syntax.lbtyp)
                   lbs
                  in
               let rec_bs =
                 let uu____4283 =
                   FStar_List.map
                     (fun v  ->
                        FStar_TypeChecker_NBETerm.Accu
                          ((FStar_TypeChecker_NBETerm.Var v), [])) vars
                    in
                 FStar_List.append uu____4283 bs  in
               let defs =
                 FStar_List.map
                   (fun lb  ->
                      translate cfg rec_bs lb.FStar_Syntax_Syntax.lbdef) lbs
                  in
               let body1 = translate cfg rec_bs body  in
               let uu____4304 =
                 let uu____4315 =
                   let uu____4316 =
                     let uu____4333 = FStar_List.zip3 vars typs defs  in
                     (uu____4333, body1, lbs)  in
                   FStar_TypeChecker_NBETerm.UnreducedLetRec uu____4316  in
                 (uu____4315, [])  in
               FStar_TypeChecker_NBETerm.Accu uu____4304
             else
               (let uu____4364 = make_rec_env lbs bs  in
                translate cfg uu____4364 body)
         | FStar_Syntax_Syntax.Tm_meta (e1,uu____4368) -> translate cfg bs e1
         | FStar_Syntax_Syntax.Tm_quoted (qt,qi) ->
             let close t =
               let bvs =
                 FStar_List.map
                   (fun uu____4389  ->
                      FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                        FStar_Syntax_Syntax.tun) bs
                  in
               let s1 =
                 FStar_List.mapi
                   (fun i  -> fun bv  -> FStar_Syntax_Syntax.DB (i, bv)) bvs
                  in
               let s2 =
                 let uu____4402 = FStar_List.zip bvs bs  in
                 FStar_List.map
                   (fun uu____4417  ->
                      match uu____4417 with
                      | (bv,t1) ->
                          let uu____4424 =
                            let uu____4431 = readback cfg t1  in
                            (bv, uu____4431)  in
                          FStar_Syntax_Syntax.NT uu____4424) uu____4402
                  in
               let uu____4436 = FStar_Syntax_Subst.subst s1 t  in
               FStar_Syntax_Subst.subst s2 uu____4436  in
             (match qi.FStar_Syntax_Syntax.qkind with
              | FStar_Syntax_Syntax.Quote_dynamic  ->
                  let qt1 = close qt  in
                  FStar_TypeChecker_NBETerm.Quote (qt1, qi)
              | FStar_Syntax_Syntax.Quote_static  ->
                  let qi1 = FStar_Syntax_Syntax.on_antiquoted close qi  in
                  FStar_TypeChecker_NBETerm.Quote (qt, qi1))
         | FStar_Syntax_Syntax.Tm_lazy li ->
             let f uu____4445 =
               let t = FStar_Syntax_Util.unfold_lazy li  in
               debug1
                 (fun uu____4452  ->
                    let uu____4453 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.print1 ">> Unfolding Tm_lazy to %s\n"
                      uu____4453);
               translate cfg bs t  in
             let uu____4456 =
               let uu____4471 = FStar_Thunk.mk f  in
               ((FStar_Util.Inl li), uu____4471)  in
             FStar_TypeChecker_NBETerm.Lazy uu____4456)

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
            let uu____4503 =
              let uu____4510 = translate cfg bs typ  in
              let uu____4511 = fmap_opt (translate_univ cfg bs) u  in
              (uu____4510, uu____4511)  in
            FStar_TypeChecker_NBETerm.Tot uu____4503
        | FStar_Syntax_Syntax.GTotal (typ,u) ->
            let uu____4526 =
              let uu____4533 = translate cfg bs typ  in
              let uu____4534 = fmap_opt (translate_univ cfg bs) u  in
              (uu____4533, uu____4534)  in
            FStar_TypeChecker_NBETerm.GTot uu____4526
        | FStar_Syntax_Syntax.Comp ctyp ->
            let uu____4540 = translate_comp_typ cfg bs ctyp  in
            FStar_TypeChecker_NBETerm.Comp uu____4540

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
                    let uu____4676 = FStar_List.splitAt m raw_args  in
                    (match uu____4676 with
                     | (uu____4717,raw_args1) -> FStar_Util.Inr raw_args1)
                | FStar_Util.Inl (ctx,xs,rc) ->
                    let uu____4786 = FStar_List.splitAt m xs  in
                    (match uu____4786 with
                     | (uu____4833,xs1) ->
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
                (let uu____4933 = FStar_List.splitAt n args  in
                 match uu____4933 with
                 | (args1,args') ->
                     let uu____4980 =
                       let uu____4981 =
                         map_rev FStar_Pervasives_Native.fst args1  in
                       f1 uu____4981  in
                     iapp cfg uu____4980 args')
        | FStar_TypeChecker_NBETerm.Accu (a,ts) ->
            FStar_TypeChecker_NBETerm.Accu
              (a, (FStar_List.rev_append args ts))
        | FStar_TypeChecker_NBETerm.Construct (i,us,ts) ->
            let rec aux args1 us1 ts1 =
              match args1 with
              | (FStar_TypeChecker_NBETerm.Univ u,uu____5100)::args2 ->
                  aux args2 (u :: us1) ts1
              | a::args2 -> aux args2 us1 (a :: ts1)
              | [] -> (us1, ts1)  in
            let uu____5144 = aux args us ts  in
            (match uu____5144 with
             | (us',ts') -> FStar_TypeChecker_NBETerm.Construct (i, us', ts'))
        | FStar_TypeChecker_NBETerm.FV (i,us,ts) ->
            let rec aux args1 us1 ts1 =
              match args1 with
              | (FStar_TypeChecker_NBETerm.Univ u,uu____5271)::args2 ->
                  aux args2 (u :: us1) ts1
              | a::args2 -> aux args2 us1 (a :: ts1)
              | [] -> (us1, ts1)  in
            let uu____5315 = aux args us ts  in
            (match uu____5315 with
             | (us',ts') -> FStar_TypeChecker_NBETerm.FV (i, us', ts'))
        | FStar_TypeChecker_NBETerm.TopLevelLet (lb,arity,args_rev) ->
            let args_rev1 = FStar_List.rev_append args args_rev  in
            let n_args_rev = FStar_List.length args_rev1  in
            let n_univs = FStar_List.length lb.FStar_Syntax_Syntax.lbunivs
               in
            (debug cfg
               (fun uu____5393  ->
                  let uu____5394 =
                    FStar_Syntax_Print.lbname_to_string
                      lb.FStar_Syntax_Syntax.lbname
                     in
                  let uu____5396 = FStar_Util.string_of_int arity  in
                  let uu____5398 = FStar_Util.string_of_int n_args_rev  in
                  FStar_Util.print3
                    "Reached iapp for %s with arity %s and n_args = %s\n"
                    uu____5394 uu____5396 uu____5398);
             if n_args_rev >= arity
             then
               (let uu____5402 =
                  let uu____5415 =
                    let uu____5416 =
                      FStar_Syntax_Util.unascribe
                        lb.FStar_Syntax_Syntax.lbdef
                       in
                    uu____5416.FStar_Syntax_Syntax.n  in
                  match uu____5415 with
                  | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____5433) ->
                      (bs, body)
                  | uu____5466 -> ([], (lb.FStar_Syntax_Syntax.lbdef))  in
                match uu____5402 with
                | (bs,body) ->
                    if (n_univs + (FStar_List.length bs)) = arity
                    then
                      let uu____5507 =
                        FStar_Util.first_N (n_args_rev - arity) args_rev1  in
                      (match uu____5507 with
                       | (extra,args_rev2) ->
                           (debug cfg
                              (fun uu____5559  ->
                                 let uu____5560 =
                                   FStar_Syntax_Print.lbname_to_string
                                     lb.FStar_Syntax_Syntax.lbname
                                    in
                                 let uu____5562 =
                                   FStar_Syntax_Print.term_to_string body  in
                                 let uu____5564 =
                                   let uu____5566 =
                                     FStar_List.map
                                       (fun uu____5578  ->
                                          match uu____5578 with
                                          | (x,uu____5585) ->
                                              FStar_TypeChecker_NBETerm.t_to_string
                                                x) args_rev2
                                      in
                                   FStar_All.pipe_right uu____5566
                                     (FStar_String.concat ", ")
                                    in
                                 FStar_Util.print3
                                   "Reducing body of %s = %s,\n\twith args = %s\n"
                                   uu____5560 uu____5562 uu____5564);
                            (let t =
                               let uu____5593 =
                                 FStar_List.map FStar_Pervasives_Native.fst
                                   args_rev2
                                  in
                               translate cfg uu____5593 body  in
                             match extra with
                             | [] -> t
                             | uu____5604 ->
                                 iapp cfg t (FStar_List.rev extra))))
                    else
                      (let uu____5617 =
                         FStar_Util.first_N (n_args_rev - n_univs) args_rev1
                          in
                       match uu____5617 with
                       | (extra,univs) ->
                           let uu____5664 =
                             let uu____5665 =
                               FStar_List.map FStar_Pervasives_Native.fst
                                 univs
                                in
                             translate cfg uu____5665
                               lb.FStar_Syntax_Syntax.lbdef
                              in
                           iapp cfg uu____5664 (FStar_List.rev extra)))
             else
               FStar_TypeChecker_NBETerm.TopLevelLet (lb, arity, args_rev1))
        | FStar_TypeChecker_NBETerm.TopLevelRec
            (lb,arity,decreases_list,args') ->
            let args1 = FStar_List.append args' args  in
            if (FStar_List.length args1) >= arity
            then
              let uu____5725 =
                should_reduce_recursive_definition args1 decreases_list  in
              (match uu____5725 with
               | (should_reduce,uu____5734,uu____5735) ->
                   if Prims.op_Negation should_reduce
                   then
                     let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname
                        in
                     (debug cfg
                        (fun uu____5743  ->
                           let uu____5744 =
                             FStar_Syntax_Print.fv_to_string fv  in
                           FStar_Util.print1
                             "Decided to not unfold recursive definition %s\n"
                             uu____5744);
                      iapp cfg (FStar_TypeChecker_NBETerm.FV (fv, [], []))
                        args1)
                   else
                     (debug cfg
                        (fun uu____5764  ->
                           let uu____5765 =
                             let uu____5767 =
                               FStar_Util.right lb.FStar_Syntax_Syntax.lbname
                                in
                             FStar_Syntax_Print.fv_to_string uu____5767  in
                           FStar_Util.print1
                             "Yes, Decided to unfold recursive definition %s\n"
                             uu____5765);
                      (let uu____5769 =
                         FStar_Util.first_N
                           (FStar_List.length lb.FStar_Syntax_Syntax.lbunivs)
                           args1
                          in
                       match uu____5769 with
                       | (univs,rest) ->
                           let uu____5816 =
                             let uu____5817 =
                               let uu____5820 =
                                 FStar_List.map FStar_Pervasives_Native.fst
                                   univs
                                  in
                               FStar_List.rev uu____5820  in
                             translate cfg uu____5817
                               lb.FStar_Syntax_Syntax.lbdef
                              in
                           iapp cfg uu____5816 rest)))
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
                  let uu____5938 =
                    should_reduce_recursive_definition args1 decreases_list
                     in
                  match uu____5938 with
                  | (should_reduce,uu____5947,uu____5948) ->
                      if Prims.op_Negation should_reduce
                      then
                        FStar_TypeChecker_NBETerm.LocalLetRec
                          (i, lb, mutual_lbs, local_env, args1,
                            Prims.int_zero, decreases_list)
                      else
                        (let env = make_rec_env mutual_lbs local_env  in
                         debug cfg
                           (fun uu____5977  ->
                              (let uu____5979 =
                                 let uu____5981 =
                                   FStar_List.map
                                     FStar_TypeChecker_NBETerm.t_to_string
                                     env
                                    in
                                 FStar_String.concat ",\n\t " uu____5981  in
                               FStar_Util.print1
                                 "LocalLetRec Env = {\n\t%s\n}\n" uu____5979);
                              (let uu____5988 =
                                 let uu____5990 =
                                   FStar_List.map
                                     (fun uu____6002  ->
                                        match uu____6002 with
                                        | (t,uu____6009) ->
                                            FStar_TypeChecker_NBETerm.t_to_string
                                              t) args1
                                    in
                                 FStar_String.concat ",\n\t " uu____5990  in
                               FStar_Util.print1
                                 "LocalLetRec Args = {\n\t%s\n}\n" uu____5988));
                         (let uu____6012 =
                            translate cfg env lb.FStar_Syntax_Syntax.lbdef
                             in
                          iapp cfg uu____6012 args1))))
        | uu____6013 ->
            let uu____6014 =
              let uu____6016 = FStar_TypeChecker_NBETerm.t_to_string f  in
              Prims.op_Hat "NBE ill-typed application: " uu____6016  in
            failwith uu____6014

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
          let uu____6033 = FStar_TypeChecker_Cfg.cfg_env cfg.core_cfg  in
          let uu____6034 = FStar_Syntax_Syntax.lid_of_fv fvar  in
          FStar_TypeChecker_Env.lookup_qname uu____6033 uu____6034  in
        let uu____6035 = (is_constr qninfo) || (is_constr_fv fvar)  in
        if uu____6035
        then FStar_TypeChecker_NBETerm.mkConstruct fvar [] []
        else
          (let uu____6044 =
             FStar_TypeChecker_Normalize.should_unfold cfg.core_cfg
               (fun uu____6046  ->
                  (cfg.core_cfg).FStar_TypeChecker_Cfg.reifying) fvar qninfo
              in
           match uu____6044 with
           | FStar_TypeChecker_Normalize.Should_unfold_fully  ->
               failwith "Not yet handled"
           | FStar_TypeChecker_Normalize.Should_unfold_no  ->
               (debug1
                  (fun uu____6053  ->
                     let uu____6054 = FStar_Syntax_Print.fv_to_string fvar
                        in
                     FStar_Util.print1 "(1) Decided to not unfold %s\n"
                       uu____6054);
                (let uu____6057 =
                   FStar_TypeChecker_Cfg.find_prim_step cfg.core_cfg fvar  in
                 match uu____6057 with
                 | FStar_Pervasives_Native.Some prim_step when
                     prim_step.FStar_TypeChecker_Cfg.strong_reduction_ok ->
                     let arity =
                       prim_step.FStar_TypeChecker_Cfg.arity +
                         prim_step.FStar_TypeChecker_Cfg.univ_arity
                        in
                     (debug1
                        (fun uu____6068  ->
                           let uu____6069 =
                             FStar_Syntax_Print.fv_to_string fvar  in
                           FStar_Util.print1 "Found a primop %s\n" uu____6069);
                      (let uu____6072 =
                         let uu____6105 =
                           let f uu____6138 =
                             let uu____6140 =
                               FStar_Syntax_Syntax.new_bv
                                 FStar_Pervasives_Native.None
                                 FStar_Syntax_Syntax.t_unit
                                in
                             (uu____6140, FStar_Pervasives_Native.None)  in
                           let uu____6143 =
                             let uu____6154 = FStar_Common.tabulate arity f
                                in
                             ([], uu____6154, FStar_Pervasives_Native.None)
                              in
                           FStar_Util.Inl uu____6143  in
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
                             let uu____6228 =
                               prim_step.FStar_TypeChecker_Cfg.interpretation_nbe
                                 callbacks args'
                                in
                             match uu____6228 with
                             | FStar_Pervasives_Native.Some x ->
                                 (debug1
                                    (fun uu____6239  ->
                                       let uu____6240 =
                                         FStar_Syntax_Print.fv_to_string fvar
                                          in
                                       let uu____6242 =
                                         FStar_TypeChecker_NBETerm.t_to_string
                                           x
                                          in
                                       FStar_Util.print2
                                         "Primitive operator %s returned %s\n"
                                         uu____6240 uu____6242);
                                  x)
                             | FStar_Pervasives_Native.None  ->
                                 (debug1
                                    (fun uu____6250  ->
                                       let uu____6251 =
                                         FStar_Syntax_Print.fv_to_string fvar
                                          in
                                       FStar_Util.print1
                                         "Primitive operator %s failed\n"
                                         uu____6251);
                                  (let uu____6254 =
                                     FStar_TypeChecker_NBETerm.mkFV fvar []
                                       []
                                      in
                                   iapp cfg uu____6254 args'))), uu____6105,
                           arity)
                          in
                       FStar_TypeChecker_NBETerm.Lam uu____6072))
                 | FStar_Pervasives_Native.Some uu____6259 ->
                     (debug1
                        (fun uu____6265  ->
                           let uu____6266 =
                             FStar_Syntax_Print.fv_to_string fvar  in
                           FStar_Util.print1 "(2) Decided to not unfold %s\n"
                             uu____6266);
                      FStar_TypeChecker_NBETerm.mkFV fvar [] [])
                 | uu____6273 ->
                     (debug1
                        (fun uu____6281  ->
                           let uu____6282 =
                             FStar_Syntax_Print.fv_to_string fvar  in
                           FStar_Util.print1 "(3) Decided to not unfold %s\n"
                             uu____6282);
                      FStar_TypeChecker_NBETerm.mkFV fvar [] [])))
           | FStar_TypeChecker_Normalize.Should_unfold_reify  ->
               let t =
                 let is_qninfo_visible =
                   let uu____6292 =
                     FStar_TypeChecker_Env.lookup_definition_qninfo
                       (cfg.core_cfg).FStar_TypeChecker_Cfg.delta_level
                       (fvar.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                       qninfo
                      in
                   FStar_Option.isSome uu____6292  in
                 if is_qninfo_visible
                 then
                   match qninfo with
                   | FStar_Pervasives_Native.Some
                       (FStar_Util.Inr
                        ({
                           FStar_Syntax_Syntax.sigel =
                             FStar_Syntax_Syntax.Sig_let ((is_rec,lbs),names);
                           FStar_Syntax_Syntax.sigrng = uu____6307;
                           FStar_Syntax_Syntax.sigquals = uu____6308;
                           FStar_Syntax_Syntax.sigmeta = uu____6309;
                           FStar_Syntax_Syntax.sigattrs = uu____6310;
                           FStar_Syntax_Syntax.sigopts = uu____6311;_},_us_opt),_rng)
                       ->
                       (debug1
                          (fun uu____6381  ->
                             let uu____6382 =
                               FStar_Syntax_Print.fv_to_string fvar  in
                             FStar_Util.print1 "(1) Decided to unfold %s\n"
                               uu____6382);
                        (let lbm = find_let lbs fvar  in
                         match lbm with
                         | FStar_Pervasives_Native.Some lb ->
                             if
                               is_rec &&
                                 ((cfg.core_cfg).FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta
                             then
                               let uu____6390 = let_rec_arity lb  in
                               (match uu____6390 with
                                | (ar,lst) ->
                                    FStar_TypeChecker_NBETerm.TopLevelRec
                                      (lb, ar, lst, []))
                             else translate_letbinding cfg bs lb
                         | FStar_Pervasives_Native.None  ->
                             failwith "Could not find let binding"))
                   | uu____6426 ->
                       (debug1
                          (fun uu____6432  ->
                             let uu____6433 =
                               FStar_Syntax_Print.fv_to_string fvar  in
                             FStar_Util.print1
                               "(1) qninfo is None for (%s)\n" uu____6433);
                        FStar_TypeChecker_NBETerm.mkFV fvar [] [])
                 else
                   (debug1
                      (fun uu____6447  ->
                         let uu____6448 =
                           FStar_Syntax_Print.fv_to_string fvar  in
                         FStar_Util.print1
                           "(1) qninfo is not visible at this level (%s)\n"
                           uu____6448);
                    FStar_TypeChecker_NBETerm.mkFV fvar [] [])
                  in
               (cache_add cfg fvar t; t)
           | FStar_TypeChecker_Normalize.Should_unfold_yes  ->
               let t =
                 let is_qninfo_visible =
                   let uu____6459 =
                     FStar_TypeChecker_Env.lookup_definition_qninfo
                       (cfg.core_cfg).FStar_TypeChecker_Cfg.delta_level
                       (fvar.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                       qninfo
                      in
                   FStar_Option.isSome uu____6459  in
                 if is_qninfo_visible
                 then
                   match qninfo with
                   | FStar_Pervasives_Native.Some
                       (FStar_Util.Inr
                        ({
                           FStar_Syntax_Syntax.sigel =
                             FStar_Syntax_Syntax.Sig_let ((is_rec,lbs),names);
                           FStar_Syntax_Syntax.sigrng = uu____6474;
                           FStar_Syntax_Syntax.sigquals = uu____6475;
                           FStar_Syntax_Syntax.sigmeta = uu____6476;
                           FStar_Syntax_Syntax.sigattrs = uu____6477;
                           FStar_Syntax_Syntax.sigopts = uu____6478;_},_us_opt),_rng)
                       ->
                       (debug1
                          (fun uu____6548  ->
                             let uu____6549 =
                               FStar_Syntax_Print.fv_to_string fvar  in
                             FStar_Util.print1 "(1) Decided to unfold %s\n"
                               uu____6549);
                        (let lbm = find_let lbs fvar  in
                         match lbm with
                         | FStar_Pervasives_Native.Some lb ->
                             if
                               is_rec &&
                                 ((cfg.core_cfg).FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta
                             then
                               let uu____6557 = let_rec_arity lb  in
                               (match uu____6557 with
                                | (ar,lst) ->
                                    FStar_TypeChecker_NBETerm.TopLevelRec
                                      (lb, ar, lst, []))
                             else translate_letbinding cfg bs lb
                         | FStar_Pervasives_Native.None  ->
                             failwith "Could not find let binding"))
                   | uu____6593 ->
                       (debug1
                          (fun uu____6599  ->
                             let uu____6600 =
                               FStar_Syntax_Print.fv_to_string fvar  in
                             FStar_Util.print1
                               "(1) qninfo is None for (%s)\n" uu____6600);
                        FStar_TypeChecker_NBETerm.mkFV fvar [] [])
                 else
                   (debug1
                      (fun uu____6614  ->
                         let uu____6615 =
                           FStar_Syntax_Print.fv_to_string fvar  in
                         FStar_Util.print1
                           "(1) qninfo is not visible at this level (%s)\n"
                           uu____6615);
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
        let uu____6639 =
          FStar_Syntax_Util.arrow_formals lb.FStar_Syntax_Syntax.lbtyp  in
        match uu____6639 with
        | (formals,uu____6647) ->
            let arity = (FStar_List.length us) + (FStar_List.length formals)
               in
            if arity = Prims.int_zero
            then translate cfg bs lb.FStar_Syntax_Syntax.lbdef
            else
              (let uu____6665 =
                 FStar_Util.is_right lb.FStar_Syntax_Syntax.lbname  in
               if uu____6665
               then
                 (debug1
                    (fun uu____6675  ->
                       let uu____6676 =
                         FStar_Syntax_Print.lbname_to_string
                           lb.FStar_Syntax_Syntax.lbname
                          in
                       let uu____6678 = FStar_Util.string_of_int arity  in
                       FStar_Util.print2
                         "Making TopLevelLet for %s with arity %s\n"
                         uu____6676 uu____6678);
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
          let uu____6703 = let_rec_arity b  in
          match uu____6703 with
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
        let uu____6773 = FStar_BigInt.big_int_of_string s  in
        FStar_TypeChecker_NBETerm.Int uu____6773
    | FStar_Const.Const_string (s,r) ->
        FStar_TypeChecker_NBETerm.String (s, r)
    | FStar_Const.Const_char c1 -> FStar_TypeChecker_NBETerm.Char c1
    | FStar_Const.Const_range r -> FStar_TypeChecker_NBETerm.Range r
    | uu____6782 -> FStar_TypeChecker_NBETerm.SConst c

and (readback_comp :
  config -> FStar_TypeChecker_NBETerm.comp -> FStar_Syntax_Syntax.comp) =
  fun cfg  ->
    fun c  ->
      let c' =
        match c with
        | FStar_TypeChecker_NBETerm.Tot (typ,u) ->
            let uu____6792 =
              let uu____6801 = readback cfg typ  in (uu____6801, u)  in
            FStar_Syntax_Syntax.Total uu____6792
        | FStar_TypeChecker_NBETerm.GTot (typ,u) ->
            let uu____6814 =
              let uu____6823 = readback cfg typ  in (uu____6823, u)  in
            FStar_Syntax_Syntax.GTotal uu____6814
        | FStar_TypeChecker_NBETerm.Comp ctyp ->
            let uu____6831 = readback_comp_typ cfg ctyp  in
            FStar_Syntax_Syntax.Comp uu____6831
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
        let uu____6837 = c  in
        match uu____6837 with
        | { FStar_Syntax_Syntax.comp_univs = comp_univs;
            FStar_Syntax_Syntax.effect_name = effect_name;
            FStar_Syntax_Syntax.result_typ = result_typ;
            FStar_Syntax_Syntax.effect_args = effect_args;
            FStar_Syntax_Syntax.flags = flags;_} ->
            let uu____6857 =
              FStar_List.map (translate_univ cfg bs) comp_univs  in
            let uu____6858 = translate cfg bs result_typ  in
            let uu____6859 =
              FStar_List.map
                (fun x  ->
                   let uu____6887 =
                     translate cfg bs (FStar_Pervasives_Native.fst x)  in
                   (uu____6887, (FStar_Pervasives_Native.snd x))) effect_args
               in
            let uu____6894 = FStar_List.map (translate_flag cfg bs) flags  in
            {
              FStar_TypeChecker_NBETerm.comp_univs = uu____6857;
              FStar_TypeChecker_NBETerm.effect_name = effect_name;
              FStar_TypeChecker_NBETerm.result_typ = uu____6858;
              FStar_TypeChecker_NBETerm.effect_args = uu____6859;
              FStar_TypeChecker_NBETerm.flags = uu____6894
            }

and (readback_comp_typ :
  config ->
    FStar_TypeChecker_NBETerm.comp_typ -> FStar_Syntax_Syntax.comp_typ)
  =
  fun cfg  ->
    fun c  ->
      let uu____6899 = readback cfg c.FStar_TypeChecker_NBETerm.result_typ
         in
      let uu____6902 =
        FStar_List.map
          (fun x  ->
             let uu____6928 = readback cfg (FStar_Pervasives_Native.fst x)
                in
             (uu____6928, (FStar_Pervasives_Native.snd x)))
          c.FStar_TypeChecker_NBETerm.effect_args
         in
      let uu____6929 =
        FStar_List.map (readback_flag cfg) c.FStar_TypeChecker_NBETerm.flags
         in
      {
        FStar_Syntax_Syntax.comp_univs =
          (c.FStar_TypeChecker_NBETerm.comp_univs);
        FStar_Syntax_Syntax.effect_name =
          (c.FStar_TypeChecker_NBETerm.effect_name);
        FStar_Syntax_Syntax.result_typ = uu____6899;
        FStar_Syntax_Syntax.effect_args = uu____6902;
        FStar_Syntax_Syntax.flags = uu____6929
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
        let uu____6937 = c  in
        match uu____6937 with
        | { FStar_Syntax_Syntax.residual_effect = residual_effect;
            FStar_Syntax_Syntax.residual_typ = residual_typ;
            FStar_Syntax_Syntax.residual_flags = residual_flags;_} ->
            let uu____6947 =
              if
                ((cfg.core_cfg).FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.for_extraction
              then FStar_Pervasives_Native.None
              else FStar_Util.map_opt residual_typ (translate cfg bs)  in
            let uu____6957 =
              FStar_List.map (translate_flag cfg bs) residual_flags  in
            {
              FStar_TypeChecker_NBETerm.residual_effect = residual_effect;
              FStar_TypeChecker_NBETerm.residual_typ = uu____6947;
              FStar_TypeChecker_NBETerm.residual_flags = uu____6957
            }

and (readback_residual_comp :
  config ->
    FStar_TypeChecker_NBETerm.residual_comp ->
      FStar_Syntax_Syntax.residual_comp)
  =
  fun cfg  ->
    fun c  ->
      let uu____6962 =
        FStar_Util.map_opt c.FStar_TypeChecker_NBETerm.residual_typ
          (fun x  ->
             debug cfg
               (fun uu____6973  ->
                  let uu____6974 = FStar_TypeChecker_NBETerm.t_to_string x
                     in
                  FStar_Util.print1 "Reading back residualtype %s\n"
                    uu____6974);
             readback cfg x)
         in
      let uu____6977 =
        FStar_List.map (readback_flag cfg)
          c.FStar_TypeChecker_NBETerm.residual_flags
         in
      {
        FStar_Syntax_Syntax.residual_effect =
          (c.FStar_TypeChecker_NBETerm.residual_effect);
        FStar_Syntax_Syntax.residual_typ = uu____6962;
        FStar_Syntax_Syntax.residual_flags = uu____6977
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
            let uu____6988 = translate cfg bs tm  in
            FStar_TypeChecker_NBETerm.DECREASES uu____6988

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
          let uu____6992 = readback cfg t  in
          FStar_Syntax_Syntax.DECREASES uu____6992

and (translate_monadic :
  (FStar_Syntax_Syntax.monad_name * FStar_Syntax_Syntax.term'
    FStar_Syntax_Syntax.syntax) ->
    config ->
      FStar_TypeChecker_NBETerm.t Prims.list ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
          FStar_TypeChecker_NBETerm.t)
  =
  fun uu____6995  ->
    fun cfg  ->
      fun bs  ->
        fun e  ->
          match uu____6995 with
          | (m,ty) ->
              let e1 = FStar_Syntax_Util.unascribe e  in
              (match e1.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                   let uu____7033 =
                     let uu____7042 =
                       FStar_TypeChecker_Env.norm_eff_name
                         (cfg.core_cfg).FStar_TypeChecker_Cfg.tcenv m
                        in
                     FStar_TypeChecker_Env.effect_decl_opt
                       (cfg.core_cfg).FStar_TypeChecker_Cfg.tcenv uu____7042
                      in
                   (match uu____7033 with
                    | FStar_Pervasives_Native.None  ->
                        let uu____7049 =
                          let uu____7051 = FStar_Ident.string_of_lid m  in
                          FStar_Util.format1
                            "Effect declaration not found: %s" uu____7051
                           in
                        failwith uu____7049
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
                          let uu____7073 =
                            let uu____7074 =
                              let uu____7093 =
                                let uu____7102 =
                                  let uu____7109 =
                                    FStar_Util.left
                                      lb.FStar_Syntax_Syntax.lbname
                                     in
                                  (uu____7109, FStar_Pervasives_Native.None)
                                   in
                                [uu____7102]  in
                              (uu____7093, body,
                                (FStar_Pervasives_Native.Some body_rc))
                               in
                            FStar_Syntax_Syntax.Tm_abs uu____7074  in
                          FStar_Syntax_Syntax.mk uu____7073
                            body.FStar_Syntax_Syntax.pos
                           in
                        let maybe_range_arg =
                          let uu____7143 =
                            FStar_Util.for_some
                              (FStar_Syntax_Util.attr_eq
                                 FStar_Syntax_Util.dm4f_bind_range_attr)
                              ed.FStar_Syntax_Syntax.eff_attrs
                             in
                          if uu____7143
                          then
                            let uu____7152 =
                              let uu____7157 =
                                let uu____7158 =
                                  FStar_TypeChecker_Cfg.embed_simple
                                    FStar_Syntax_Embeddings.e_range
                                    lb.FStar_Syntax_Syntax.lbpos
                                    lb.FStar_Syntax_Syntax.lbpos
                                   in
                                translate cfg [] uu____7158  in
                              (uu____7157, FStar_Pervasives_Native.None)  in
                            let uu____7159 =
                              let uu____7166 =
                                let uu____7171 =
                                  let uu____7172 =
                                    FStar_TypeChecker_Cfg.embed_simple
                                      FStar_Syntax_Embeddings.e_range
                                      body.FStar_Syntax_Syntax.pos
                                      body.FStar_Syntax_Syntax.pos
                                     in
                                  translate cfg [] uu____7172  in
                                (uu____7171, FStar_Pervasives_Native.None)
                                 in
                              [uu____7166]  in
                            uu____7152 :: uu____7159
                          else []  in
                        let t =
                          let uu____7192 =
                            let uu____7193 =
                              let uu____7194 =
                                let uu____7195 =
                                  let uu____7196 =
                                    let uu____7203 =
                                      FStar_All.pipe_right ed
                                        FStar_Syntax_Util.get_bind_repr
                                       in
                                    FStar_All.pipe_right uu____7203
                                      FStar_Util.must
                                     in
                                  FStar_All.pipe_right uu____7196
                                    FStar_Pervasives_Native.snd
                                   in
                                FStar_Syntax_Util.un_uinst uu____7195  in
                              translate cfg' [] uu____7194  in
                            iapp cfg uu____7193
                              [((FStar_TypeChecker_NBETerm.Univ
                                   FStar_Syntax_Syntax.U_unknown),
                                 FStar_Pervasives_Native.None);
                              ((FStar_TypeChecker_NBETerm.Univ
                                  FStar_Syntax_Syntax.U_unknown),
                                FStar_Pervasives_Native.None)]
                             in
                          let uu____7236 =
                            let uu____7237 =
                              let uu____7244 =
                                let uu____7249 =
                                  translate cfg' bs
                                    lb.FStar_Syntax_Syntax.lbtyp
                                   in
                                (uu____7249, FStar_Pervasives_Native.None)
                                 in
                              let uu____7250 =
                                let uu____7257 =
                                  let uu____7262 = translate cfg' bs ty  in
                                  (uu____7262, FStar_Pervasives_Native.None)
                                   in
                                [uu____7257]  in
                              uu____7244 :: uu____7250  in
                            let uu____7275 =
                              let uu____7282 =
                                let uu____7289 =
                                  let uu____7296 =
                                    let uu____7301 =
                                      translate cfg bs
                                        lb.FStar_Syntax_Syntax.lbdef
                                       in
                                    (uu____7301,
                                      FStar_Pervasives_Native.None)
                                     in
                                  let uu____7302 =
                                    let uu____7309 =
                                      let uu____7316 =
                                        let uu____7321 =
                                          translate cfg bs body_lam  in
                                        (uu____7321,
                                          FStar_Pervasives_Native.None)
                                         in
                                      [uu____7316]  in
                                    (FStar_TypeChecker_NBETerm.Unknown,
                                      FStar_Pervasives_Native.None) ::
                                      uu____7309
                                     in
                                  uu____7296 :: uu____7302  in
                                (FStar_TypeChecker_NBETerm.Unknown,
                                  FStar_Pervasives_Native.None) :: uu____7289
                                 in
                              FStar_List.append maybe_range_arg uu____7282
                               in
                            FStar_List.append uu____7237 uu____7275  in
                          iapp cfg uu____7192 uu____7236  in
                        (debug cfg
                           (fun uu____7353  ->
                              let uu____7354 =
                                FStar_TypeChecker_NBETerm.t_to_string t  in
                              FStar_Util.print1 "translate_monadic: %s\n"
                                uu____7354);
                         t))
               | FStar_Syntax_Syntax.Tm_app
                   ({
                      FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                        (FStar_Const.Const_reflect uu____7357);
                      FStar_Syntax_Syntax.pos = uu____7358;
                      FStar_Syntax_Syntax.vars = uu____7359;_},(e2,uu____7361)::[])
                   ->
                   let uu____7400 = reifying_false cfg  in
                   translate uu____7400 bs e2
               | FStar_Syntax_Syntax.Tm_app (head,args) ->
                   (debug cfg
                      (fun uu____7431  ->
                         let uu____7432 =
                           FStar_Syntax_Print.term_to_string head  in
                         let uu____7434 =
                           FStar_Syntax_Print.args_to_string args  in
                         FStar_Util.print2
                           "translate_monadic app (%s) @ (%s)\n" uu____7432
                           uu____7434);
                    (let fallback1 uu____7442 = translate cfg bs e1  in
                     let fallback2 uu____7448 =
                       let uu____7449 = reifying_false cfg  in
                       let uu____7450 =
                         FStar_Syntax_Syntax.mk
                           (FStar_Syntax_Syntax.Tm_meta
                              (e1,
                                (FStar_Syntax_Syntax.Meta_monadic (m, ty))))
                           e1.FStar_Syntax_Syntax.pos
                          in
                       translate uu____7449 bs uu____7450  in
                     let uu____7455 =
                       let uu____7456 = FStar_Syntax_Util.un_uinst head  in
                       uu____7456.FStar_Syntax_Syntax.n  in
                     match uu____7455 with
                     | FStar_Syntax_Syntax.Tm_fvar fv ->
                         let lid = FStar_Syntax_Syntax.lid_of_fv fv  in
                         let qninfo =
                           FStar_TypeChecker_Env.lookup_qname
                             (cfg.core_cfg).FStar_TypeChecker_Cfg.tcenv lid
                            in
                         let uu____7462 =
                           let uu____7464 =
                             FStar_TypeChecker_Env.is_action
                               (cfg.core_cfg).FStar_TypeChecker_Cfg.tcenv lid
                              in
                           Prims.op_Negation uu____7464  in
                         if uu____7462
                         then fallback1 ()
                         else
                           (let uu____7469 =
                              let uu____7471 =
                                FStar_TypeChecker_Env.lookup_definition_qninfo
                                  (cfg.core_cfg).FStar_TypeChecker_Cfg.delta_level
                                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                  qninfo
                                 in
                              FStar_Option.isNone uu____7471  in
                            if uu____7469
                            then fallback2 ()
                            else
                              (let e2 =
                                 let uu____7486 =
                                   FStar_Syntax_Util.mk_reify head  in
                                 FStar_Syntax_Syntax.mk_Tm_app uu____7486
                                   args e1.FStar_Syntax_Syntax.pos
                                  in
                               let uu____7487 = reifying_false cfg  in
                               translate uu____7487 bs e2))
                     | uu____7488 -> fallback1 ()))
               | FStar_Syntax_Syntax.Tm_match (sc,branches) ->
                   let branches1 =
                     FStar_All.pipe_right branches
                       (FStar_List.map
                          (fun uu____7609  ->
                             match uu____7609 with
                             | (pat,wopt,tm) ->
                                 let uu____7657 =
                                   FStar_Syntax_Util.mk_reify tm  in
                                 (pat, wopt, uu____7657)))
                      in
                   let tm =
                     FStar_Syntax_Syntax.mk
                       (FStar_Syntax_Syntax.Tm_match (sc, branches1))
                       e1.FStar_Syntax_Syntax.pos
                      in
                   let uu____7689 = reifying_false cfg  in
                   translate uu____7689 bs tm
               | FStar_Syntax_Syntax.Tm_meta
                   (t,FStar_Syntax_Syntax.Meta_monadic uu____7691) ->
                   translate_monadic (m, ty) cfg bs e1
               | FStar_Syntax_Syntax.Tm_meta
                   (t,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,ty'))
                   -> translate_monadic_lift (msrc, mtgt, ty') cfg bs e1
               | uu____7718 ->
                   let uu____7719 =
                     let uu____7721 = FStar_Syntax_Print.tag_of_term e1  in
                     FStar_Util.format1
                       "Unexpected case in translate_monadic: %s" uu____7721
                      in
                   failwith uu____7719)

and (translate_monadic_lift :
  (FStar_Syntax_Syntax.monad_name * FStar_Syntax_Syntax.monad_name *
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax) ->
    config ->
      FStar_TypeChecker_NBETerm.t Prims.list ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
          FStar_TypeChecker_NBETerm.t)
  =
  fun uu____7724  ->
    fun cfg  ->
      fun bs  ->
        fun e  ->
          match uu____7724 with
          | (msrc,mtgt,ty) ->
              let e1 = FStar_Syntax_Util.unascribe e  in
              let uu____7748 =
                (FStar_Syntax_Util.is_pure_effect msrc) ||
                  (FStar_Syntax_Util.is_div_effect msrc)
                 in
              if uu____7748
              then
                let ed =
                  let uu____7752 =
                    FStar_TypeChecker_Env.norm_eff_name
                      (cfg.core_cfg).FStar_TypeChecker_Cfg.tcenv mtgt
                     in
                  FStar_TypeChecker_Env.get_effect_decl
                    (cfg.core_cfg).FStar_TypeChecker_Cfg.tcenv uu____7752
                   in
                let ret =
                  let uu____7754 =
                    let uu____7755 =
                      let uu____7758 =
                        let uu____7759 =
                          let uu____7766 =
                            FStar_All.pipe_right ed
                              FStar_Syntax_Util.get_return_repr
                             in
                          FStar_All.pipe_right uu____7766 FStar_Util.must  in
                        FStar_All.pipe_right uu____7759
                          FStar_Pervasives_Native.snd
                         in
                      FStar_Syntax_Subst.compress uu____7758  in
                    uu____7755.FStar_Syntax_Syntax.n  in
                  match uu____7754 with
                  | FStar_Syntax_Syntax.Tm_uinst (ret,uu____7812::[]) ->
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_uinst
                           (ret, [FStar_Syntax_Syntax.U_unknown]))
                        e1.FStar_Syntax_Syntax.pos
                  | uu____7819 ->
                      failwith "NYI: Reification of indexed effect (NBE)"
                   in
                let cfg' = reifying_false cfg  in
                let t =
                  let uu____7823 =
                    let uu____7824 = translate cfg' [] ret  in
                    iapp cfg' uu____7824
                      [((FStar_TypeChecker_NBETerm.Univ
                           FStar_Syntax_Syntax.U_unknown),
                         FStar_Pervasives_Native.None)]
                     in
                  let uu____7833 =
                    let uu____7834 =
                      let uu____7839 = translate cfg' bs ty  in
                      (uu____7839, FStar_Pervasives_Native.None)  in
                    let uu____7840 =
                      let uu____7847 =
                        let uu____7852 = translate cfg' bs e1  in
                        (uu____7852, FStar_Pervasives_Native.None)  in
                      [uu____7847]  in
                    uu____7834 :: uu____7840  in
                  iapp cfg' uu____7823 uu____7833  in
                (debug cfg
                   (fun uu____7868  ->
                      let uu____7869 =
                        FStar_TypeChecker_NBETerm.t_to_string t  in
                      FStar_Util.print1 "translate_monadic_lift(1): %s\n"
                        uu____7869);
                 t)
              else
                (let uu____7874 =
                   FStar_TypeChecker_Env.monad_leq
                     (cfg.core_cfg).FStar_TypeChecker_Cfg.tcenv msrc mtgt
                    in
                 match uu____7874 with
                 | FStar_Pervasives_Native.None  ->
                     let uu____7877 =
                       let uu____7879 = FStar_Ident.string_of_lid msrc  in
                       let uu____7881 = FStar_Ident.string_of_lid mtgt  in
                       FStar_Util.format2
                         "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                         uu____7879 uu____7881
                        in
                     failwith uu____7877
                 | FStar_Pervasives_Native.Some
                     { FStar_TypeChecker_Env.msource = uu____7884;
                       FStar_TypeChecker_Env.mtarget = uu____7885;
                       FStar_TypeChecker_Env.mlift =
                         { FStar_TypeChecker_Env.mlift_wp = uu____7886;
                           FStar_TypeChecker_Env.mlift_term =
                             FStar_Pervasives_Native.None ;_};_}
                     ->
                     let uu____7906 =
                       let uu____7908 = FStar_Ident.string_of_lid msrc  in
                       let uu____7910 = FStar_Ident.string_of_lid mtgt  in
                       FStar_Util.format2
                         "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
                         uu____7908 uu____7910
                        in
                     failwith uu____7906
                 | FStar_Pervasives_Native.Some
                     { FStar_TypeChecker_Env.msource = uu____7913;
                       FStar_TypeChecker_Env.mtarget = uu____7914;
                       FStar_TypeChecker_Env.mlift =
                         { FStar_TypeChecker_Env.mlift_wp = uu____7915;
                           FStar_TypeChecker_Env.mlift_term =
                             FStar_Pervasives_Native.Some lift;_};_}
                     ->
                     let lift_lam =
                       let x =
                         FStar_Syntax_Syntax.new_bv
                           FStar_Pervasives_Native.None
                           FStar_Syntax_Syntax.tun
                          in
                       let uu____7949 =
                         let uu____7952 = FStar_Syntax_Syntax.bv_to_name x
                            in
                         lift FStar_Syntax_Syntax.U_unknown ty uu____7952  in
                       FStar_Syntax_Util.abs
                         [(x, FStar_Pervasives_Native.None)] uu____7949
                         FStar_Pervasives_Native.None
                        in
                     let cfg' = reifying_false cfg  in
                     let t =
                       let uu____7969 = translate cfg' [] lift_lam  in
                       let uu____7970 =
                         let uu____7971 =
                           let uu____7976 = translate cfg bs e1  in
                           (uu____7976, FStar_Pervasives_Native.None)  in
                         [uu____7971]  in
                       iapp cfg uu____7969 uu____7970  in
                     (debug cfg
                        (fun uu____7988  ->
                           let uu____7989 =
                             FStar_TypeChecker_NBETerm.t_to_string t  in
                           FStar_Util.print1
                             "translate_monadic_lift(2): %s\n" uu____7989);
                      t))

and (readback :
  config -> FStar_TypeChecker_NBETerm.t -> FStar_Syntax_Syntax.term) =
  fun cfg  ->
    fun x  ->
      let debug1 = debug cfg  in
      let readback_args cfg1 args =
        map_rev
          (fun uu____8043  ->
             match uu____8043 with
             | (x1,q) ->
                 let uu____8054 = readback cfg1 x1  in (uu____8054, q)) args
         in
      debug1
        (fun uu____8060  ->
           let uu____8061 = FStar_TypeChecker_NBETerm.t_to_string x  in
           FStar_Util.print1 "Readback: %s\n" uu____8061);
      (match x with
       | FStar_TypeChecker_NBETerm.Univ u ->
           failwith "Readback of universes should not occur"
       | FStar_TypeChecker_NBETerm.Unknown  ->
           FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
             FStar_Range.dummyRange
       | FStar_TypeChecker_NBETerm.Constant (FStar_TypeChecker_NBETerm.Unit )
           -> FStar_Syntax_Syntax.unit_const
       | FStar_TypeChecker_NBETerm.Constant (FStar_TypeChecker_NBETerm.Bool
           (true )) -> FStar_Syntax_Util.exp_true_bool
       | FStar_TypeChecker_NBETerm.Constant (FStar_TypeChecker_NBETerm.Bool
           (false )) -> FStar_Syntax_Util.exp_false_bool
       | FStar_TypeChecker_NBETerm.Constant (FStar_TypeChecker_NBETerm.Int i)
           ->
           let uu____8069 = FStar_BigInt.string_of_big_int i  in
           FStar_All.pipe_right uu____8069 FStar_Syntax_Util.exp_int
       | FStar_TypeChecker_NBETerm.Constant (FStar_TypeChecker_NBETerm.String
           (s,r)) ->
           FStar_Syntax_Syntax.mk
             (FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_string (s, r))) FStar_Range.dummyRange
       | FStar_TypeChecker_NBETerm.Constant (FStar_TypeChecker_NBETerm.Char
           c) -> FStar_Syntax_Util.exp_char c
       | FStar_TypeChecker_NBETerm.Constant (FStar_TypeChecker_NBETerm.Range
           r) ->
           FStar_TypeChecker_Cfg.embed_simple FStar_Syntax_Embeddings.e_range
             r FStar_Range.dummyRange
       | FStar_TypeChecker_NBETerm.Constant (FStar_TypeChecker_NBETerm.SConst
           c) ->
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant c)
             FStar_Range.dummyRange
       | FStar_TypeChecker_NBETerm.Type_t u ->
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type u)
             FStar_Range.dummyRange
       | FStar_TypeChecker_NBETerm.Lam (f,binders,arity) ->
           let uu____8137 =
             match binders with
             | FStar_Util.Inl (ctx,binders1,rc) ->
                 let uu____8185 =
                   FStar_List.fold_left
                     (fun uu____8239  ->
                        fun uu____8240  ->
                          match (uu____8239, uu____8240) with
                          | ((ctx1,binders_rev,accus_rev),(x1,q)) ->
                              let tnorm =
                                let uu____8365 =
                                  translate cfg ctx1
                                    x1.FStar_Syntax_Syntax.sort
                                   in
                                readback cfg uu____8365  in
                              let x2 =
                                let uu___1227_8367 =
                                  FStar_Syntax_Syntax.freshen_bv x1  in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___1227_8367.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___1227_8367.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = tnorm
                                }  in
                              let ax = FStar_TypeChecker_NBETerm.mkAccuVar x2
                                 in
                              let ctx2 = ax :: ctx1  in
                              (ctx2, ((x2, q) :: binders_rev), (ax ::
                                accus_rev))) (ctx, [], []) binders1
                    in
                 (match uu____8185 with
                  | (ctx1,binders_rev,accus_rev) ->
                      let rc1 =
                        match rc with
                        | FStar_Pervasives_Native.None  ->
                            FStar_Pervasives_Native.None
                        | FStar_Pervasives_Native.Some rc1 ->
                            let uu____8453 =
                              let uu____8454 =
                                translate_residual_comp cfg ctx1 rc1  in
                              readback_residual_comp cfg uu____8454  in
                            FStar_Pervasives_Native.Some uu____8453
                         in
                      ((FStar_List.rev binders_rev), accus_rev, rc1))
             | FStar_Util.Inr args ->
                 let uu____8488 =
                   FStar_List.fold_right
                     (fun uu____8529  ->
                        fun uu____8530  ->
                          match (uu____8529, uu____8530) with
                          | ((t,uu____8582),(binders1,accus)) ->
                              let x1 =
                                let uu____8624 = readback cfg t  in
                                FStar_Syntax_Syntax.new_bv
                                  FStar_Pervasives_Native.None uu____8624
                                 in
                              let uu____8625 =
                                let uu____8628 =
                                  FStar_TypeChecker_NBETerm.mkAccuVar x1  in
                                uu____8628 :: accus  in
                              (((x1, FStar_Pervasives_Native.None) ::
                                binders1), uu____8625)) args ([], [])
                    in
                 (match uu____8488 with
                  | (binders1,accus) ->
                      (binders1, (FStar_List.rev accus),
                        FStar_Pervasives_Native.None))
              in
           (match uu____8137 with
            | (binders1,accus_rev,rc) ->
                let body =
                  let uu____8711 = f accus_rev  in readback cfg uu____8711
                   in
                FStar_Syntax_Util.abs binders1 body rc)
       | FStar_TypeChecker_NBETerm.Refinement (f,targ) ->
           if
             ((cfg.core_cfg).FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.for_extraction
           then
             let uu____8735 =
               let uu____8736 = targ ()  in
               FStar_Pervasives_Native.fst uu____8736  in
             readback cfg uu____8735
           else
             (let x1 =
                let uu____8744 =
                  let uu____8745 =
                    let uu____8746 = targ ()  in
                    FStar_Pervasives_Native.fst uu____8746  in
                  readback cfg uu____8745  in
                FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                  uu____8744
                 in
              let body =
                let uu____8752 =
                  let uu____8753 = FStar_TypeChecker_NBETerm.mkAccuVar x1  in
                  f uu____8753  in
                readback cfg uu____8752  in
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
               (fun uu____8823  ->
                  match uu____8823 with
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
               (fun uu____8875  ->
                  match uu____8875 with
                  | (x1,q) ->
                      let uu____8886 = readback cfg x1  in (uu____8886, q))
               args
              in
           let fv1 =
             FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
               FStar_Range.dummyRange
              in
           let app =
             let uu____8893 =
               FStar_Syntax_Syntax.mk_Tm_uinst fv1 (FStar_List.rev us)  in
             FStar_Syntax_Util.mk_app uu____8893 args1  in
           app
       | FStar_TypeChecker_NBETerm.FV (fv,us,args) ->
           let args1 =
             map_rev
               (fun uu____8934  ->
                  match uu____8934 with
                  | (x1,q) ->
                      let uu____8945 = readback cfg x1  in (uu____8945, q))
               args
              in
           let fv1 =
             FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
               FStar_Range.dummyRange
              in
           let app =
             let uu____8952 =
               FStar_Syntax_Syntax.mk_Tm_uinst fv1 (FStar_List.rev us)  in
             FStar_Syntax_Util.mk_app uu____8952 args1  in
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
             let uu____8993 = FStar_Syntax_Syntax.bv_to_name bv  in
             FStar_Syntax_Util.mk_app uu____8993 args1  in
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
               FStar_Range.dummyRange
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
             let uu____9093 = FStar_Thunk.force typ  in
             readback cfg uu____9093  in
           let defn1 =
             let uu____9095 = FStar_Thunk.force defn  in
             readback cfg uu____9095  in
           let body1 =
             let uu____9097 =
               let uu____9098 = FStar_Thunk.force body  in
               readback cfg uu____9098  in
             FStar_Syntax_Subst.close [(var, FStar_Pervasives_Native.None)]
               uu____9097
              in
           let lbname =
             let uu____9118 =
               let uu___1346_9119 =
                 FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
               {
                 FStar_Syntax_Syntax.ppname =
                   (uu___1346_9119.FStar_Syntax_Syntax.ppname);
                 FStar_Syntax_Syntax.index =
                   (uu___1346_9119.FStar_Syntax_Syntax.index);
                 FStar_Syntax_Syntax.sort = typ1
               }  in
             FStar_Util.Inl uu____9118  in
           let lb1 =
             let uu___1349_9121 = lb  in
             {
               FStar_Syntax_Syntax.lbname = lbname;
               FStar_Syntax_Syntax.lbunivs =
                 (uu___1349_9121.FStar_Syntax_Syntax.lbunivs);
               FStar_Syntax_Syntax.lbtyp = typ1;
               FStar_Syntax_Syntax.lbeff =
                 (uu___1349_9121.FStar_Syntax_Syntax.lbeff);
               FStar_Syntax_Syntax.lbdef = defn1;
               FStar_Syntax_Syntax.lbattrs =
                 (uu___1349_9121.FStar_Syntax_Syntax.lbattrs);
               FStar_Syntax_Syntax.lbpos =
                 (uu___1349_9121.FStar_Syntax_Syntax.lbpos)
             }  in
           let hd =
             FStar_Syntax_Syntax.mk
               (FStar_Syntax_Syntax.Tm_let ((false, [lb1]), body1))
               FStar_Range.dummyRange
              in
           let args1 = readback_args cfg args  in
           FStar_Syntax_Util.mk_app hd args1
       | FStar_TypeChecker_NBETerm.Accu
           (FStar_TypeChecker_NBETerm.UnreducedLetRec
            (vars_typs_defns,body,lbs),args)
           ->
           let lbs1 =
             FStar_List.map2
               (fun uu____9199  ->
                  fun lb  ->
                    match uu____9199 with
                    | (v,t,d) ->
                        let t1 = readback cfg t  in
                        let def = readback cfg d  in
                        let v1 =
                          let uu___1369_9213 = v  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___1369_9213.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___1369_9213.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t1
                          }  in
                        let uu___1372_9214 = lb  in
                        {
                          FStar_Syntax_Syntax.lbname = (FStar_Util.Inl v1);
                          FStar_Syntax_Syntax.lbunivs =
                            (uu___1372_9214.FStar_Syntax_Syntax.lbunivs);
                          FStar_Syntax_Syntax.lbtyp = t1;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___1372_9214.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = def;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___1372_9214.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___1372_9214.FStar_Syntax_Syntax.lbpos)
                        }) vars_typs_defns lbs
              in
           let body1 = readback cfg body  in
           let uu____9216 = FStar_Syntax_Subst.close_let_rec lbs1 body1  in
           (match uu____9216 with
            | (lbs2,body2) ->
                let hd =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_let ((true, lbs2), body2))
                    FStar_Range.dummyRange
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
           let uu____9299 = FStar_Util.first_N (n_args - n_univs) args_rev
              in
           (match uu____9299 with
            | (args_rev1,univs) ->
                let uu____9346 =
                  let uu____9347 =
                    let uu____9348 =
                      FStar_List.map FStar_Pervasives_Native.fst univs  in
                    translate cfg uu____9348 lb.FStar_Syntax_Syntax.lbdef  in
                  iapp cfg uu____9347 (FStar_List.rev args_rev1)  in
                readback cfg uu____9346)
       | FStar_TypeChecker_NBETerm.TopLevelRec
           (lb,uu____9360,uu____9361,args) ->
           let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
           let head =
             FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
               FStar_Range.dummyRange
              in
           let args1 =
             FStar_List.map
               (fun uu____9406  ->
                  match uu____9406 with
                  | (t,q) ->
                      let uu____9417 = readback cfg t  in (uu____9417, q))
               args
              in
           FStar_Syntax_Util.mk_app head args1
       | FStar_TypeChecker_NBETerm.LocalLetRec
           (i,uu____9419,lbs,bs,args,_ar,_ar_lst) ->
           let lbnames =
             FStar_List.map
               (fun lb  ->
                  let uu____9461 =
                    let uu____9463 =
                      let uu____9464 =
                        FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                      uu____9464.FStar_Syntax_Syntax.ppname  in
                    FStar_Ident.string_of_id uu____9463  in
                  FStar_Syntax_Syntax.gen_bv uu____9461
                    FStar_Pervasives_Native.None lb.FStar_Syntax_Syntax.lbtyp)
               lbs
              in
           let let_rec_env =
             let uu____9468 =
               FStar_List.map
                 (fun x1  ->
                    FStar_TypeChecker_NBETerm.Accu
                      ((FStar_TypeChecker_NBETerm.Var x1), [])) lbnames
                in
             FStar_List.rev_append uu____9468 bs  in
           let lbs1 =
             FStar_List.map2
               (fun lb  ->
                  fun lbname  ->
                    let lbdef =
                      let uu____9494 =
                        translate cfg let_rec_env
                          lb.FStar_Syntax_Syntax.lbdef
                         in
                      readback cfg uu____9494  in
                    let lbtyp =
                      let uu____9496 =
                        translate cfg bs lb.FStar_Syntax_Syntax.lbtyp  in
                      readback cfg uu____9496  in
                    let uu___1427_9497 = lb  in
                    {
                      FStar_Syntax_Syntax.lbname = (FStar_Util.Inl lbname);
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___1427_9497.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = lbtyp;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___1427_9497.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = lbdef;
                      FStar_Syntax_Syntax.lbattrs =
                        (uu___1427_9497.FStar_Syntax_Syntax.lbattrs);
                      FStar_Syntax_Syntax.lbpos =
                        (uu___1427_9497.FStar_Syntax_Syntax.lbpos)
                    }) lbs lbnames
              in
           let body =
             let uu____9499 = FStar_List.nth lbnames i  in
             FStar_Syntax_Syntax.bv_to_name uu____9499  in
           let uu____9500 = FStar_Syntax_Subst.close_let_rec lbs1 body  in
           (match uu____9500 with
            | (lbs2,body1) ->
                let head =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_let ((true, lbs2), body1))
                    FStar_Range.dummyRange
                   in
                let args1 =
                  FStar_List.map
                    (fun uu____9548  ->
                       match uu____9548 with
                       | (x1,q) ->
                           let uu____9559 = readback cfg x1  in
                           (uu____9559, q)) args
                   in
                FStar_Syntax_Util.mk_app head args1)
       | FStar_TypeChecker_NBETerm.Quote (qt,qi) ->
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_quoted (qt, qi))
             FStar_Range.dummyRange
       | FStar_TypeChecker_NBETerm.Lazy (FStar_Util.Inl li,uu____9565) ->
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_lazy li)
             FStar_Range.dummyRange
       | FStar_TypeChecker_NBETerm.Lazy (uu____9582,thunk) ->
           let uu____9604 = FStar_Thunk.force thunk  in
           readback cfg uu____9604)

type step =
  | Primops 
  | UnfoldUntil of FStar_Syntax_Syntax.delta_depth 
  | UnfoldOnly of FStar_Ident.lid Prims.list 
  | UnfoldAttr of FStar_Ident.lid Prims.list 
  | UnfoldTac 
  | Reify 
let (uu___is_Primops : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Primops  -> true | uu____9633 -> false
  
let (uu___is_UnfoldUntil : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldUntil _0 -> true | uu____9645 -> false
  
let (__proj__UnfoldUntil__item___0 : step -> FStar_Syntax_Syntax.delta_depth)
  = fun projectee  -> match projectee with | UnfoldUntil _0 -> _0 
let (uu___is_UnfoldOnly : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldOnly _0 -> true | uu____9666 -> false
  
let (__proj__UnfoldOnly__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldOnly _0 -> _0 
let (uu___is_UnfoldAttr : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldAttr _0 -> true | uu____9693 -> false
  
let (__proj__UnfoldAttr__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldAttr _0 -> _0 
let (uu___is_UnfoldTac : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldTac  -> true | uu____9717 -> false
  
let (uu___is_Reify : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reify  -> true | uu____9728 -> false
  
let (step_as_normalizer_step : step -> FStar_TypeChecker_Env.step) =
  fun uu___2_9735  ->
    match uu___2_9735 with
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
      fun args  -> let uu____9759 = new_config cfg  in iapp uu____9759 t args
  
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
            let uu___1473_9791 = cfg  in
            {
              FStar_TypeChecker_Cfg.steps =
                (let uu___1475_9794 = cfg.FStar_TypeChecker_Cfg.steps  in
                 {
                   FStar_TypeChecker_Cfg.beta =
                     (uu___1475_9794.FStar_TypeChecker_Cfg.beta);
                   FStar_TypeChecker_Cfg.iota =
                     (uu___1475_9794.FStar_TypeChecker_Cfg.iota);
                   FStar_TypeChecker_Cfg.zeta =
                     (uu___1475_9794.FStar_TypeChecker_Cfg.zeta);
                   FStar_TypeChecker_Cfg.zeta_full =
                     (uu___1475_9794.FStar_TypeChecker_Cfg.zeta_full);
                   FStar_TypeChecker_Cfg.weak =
                     (uu___1475_9794.FStar_TypeChecker_Cfg.weak);
                   FStar_TypeChecker_Cfg.hnf =
                     (uu___1475_9794.FStar_TypeChecker_Cfg.hnf);
                   FStar_TypeChecker_Cfg.primops =
                     (uu___1475_9794.FStar_TypeChecker_Cfg.primops);
                   FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                     (uu___1475_9794.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                   FStar_TypeChecker_Cfg.unfold_until =
                     (uu___1475_9794.FStar_TypeChecker_Cfg.unfold_until);
                   FStar_TypeChecker_Cfg.unfold_only =
                     (uu___1475_9794.FStar_TypeChecker_Cfg.unfold_only);
                   FStar_TypeChecker_Cfg.unfold_fully =
                     (uu___1475_9794.FStar_TypeChecker_Cfg.unfold_fully);
                   FStar_TypeChecker_Cfg.unfold_attr =
                     (uu___1475_9794.FStar_TypeChecker_Cfg.unfold_attr);
                   FStar_TypeChecker_Cfg.unfold_tac =
                     (uu___1475_9794.FStar_TypeChecker_Cfg.unfold_tac);
                   FStar_TypeChecker_Cfg.pure_subterms_within_computations =
                     (uu___1475_9794.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                   FStar_TypeChecker_Cfg.simplify =
                     (uu___1475_9794.FStar_TypeChecker_Cfg.simplify);
                   FStar_TypeChecker_Cfg.erase_universes =
                     (uu___1475_9794.FStar_TypeChecker_Cfg.erase_universes);
                   FStar_TypeChecker_Cfg.allow_unbound_universes =
                     (uu___1475_9794.FStar_TypeChecker_Cfg.allow_unbound_universes);
                   FStar_TypeChecker_Cfg.reify_ = true;
                   FStar_TypeChecker_Cfg.compress_uvars =
                     (uu___1475_9794.FStar_TypeChecker_Cfg.compress_uvars);
                   FStar_TypeChecker_Cfg.no_full_norm =
                     (uu___1475_9794.FStar_TypeChecker_Cfg.no_full_norm);
                   FStar_TypeChecker_Cfg.check_no_uvars =
                     (uu___1475_9794.FStar_TypeChecker_Cfg.check_no_uvars);
                   FStar_TypeChecker_Cfg.unmeta =
                     (uu___1475_9794.FStar_TypeChecker_Cfg.unmeta);
                   FStar_TypeChecker_Cfg.unascribe =
                     (uu___1475_9794.FStar_TypeChecker_Cfg.unascribe);
                   FStar_TypeChecker_Cfg.in_full_norm_request =
                     (uu___1475_9794.FStar_TypeChecker_Cfg.in_full_norm_request);
                   FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                     (uu___1475_9794.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                   FStar_TypeChecker_Cfg.nbe_step =
                     (uu___1475_9794.FStar_TypeChecker_Cfg.nbe_step);
                   FStar_TypeChecker_Cfg.for_extraction =
                     (uu___1475_9794.FStar_TypeChecker_Cfg.for_extraction)
                 });
              FStar_TypeChecker_Cfg.tcenv =
                (uu___1473_9791.FStar_TypeChecker_Cfg.tcenv);
              FStar_TypeChecker_Cfg.debug =
                (uu___1473_9791.FStar_TypeChecker_Cfg.debug);
              FStar_TypeChecker_Cfg.delta_level =
                (uu___1473_9791.FStar_TypeChecker_Cfg.delta_level);
              FStar_TypeChecker_Cfg.primitive_steps =
                (uu___1473_9791.FStar_TypeChecker_Cfg.primitive_steps);
              FStar_TypeChecker_Cfg.strong =
                (uu___1473_9791.FStar_TypeChecker_Cfg.strong);
              FStar_TypeChecker_Cfg.memoize_lazy =
                (uu___1473_9791.FStar_TypeChecker_Cfg.memoize_lazy);
              FStar_TypeChecker_Cfg.normalize_pure_lets =
                (uu___1473_9791.FStar_TypeChecker_Cfg.normalize_pure_lets);
              FStar_TypeChecker_Cfg.reifying =
                (uu___1473_9791.FStar_TypeChecker_Cfg.reifying)
            }  in
          (let uu____9797 =
             (FStar_TypeChecker_Env.debug env (FStar_Options.Other "NBETop"))
               ||
               (FStar_TypeChecker_Env.debug env (FStar_Options.Other "NBE"))
              in
           if uu____9797
           then
             let uu____9802 = FStar_Syntax_Print.term_to_string e  in
             FStar_Util.print1 "Calling NBE with (%s) {\n" uu____9802
           else ());
          (let cfg2 = new_config cfg1  in
           let r =
             let uu____9809 = translate cfg2 [] e  in
             readback cfg2 uu____9809  in
           (let uu____9811 =
              (FStar_TypeChecker_Env.debug env (FStar_Options.Other "NBETop"))
                ||
                (FStar_TypeChecker_Env.debug env (FStar_Options.Other "NBE"))
               in
            if uu____9811
            then
              let uu____9816 = FStar_Syntax_Print.term_to_string r  in
              FStar_Util.print1 "}\nNBE returned (%s)\n" uu____9816
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
          let uu___1491_9843 = cfg  in
          {
            FStar_TypeChecker_Cfg.steps =
              (let uu___1493_9846 = cfg.FStar_TypeChecker_Cfg.steps  in
               {
                 FStar_TypeChecker_Cfg.beta =
                   (uu___1493_9846.FStar_TypeChecker_Cfg.beta);
                 FStar_TypeChecker_Cfg.iota =
                   (uu___1493_9846.FStar_TypeChecker_Cfg.iota);
                 FStar_TypeChecker_Cfg.zeta =
                   (uu___1493_9846.FStar_TypeChecker_Cfg.zeta);
                 FStar_TypeChecker_Cfg.zeta_full =
                   (uu___1493_9846.FStar_TypeChecker_Cfg.zeta_full);
                 FStar_TypeChecker_Cfg.weak =
                   (uu___1493_9846.FStar_TypeChecker_Cfg.weak);
                 FStar_TypeChecker_Cfg.hnf =
                   (uu___1493_9846.FStar_TypeChecker_Cfg.hnf);
                 FStar_TypeChecker_Cfg.primops =
                   (uu___1493_9846.FStar_TypeChecker_Cfg.primops);
                 FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                   (uu___1493_9846.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                 FStar_TypeChecker_Cfg.unfold_until =
                   (uu___1493_9846.FStar_TypeChecker_Cfg.unfold_until);
                 FStar_TypeChecker_Cfg.unfold_only =
                   (uu___1493_9846.FStar_TypeChecker_Cfg.unfold_only);
                 FStar_TypeChecker_Cfg.unfold_fully =
                   (uu___1493_9846.FStar_TypeChecker_Cfg.unfold_fully);
                 FStar_TypeChecker_Cfg.unfold_attr =
                   (uu___1493_9846.FStar_TypeChecker_Cfg.unfold_attr);
                 FStar_TypeChecker_Cfg.unfold_tac =
                   (uu___1493_9846.FStar_TypeChecker_Cfg.unfold_tac);
                 FStar_TypeChecker_Cfg.pure_subterms_within_computations =
                   (uu___1493_9846.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                 FStar_TypeChecker_Cfg.simplify =
                   (uu___1493_9846.FStar_TypeChecker_Cfg.simplify);
                 FStar_TypeChecker_Cfg.erase_universes =
                   (uu___1493_9846.FStar_TypeChecker_Cfg.erase_universes);
                 FStar_TypeChecker_Cfg.allow_unbound_universes =
                   (uu___1493_9846.FStar_TypeChecker_Cfg.allow_unbound_universes);
                 FStar_TypeChecker_Cfg.reify_ = true;
                 FStar_TypeChecker_Cfg.compress_uvars =
                   (uu___1493_9846.FStar_TypeChecker_Cfg.compress_uvars);
                 FStar_TypeChecker_Cfg.no_full_norm =
                   (uu___1493_9846.FStar_TypeChecker_Cfg.no_full_norm);
                 FStar_TypeChecker_Cfg.check_no_uvars =
                   (uu___1493_9846.FStar_TypeChecker_Cfg.check_no_uvars);
                 FStar_TypeChecker_Cfg.unmeta =
                   (uu___1493_9846.FStar_TypeChecker_Cfg.unmeta);
                 FStar_TypeChecker_Cfg.unascribe =
                   (uu___1493_9846.FStar_TypeChecker_Cfg.unascribe);
                 FStar_TypeChecker_Cfg.in_full_norm_request =
                   (uu___1493_9846.FStar_TypeChecker_Cfg.in_full_norm_request);
                 FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                   (uu___1493_9846.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                 FStar_TypeChecker_Cfg.nbe_step =
                   (uu___1493_9846.FStar_TypeChecker_Cfg.nbe_step);
                 FStar_TypeChecker_Cfg.for_extraction =
                   (uu___1493_9846.FStar_TypeChecker_Cfg.for_extraction)
               });
            FStar_TypeChecker_Cfg.tcenv =
              (uu___1491_9843.FStar_TypeChecker_Cfg.tcenv);
            FStar_TypeChecker_Cfg.debug =
              (uu___1491_9843.FStar_TypeChecker_Cfg.debug);
            FStar_TypeChecker_Cfg.delta_level =
              (uu___1491_9843.FStar_TypeChecker_Cfg.delta_level);
            FStar_TypeChecker_Cfg.primitive_steps =
              (uu___1491_9843.FStar_TypeChecker_Cfg.primitive_steps);
            FStar_TypeChecker_Cfg.strong =
              (uu___1491_9843.FStar_TypeChecker_Cfg.strong);
            FStar_TypeChecker_Cfg.memoize_lazy =
              (uu___1491_9843.FStar_TypeChecker_Cfg.memoize_lazy);
            FStar_TypeChecker_Cfg.normalize_pure_lets =
              (uu___1491_9843.FStar_TypeChecker_Cfg.normalize_pure_lets);
            FStar_TypeChecker_Cfg.reifying =
              (uu___1491_9843.FStar_TypeChecker_Cfg.reifying)
          }  in
        let cfg2 = new_config cfg1  in
        debug cfg2
          (fun uu____9852  ->
             let uu____9853 = FStar_Syntax_Print.term_to_string e  in
             FStar_Util.print1 "Calling NBE with (%s) {\n" uu____9853);
        (let r =
           let uu____9857 = translate cfg2 [] e  in readback cfg2 uu____9857
            in
         debug cfg2
           (fun uu____9861  ->
              let uu____9862 = FStar_Syntax_Print.term_to_string r  in
              FStar_Util.print1 "}\nNBE returned (%s)\n" uu____9862);
         r)
  