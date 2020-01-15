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
    | FStar_TypeChecker_NBETerm.Lazy (uu____657,t1) -> FStar_Thunk.force t1
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
              (fun uu____788  ->
                 let uu____789 =
                   FStar_TypeChecker_NBETerm.t_to_string scrutinee0  in
                 let uu____791 = FStar_Syntax_Print.pat_to_string p  in
                 FStar_Util.print2 "matches_pat (%s, %s)\n" uu____789
                   uu____791);
            (let scrutinee = unlazy scrutinee0  in
             let r =
               match p.FStar_Syntax_Syntax.v with
               | FStar_Syntax_Syntax.Pat_var bv ->
                   FStar_Util.Inl [scrutinee0]
               | FStar_Syntax_Syntax.Pat_wild bv ->
                   FStar_Util.Inl [scrutinee0]
               | FStar_Syntax_Syntax.Pat_dot_term uu____818 ->
                   FStar_Util.Inl []
               | FStar_Syntax_Syntax.Pat_constant s ->
                   let matches_const c s1 =
                     debug cfg
                       (fun uu____845  ->
                          let uu____846 =
                            FStar_TypeChecker_NBETerm.t_to_string c  in
                          let uu____848 =
                            FStar_Syntax_Print.const_to_string s1  in
                          FStar_Util.print2
                            "Testing term %s against pattern %s\n" uu____846
                            uu____848);
                     (match c with
                      | FStar_TypeChecker_NBETerm.Constant
                          (FStar_TypeChecker_NBETerm.Unit ) ->
                          s1 = FStar_Const.Const_unit
                      | FStar_TypeChecker_NBETerm.Constant
                          (FStar_TypeChecker_NBETerm.Bool b) ->
                          (match s1 with
                           | FStar_Const.Const_bool p1 -> b = p1
                           | uu____858 -> false)
                      | FStar_TypeChecker_NBETerm.Constant
                          (FStar_TypeChecker_NBETerm.Int i) ->
                          (match s1 with
                           | FStar_Const.Const_int
                               (p1,FStar_Pervasives_Native.None ) ->
                               let uu____875 =
                                 FStar_BigInt.big_int_of_string p1  in
                               i = uu____875
                           | uu____876 -> false)
                      | FStar_TypeChecker_NBETerm.Constant
                          (FStar_TypeChecker_NBETerm.String (st,uu____879))
                          ->
                          (match s1 with
                           | FStar_Const.Const_string (p1,uu____884) ->
                               st = p1
                           | uu____888 -> false)
                      | FStar_TypeChecker_NBETerm.Constant
                          (FStar_TypeChecker_NBETerm.Char c1) ->
                          (match s1 with
                           | FStar_Const.Const_char p1 -> c1 = p1
                           | uu____896 -> false)
                      | uu____898 -> false)
                      in
                   let uu____900 = matches_const scrutinee s  in
                   if uu____900
                   then FStar_Util.Inl []
                   else FStar_Util.Inr false
               | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                   let rec matches_args out a p1 =
                     match (a, p1) with
                     | ([],[]) -> FStar_Util.Inl out
                     | ((t,uu____1038)::rest_a,(p2,uu____1041)::rest_p) ->
                         let uu____1080 = matches_pat t p2  in
                         (match uu____1080 with
                          | FStar_Util.Inl s ->
                              matches_args (FStar_List.append out s) rest_a
                                rest_p
                          | m -> m)
                     | uu____1109 -> FStar_Util.Inr false  in
                   (match scrutinee with
                    | FStar_TypeChecker_NBETerm.Construct (fv',_us,args_rev)
                        ->
                        let uu____1157 = FStar_Syntax_Syntax.fv_eq fv fv'  in
                        if uu____1157
                        then
                          matches_args [] (FStar_List.rev args_rev) arg_pats
                        else FStar_Util.Inr false
                    | uu____1177 -> FStar_Util.Inr true)
                in
             let res_to_string uu___0_1195 =
               match uu___0_1195 with
               | FStar_Util.Inr b ->
                   let uu____1209 = FStar_Util.string_of_bool b  in
                   Prims.op_Hat "Inr " uu____1209
               | FStar_Util.Inl bs ->
                   let uu____1218 =
                     FStar_Util.string_of_int (FStar_List.length bs)  in
                   Prims.op_Hat "Inl " uu____1218
                in
             debug cfg
               (fun uu____1226  ->
                  let uu____1227 =
                    FStar_TypeChecker_NBETerm.t_to_string scrutinee  in
                  let uu____1229 = FStar_Syntax_Print.pat_to_string p  in
                  let uu____1231 = res_to_string r  in
                  FStar_Util.print3 "matches_pat (%s, %s) = %s\n" uu____1227
                    uu____1229 uu____1231);
             r)
             in
          match branches1 with
          | [] -> FStar_Pervasives_Native.None
          | (p,_wopt,e)::branches2 ->
              let uu____1270 = matches_pat scrut1 p  in
              (match uu____1270 with
               | FStar_Util.Inl matches ->
                   (debug cfg
                      (fun uu____1295  ->
                         let uu____1296 = FStar_Syntax_Print.pat_to_string p
                            in
                         FStar_Util.print1 "Pattern %s matches\n" uu____1296);
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
        | (uu____1445,[]) -> (true, acc, ts)
        | ([],uu____1476::uu____1477) -> (false, acc, [])
        | (t::ts1,in_decreases_clause::bs) ->
            let uu____1546 =
              in_decreases_clause &&
                (FStar_TypeChecker_NBETerm.isAccu
                   (FStar_Pervasives_Native.fst t))
               in
            if uu____1546
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
        let mapper uu____1645 =
          match uu____1645 with
          | (lr,rng) ->
              (match lr with
               | FStar_Util.Inr (elt,FStar_Pervasives_Native.None ) ->
                   FStar_Pervasives_Native.Some elt
               | FStar_Util.Inr (elt,FStar_Pervasives_Native.Some us) ->
                   (debug cfg
                      (fun uu____1728  ->
                         let uu____1729 =
                           FStar_Syntax_Print.univs_to_string us  in
                         FStar_Util.print1
                           "Universes in local declaration: %s\n" uu____1729);
                    FStar_Pervasives_Native.Some elt)
               | uu____1732 -> FStar_Pervasives_Native.None)
           in
        let uu____1747 = FStar_TypeChecker_Env.lookup_qname env lid  in
        FStar_Util.bind_opt uu____1747 mapper
  
let (is_univ : FStar_TypeChecker_NBETerm.t -> Prims.bool) =
  fun tm  ->
    match tm with
    | FStar_TypeChecker_NBETerm.Univ uu____1794 -> true
    | uu____1796 -> false
  
let (un_univ : FStar_TypeChecker_NBETerm.t -> FStar_Syntax_Syntax.universe) =
  fun tm  ->
    match tm with
    | FStar_TypeChecker_NBETerm.Univ u -> u
    | t ->
        let uu____1806 =
          let uu____1808 = FStar_TypeChecker_NBETerm.t_to_string t  in
          Prims.op_Hat "Not a universe: " uu____1808  in
        failwith uu____1806
  
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
              (uu____1830,uu____1831,uu____1832,uu____1833,uu____1834,uu____1835);
            FStar_Syntax_Syntax.sigrng = uu____1836;
            FStar_Syntax_Syntax.sigquals = uu____1837;
            FStar_Syntax_Syntax.sigmeta = uu____1838;
            FStar_Syntax_Syntax.sigattrs = uu____1839;
            FStar_Syntax_Syntax.sigopts = uu____1840;_},uu____1841),uu____1842)
        -> true
    | uu____1902 -> false
  
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
              let uu____1942 = aux u3  in
              FStar_Syntax_Syntax.U_succ uu____1942
          | FStar_Syntax_Syntax.U_max us ->
              let uu____1946 = FStar_List.map aux us  in
              FStar_Syntax_Syntax.U_max uu____1946
          | FStar_Syntax_Syntax.U_unknown  -> u2
          | FStar_Syntax_Syntax.U_name uu____1949 -> u2
          | FStar_Syntax_Syntax.U_unif uu____1950 -> u2
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
           | FStar_Util.Inl uu____1981 -> failwith "find_let : impossible"
           | FStar_Util.Inr name ->
               let uu____1986 = FStar_Syntax_Syntax.fv_eq name fvar1  in
               if uu____1986
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
          (fun uu____2257  ->
             let uu____2258 =
               let uu____2260 = FStar_Syntax_Subst.compress e  in
               FStar_Syntax_Print.tag_of_term uu____2260  in
             let uu____2261 =
               let uu____2263 = FStar_Syntax_Subst.compress e  in
               FStar_Syntax_Print.term_to_string uu____2263  in
             FStar_Util.print2 "Term: %s - %s\n" uu____2258 uu____2261);
        (let uu____2265 =
           let uu____2266 = FStar_Syntax_Subst.compress e  in
           uu____2266.FStar_Syntax_Syntax.n  in
         match uu____2265 with
         | FStar_Syntax_Syntax.Tm_delayed (uu____2269,uu____2270) ->
             failwith "Tm_delayed: Impossible"
         | FStar_Syntax_Syntax.Tm_unknown  ->
             FStar_TypeChecker_NBETerm.Unknown
         | FStar_Syntax_Syntax.Tm_constant c ->
             let uu____2309 = translate_constant c  in
             FStar_TypeChecker_NBETerm.Constant uu____2309
         | FStar_Syntax_Syntax.Tm_bvar db ->
             if db.FStar_Syntax_Syntax.index < (FStar_List.length bs)
             then
               let t = FStar_List.nth bs db.FStar_Syntax_Syntax.index  in
               (debug1
                  (fun uu____2320  ->
                     let uu____2321 = FStar_TypeChecker_NBETerm.t_to_string t
                        in
                     let uu____2323 =
                       let uu____2325 =
                         FStar_List.map FStar_TypeChecker_NBETerm.t_to_string
                           bs
                          in
                       FStar_All.pipe_right uu____2325
                         (FStar_String.concat "; ")
                        in
                     FStar_Util.print2
                       "Resolved bvar to %s\n\tcontext is [%s]\n" uu____2321
                       uu____2323);
                t)
             else failwith "de Bruijn index out of bounds"
         | FStar_Syntax_Syntax.Tm_uinst (t,us) ->
             (debug1
                (fun uu____2352  ->
                   let uu____2353 = FStar_Syntax_Print.term_to_string t  in
                   let uu____2355 =
                     let uu____2357 =
                       FStar_List.map FStar_Syntax_Print.univ_to_string us
                        in
                     FStar_All.pipe_right uu____2357
                       (FStar_String.concat ", ")
                      in
                   FStar_Util.print2 "Uinst term : %s\nUnivs : %s\n"
                     uu____2353 uu____2355);
              (let uu____2368 = translate cfg bs t  in
               let uu____2369 =
                 FStar_List.map
                   (fun x  ->
                      let uu____2373 =
                        let uu____2374 = translate_univ cfg bs x  in
                        FStar_TypeChecker_NBETerm.Univ uu____2374  in
                      FStar_TypeChecker_NBETerm.as_arg uu____2373) us
                  in
               iapp cfg uu____2368 uu____2369))
         | FStar_Syntax_Syntax.Tm_type u ->
             let uu____2376 = translate_univ cfg bs u  in
             FStar_TypeChecker_NBETerm.Type_t uu____2376
         | FStar_Syntax_Syntax.Tm_arrow (xs,c) ->
             let norm1 uu____2406 =
               let uu____2407 =
                 FStar_List.fold_left
                   (fun uu____2451  ->
                      fun uu____2452  ->
                        match (uu____2451, uu____2452) with
                        | ((ctx,binders_rev),(x,q)) ->
                            let t =
                              let uu____2556 =
                                translate cfg ctx x.FStar_Syntax_Syntax.sort
                                 in
                              readback cfg uu____2556  in
                            let x1 =
                              let uu___380_2558 =
                                FStar_Syntax_Syntax.freshen_bv x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___380_2558.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___380_2558.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t
                              }  in
                            let ctx1 =
                              let uu____2562 =
                                FStar_TypeChecker_NBETerm.mkAccuVar x1  in
                              uu____2562 :: ctx  in
                            (ctx1, ((x1, q) :: binders_rev))) (bs, []) xs
                  in
               match uu____2407 with
               | (ctx,binders_rev) ->
                   let c1 =
                     let uu____2622 = translate_comp cfg ctx c  in
                     readback_comp cfg uu____2622  in
                   FStar_Syntax_Util.arrow (FStar_List.rev binders_rev) c1
                in
             let uu____2629 =
               let uu____2646 = FStar_Thunk.mk norm1  in
               FStar_Util.Inl uu____2646  in
             FStar_TypeChecker_NBETerm.Arrow uu____2629
         | FStar_Syntax_Syntax.Tm_refine (bv,tm) ->
             if
               ((cfg.core_cfg).FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.for_extraction
             then translate cfg bs bv.FStar_Syntax_Syntax.sort
             else
               FStar_TypeChecker_NBETerm.Refinement
                 (((fun y  -> translate cfg (y :: bs) tm)),
                   ((fun uu____2684  ->
                       let uu____2685 =
                         translate cfg bs bv.FStar_Syntax_Syntax.sort  in
                       FStar_TypeChecker_NBETerm.as_arg uu____2685)))
         | FStar_Syntax_Syntax.Tm_ascribed (t,uu____2687,uu____2688) ->
             translate cfg bs t
         | FStar_Syntax_Syntax.Tm_uvar (u,(subst1,set_use_range1)) ->
             let norm_uvar uu____2755 =
               let norm_subst_elt uu___1_2761 =
                 match uu___1_2761 with
                 | FStar_Syntax_Syntax.NT (x,t) ->
                     let uu____2768 =
                       let uu____2775 =
                         let uu____2778 = translate cfg bs t  in
                         readback cfg uu____2778  in
                       (x, uu____2775)  in
                     FStar_Syntax_Syntax.NT uu____2768
                 | FStar_Syntax_Syntax.NM (x,i) ->
                     let x_i =
                       FStar_Syntax_Syntax.bv_to_tm
                         (let uu___417_2788 = x  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___417_2788.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index = i;
                            FStar_Syntax_Syntax.sort =
                              (uu___417_2788.FStar_Syntax_Syntax.sort)
                          })
                        in
                     let t =
                       let uu____2790 = translate cfg bs x_i  in
                       readback cfg uu____2790  in
                     (match t.FStar_Syntax_Syntax.n with
                      | FStar_Syntax_Syntax.Tm_bvar x_j ->
                          FStar_Syntax_Syntax.NM
                            (x, (x_j.FStar_Syntax_Syntax.index))
                      | uu____2793 -> FStar_Syntax_Syntax.NT (x, t))
                 | uu____2796 ->
                     failwith "Impossible: subst invariant of uvar nodes"
                  in
               let subst2 =
                 FStar_List.map (FStar_List.map norm_subst_elt) subst1  in
               let uu___427_2807 = e  in
               {
                 FStar_Syntax_Syntax.n =
                   (FStar_Syntax_Syntax.Tm_uvar (u, (subst2, set_use_range1)));
                 FStar_Syntax_Syntax.pos =
                   (uu___427_2807.FStar_Syntax_Syntax.pos);
                 FStar_Syntax_Syntax.vars =
                   (uu___427_2807.FStar_Syntax_Syntax.vars)
               }  in
             let uu____2820 =
               let uu____2831 =
                 let uu____2832 = FStar_Thunk.mk norm_uvar  in
                 FStar_TypeChecker_NBETerm.UVar uu____2832  in
               (uu____2831, [])  in
             FStar_TypeChecker_NBETerm.Accu uu____2820
         | FStar_Syntax_Syntax.Tm_name x ->
             FStar_TypeChecker_NBETerm.mkAccuVar x
         | FStar_Syntax_Syntax.Tm_abs ([],uu____2846,uu____2847) ->
             failwith "Impossible: abstraction with no binders"
         | FStar_Syntax_Syntax.Tm_abs (xs,body,resc) ->
             FStar_TypeChecker_NBETerm.Lam
               (((fun ys  -> translate cfg (FStar_List.append ys bs) body)),
                 (FStar_Util.Inl (bs, xs, resc)), (FStar_List.length xs))
         | FStar_Syntax_Syntax.Tm_fvar fvar1 ->
             let uu____2955 = try_in_cache cfg fvar1  in
             (match uu____2955 with
              | FStar_Pervasives_Native.Some t -> t
              | uu____2959 -> translate_fv cfg bs fvar1)
         | FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                  (FStar_Const.Const_reify );
                FStar_Syntax_Syntax.pos = uu____2962;
                FStar_Syntax_Syntax.vars = uu____2963;_},arg::more::args)
             ->
             let uu____3023 = FStar_Syntax_Util.head_and_args e  in
             (match uu____3023 with
              | (head1,uu____3041) ->
                  let head2 =
                    FStar_Syntax_Syntax.mk_Tm_app head1 [arg]
                      FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
                     in
                  let uu____3085 =
                    FStar_Syntax_Syntax.mk_Tm_app head2 (more :: args)
                      FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
                     in
                  translate cfg bs uu____3085)
         | FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                  (FStar_Const.Const_reflect uu____3094);
                FStar_Syntax_Syntax.pos = uu____3095;
                FStar_Syntax_Syntax.vars = uu____3096;_},arg::more::args)
             ->
             let uu____3156 = FStar_Syntax_Util.head_and_args e  in
             (match uu____3156 with
              | (head1,uu____3174) ->
                  let head2 =
                    FStar_Syntax_Syntax.mk_Tm_app head1 [arg]
                      FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
                     in
                  let uu____3218 =
                    FStar_Syntax_Syntax.mk_Tm_app head2 (more :: args)
                      FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
                     in
                  translate cfg bs uu____3218)
         | FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                  (FStar_Const.Const_reflect uu____3227);
                FStar_Syntax_Syntax.pos = uu____3228;
                FStar_Syntax_Syntax.vars = uu____3229;_},arg::[])
             when (cfg.core_cfg).FStar_TypeChecker_Cfg.reifying ->
             let cfg1 = reifying_false cfg  in
             translate cfg1 bs (FStar_Pervasives_Native.fst arg)
         | FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                  (FStar_Const.Const_reflect uu____3274);
                FStar_Syntax_Syntax.pos = uu____3275;
                FStar_Syntax_Syntax.vars = uu____3276;_},arg::[])
             ->
             let uu____3316 =
               translate cfg bs (FStar_Pervasives_Native.fst arg)  in
             FStar_TypeChecker_NBETerm.Reflect uu____3316
         | FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                  (FStar_Const.Const_reify );
                FStar_Syntax_Syntax.pos = uu____3321;
                FStar_Syntax_Syntax.vars = uu____3322;_},arg::[])
             when
             ((cfg.core_cfg).FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.reify_
             ->
             let cfg1 = reifying_true cfg  in
             translate cfg1 bs (FStar_Pervasives_Native.fst arg)
         | FStar_Syntax_Syntax.Tm_app (head1,args) ->
             (debug1
                (fun uu____3401  ->
                   let uu____3402 = FStar_Syntax_Print.term_to_string head1
                      in
                   let uu____3404 = FStar_Syntax_Print.args_to_string args
                      in
                   FStar_Util.print2 "Application: %s @ %s\n" uu____3402
                     uu____3404);
              (let uu____3407 = translate cfg bs head1  in
               let uu____3408 =
                 FStar_List.map
                   (fun x  ->
                      let uu____3430 =
                        translate cfg bs (FStar_Pervasives_Native.fst x)  in
                      (uu____3430, (FStar_Pervasives_Native.snd x))) args
                  in
               iapp cfg uu____3407 uu____3408))
         | FStar_Syntax_Syntax.Tm_match (scrut,branches) ->
             let make_branches uu____3482 =
               let cfg1 = zeta_false cfg  in
               let rec process_pattern bs1 p =
                 let uu____3513 =
                   match p.FStar_Syntax_Syntax.v with
                   | FStar_Syntax_Syntax.Pat_constant c ->
                       (bs1, (FStar_Syntax_Syntax.Pat_constant c))
                   | FStar_Syntax_Syntax.Pat_cons (fvar1,args) ->
                       let uu____3549 =
                         FStar_List.fold_left
                           (fun uu____3590  ->
                              fun uu____3591  ->
                                match (uu____3590, uu____3591) with
                                | ((bs2,args1),(arg,b)) ->
                                    let uu____3683 = process_pattern bs2 arg
                                       in
                                    (match uu____3683 with
                                     | (bs',arg') ->
                                         (bs', ((arg', b) :: args1))))
                           (bs1, []) args
                          in
                       (match uu____3549 with
                        | (bs',args') ->
                            (bs',
                              (FStar_Syntax_Syntax.Pat_cons
                                 (fvar1, (FStar_List.rev args')))))
                   | FStar_Syntax_Syntax.Pat_var bvar ->
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
                       (uu____3784, (FStar_Syntax_Syntax.Pat_var x))
                   | FStar_Syntax_Syntax.Pat_wild bvar ->
                       let x =
                         let uu____3792 =
                           let uu____3793 =
                             translate cfg1 bs1 bvar.FStar_Syntax_Syntax.sort
                              in
                           readback cfg1 uu____3793  in
                         FStar_Syntax_Syntax.new_bv
                           FStar_Pervasives_Native.None uu____3792
                          in
                       let uu____3794 =
                         let uu____3797 =
                           FStar_TypeChecker_NBETerm.mkAccuVar x  in
                         uu____3797 :: bs1  in
                       (uu____3794, (FStar_Syntax_Syntax.Pat_wild x))
                   | FStar_Syntax_Syntax.Pat_dot_term (bvar,tm) ->
                       let x =
                         let uu____3807 =
                           let uu____3808 =
                             translate cfg1 bs1 bvar.FStar_Syntax_Syntax.sort
                              in
                           readback cfg1 uu____3808  in
                         FStar_Syntax_Syntax.new_bv
                           FStar_Pervasives_Native.None uu____3807
                          in
                       let uu____3809 =
                         let uu____3810 =
                           let uu____3817 =
                             let uu____3820 = translate cfg1 bs1 tm  in
                             readback cfg1 uu____3820  in
                           (x, uu____3817)  in
                         FStar_Syntax_Syntax.Pat_dot_term uu____3810  in
                       (bs1, uu____3809)
                    in
                 match uu____3513 with
                 | (bs2,p_new) ->
                     (bs2,
                       (let uu___554_3840 = p  in
                        {
                          FStar_Syntax_Syntax.v = p_new;
                          FStar_Syntax_Syntax.p =
                            (uu___554_3840.FStar_Syntax_Syntax.p)
                        }))
                  in
               FStar_List.map
                 (fun uu____3859  ->
                    match uu____3859 with
                    | (pat,when_clause,e1) ->
                        let uu____3881 = process_pattern bs pat  in
                        (match uu____3881 with
                         | (bs',pat') ->
                             let uu____3894 =
                               let uu____3895 =
                                 let uu____3898 = translate cfg1 bs' e1  in
                                 readback cfg1 uu____3898  in
                               (pat', when_clause, uu____3895)  in
                             FStar_Syntax_Util.branch uu____3894)) branches
                in
             let scrut1 = translate cfg bs scrut  in
             (debug1
                (fun uu____3915  ->
                   let uu____3916 =
                     FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos
                      in
                   let uu____3918 = FStar_Syntax_Print.term_to_string e  in
                   FStar_Util.print2 "%s: Translating match %s\n" uu____3916
                     uu____3918);
              (let scrut2 = unlazy scrut1  in
               match scrut2 with
               | FStar_TypeChecker_NBETerm.Construct (c,us,args) ->
                   (debug1
                      (fun uu____3946  ->
                         let uu____3947 =
                           let uu____3949 =
                             FStar_All.pipe_right args
                               (FStar_List.map
                                  (fun uu____3975  ->
                                     match uu____3975 with
                                     | (x,q) ->
                                         let uu____3989 =
                                           FStar_TypeChecker_NBETerm.t_to_string
                                             x
                                            in
                                         Prims.op_Hat
                                           (if FStar_Util.is_some q
                                            then "#"
                                            else "") uu____3989))
                              in
                           FStar_All.pipe_right uu____3949
                             (FStar_String.concat "; ")
                            in
                         FStar_Util.print1 "Match args: %s\n" uu____3947);
                    (let uu____4003 = pickBranch cfg scrut2 branches  in
                     match uu____4003 with
                     | FStar_Pervasives_Native.Some (branch1,args1) ->
                         let uu____4024 =
                           FStar_List.fold_left
                             (fun bs1  -> fun x  -> x :: bs1) bs args1
                            in
                         translate cfg uu____4024 branch1
                     | FStar_Pervasives_Native.None  ->
                         FStar_TypeChecker_NBETerm.mkAccuMatch scrut2
                           make_branches))
               | FStar_TypeChecker_NBETerm.Constant c ->
                   (debug1
                      (fun uu____4047  ->
                         let uu____4048 =
                           FStar_TypeChecker_NBETerm.t_to_string scrut2  in
                         FStar_Util.print1 "Match constant : %s\n" uu____4048);
                    (let uu____4051 = pickBranch cfg scrut2 branches  in
                     match uu____4051 with
                     | FStar_Pervasives_Native.Some (branch1,[]) ->
                         translate cfg bs branch1
                     | FStar_Pervasives_Native.Some (branch1,arg::[]) ->
                         translate cfg (arg :: bs) branch1
                     | FStar_Pervasives_Native.None  ->
                         FStar_TypeChecker_NBETerm.mkAccuMatch scrut2
                           make_branches
                     | FStar_Pervasives_Native.Some (uu____4085,hd1::tl1) ->
                         failwith
                           "Impossible: Matching on constants cannot bind more than one variable"))
               | uu____4099 ->
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
             let uu____4144 =
               FStar_TypeChecker_Cfg.should_reduce_local_let cfg.core_cfg lb
                in
             if uu____4144
             then
               let uu____4147 =
                 (((cfg.core_cfg).FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.for_extraction
                    &&
                    (FStar_Syntax_Util.is_unit lb.FStar_Syntax_Syntax.lbtyp))
                   &&
                   (FStar_Syntax_Util.is_pure_or_ghost_effect
                      lb.FStar_Syntax_Syntax.lbeff)
                  in
               (if uu____4147
                then
                  let bs1 =
                    (FStar_TypeChecker_NBETerm.Constant
                       FStar_TypeChecker_NBETerm.Unit)
                    :: bs  in
                  translate cfg bs1 body
                else
                  (let bs1 =
                     let uu____4158 = translate_letbinding cfg bs lb  in
                     uu____4158 :: bs  in
                   translate cfg bs1 body))
             else
               (let def uu____4166 =
                  let uu____4167 =
                    (((cfg.core_cfg).FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.for_extraction
                       &&
                       (FStar_Syntax_Util.is_unit
                          lb.FStar_Syntax_Syntax.lbtyp))
                      &&
                      (FStar_Syntax_Util.is_pure_or_ghost_effect
                         lb.FStar_Syntax_Syntax.lbeff)
                     in
                  if uu____4167
                  then
                    FStar_TypeChecker_NBETerm.Constant
                      FStar_TypeChecker_NBETerm.Unit
                  else translate cfg bs lb.FStar_Syntax_Syntax.lbdef  in
                let typ uu____4177 =
                  translate cfg bs lb.FStar_Syntax_Syntax.lbtyp  in
                let name =
                  let uu____4179 =
                    FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                  FStar_Syntax_Syntax.freshen_bv uu____4179  in
                let bs1 =
                  (FStar_TypeChecker_NBETerm.Accu
                     ((FStar_TypeChecker_NBETerm.Var name), []))
                  :: bs  in
                let body1 uu____4198 = translate cfg bs1 body  in
                let uu____4199 =
                  let uu____4210 =
                    let uu____4211 =
                      let uu____4228 = FStar_Thunk.mk typ  in
                      let uu____4231 = FStar_Thunk.mk def  in
                      let uu____4234 = FStar_Thunk.mk body1  in
                      (name, uu____4228, uu____4231, uu____4234, lb)  in
                    FStar_TypeChecker_NBETerm.UnreducedLet uu____4211  in
                  (uu____4210, [])  in
                FStar_TypeChecker_NBETerm.Accu uu____4199)
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
                      let uu____4280 =
                        FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                      FStar_Syntax_Syntax.freshen_bv uu____4280) lbs
                  in
               let typs =
                 FStar_List.map
                   (fun lb  -> translate cfg bs lb.FStar_Syntax_Syntax.lbtyp)
                   lbs
                  in
               let rec_bs =
                 let uu____4289 =
                   FStar_List.map
                     (fun v1  ->
                        FStar_TypeChecker_NBETerm.Accu
                          ((FStar_TypeChecker_NBETerm.Var v1), [])) vars
                    in
                 FStar_List.append uu____4289 bs  in
               let defs =
                 FStar_List.map
                   (fun lb  ->
                      translate cfg rec_bs lb.FStar_Syntax_Syntax.lbdef) lbs
                  in
               let body1 = translate cfg rec_bs body  in
               let uu____4310 =
                 let uu____4321 =
                   let uu____4322 =
                     let uu____4339 = FStar_List.zip3 vars typs defs  in
                     (uu____4339, body1, lbs)  in
                   FStar_TypeChecker_NBETerm.UnreducedLetRec uu____4322  in
                 (uu____4321, [])  in
               FStar_TypeChecker_NBETerm.Accu uu____4310
             else
               (let uu____4370 = make_rec_env lbs bs  in
                translate cfg uu____4370 body)
         | FStar_Syntax_Syntax.Tm_meta (e1,uu____4374) -> translate cfg bs e1
         | FStar_Syntax_Syntax.Tm_quoted (qt,qi) ->
             let close1 t =
               let bvs =
                 FStar_List.map
                   (fun uu____4395  ->
                      FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                        FStar_Syntax_Syntax.tun) bs
                  in
               let s1 =
                 FStar_List.mapi
                   (fun i  -> fun bv  -> FStar_Syntax_Syntax.DB (i, bv)) bvs
                  in
               let s2 =
                 let uu____4408 = FStar_List.zip bvs bs  in
                 FStar_List.map
                   (fun uu____4423  ->
                      match uu____4423 with
                      | (bv,t1) ->
                          let uu____4430 =
                            let uu____4437 = readback cfg t1  in
                            (bv, uu____4437)  in
                          FStar_Syntax_Syntax.NT uu____4430) uu____4408
                  in
               let uu____4442 = FStar_Syntax_Subst.subst s1 t  in
               FStar_Syntax_Subst.subst s2 uu____4442  in
             (match qi.FStar_Syntax_Syntax.qkind with
              | FStar_Syntax_Syntax.Quote_dynamic  ->
                  let qt1 = close1 qt  in
                  FStar_TypeChecker_NBETerm.Quote (qt1, qi)
              | FStar_Syntax_Syntax.Quote_static  ->
                  let qi1 = FStar_Syntax_Syntax.on_antiquoted close1 qi  in
                  FStar_TypeChecker_NBETerm.Quote (qt, qi1))
         | FStar_Syntax_Syntax.Tm_lazy li ->
             let f uu____4451 =
               let t = FStar_Syntax_Util.unfold_lazy li  in
               debug1
                 (fun uu____4458  ->
                    let uu____4459 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.print1 ">> Unfolding Tm_lazy to %s\n"
                      uu____4459);
               translate cfg bs t  in
             let uu____4462 =
               let uu____4477 = FStar_Thunk.mk f  in
               ((FStar_Util.Inl li), uu____4477)  in
             FStar_TypeChecker_NBETerm.Lazy uu____4462)

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
            let uu____4509 =
              let uu____4516 = translate cfg bs typ  in
              let uu____4517 = fmap_opt (translate_univ cfg bs) u  in
              (uu____4516, uu____4517)  in
            FStar_TypeChecker_NBETerm.Tot uu____4509
        | FStar_Syntax_Syntax.GTotal (typ,u) ->
            let uu____4532 =
              let uu____4539 = translate cfg bs typ  in
              let uu____4540 = fmap_opt (translate_univ cfg bs) u  in
              (uu____4539, uu____4540)  in
            FStar_TypeChecker_NBETerm.GTot uu____4532
        | FStar_Syntax_Syntax.Comp ctyp ->
            let uu____4546 = translate_comp_typ cfg bs ctyp  in
            FStar_TypeChecker_NBETerm.Comp uu____4546

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
                    let uu____4682 = FStar_List.splitAt m raw_args  in
                    (match uu____4682 with
                     | (uu____4723,raw_args1) -> FStar_Util.Inr raw_args1)
                | FStar_Util.Inl (ctx,xs,rc) ->
                    let uu____4792 = FStar_List.splitAt m xs  in
                    (match uu____4792 with
                     | (uu____4839,xs1) ->
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
                (let uu____4939 = FStar_List.splitAt n1 args  in
                 match uu____4939 with
                 | (args1,args') ->
                     let uu____4986 =
                       let uu____4987 =
                         map_rev FStar_Pervasives_Native.fst args1  in
                       f1 uu____4987  in
                     iapp cfg uu____4986 args')
        | FStar_TypeChecker_NBETerm.Accu (a,ts) ->
            FStar_TypeChecker_NBETerm.Accu
              (a, (FStar_List.rev_append args ts))
        | FStar_TypeChecker_NBETerm.Construct (i,us,ts) ->
            let rec aux args1 us1 ts1 =
              match args1 with
              | (FStar_TypeChecker_NBETerm.Univ u,uu____5106)::args2 ->
                  aux args2 (u :: us1) ts1
              | a::args2 -> aux args2 us1 (a :: ts1)
              | [] -> (us1, ts1)  in
            let uu____5150 = aux args us ts  in
            (match uu____5150 with
             | (us',ts') -> FStar_TypeChecker_NBETerm.Construct (i, us', ts'))
        | FStar_TypeChecker_NBETerm.FV (i,us,ts) ->
            let rec aux args1 us1 ts1 =
              match args1 with
              | (FStar_TypeChecker_NBETerm.Univ u,uu____5277)::args2 ->
                  aux args2 (u :: us1) ts1
              | a::args2 -> aux args2 us1 (a :: ts1)
              | [] -> (us1, ts1)  in
            let uu____5321 = aux args us ts  in
            (match uu____5321 with
             | (us',ts') -> FStar_TypeChecker_NBETerm.FV (i, us', ts'))
        | FStar_TypeChecker_NBETerm.TopLevelLet (lb,arity,args_rev) ->
            let args_rev1 = FStar_List.rev_append args args_rev  in
            let n_args_rev = FStar_List.length args_rev1  in
            let n_univs = FStar_List.length lb.FStar_Syntax_Syntax.lbunivs
               in
            (debug cfg
               (fun uu____5399  ->
                  let uu____5400 =
                    FStar_Syntax_Print.lbname_to_string
                      lb.FStar_Syntax_Syntax.lbname
                     in
                  let uu____5402 = FStar_Util.string_of_int arity  in
                  let uu____5404 = FStar_Util.string_of_int n_args_rev  in
                  FStar_Util.print3
                    "Reached iapp for %s with arity %s and n_args = %s\n"
                    uu____5400 uu____5402 uu____5404);
             if n_args_rev >= arity
             then
               (let uu____5408 =
                  let uu____5421 =
                    let uu____5422 =
                      FStar_Syntax_Util.unascribe
                        lb.FStar_Syntax_Syntax.lbdef
                       in
                    uu____5422.FStar_Syntax_Syntax.n  in
                  match uu____5421 with
                  | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____5439) ->
                      (bs, body)
                  | uu____5472 -> ([], (lb.FStar_Syntax_Syntax.lbdef))  in
                match uu____5408 with
                | (bs,body) ->
                    if (n_univs + (FStar_List.length bs)) = arity
                    then
                      let uu____5513 =
                        FStar_Util.first_N (n_args_rev - arity) args_rev1  in
                      (match uu____5513 with
                       | (extra,args_rev2) ->
                           (debug cfg
                              (fun uu____5565  ->
                                 let uu____5566 =
                                   FStar_Syntax_Print.lbname_to_string
                                     lb.FStar_Syntax_Syntax.lbname
                                    in
                                 let uu____5568 =
                                   FStar_Syntax_Print.term_to_string body  in
                                 let uu____5570 =
                                   let uu____5572 =
                                     FStar_List.map
                                       (fun uu____5584  ->
                                          match uu____5584 with
                                          | (x,uu____5591) ->
                                              FStar_TypeChecker_NBETerm.t_to_string
                                                x) args_rev2
                                      in
                                   FStar_All.pipe_right uu____5572
                                     (FStar_String.concat ", ")
                                    in
                                 FStar_Util.print3
                                   "Reducing body of %s = %s,\n\twith args = %s\n"
                                   uu____5566 uu____5568 uu____5570);
                            (let t =
                               let uu____5599 =
                                 FStar_List.map FStar_Pervasives_Native.fst
                                   args_rev2
                                  in
                               translate cfg uu____5599 body  in
                             match extra with
                             | [] -> t
                             | uu____5610 ->
                                 iapp cfg t (FStar_List.rev extra))))
                    else
                      (let uu____5623 =
                         FStar_Util.first_N (n_args_rev - n_univs) args_rev1
                          in
                       match uu____5623 with
                       | (extra,univs1) ->
                           let uu____5670 =
                             let uu____5671 =
                               FStar_List.map FStar_Pervasives_Native.fst
                                 univs1
                                in
                             translate cfg uu____5671
                               lb.FStar_Syntax_Syntax.lbdef
                              in
                           iapp cfg uu____5670 (FStar_List.rev extra)))
             else
               FStar_TypeChecker_NBETerm.TopLevelLet (lb, arity, args_rev1))
        | FStar_TypeChecker_NBETerm.TopLevelRec
            (lb,arity,decreases_list,args') ->
            let args1 = FStar_List.append args' args  in
            if (FStar_List.length args1) >= arity
            then
              let uu____5731 =
                should_reduce_recursive_definition args1 decreases_list  in
              (match uu____5731 with
               | (should_reduce,uu____5740,uu____5741) ->
                   if Prims.op_Negation should_reduce
                   then
                     let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname
                        in
                     (debug cfg
                        (fun uu____5749  ->
                           let uu____5750 =
                             FStar_Syntax_Print.fv_to_string fv  in
                           FStar_Util.print1
                             "Decided to not unfold recursive definition %s\n"
                             uu____5750);
                      iapp cfg (FStar_TypeChecker_NBETerm.FV (fv, [], []))
                        args1)
                   else
                     (debug cfg
                        (fun uu____5770  ->
                           let uu____5771 =
                             let uu____5773 =
                               FStar_Util.right lb.FStar_Syntax_Syntax.lbname
                                in
                             FStar_Syntax_Print.fv_to_string uu____5773  in
                           FStar_Util.print1
                             "Yes, Decided to unfold recursive definition %s\n"
                             uu____5771);
                      (let uu____5775 =
                         FStar_Util.first_N
                           (FStar_List.length lb.FStar_Syntax_Syntax.lbunivs)
                           args1
                          in
                       match uu____5775 with
                       | (univs1,rest) ->
                           let uu____5822 =
                             let uu____5823 =
                               let uu____5826 =
                                 FStar_List.map FStar_Pervasives_Native.fst
                                   univs1
                                  in
                               FStar_List.rev uu____5826  in
                             translate cfg uu____5823
                               lb.FStar_Syntax_Syntax.lbdef
                              in
                           iapp cfg uu____5822 rest)))
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
                  let uu____5944 =
                    should_reduce_recursive_definition args1 decreases_list
                     in
                  match uu____5944 with
                  | (should_reduce,uu____5953,uu____5954) ->
                      if Prims.op_Negation should_reduce
                      then
                        FStar_TypeChecker_NBETerm.LocalLetRec
                          (i, lb, mutual_lbs, local_env, args1,
                            Prims.int_zero, decreases_list)
                      else
                        (let env = make_rec_env mutual_lbs local_env  in
                         debug cfg
                           (fun uu____5983  ->
                              (let uu____5985 =
                                 let uu____5987 =
                                   FStar_List.map
                                     FStar_TypeChecker_NBETerm.t_to_string
                                     env
                                    in
                                 FStar_String.concat ",\n\t " uu____5987  in
                               FStar_Util.print1
                                 "LocalLetRec Env = {\n\t%s\n}\n" uu____5985);
                              (let uu____5994 =
                                 let uu____5996 =
                                   FStar_List.map
                                     (fun uu____6008  ->
                                        match uu____6008 with
                                        | (t,uu____6015) ->
                                            FStar_TypeChecker_NBETerm.t_to_string
                                              t) args1
                                    in
                                 FStar_String.concat ",\n\t " uu____5996  in
                               FStar_Util.print1
                                 "LocalLetRec Args = {\n\t%s\n}\n" uu____5994));
                         (let uu____6018 =
                            translate cfg env lb.FStar_Syntax_Syntax.lbdef
                             in
                          iapp cfg uu____6018 args1))))
        | uu____6019 ->
            let uu____6020 =
              let uu____6022 = FStar_TypeChecker_NBETerm.t_to_string f  in
              Prims.op_Hat "NBE ill-typed application: " uu____6022  in
            failwith uu____6020

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
          let uu____6039 = FStar_TypeChecker_Cfg.cfg_env cfg.core_cfg  in
          let uu____6040 = FStar_Syntax_Syntax.lid_of_fv fvar1  in
          FStar_TypeChecker_Env.lookup_qname uu____6039 uu____6040  in
        let uu____6041 = (is_constr qninfo) || (is_constr_fv fvar1)  in
        if uu____6041
        then FStar_TypeChecker_NBETerm.mkConstruct fvar1 [] []
        else
          (let uu____6050 =
             FStar_TypeChecker_Normalize.should_unfold cfg.core_cfg
               (fun uu____6052  ->
                  (cfg.core_cfg).FStar_TypeChecker_Cfg.reifying) fvar1 qninfo
              in
           match uu____6050 with
           | FStar_TypeChecker_Normalize.Should_unfold_fully  ->
               failwith "Not yet handled"
           | FStar_TypeChecker_Normalize.Should_unfold_no  ->
               (debug1
                  (fun uu____6059  ->
                     let uu____6060 = FStar_Syntax_Print.fv_to_string fvar1
                        in
                     FStar_Util.print1 "(1) Decided to not unfold %s\n"
                       uu____6060);
                (let uu____6063 =
                   FStar_TypeChecker_Cfg.find_prim_step cfg.core_cfg fvar1
                    in
                 match uu____6063 with
                 | FStar_Pervasives_Native.Some prim_step when
                     prim_step.FStar_TypeChecker_Cfg.strong_reduction_ok ->
                     let arity =
                       prim_step.FStar_TypeChecker_Cfg.arity +
                         prim_step.FStar_TypeChecker_Cfg.univ_arity
                        in
                     (debug1
                        (fun uu____6074  ->
                           let uu____6075 =
                             FStar_Syntax_Print.fv_to_string fvar1  in
                           FStar_Util.print1 "Found a primop %s\n" uu____6075);
                      (let uu____6078 =
                         let uu____6111 =
                           let f uu____6144 =
                             let uu____6146 =
                               FStar_Syntax_Syntax.new_bv
                                 FStar_Pervasives_Native.None
                                 FStar_Syntax_Syntax.t_unit
                                in
                             (uu____6146, FStar_Pervasives_Native.None)  in
                           let uu____6149 =
                             let uu____6160 = FStar_Common.tabulate arity f
                                in
                             ([], uu____6160, FStar_Pervasives_Native.None)
                              in
                           FStar_Util.Inl uu____6149  in
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
                             let uu____6234 =
                               prim_step.FStar_TypeChecker_Cfg.interpretation_nbe
                                 callbacks args'
                                in
                             match uu____6234 with
                             | FStar_Pervasives_Native.Some x ->
                                 (debug1
                                    (fun uu____6245  ->
                                       let uu____6246 =
                                         FStar_Syntax_Print.fv_to_string
                                           fvar1
                                          in
                                       let uu____6248 =
                                         FStar_TypeChecker_NBETerm.t_to_string
                                           x
                                          in
                                       FStar_Util.print2
                                         "Primitive operator %s returned %s\n"
                                         uu____6246 uu____6248);
                                  x)
                             | FStar_Pervasives_Native.None  ->
                                 (debug1
                                    (fun uu____6256  ->
                                       let uu____6257 =
                                         FStar_Syntax_Print.fv_to_string
                                           fvar1
                                          in
                                       FStar_Util.print1
                                         "Primitive operator %s failed\n"
                                         uu____6257);
                                  (let uu____6260 =
                                     FStar_TypeChecker_NBETerm.mkFV fvar1 []
                                       []
                                      in
                                   iapp cfg uu____6260 args'))), uu____6111,
                           arity)
                          in
                       FStar_TypeChecker_NBETerm.Lam uu____6078))
                 | FStar_Pervasives_Native.Some uu____6265 ->
                     (debug1
                        (fun uu____6271  ->
                           let uu____6272 =
                             FStar_Syntax_Print.fv_to_string fvar1  in
                           FStar_Util.print1 "(2) Decided to not unfold %s\n"
                             uu____6272);
                      FStar_TypeChecker_NBETerm.mkFV fvar1 [] [])
                 | uu____6279 ->
                     (debug1
                        (fun uu____6287  ->
                           let uu____6288 =
                             FStar_Syntax_Print.fv_to_string fvar1  in
                           FStar_Util.print1 "(3) Decided to not unfold %s\n"
                             uu____6288);
                      FStar_TypeChecker_NBETerm.mkFV fvar1 [] [])))
           | FStar_TypeChecker_Normalize.Should_unfold_reify  ->
               let t =
                 let is_qninfo_visible =
                   let uu____6298 =
                     FStar_TypeChecker_Env.lookup_definition_qninfo
                       (cfg.core_cfg).FStar_TypeChecker_Cfg.delta_level
                       (fvar1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                       qninfo
                      in
                   FStar_Option.isSome uu____6298  in
                 if is_qninfo_visible
                 then
                   match qninfo with
                   | FStar_Pervasives_Native.Some
                       (FStar_Util.Inr
                        ({
                           FStar_Syntax_Syntax.sigel =
                             FStar_Syntax_Syntax.Sig_let
                             ((is_rec,lbs),names1);
                           FStar_Syntax_Syntax.sigrng = uu____6313;
                           FStar_Syntax_Syntax.sigquals = uu____6314;
                           FStar_Syntax_Syntax.sigmeta = uu____6315;
                           FStar_Syntax_Syntax.sigattrs = uu____6316;
                           FStar_Syntax_Syntax.sigopts = uu____6317;_},_us_opt),_rng)
                       ->
                       (debug1
                          (fun uu____6387  ->
                             let uu____6388 =
                               FStar_Syntax_Print.fv_to_string fvar1  in
                             FStar_Util.print1 "(1) Decided to unfold %s\n"
                               uu____6388);
                        (let lbm = find_let lbs fvar1  in
                         match lbm with
                         | FStar_Pervasives_Native.Some lb ->
                             if
                               is_rec &&
                                 ((cfg.core_cfg).FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta
                             then
                               let uu____6396 = let_rec_arity lb  in
                               (match uu____6396 with
                                | (ar,lst) ->
                                    FStar_TypeChecker_NBETerm.TopLevelRec
                                      (lb, ar, lst, []))
                             else translate_letbinding cfg bs lb
                         | FStar_Pervasives_Native.None  ->
                             failwith "Could not find let binding"))
                   | uu____6432 ->
                       (debug1
                          (fun uu____6438  ->
                             let uu____6439 =
                               FStar_Syntax_Print.fv_to_string fvar1  in
                             FStar_Util.print1
                               "(1) qninfo is None for (%s)\n" uu____6439);
                        FStar_TypeChecker_NBETerm.mkFV fvar1 [] [])
                 else
                   (debug1
                      (fun uu____6453  ->
                         let uu____6454 =
                           FStar_Syntax_Print.fv_to_string fvar1  in
                         FStar_Util.print1
                           "(1) qninfo is not visible at this level (%s)\n"
                           uu____6454);
                    FStar_TypeChecker_NBETerm.mkFV fvar1 [] [])
                  in
               (cache_add cfg fvar1 t; t)
           | FStar_TypeChecker_Normalize.Should_unfold_yes  ->
               let t =
                 let is_qninfo_visible =
                   let uu____6465 =
                     FStar_TypeChecker_Env.lookup_definition_qninfo
                       (cfg.core_cfg).FStar_TypeChecker_Cfg.delta_level
                       (fvar1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                       qninfo
                      in
                   FStar_Option.isSome uu____6465  in
                 if is_qninfo_visible
                 then
                   match qninfo with
                   | FStar_Pervasives_Native.Some
                       (FStar_Util.Inr
                        ({
                           FStar_Syntax_Syntax.sigel =
                             FStar_Syntax_Syntax.Sig_let
                             ((is_rec,lbs),names1);
                           FStar_Syntax_Syntax.sigrng = uu____6480;
                           FStar_Syntax_Syntax.sigquals = uu____6481;
                           FStar_Syntax_Syntax.sigmeta = uu____6482;
                           FStar_Syntax_Syntax.sigattrs = uu____6483;
                           FStar_Syntax_Syntax.sigopts = uu____6484;_},_us_opt),_rng)
                       ->
                       (debug1
                          (fun uu____6554  ->
                             let uu____6555 =
                               FStar_Syntax_Print.fv_to_string fvar1  in
                             FStar_Util.print1 "(1) Decided to unfold %s\n"
                               uu____6555);
                        (let lbm = find_let lbs fvar1  in
                         match lbm with
                         | FStar_Pervasives_Native.Some lb ->
                             if
                               is_rec &&
                                 ((cfg.core_cfg).FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta
                             then
                               let uu____6563 = let_rec_arity lb  in
                               (match uu____6563 with
                                | (ar,lst) ->
                                    FStar_TypeChecker_NBETerm.TopLevelRec
                                      (lb, ar, lst, []))
                             else translate_letbinding cfg bs lb
                         | FStar_Pervasives_Native.None  ->
                             failwith "Could not find let binding"))
                   | uu____6599 ->
                       (debug1
                          (fun uu____6605  ->
                             let uu____6606 =
                               FStar_Syntax_Print.fv_to_string fvar1  in
                             FStar_Util.print1
                               "(1) qninfo is None for (%s)\n" uu____6606);
                        FStar_TypeChecker_NBETerm.mkFV fvar1 [] [])
                 else
                   (debug1
                      (fun uu____6620  ->
                         let uu____6621 =
                           FStar_Syntax_Print.fv_to_string fvar1  in
                         FStar_Util.print1
                           "(1) qninfo is not visible at this level (%s)\n"
                           uu____6621);
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
        let uu____6645 =
          FStar_Syntax_Util.arrow_formals lb.FStar_Syntax_Syntax.lbtyp  in
        match uu____6645 with
        | (formals,uu____6661) ->
            let arity = (FStar_List.length us) + (FStar_List.length formals)
               in
            if arity = Prims.int_zero
            then translate cfg bs lb.FStar_Syntax_Syntax.lbdef
            else
              (let uu____6695 =
                 FStar_Util.is_right lb.FStar_Syntax_Syntax.lbname  in
               if uu____6695
               then
                 (debug1
                    (fun uu____6705  ->
                       let uu____6706 =
                         FStar_Syntax_Print.lbname_to_string
                           lb.FStar_Syntax_Syntax.lbname
                          in
                       let uu____6708 = FStar_Util.string_of_int arity  in
                       FStar_Util.print2
                         "Making TopLevelLet for %s with arity %s\n"
                         uu____6706 uu____6708);
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
          let uu____6733 = let_rec_arity b  in
          match uu____6733 with
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
        let uu____6803 = FStar_BigInt.big_int_of_string s  in
        FStar_TypeChecker_NBETerm.Int uu____6803
    | FStar_Const.Const_string (s,r) ->
        FStar_TypeChecker_NBETerm.String (s, r)
    | FStar_Const.Const_char c1 -> FStar_TypeChecker_NBETerm.Char c1
    | FStar_Const.Const_range r -> FStar_TypeChecker_NBETerm.Range r
    | uu____6812 -> FStar_TypeChecker_NBETerm.SConst c

and (readback_comp :
  config -> FStar_TypeChecker_NBETerm.comp -> FStar_Syntax_Syntax.comp) =
  fun cfg  ->
    fun c  ->
      let c' =
        match c with
        | FStar_TypeChecker_NBETerm.Tot (typ,u) ->
            let uu____6822 =
              let uu____6831 = readback cfg typ  in (uu____6831, u)  in
            FStar_Syntax_Syntax.Total uu____6822
        | FStar_TypeChecker_NBETerm.GTot (typ,u) ->
            let uu____6844 =
              let uu____6853 = readback cfg typ  in (uu____6853, u)  in
            FStar_Syntax_Syntax.GTotal uu____6844
        | FStar_TypeChecker_NBETerm.Comp ctyp ->
            let uu____6861 = readback_comp_typ cfg ctyp  in
            FStar_Syntax_Syntax.Comp uu____6861
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
        let uu____6867 = c  in
        match uu____6867 with
        | { FStar_Syntax_Syntax.comp_univs = comp_univs;
            FStar_Syntax_Syntax.effect_name = effect_name;
            FStar_Syntax_Syntax.result_typ = result_typ;
            FStar_Syntax_Syntax.effect_args = effect_args;
            FStar_Syntax_Syntax.flags = flags;_} ->
            let uu____6887 =
              FStar_List.map (translate_univ cfg bs) comp_univs  in
            let uu____6888 = translate cfg bs result_typ  in
            let uu____6889 =
              FStar_List.map
                (fun x  ->
                   let uu____6917 =
                     translate cfg bs (FStar_Pervasives_Native.fst x)  in
                   (uu____6917, (FStar_Pervasives_Native.snd x))) effect_args
               in
            let uu____6924 = FStar_List.map (translate_flag cfg bs) flags  in
            {
              FStar_TypeChecker_NBETerm.comp_univs = uu____6887;
              FStar_TypeChecker_NBETerm.effect_name = effect_name;
              FStar_TypeChecker_NBETerm.result_typ = uu____6888;
              FStar_TypeChecker_NBETerm.effect_args = uu____6889;
              FStar_TypeChecker_NBETerm.flags = uu____6924
            }

and (readback_comp_typ :
  config ->
    FStar_TypeChecker_NBETerm.comp_typ -> FStar_Syntax_Syntax.comp_typ)
  =
  fun cfg  ->
    fun c  ->
      let uu____6929 = readback cfg c.FStar_TypeChecker_NBETerm.result_typ
         in
      let uu____6932 =
        FStar_List.map
          (fun x  ->
             let uu____6958 = readback cfg (FStar_Pervasives_Native.fst x)
                in
             (uu____6958, (FStar_Pervasives_Native.snd x)))
          c.FStar_TypeChecker_NBETerm.effect_args
         in
      let uu____6959 =
        FStar_List.map (readback_flag cfg) c.FStar_TypeChecker_NBETerm.flags
         in
      {
        FStar_Syntax_Syntax.comp_univs =
          (c.FStar_TypeChecker_NBETerm.comp_univs);
        FStar_Syntax_Syntax.effect_name =
          (c.FStar_TypeChecker_NBETerm.effect_name);
        FStar_Syntax_Syntax.result_typ = uu____6929;
        FStar_Syntax_Syntax.effect_args = uu____6932;
        FStar_Syntax_Syntax.flags = uu____6959
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
        let uu____6967 = c  in
        match uu____6967 with
        | { FStar_Syntax_Syntax.residual_effect = residual_effect;
            FStar_Syntax_Syntax.residual_typ = residual_typ;
            FStar_Syntax_Syntax.residual_flags = residual_flags;_} ->
            let uu____6977 =
              if
                ((cfg.core_cfg).FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.for_extraction
              then FStar_Pervasives_Native.None
              else FStar_Util.map_opt residual_typ (translate cfg bs)  in
            let uu____6987 =
              FStar_List.map (translate_flag cfg bs) residual_flags  in
            {
              FStar_TypeChecker_NBETerm.residual_effect = residual_effect;
              FStar_TypeChecker_NBETerm.residual_typ = uu____6977;
              FStar_TypeChecker_NBETerm.residual_flags = uu____6987
            }

and (readback_residual_comp :
  config ->
    FStar_TypeChecker_NBETerm.residual_comp ->
      FStar_Syntax_Syntax.residual_comp)
  =
  fun cfg  ->
    fun c  ->
      let uu____6992 =
        FStar_Util.map_opt c.FStar_TypeChecker_NBETerm.residual_typ
          (fun x  ->
             debug cfg
               (fun uu____7003  ->
                  let uu____7004 = FStar_TypeChecker_NBETerm.t_to_string x
                     in
                  FStar_Util.print1 "Reading back residualtype %s\n"
                    uu____7004);
             readback cfg x)
         in
      let uu____7007 =
        FStar_List.map (readback_flag cfg)
          c.FStar_TypeChecker_NBETerm.residual_flags
         in
      {
        FStar_Syntax_Syntax.residual_effect =
          (c.FStar_TypeChecker_NBETerm.residual_effect);
        FStar_Syntax_Syntax.residual_typ = uu____6992;
        FStar_Syntax_Syntax.residual_flags = uu____7007
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
            let uu____7018 = translate cfg bs tm  in
            FStar_TypeChecker_NBETerm.DECREASES uu____7018

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
          let uu____7022 = readback cfg t  in
          FStar_Syntax_Syntax.DECREASES uu____7022

and (translate_monadic :
  (FStar_Syntax_Syntax.monad_name * FStar_Syntax_Syntax.term'
    FStar_Syntax_Syntax.syntax) ->
    config ->
      FStar_TypeChecker_NBETerm.t Prims.list ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
          FStar_TypeChecker_NBETerm.t)
  =
  fun uu____7025  ->
    fun cfg  ->
      fun bs  ->
        fun e  ->
          match uu____7025 with
          | (m,ty) ->
              let e1 = FStar_Syntax_Util.unascribe e  in
              (match e1.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                   let uu____7063 =
                     let uu____7072 =
                       FStar_TypeChecker_Env.norm_eff_name
                         (cfg.core_cfg).FStar_TypeChecker_Cfg.tcenv m
                        in
                     FStar_TypeChecker_Env.effect_decl_opt
                       (cfg.core_cfg).FStar_TypeChecker_Cfg.tcenv uu____7072
                      in
                   (match uu____7063 with
                    | FStar_Pervasives_Native.None  ->
                        let uu____7079 =
                          let uu____7081 = FStar_Ident.string_of_lid m  in
                          FStar_Util.format1
                            "Effect declaration not found: %s" uu____7081
                           in
                        failwith uu____7079
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
                          let uu____7103 =
                            let uu____7110 =
                              let uu____7111 =
                                let uu____7130 =
                                  let uu____7139 =
                                    let uu____7146 =
                                      FStar_Util.left
                                        lb.FStar_Syntax_Syntax.lbname
                                       in
                                    (uu____7146,
                                      FStar_Pervasives_Native.None)
                                     in
                                  [uu____7139]  in
                                (uu____7130, body,
                                  (FStar_Pervasives_Native.Some body_rc))
                                 in
                              FStar_Syntax_Syntax.Tm_abs uu____7111  in
                            FStar_Syntax_Syntax.mk uu____7110  in
                          uu____7103 FStar_Pervasives_Native.None
                            body.FStar_Syntax_Syntax.pos
                           in
                        let maybe_range_arg =
                          let uu____7180 =
                            FStar_Util.for_some
                              (FStar_Syntax_Util.attr_eq
                                 FStar_Syntax_Util.dm4f_bind_range_attr)
                              ed.FStar_Syntax_Syntax.eff_attrs
                             in
                          if uu____7180
                          then
                            let uu____7189 =
                              let uu____7194 =
                                let uu____7195 =
                                  FStar_TypeChecker_Cfg.embed_simple
                                    FStar_Syntax_Embeddings.e_range
                                    lb.FStar_Syntax_Syntax.lbpos
                                    lb.FStar_Syntax_Syntax.lbpos
                                   in
                                translate cfg [] uu____7195  in
                              (uu____7194, FStar_Pervasives_Native.None)  in
                            let uu____7196 =
                              let uu____7203 =
                                let uu____7208 =
                                  let uu____7209 =
                                    FStar_TypeChecker_Cfg.embed_simple
                                      FStar_Syntax_Embeddings.e_range
                                      body.FStar_Syntax_Syntax.pos
                                      body.FStar_Syntax_Syntax.pos
                                     in
                                  translate cfg [] uu____7209  in
                                (uu____7208, FStar_Pervasives_Native.None)
                                 in
                              [uu____7203]  in
                            uu____7189 :: uu____7196
                          else []  in
                        let t =
                          let uu____7229 =
                            let uu____7230 =
                              let uu____7231 =
                                let uu____7232 =
                                  let uu____7233 =
                                    let uu____7240 =
                                      FStar_All.pipe_right ed
                                        FStar_Syntax_Util.get_bind_repr
                                       in
                                    FStar_All.pipe_right uu____7240
                                      FStar_Util.must
                                     in
                                  FStar_All.pipe_right uu____7233
                                    FStar_Pervasives_Native.snd
                                   in
                                FStar_Syntax_Util.un_uinst uu____7232  in
                              translate cfg' [] uu____7231  in
                            iapp cfg uu____7230
                              [((FStar_TypeChecker_NBETerm.Univ
                                   FStar_Syntax_Syntax.U_unknown),
                                 FStar_Pervasives_Native.None);
                              ((FStar_TypeChecker_NBETerm.Univ
                                  FStar_Syntax_Syntax.U_unknown),
                                FStar_Pervasives_Native.None)]
                             in
                          let uu____7273 =
                            let uu____7274 =
                              let uu____7281 =
                                let uu____7286 =
                                  translate cfg' bs
                                    lb.FStar_Syntax_Syntax.lbtyp
                                   in
                                (uu____7286, FStar_Pervasives_Native.None)
                                 in
                              let uu____7287 =
                                let uu____7294 =
                                  let uu____7299 = translate cfg' bs ty  in
                                  (uu____7299, FStar_Pervasives_Native.None)
                                   in
                                [uu____7294]  in
                              uu____7281 :: uu____7287  in
                            let uu____7312 =
                              let uu____7319 =
                                let uu____7326 =
                                  let uu____7333 =
                                    let uu____7338 =
                                      translate cfg bs
                                        lb.FStar_Syntax_Syntax.lbdef
                                       in
                                    (uu____7338,
                                      FStar_Pervasives_Native.None)
                                     in
                                  let uu____7339 =
                                    let uu____7346 =
                                      let uu____7353 =
                                        let uu____7358 =
                                          translate cfg bs body_lam  in
                                        (uu____7358,
                                          FStar_Pervasives_Native.None)
                                         in
                                      [uu____7353]  in
                                    (FStar_TypeChecker_NBETerm.Unknown,
                                      FStar_Pervasives_Native.None) ::
                                      uu____7346
                                     in
                                  uu____7333 :: uu____7339  in
                                (FStar_TypeChecker_NBETerm.Unknown,
                                  FStar_Pervasives_Native.None) :: uu____7326
                                 in
                              FStar_List.append maybe_range_arg uu____7319
                               in
                            FStar_List.append uu____7274 uu____7312  in
                          iapp cfg uu____7229 uu____7273  in
                        (debug cfg
                           (fun uu____7390  ->
                              let uu____7391 =
                                FStar_TypeChecker_NBETerm.t_to_string t  in
                              FStar_Util.print1 "translate_monadic: %s\n"
                                uu____7391);
                         t))
               | FStar_Syntax_Syntax.Tm_app
                   ({
                      FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                        (FStar_Const.Const_reflect uu____7394);
                      FStar_Syntax_Syntax.pos = uu____7395;
                      FStar_Syntax_Syntax.vars = uu____7396;_},(e2,uu____7398)::[])
                   ->
                   let uu____7437 = reifying_false cfg  in
                   translate uu____7437 bs e2
               | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                   (debug cfg
                      (fun uu____7468  ->
                         let uu____7469 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____7471 =
                           FStar_Syntax_Print.args_to_string args  in
                         FStar_Util.print2
                           "translate_monadic app (%s) @ (%s)\n" uu____7469
                           uu____7471);
                    (let fallback1 uu____7479 = translate cfg bs e1  in
                     let fallback2 uu____7485 =
                       let uu____7486 = reifying_false cfg  in
                       let uu____7487 =
                         FStar_Syntax_Syntax.mk
                           (FStar_Syntax_Syntax.Tm_meta
                              (e1,
                                (FStar_Syntax_Syntax.Meta_monadic (m, ty))))
                           FStar_Pervasives_Native.None
                           e1.FStar_Syntax_Syntax.pos
                          in
                       translate uu____7486 bs uu____7487  in
                     let uu____7492 =
                       let uu____7493 = FStar_Syntax_Util.un_uinst head1  in
                       uu____7493.FStar_Syntax_Syntax.n  in
                     match uu____7492 with
                     | FStar_Syntax_Syntax.Tm_fvar fv ->
                         let lid = FStar_Syntax_Syntax.lid_of_fv fv  in
                         let qninfo =
                           FStar_TypeChecker_Env.lookup_qname
                             (cfg.core_cfg).FStar_TypeChecker_Cfg.tcenv lid
                            in
                         let uu____7499 =
                           let uu____7501 =
                             FStar_TypeChecker_Env.is_action
                               (cfg.core_cfg).FStar_TypeChecker_Cfg.tcenv lid
                              in
                           Prims.op_Negation uu____7501  in
                         if uu____7499
                         then fallback1 ()
                         else
                           (let uu____7506 =
                              let uu____7508 =
                                FStar_TypeChecker_Env.lookup_definition_qninfo
                                  (cfg.core_cfg).FStar_TypeChecker_Cfg.delta_level
                                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                  qninfo
                                 in
                              FStar_Option.isNone uu____7508  in
                            if uu____7506
                            then fallback2 ()
                            else
                              (let e2 =
                                 let uu____7525 =
                                   let uu____7530 =
                                     FStar_Syntax_Util.mk_reify head1  in
                                   FStar_Syntax_Syntax.mk_Tm_app uu____7530
                                     args
                                    in
                                 uu____7525 FStar_Pervasives_Native.None
                                   e1.FStar_Syntax_Syntax.pos
                                  in
                               let uu____7531 = reifying_false cfg  in
                               translate uu____7531 bs e2))
                     | uu____7532 -> fallback1 ()))
               | FStar_Syntax_Syntax.Tm_match (sc,branches) ->
                   let branches1 =
                     FStar_All.pipe_right branches
                       (FStar_List.map
                          (fun uu____7653  ->
                             match uu____7653 with
                             | (pat,wopt,tm) ->
                                 let uu____7701 =
                                   FStar_Syntax_Util.mk_reify tm  in
                                 (pat, wopt, uu____7701)))
                      in
                   let tm =
                     FStar_Syntax_Syntax.mk
                       (FStar_Syntax_Syntax.Tm_match (sc, branches1))
                       FStar_Pervasives_Native.None
                       e1.FStar_Syntax_Syntax.pos
                      in
                   let uu____7733 = reifying_false cfg  in
                   translate uu____7733 bs tm
               | FStar_Syntax_Syntax.Tm_meta
                   (t,FStar_Syntax_Syntax.Meta_monadic uu____7735) ->
                   translate_monadic (m, ty) cfg bs e1
               | FStar_Syntax_Syntax.Tm_meta
                   (t,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,ty'))
                   -> translate_monadic_lift (msrc, mtgt, ty') cfg bs e1
               | uu____7762 ->
                   let uu____7763 =
                     let uu____7765 = FStar_Syntax_Print.tag_of_term e1  in
                     FStar_Util.format1
                       "Unexpected case in translate_monadic: %s" uu____7765
                      in
                   failwith uu____7763)

and (translate_monadic_lift :
  (FStar_Syntax_Syntax.monad_name * FStar_Syntax_Syntax.monad_name *
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax) ->
    config ->
      FStar_TypeChecker_NBETerm.t Prims.list ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
          FStar_TypeChecker_NBETerm.t)
  =
  fun uu____7768  ->
    fun cfg  ->
      fun bs  ->
        fun e  ->
          match uu____7768 with
          | (msrc,mtgt,ty) ->
              let e1 = FStar_Syntax_Util.unascribe e  in
              let uu____7792 =
                (FStar_Syntax_Util.is_pure_effect msrc) ||
                  (FStar_Syntax_Util.is_div_effect msrc)
                 in
              if uu____7792
              then
                let ed =
                  let uu____7796 =
                    FStar_TypeChecker_Env.norm_eff_name
                      (cfg.core_cfg).FStar_TypeChecker_Cfg.tcenv mtgt
                     in
                  FStar_TypeChecker_Env.get_effect_decl
                    (cfg.core_cfg).FStar_TypeChecker_Cfg.tcenv uu____7796
                   in
                let ret1 =
                  let uu____7798 =
                    let uu____7799 =
                      let uu____7802 =
                        let uu____7803 =
                          let uu____7810 =
                            FStar_All.pipe_right ed
                              FStar_Syntax_Util.get_return_repr
                             in
                          FStar_All.pipe_right uu____7810 FStar_Util.must  in
                        FStar_All.pipe_right uu____7803
                          FStar_Pervasives_Native.snd
                         in
                      FStar_Syntax_Subst.compress uu____7802  in
                    uu____7799.FStar_Syntax_Syntax.n  in
                  match uu____7798 with
                  | FStar_Syntax_Syntax.Tm_uinst (ret1,uu____7856::[]) ->
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_uinst
                           (ret1, [FStar_Syntax_Syntax.U_unknown]))
                        FStar_Pervasives_Native.None
                        e1.FStar_Syntax_Syntax.pos
                  | uu____7863 ->
                      failwith "NYI: Reification of indexed effect (NBE)"
                   in
                let cfg' = reifying_false cfg  in
                let t =
                  let uu____7867 =
                    let uu____7868 = translate cfg' [] ret1  in
                    iapp cfg' uu____7868
                      [((FStar_TypeChecker_NBETerm.Univ
                           FStar_Syntax_Syntax.U_unknown),
                         FStar_Pervasives_Native.None)]
                     in
                  let uu____7877 =
                    let uu____7878 =
                      let uu____7883 = translate cfg' bs ty  in
                      (uu____7883, FStar_Pervasives_Native.None)  in
                    let uu____7884 =
                      let uu____7891 =
                        let uu____7896 = translate cfg' bs e1  in
                        (uu____7896, FStar_Pervasives_Native.None)  in
                      [uu____7891]  in
                    uu____7878 :: uu____7884  in
                  iapp cfg' uu____7867 uu____7877  in
                (debug cfg
                   (fun uu____7912  ->
                      let uu____7913 =
                        FStar_TypeChecker_NBETerm.t_to_string t  in
                      FStar_Util.print1 "translate_monadic_lift(1): %s\n"
                        uu____7913);
                 t)
              else
                (let uu____7918 =
                   FStar_TypeChecker_Env.monad_leq
                     (cfg.core_cfg).FStar_TypeChecker_Cfg.tcenv msrc mtgt
                    in
                 match uu____7918 with
                 | FStar_Pervasives_Native.None  ->
                     let uu____7921 =
                       let uu____7923 = FStar_Ident.text_of_lid msrc  in
                       let uu____7925 = FStar_Ident.text_of_lid mtgt  in
                       FStar_Util.format2
                         "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                         uu____7923 uu____7925
                        in
                     failwith uu____7921
                 | FStar_Pervasives_Native.Some
                     { FStar_TypeChecker_Env.msource = uu____7928;
                       FStar_TypeChecker_Env.mtarget = uu____7929;
                       FStar_TypeChecker_Env.mlift =
                         { FStar_TypeChecker_Env.mlift_wp = uu____7930;
                           FStar_TypeChecker_Env.mlift_term =
                             FStar_Pervasives_Native.None ;_};_}
                     ->
                     let uu____7950 =
                       let uu____7952 = FStar_Ident.text_of_lid msrc  in
                       let uu____7954 = FStar_Ident.text_of_lid mtgt  in
                       FStar_Util.format2
                         "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
                         uu____7952 uu____7954
                        in
                     failwith uu____7950
                 | FStar_Pervasives_Native.Some
                     { FStar_TypeChecker_Env.msource = uu____7957;
                       FStar_TypeChecker_Env.mtarget = uu____7958;
                       FStar_TypeChecker_Env.mlift =
                         { FStar_TypeChecker_Env.mlift_wp = uu____7959;
                           FStar_TypeChecker_Env.mlift_term =
                             FStar_Pervasives_Native.Some lift;_};_}
                     ->
                     let lift_lam =
                       let x =
                         FStar_Syntax_Syntax.new_bv
                           FStar_Pervasives_Native.None
                           FStar_Syntax_Syntax.tun
                          in
                       let uu____7993 =
                         let uu____7996 = FStar_Syntax_Syntax.bv_to_name x
                            in
                         lift FStar_Syntax_Syntax.U_unknown ty uu____7996  in
                       FStar_Syntax_Util.abs
                         [(x, FStar_Pervasives_Native.None)] uu____7993
                         FStar_Pervasives_Native.None
                        in
                     let cfg' = reifying_false cfg  in
                     let t =
                       let uu____8013 = translate cfg' [] lift_lam  in
                       let uu____8014 =
                         let uu____8015 =
                           let uu____8020 = translate cfg bs e1  in
                           (uu____8020, FStar_Pervasives_Native.None)  in
                         [uu____8015]  in
                       iapp cfg uu____8013 uu____8014  in
                     (debug cfg
                        (fun uu____8032  ->
                           let uu____8033 =
                             FStar_TypeChecker_NBETerm.t_to_string t  in
                           FStar_Util.print1
                             "translate_monadic_lift(2): %s\n" uu____8033);
                      t))

and (readback :
  config -> FStar_TypeChecker_NBETerm.t -> FStar_Syntax_Syntax.term) =
  fun cfg  ->
    fun x  ->
      let debug1 = debug cfg  in
      let readback_args cfg1 args =
        map_rev
          (fun uu____8087  ->
             match uu____8087 with
             | (x1,q) ->
                 let uu____8098 = readback cfg1 x1  in (uu____8098, q)) args
         in
      debug1
        (fun uu____8104  ->
           let uu____8105 = FStar_TypeChecker_NBETerm.t_to_string x  in
           FStar_Util.print1 "Readback: %s\n" uu____8105);
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
           let uu____8113 = FStar_BigInt.string_of_big_int i  in
           FStar_All.pipe_right uu____8113 FStar_Syntax_Util.exp_int
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
           let uu____8181 =
             match binders with
             | FStar_Util.Inl (ctx,binders1,rc) ->
                 let uu____8229 =
                   FStar_List.fold_left
                     (fun uu____8283  ->
                        fun uu____8284  ->
                          match (uu____8283, uu____8284) with
                          | ((ctx1,binders_rev,accus_rev),(x1,q)) ->
                              let tnorm =
                                let uu____8409 =
                                  translate cfg ctx1
                                    x1.FStar_Syntax_Syntax.sort
                                   in
                                readback cfg uu____8409  in
                              let x2 =
                                let uu___1227_8411 =
                                  FStar_Syntax_Syntax.freshen_bv x1  in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___1227_8411.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___1227_8411.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = tnorm
                                }  in
                              let ax = FStar_TypeChecker_NBETerm.mkAccuVar x2
                                 in
                              let ctx2 = ax :: ctx1  in
                              (ctx2, ((x2, q) :: binders_rev), (ax ::
                                accus_rev))) (ctx, [], []) binders1
                    in
                 (match uu____8229 with
                  | (ctx1,binders_rev,accus_rev) ->
                      let rc1 =
                        match rc with
                        | FStar_Pervasives_Native.None  ->
                            FStar_Pervasives_Native.None
                        | FStar_Pervasives_Native.Some rc1 ->
                            let uu____8497 =
                              let uu____8498 =
                                translate_residual_comp cfg ctx1 rc1  in
                              readback_residual_comp cfg uu____8498  in
                            FStar_Pervasives_Native.Some uu____8497
                         in
                      ((FStar_List.rev binders_rev), accus_rev, rc1))
             | FStar_Util.Inr args ->
                 let uu____8532 =
                   FStar_List.fold_right
                     (fun uu____8573  ->
                        fun uu____8574  ->
                          match (uu____8573, uu____8574) with
                          | ((t,uu____8626),(binders1,accus)) ->
                              let x1 =
                                let uu____8668 = readback cfg t  in
                                FStar_Syntax_Syntax.new_bv
                                  FStar_Pervasives_Native.None uu____8668
                                 in
                              let uu____8669 =
                                let uu____8672 =
                                  FStar_TypeChecker_NBETerm.mkAccuVar x1  in
                                uu____8672 :: accus  in
                              (((x1, FStar_Pervasives_Native.None) ::
                                binders1), uu____8669)) args ([], [])
                    in
                 (match uu____8532 with
                  | (binders1,accus) ->
                      (binders1, (FStar_List.rev accus),
                        FStar_Pervasives_Native.None))
              in
           (match uu____8181 with
            | (binders1,accus_rev,rc) ->
                let body =
                  let uu____8755 = f accus_rev  in readback cfg uu____8755
                   in
                FStar_Syntax_Util.abs binders1 body rc)
       | FStar_TypeChecker_NBETerm.Refinement (f,targ) ->
           if
             ((cfg.core_cfg).FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.for_extraction
           then
             let uu____8779 =
               let uu____8780 = targ ()  in
               FStar_Pervasives_Native.fst uu____8780  in
             readback cfg uu____8779
           else
             (let x1 =
                let uu____8788 =
                  let uu____8789 =
                    let uu____8790 = targ ()  in
                    FStar_Pervasives_Native.fst uu____8790  in
                  readback cfg uu____8789  in
                FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                  uu____8788
                 in
              let body =
                let uu____8796 =
                  let uu____8797 = FStar_TypeChecker_NBETerm.mkAccuVar x1  in
                  f uu____8797  in
                readback cfg uu____8796  in
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
               (fun uu____8867  ->
                  match uu____8867 with
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
               (fun uu____8919  ->
                  match uu____8919 with
                  | (x1,q) ->
                      let uu____8930 = readback cfg x1  in (uu____8930, q))
               args
              in
           let fv1 =
             FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
               FStar_Pervasives_Native.None FStar_Range.dummyRange
              in
           let app =
             let uu____8937 =
               FStar_Syntax_Syntax.mk_Tm_uinst fv1 (FStar_List.rev us)  in
             FStar_Syntax_Util.mk_app uu____8937 args1  in
           app
       | FStar_TypeChecker_NBETerm.FV (fv,us,args) ->
           let args1 =
             map_rev
               (fun uu____8978  ->
                  match uu____8978 with
                  | (x1,q) ->
                      let uu____8989 = readback cfg x1  in (uu____8989, q))
               args
              in
           let fv1 =
             FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
               FStar_Pervasives_Native.None FStar_Range.dummyRange
              in
           let app =
             let uu____8996 =
               FStar_Syntax_Syntax.mk_Tm_uinst fv1 (FStar_List.rev us)  in
             FStar_Syntax_Util.mk_app uu____8996 args1  in
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
             let uu____9037 = FStar_Syntax_Syntax.bv_to_name bv  in
             FStar_Syntax_Util.mk_app uu____9037 args1  in
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
             let uu____9137 = FStar_Thunk.force typ  in
             readback cfg uu____9137  in
           let defn1 =
             let uu____9139 = FStar_Thunk.force defn  in
             readback cfg uu____9139  in
           let body1 =
             let uu____9141 =
               let uu____9142 = FStar_Thunk.force body  in
               readback cfg uu____9142  in
             FStar_Syntax_Subst.close [(var, FStar_Pervasives_Native.None)]
               uu____9141
              in
           let lbname =
             let uu____9162 =
               let uu___1346_9163 =
                 FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
               {
                 FStar_Syntax_Syntax.ppname =
                   (uu___1346_9163.FStar_Syntax_Syntax.ppname);
                 FStar_Syntax_Syntax.index =
                   (uu___1346_9163.FStar_Syntax_Syntax.index);
                 FStar_Syntax_Syntax.sort = typ1
               }  in
             FStar_Util.Inl uu____9162  in
           let lb1 =
             let uu___1349_9165 = lb  in
             {
               FStar_Syntax_Syntax.lbname = lbname;
               FStar_Syntax_Syntax.lbunivs =
                 (uu___1349_9165.FStar_Syntax_Syntax.lbunivs);
               FStar_Syntax_Syntax.lbtyp = typ1;
               FStar_Syntax_Syntax.lbeff =
                 (uu___1349_9165.FStar_Syntax_Syntax.lbeff);
               FStar_Syntax_Syntax.lbdef = defn1;
               FStar_Syntax_Syntax.lbattrs =
                 (uu___1349_9165.FStar_Syntax_Syntax.lbattrs);
               FStar_Syntax_Syntax.lbpos =
                 (uu___1349_9165.FStar_Syntax_Syntax.lbpos)
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
               (fun uu____9243  ->
                  fun lb  ->
                    match uu____9243 with
                    | (v1,t,d) ->
                        let t1 = readback cfg t  in
                        let def = readback cfg d  in
                        let v2 =
                          let uu___1369_9257 = v1  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___1369_9257.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___1369_9257.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t1
                          }  in
                        let uu___1372_9258 = lb  in
                        {
                          FStar_Syntax_Syntax.lbname = (FStar_Util.Inl v2);
                          FStar_Syntax_Syntax.lbunivs =
                            (uu___1372_9258.FStar_Syntax_Syntax.lbunivs);
                          FStar_Syntax_Syntax.lbtyp = t1;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___1372_9258.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = def;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___1372_9258.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___1372_9258.FStar_Syntax_Syntax.lbpos)
                        }) vars_typs_defns lbs
              in
           let body1 = readback cfg body  in
           let uu____9260 = FStar_Syntax_Subst.close_let_rec lbs1 body1  in
           (match uu____9260 with
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
           let uu____9343 = FStar_Util.first_N (n_args - n_univs) args_rev
              in
           (match uu____9343 with
            | (args_rev1,univs1) ->
                let uu____9390 =
                  let uu____9391 =
                    let uu____9392 =
                      FStar_List.map FStar_Pervasives_Native.fst univs1  in
                    translate cfg uu____9392 lb.FStar_Syntax_Syntax.lbdef  in
                  iapp cfg uu____9391 (FStar_List.rev args_rev1)  in
                readback cfg uu____9390)
       | FStar_TypeChecker_NBETerm.TopLevelRec
           (lb,uu____9404,uu____9405,args) ->
           let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
           let head1 =
             FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
               FStar_Pervasives_Native.None FStar_Range.dummyRange
              in
           let args1 =
             FStar_List.map
               (fun uu____9450  ->
                  match uu____9450 with
                  | (t,q) ->
                      let uu____9461 = readback cfg t  in (uu____9461, q))
               args
              in
           FStar_Syntax_Util.mk_app head1 args1
       | FStar_TypeChecker_NBETerm.LocalLetRec
           (i,uu____9463,lbs,bs,args,_ar,_ar_lst) ->
           let lbnames =
             FStar_List.map
               (fun lb  ->
                  let uu____9505 =
                    let uu____9507 =
                      let uu____9508 =
                        FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                      uu____9508.FStar_Syntax_Syntax.ppname  in
                    FStar_Ident.text_of_id uu____9507  in
                  FStar_Syntax_Syntax.gen_bv uu____9505
                    FStar_Pervasives_Native.None lb.FStar_Syntax_Syntax.lbtyp)
               lbs
              in
           let let_rec_env =
             let uu____9512 =
               FStar_List.map
                 (fun x1  ->
                    FStar_TypeChecker_NBETerm.Accu
                      ((FStar_TypeChecker_NBETerm.Var x1), [])) lbnames
                in
             FStar_List.rev_append uu____9512 bs  in
           let lbs1 =
             FStar_List.map2
               (fun lb  ->
                  fun lbname  ->
                    let lbdef =
                      let uu____9538 =
                        translate cfg let_rec_env
                          lb.FStar_Syntax_Syntax.lbdef
                         in
                      readback cfg uu____9538  in
                    let lbtyp =
                      let uu____9540 =
                        translate cfg bs lb.FStar_Syntax_Syntax.lbtyp  in
                      readback cfg uu____9540  in
                    let uu___1427_9541 = lb  in
                    {
                      FStar_Syntax_Syntax.lbname = (FStar_Util.Inl lbname);
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___1427_9541.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = lbtyp;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___1427_9541.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = lbdef;
                      FStar_Syntax_Syntax.lbattrs =
                        (uu___1427_9541.FStar_Syntax_Syntax.lbattrs);
                      FStar_Syntax_Syntax.lbpos =
                        (uu___1427_9541.FStar_Syntax_Syntax.lbpos)
                    }) lbs lbnames
              in
           let body =
             let uu____9543 = FStar_List.nth lbnames i  in
             FStar_Syntax_Syntax.bv_to_name uu____9543  in
           let uu____9544 = FStar_Syntax_Subst.close_let_rec lbs1 body  in
           (match uu____9544 with
            | (lbs2,body1) ->
                let head1 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_let ((true, lbs2), body1))
                    FStar_Pervasives_Native.None FStar_Range.dummyRange
                   in
                let args1 =
                  FStar_List.map
                    (fun uu____9592  ->
                       match uu____9592 with
                       | (x1,q) ->
                           let uu____9603 = readback cfg x1  in
                           (uu____9603, q)) args
                   in
                FStar_Syntax_Util.mk_app head1 args1)
       | FStar_TypeChecker_NBETerm.Quote (qt,qi) ->
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_quoted (qt, qi))
             FStar_Pervasives_Native.None FStar_Range.dummyRange
       | FStar_TypeChecker_NBETerm.Lazy (FStar_Util.Inl li,uu____9609) ->
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_lazy li)
             FStar_Pervasives_Native.None FStar_Range.dummyRange
       | FStar_TypeChecker_NBETerm.Lazy (uu____9626,thunk1) ->
           let uu____9648 = FStar_Thunk.force thunk1  in
           readback cfg uu____9648)

type step =
  | Primops 
  | UnfoldUntil of FStar_Syntax_Syntax.delta_depth 
  | UnfoldOnly of FStar_Ident.lid Prims.list 
  | UnfoldAttr of FStar_Ident.lid Prims.list 
  | UnfoldTac 
  | Reify 
let (uu___is_Primops : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Primops  -> true | uu____9677 -> false
  
let (uu___is_UnfoldUntil : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldUntil _0 -> true | uu____9689 -> false
  
let (__proj__UnfoldUntil__item___0 : step -> FStar_Syntax_Syntax.delta_depth)
  = fun projectee  -> match projectee with | UnfoldUntil _0 -> _0 
let (uu___is_UnfoldOnly : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldOnly _0 -> true | uu____9710 -> false
  
let (__proj__UnfoldOnly__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldOnly _0 -> _0 
let (uu___is_UnfoldAttr : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldAttr _0 -> true | uu____9737 -> false
  
let (__proj__UnfoldAttr__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldAttr _0 -> _0 
let (uu___is_UnfoldTac : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldTac  -> true | uu____9761 -> false
  
let (uu___is_Reify : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reify  -> true | uu____9772 -> false
  
let (step_as_normalizer_step : step -> FStar_TypeChecker_Env.step) =
  fun uu___2_9779  ->
    match uu___2_9779 with
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
      fun args  -> let uu____9803 = new_config cfg  in iapp uu____9803 t args
  
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
            let uu___1473_9835 = cfg  in
            {
              FStar_TypeChecker_Cfg.steps =
                (let uu___1475_9838 = cfg.FStar_TypeChecker_Cfg.steps  in
                 {
                   FStar_TypeChecker_Cfg.beta =
                     (uu___1475_9838.FStar_TypeChecker_Cfg.beta);
                   FStar_TypeChecker_Cfg.iota =
                     (uu___1475_9838.FStar_TypeChecker_Cfg.iota);
                   FStar_TypeChecker_Cfg.zeta =
                     (uu___1475_9838.FStar_TypeChecker_Cfg.zeta);
                   FStar_TypeChecker_Cfg.weak =
                     (uu___1475_9838.FStar_TypeChecker_Cfg.weak);
                   FStar_TypeChecker_Cfg.hnf =
                     (uu___1475_9838.FStar_TypeChecker_Cfg.hnf);
                   FStar_TypeChecker_Cfg.primops =
                     (uu___1475_9838.FStar_TypeChecker_Cfg.primops);
                   FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                     (uu___1475_9838.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                   FStar_TypeChecker_Cfg.unfold_until =
                     (uu___1475_9838.FStar_TypeChecker_Cfg.unfold_until);
                   FStar_TypeChecker_Cfg.unfold_only =
                     (uu___1475_9838.FStar_TypeChecker_Cfg.unfold_only);
                   FStar_TypeChecker_Cfg.unfold_fully =
                     (uu___1475_9838.FStar_TypeChecker_Cfg.unfold_fully);
                   FStar_TypeChecker_Cfg.unfold_attr =
                     (uu___1475_9838.FStar_TypeChecker_Cfg.unfold_attr);
                   FStar_TypeChecker_Cfg.unfold_tac =
                     (uu___1475_9838.FStar_TypeChecker_Cfg.unfold_tac);
                   FStar_TypeChecker_Cfg.pure_subterms_within_computations =
                     (uu___1475_9838.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                   FStar_TypeChecker_Cfg.simplify =
                     (uu___1475_9838.FStar_TypeChecker_Cfg.simplify);
                   FStar_TypeChecker_Cfg.erase_universes =
                     (uu___1475_9838.FStar_TypeChecker_Cfg.erase_universes);
                   FStar_TypeChecker_Cfg.allow_unbound_universes =
                     (uu___1475_9838.FStar_TypeChecker_Cfg.allow_unbound_universes);
                   FStar_TypeChecker_Cfg.reify_ = true;
                   FStar_TypeChecker_Cfg.compress_uvars =
                     (uu___1475_9838.FStar_TypeChecker_Cfg.compress_uvars);
                   FStar_TypeChecker_Cfg.no_full_norm =
                     (uu___1475_9838.FStar_TypeChecker_Cfg.no_full_norm);
                   FStar_TypeChecker_Cfg.check_no_uvars =
                     (uu___1475_9838.FStar_TypeChecker_Cfg.check_no_uvars);
                   FStar_TypeChecker_Cfg.unmeta =
                     (uu___1475_9838.FStar_TypeChecker_Cfg.unmeta);
                   FStar_TypeChecker_Cfg.unascribe =
                     (uu___1475_9838.FStar_TypeChecker_Cfg.unascribe);
                   FStar_TypeChecker_Cfg.in_full_norm_request =
                     (uu___1475_9838.FStar_TypeChecker_Cfg.in_full_norm_request);
                   FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                     (uu___1475_9838.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                   FStar_TypeChecker_Cfg.nbe_step =
                     (uu___1475_9838.FStar_TypeChecker_Cfg.nbe_step);
                   FStar_TypeChecker_Cfg.for_extraction =
                     (uu___1475_9838.FStar_TypeChecker_Cfg.for_extraction)
                 });
              FStar_TypeChecker_Cfg.tcenv =
                (uu___1473_9835.FStar_TypeChecker_Cfg.tcenv);
              FStar_TypeChecker_Cfg.debug =
                (uu___1473_9835.FStar_TypeChecker_Cfg.debug);
              FStar_TypeChecker_Cfg.delta_level =
                (uu___1473_9835.FStar_TypeChecker_Cfg.delta_level);
              FStar_TypeChecker_Cfg.primitive_steps =
                (uu___1473_9835.FStar_TypeChecker_Cfg.primitive_steps);
              FStar_TypeChecker_Cfg.strong =
                (uu___1473_9835.FStar_TypeChecker_Cfg.strong);
              FStar_TypeChecker_Cfg.memoize_lazy =
                (uu___1473_9835.FStar_TypeChecker_Cfg.memoize_lazy);
              FStar_TypeChecker_Cfg.normalize_pure_lets =
                (uu___1473_9835.FStar_TypeChecker_Cfg.normalize_pure_lets);
              FStar_TypeChecker_Cfg.reifying =
                (uu___1473_9835.FStar_TypeChecker_Cfg.reifying)
            }  in
          (let uu____9841 =
             (FStar_TypeChecker_Env.debug env (FStar_Options.Other "NBETop"))
               ||
               (FStar_TypeChecker_Env.debug env (FStar_Options.Other "NBE"))
              in
           if uu____9841
           then
             let uu____9846 = FStar_Syntax_Print.term_to_string e  in
             FStar_Util.print1 "Calling NBE with (%s) {\n" uu____9846
           else ());
          (let cfg2 = new_config cfg1  in
           let r =
             let uu____9853 = translate cfg2 [] e  in
             readback cfg2 uu____9853  in
           (let uu____9855 =
              (FStar_TypeChecker_Env.debug env (FStar_Options.Other "NBETop"))
                ||
                (FStar_TypeChecker_Env.debug env (FStar_Options.Other "NBE"))
               in
            if uu____9855
            then
              let uu____9860 = FStar_Syntax_Print.term_to_string r  in
              FStar_Util.print1 "}\nNBE returned (%s)\n" uu____9860
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
          let uu___1491_9887 = cfg  in
          {
            FStar_TypeChecker_Cfg.steps =
              (let uu___1493_9890 = cfg.FStar_TypeChecker_Cfg.steps  in
               {
                 FStar_TypeChecker_Cfg.beta =
                   (uu___1493_9890.FStar_TypeChecker_Cfg.beta);
                 FStar_TypeChecker_Cfg.iota =
                   (uu___1493_9890.FStar_TypeChecker_Cfg.iota);
                 FStar_TypeChecker_Cfg.zeta =
                   (uu___1493_9890.FStar_TypeChecker_Cfg.zeta);
                 FStar_TypeChecker_Cfg.weak =
                   (uu___1493_9890.FStar_TypeChecker_Cfg.weak);
                 FStar_TypeChecker_Cfg.hnf =
                   (uu___1493_9890.FStar_TypeChecker_Cfg.hnf);
                 FStar_TypeChecker_Cfg.primops =
                   (uu___1493_9890.FStar_TypeChecker_Cfg.primops);
                 FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                   (uu___1493_9890.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                 FStar_TypeChecker_Cfg.unfold_until =
                   (uu___1493_9890.FStar_TypeChecker_Cfg.unfold_until);
                 FStar_TypeChecker_Cfg.unfold_only =
                   (uu___1493_9890.FStar_TypeChecker_Cfg.unfold_only);
                 FStar_TypeChecker_Cfg.unfold_fully =
                   (uu___1493_9890.FStar_TypeChecker_Cfg.unfold_fully);
                 FStar_TypeChecker_Cfg.unfold_attr =
                   (uu___1493_9890.FStar_TypeChecker_Cfg.unfold_attr);
                 FStar_TypeChecker_Cfg.unfold_tac =
                   (uu___1493_9890.FStar_TypeChecker_Cfg.unfold_tac);
                 FStar_TypeChecker_Cfg.pure_subterms_within_computations =
                   (uu___1493_9890.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                 FStar_TypeChecker_Cfg.simplify =
                   (uu___1493_9890.FStar_TypeChecker_Cfg.simplify);
                 FStar_TypeChecker_Cfg.erase_universes =
                   (uu___1493_9890.FStar_TypeChecker_Cfg.erase_universes);
                 FStar_TypeChecker_Cfg.allow_unbound_universes =
                   (uu___1493_9890.FStar_TypeChecker_Cfg.allow_unbound_universes);
                 FStar_TypeChecker_Cfg.reify_ = true;
                 FStar_TypeChecker_Cfg.compress_uvars =
                   (uu___1493_9890.FStar_TypeChecker_Cfg.compress_uvars);
                 FStar_TypeChecker_Cfg.no_full_norm =
                   (uu___1493_9890.FStar_TypeChecker_Cfg.no_full_norm);
                 FStar_TypeChecker_Cfg.check_no_uvars =
                   (uu___1493_9890.FStar_TypeChecker_Cfg.check_no_uvars);
                 FStar_TypeChecker_Cfg.unmeta =
                   (uu___1493_9890.FStar_TypeChecker_Cfg.unmeta);
                 FStar_TypeChecker_Cfg.unascribe =
                   (uu___1493_9890.FStar_TypeChecker_Cfg.unascribe);
                 FStar_TypeChecker_Cfg.in_full_norm_request =
                   (uu___1493_9890.FStar_TypeChecker_Cfg.in_full_norm_request);
                 FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                   (uu___1493_9890.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                 FStar_TypeChecker_Cfg.nbe_step =
                   (uu___1493_9890.FStar_TypeChecker_Cfg.nbe_step);
                 FStar_TypeChecker_Cfg.for_extraction =
                   (uu___1493_9890.FStar_TypeChecker_Cfg.for_extraction)
               });
            FStar_TypeChecker_Cfg.tcenv =
              (uu___1491_9887.FStar_TypeChecker_Cfg.tcenv);
            FStar_TypeChecker_Cfg.debug =
              (uu___1491_9887.FStar_TypeChecker_Cfg.debug);
            FStar_TypeChecker_Cfg.delta_level =
              (uu___1491_9887.FStar_TypeChecker_Cfg.delta_level);
            FStar_TypeChecker_Cfg.primitive_steps =
              (uu___1491_9887.FStar_TypeChecker_Cfg.primitive_steps);
            FStar_TypeChecker_Cfg.strong =
              (uu___1491_9887.FStar_TypeChecker_Cfg.strong);
            FStar_TypeChecker_Cfg.memoize_lazy =
              (uu___1491_9887.FStar_TypeChecker_Cfg.memoize_lazy);
            FStar_TypeChecker_Cfg.normalize_pure_lets =
              (uu___1491_9887.FStar_TypeChecker_Cfg.normalize_pure_lets);
            FStar_TypeChecker_Cfg.reifying =
              (uu___1491_9887.FStar_TypeChecker_Cfg.reifying)
          }  in
        let cfg2 = new_config cfg1  in
        debug cfg2
          (fun uu____9896  ->
             let uu____9897 = FStar_Syntax_Print.term_to_string e  in
             FStar_Util.print1 "Calling NBE with (%s) {\n" uu____9897);
        (let r =
           let uu____9901 = translate cfg2 [] e  in readback cfg2 uu____9901
            in
         debug cfg2
           (fun uu____9905  ->
              let uu____9906 = FStar_Syntax_Print.term_to_string r  in
              FStar_Util.print1 "}\nNBE returned (%s)\n" uu____9906);
         r)
  