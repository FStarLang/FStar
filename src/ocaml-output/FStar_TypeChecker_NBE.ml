open Prims
let (max : Prims.int -> Prims.int -> Prims.int) =
  fun a -> fun b -> if a > b then a else b
let map_rev : 'a 'b . ('a -> 'b) -> 'a Prims.list -> 'b Prims.list =
  fun f ->
    fun l ->
      let rec aux l1 acc =
        match l1 with
        | [] -> acc
        | x::xs ->
            let uu___ = let uu___1 = f x in uu___1 :: acc in aux xs uu___ in
      aux l []
let map_rev_append :
  'a 'b . ('a -> 'b) -> 'a Prims.list -> 'b Prims.list -> 'b Prims.list =
  fun f ->
    fun l1 ->
      fun l2 ->
        let rec aux l acc =
          match l with
          | [] -> l2
          | x::xs ->
              let uu___ = let uu___1 = f x in uu___1 :: acc in aux xs uu___ in
        aux l1 l2
let rec map_append :
  'a 'b . ('a -> 'b) -> 'a Prims.list -> 'b Prims.list -> 'b Prims.list =
  fun f ->
    fun l1 ->
      fun l2 ->
        match l1 with
        | [] -> l2
        | x::xs ->
            let uu___ = f x in
            let uu___1 = map_append f xs l2 in uu___ :: uu___1
let rec drop : 'a . ('a -> Prims.bool) -> 'a Prims.list -> 'a Prims.list =
  fun p ->
    fun l ->
      match l with
      | [] -> []
      | x::xs -> let uu___ = p x in if uu___ then x :: xs else drop p xs
let fmap_opt :
  'a 'b .
    ('a -> 'b) ->
      'a FStar_Pervasives_Native.option -> 'b FStar_Pervasives_Native.option
  =
  fun f ->
    fun x ->
      FStar_Util.bind_opt x
        (fun x1 -> let uu___ = f x1 in FStar_Pervasives_Native.Some uu___)
let drop_until : 'a . ('a -> Prims.bool) -> 'a Prims.list -> 'a Prims.list =
  fun f ->
    fun l ->
      let rec aux l1 =
        match l1 with
        | [] -> []
        | x::xs -> let uu___ = f x in if uu___ then l1 else aux xs in
      aux l
let (trim : Prims.bool Prims.list -> Prims.bool Prims.list) =
  fun l ->
    let uu___ = drop_until FStar_Pervasives.id (FStar_List.rev l) in
    FStar_List.rev uu___
let (implies : Prims.bool -> Prims.bool -> Prims.bool) =
  fun b1 ->
    fun b2 ->
      match (b1, b2) with | (false, uu___) -> true | (true, b21) -> b21
let (let_rec_arity :
  FStar_Syntax_Syntax.letbinding -> (Prims.int * Prims.bool Prims.list)) =
  fun b ->
    let uu___ = FStar_Syntax_Util.let_rec_arity b in
    match uu___ with
    | (ar, maybe_lst) ->
        (match maybe_lst with
         | FStar_Pervasives_Native.None ->
             let uu___1 = FStar_Common.tabulate ar (fun uu___2 -> true) in
             (ar, uu___1)
         | FStar_Pervasives_Native.Some lst -> (ar, lst))
let (debug_term : FStar_Syntax_Syntax.term -> unit) =
  fun t ->
    let uu___ = FStar_Syntax_Print.term_to_string t in
    FStar_Util.print1 "%s\n" uu___
let (debug_sigmap : FStar_Syntax_Syntax.sigelt FStar_Util.smap -> unit) =
  fun m ->
    FStar_Util.smap_fold m
      (fun k ->
         fun v ->
           fun u ->
             let uu___ = FStar_Syntax_Print.sigelt_to_string_short v in
             FStar_Util.print2 "%s -> %%s\n" k uu___) ()
type config =
  {
  core_cfg: FStar_TypeChecker_Cfg.cfg ;
  fv_cache: FStar_TypeChecker_NBETerm.t FStar_Util.smap }
let (__proj__Mkconfig__item__core_cfg : config -> FStar_TypeChecker_Cfg.cfg)
  =
  fun projectee -> match projectee with | { core_cfg; fv_cache;_} -> core_cfg
let (__proj__Mkconfig__item__fv_cache :
  config -> FStar_TypeChecker_NBETerm.t FStar_Util.smap) =
  fun projectee -> match projectee with | { core_cfg; fv_cache;_} -> fv_cache
let (new_config : FStar_TypeChecker_Cfg.cfg -> config) =
  fun cfg ->
    let uu___ = FStar_Util.smap_create (Prims.of_int (51)) in
    { core_cfg = cfg; fv_cache = uu___ }
let (reifying_false : config -> config) =
  fun cfg ->
    if (cfg.core_cfg).FStar_TypeChecker_Cfg.reifying
    then
      new_config
        (let uu___ = cfg.core_cfg in
         {
           FStar_TypeChecker_Cfg.steps = (uu___.FStar_TypeChecker_Cfg.steps);
           FStar_TypeChecker_Cfg.tcenv = (uu___.FStar_TypeChecker_Cfg.tcenv);
           FStar_TypeChecker_Cfg.debug = (uu___.FStar_TypeChecker_Cfg.debug);
           FStar_TypeChecker_Cfg.delta_level =
             (uu___.FStar_TypeChecker_Cfg.delta_level);
           FStar_TypeChecker_Cfg.primitive_steps =
             (uu___.FStar_TypeChecker_Cfg.primitive_steps);
           FStar_TypeChecker_Cfg.strong =
             (uu___.FStar_TypeChecker_Cfg.strong);
           FStar_TypeChecker_Cfg.memoize_lazy =
             (uu___.FStar_TypeChecker_Cfg.memoize_lazy);
           FStar_TypeChecker_Cfg.normalize_pure_lets =
             (uu___.FStar_TypeChecker_Cfg.normalize_pure_lets);
           FStar_TypeChecker_Cfg.reifying = false
         })
    else cfg
let (reifying_true : config -> config) =
  fun cfg ->
    if Prims.op_Negation (cfg.core_cfg).FStar_TypeChecker_Cfg.reifying
    then
      new_config
        (let uu___ = cfg.core_cfg in
         {
           FStar_TypeChecker_Cfg.steps = (uu___.FStar_TypeChecker_Cfg.steps);
           FStar_TypeChecker_Cfg.tcenv = (uu___.FStar_TypeChecker_Cfg.tcenv);
           FStar_TypeChecker_Cfg.debug = (uu___.FStar_TypeChecker_Cfg.debug);
           FStar_TypeChecker_Cfg.delta_level =
             (uu___.FStar_TypeChecker_Cfg.delta_level);
           FStar_TypeChecker_Cfg.primitive_steps =
             (uu___.FStar_TypeChecker_Cfg.primitive_steps);
           FStar_TypeChecker_Cfg.strong =
             (uu___.FStar_TypeChecker_Cfg.strong);
           FStar_TypeChecker_Cfg.memoize_lazy =
             (uu___.FStar_TypeChecker_Cfg.memoize_lazy);
           FStar_TypeChecker_Cfg.normalize_pure_lets =
             (uu___.FStar_TypeChecker_Cfg.normalize_pure_lets);
           FStar_TypeChecker_Cfg.reifying = true
         })
    else cfg
let (zeta_false : config -> config) =
  fun cfg ->
    let cfg_core = cfg.core_cfg in
    if (cfg_core.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta
    then
      let cfg_core' =
        let uu___ = cfg_core in
        {
          FStar_TypeChecker_Cfg.steps =
            (let uu___1 = cfg_core.FStar_TypeChecker_Cfg.steps in
             {
               FStar_TypeChecker_Cfg.beta =
                 (uu___1.FStar_TypeChecker_Cfg.beta);
               FStar_TypeChecker_Cfg.iota =
                 (uu___1.FStar_TypeChecker_Cfg.iota);
               FStar_TypeChecker_Cfg.zeta = false;
               FStar_TypeChecker_Cfg.zeta_full =
                 (uu___1.FStar_TypeChecker_Cfg.zeta_full);
               FStar_TypeChecker_Cfg.weak =
                 (uu___1.FStar_TypeChecker_Cfg.weak);
               FStar_TypeChecker_Cfg.hnf = (uu___1.FStar_TypeChecker_Cfg.hnf);
               FStar_TypeChecker_Cfg.primops =
                 (uu___1.FStar_TypeChecker_Cfg.primops);
               FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                 (uu___1.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
               FStar_TypeChecker_Cfg.unfold_until =
                 (uu___1.FStar_TypeChecker_Cfg.unfold_until);
               FStar_TypeChecker_Cfg.unfold_only =
                 (uu___1.FStar_TypeChecker_Cfg.unfold_only);
               FStar_TypeChecker_Cfg.unfold_fully =
                 (uu___1.FStar_TypeChecker_Cfg.unfold_fully);
               FStar_TypeChecker_Cfg.unfold_attr =
                 (uu___1.FStar_TypeChecker_Cfg.unfold_attr);
               FStar_TypeChecker_Cfg.unfold_qual =
                 (uu___1.FStar_TypeChecker_Cfg.unfold_qual);
               FStar_TypeChecker_Cfg.unfold_tac =
                 (uu___1.FStar_TypeChecker_Cfg.unfold_tac);
               FStar_TypeChecker_Cfg.pure_subterms_within_computations =
                 (uu___1.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
               FStar_TypeChecker_Cfg.simplify =
                 (uu___1.FStar_TypeChecker_Cfg.simplify);
               FStar_TypeChecker_Cfg.erase_universes =
                 (uu___1.FStar_TypeChecker_Cfg.erase_universes);
               FStar_TypeChecker_Cfg.allow_unbound_universes =
                 (uu___1.FStar_TypeChecker_Cfg.allow_unbound_universes);
               FStar_TypeChecker_Cfg.reify_ =
                 (uu___1.FStar_TypeChecker_Cfg.reify_);
               FStar_TypeChecker_Cfg.compress_uvars =
                 (uu___1.FStar_TypeChecker_Cfg.compress_uvars);
               FStar_TypeChecker_Cfg.no_full_norm =
                 (uu___1.FStar_TypeChecker_Cfg.no_full_norm);
               FStar_TypeChecker_Cfg.check_no_uvars =
                 (uu___1.FStar_TypeChecker_Cfg.check_no_uvars);
               FStar_TypeChecker_Cfg.unmeta =
                 (uu___1.FStar_TypeChecker_Cfg.unmeta);
               FStar_TypeChecker_Cfg.unascribe =
                 (uu___1.FStar_TypeChecker_Cfg.unascribe);
               FStar_TypeChecker_Cfg.in_full_norm_request =
                 (uu___1.FStar_TypeChecker_Cfg.in_full_norm_request);
               FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                 (uu___1.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
               FStar_TypeChecker_Cfg.nbe_step =
                 (uu___1.FStar_TypeChecker_Cfg.nbe_step);
               FStar_TypeChecker_Cfg.for_extraction =
                 (uu___1.FStar_TypeChecker_Cfg.for_extraction)
             });
          FStar_TypeChecker_Cfg.tcenv = (uu___.FStar_TypeChecker_Cfg.tcenv);
          FStar_TypeChecker_Cfg.debug = (uu___.FStar_TypeChecker_Cfg.debug);
          FStar_TypeChecker_Cfg.delta_level =
            (uu___.FStar_TypeChecker_Cfg.delta_level);
          FStar_TypeChecker_Cfg.primitive_steps =
            (uu___.FStar_TypeChecker_Cfg.primitive_steps);
          FStar_TypeChecker_Cfg.strong = (uu___.FStar_TypeChecker_Cfg.strong);
          FStar_TypeChecker_Cfg.memoize_lazy =
            (uu___.FStar_TypeChecker_Cfg.memoize_lazy);
          FStar_TypeChecker_Cfg.normalize_pure_lets =
            (uu___.FStar_TypeChecker_Cfg.normalize_pure_lets);
          FStar_TypeChecker_Cfg.reifying =
            (uu___.FStar_TypeChecker_Cfg.reifying)
        } in
      new_config cfg_core'
    else cfg
let (cache_add :
  config -> FStar_Syntax_Syntax.fv -> FStar_TypeChecker_NBETerm.t -> unit) =
  fun cfg ->
    fun fv ->
      fun v ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
        let uu___ = FStar_Ident.string_of_lid lid in
        FStar_Util.smap_add cfg.fv_cache uu___ v
let (try_in_cache :
  config ->
    FStar_Syntax_Syntax.fv ->
      FStar_TypeChecker_NBETerm.t FStar_Pervasives_Native.option)
  =
  fun cfg ->
    fun fv ->
      let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
      let uu___ = FStar_Ident.string_of_lid lid in
      FStar_Util.smap_try_find cfg.fv_cache uu___
let (debug : config -> (unit -> unit) -> unit) =
  fun cfg -> fun f -> FStar_TypeChecker_Cfg.log_nbe cfg.core_cfg f
let rec (unlazy_unmeta :
  FStar_TypeChecker_NBETerm.t -> FStar_TypeChecker_NBETerm.t) =
  fun t ->
    match t.FStar_TypeChecker_NBETerm.nbe_t with
    | FStar_TypeChecker_NBETerm.Lazy (uu___, t1) ->
        let uu___1 = FStar_Thunk.force t1 in unlazy_unmeta uu___1
    | FStar_TypeChecker_NBETerm.Meta (t0, m) ->
        let uu___ = FStar_Thunk.force m in
        (match uu___ with
         | FStar_Syntax_Syntax.Meta_monadic (uu___1, uu___2) -> t
         | FStar_Syntax_Syntax.Meta_monadic_lift (uu___1, uu___2, uu___3) ->
             t
         | uu___1 -> unlazy_unmeta t0)
    | uu___ -> t
let (pickBranch :
  config ->
    FStar_TypeChecker_NBETerm.t ->
      FStar_Syntax_Syntax.branch Prims.list ->
        (FStar_Syntax_Syntax.term * FStar_TypeChecker_NBETerm.t Prims.list)
          FStar_Pervasives_Native.option)
  =
  fun cfg ->
    fun scrut ->
      fun branches ->
        let all_branches = branches in
        let rec pickBranch_aux scrut1 branches1 branches0 =
          let rec matches_pat scrutinee0 p =
            debug cfg
              (fun uu___1 ->
                 let uu___2 =
                   FStar_TypeChecker_NBETerm.t_to_string scrutinee0 in
                 let uu___3 = FStar_Syntax_Print.pat_to_string p in
                 FStar_Util.print2 "matches_pat (%s, %s)\n" uu___2 uu___3);
            (let scrutinee = unlazy_unmeta scrutinee0 in
             let r =
               match p.FStar_Syntax_Syntax.v with
               | FStar_Syntax_Syntax.Pat_var bv ->
                   FStar_Pervasives.Inl [scrutinee0]
               | FStar_Syntax_Syntax.Pat_wild bv ->
                   FStar_Pervasives.Inl [scrutinee0]
               | FStar_Syntax_Syntax.Pat_dot_term uu___1 ->
                   FStar_Pervasives.Inl []
               | FStar_Syntax_Syntax.Pat_constant s ->
                   let matches_const c s1 =
                     debug cfg
                       (fun uu___2 ->
                          let uu___3 =
                            FStar_TypeChecker_NBETerm.t_to_string c in
                          let uu___4 = FStar_Syntax_Print.const_to_string s1 in
                          FStar_Util.print2
                            "Testing term %s against pattern %s\n" uu___3
                            uu___4);
                     (match c.FStar_TypeChecker_NBETerm.nbe_t with
                      | FStar_TypeChecker_NBETerm.Constant
                          (FStar_TypeChecker_NBETerm.Unit) ->
                          s1 = FStar_Const.Const_unit
                      | FStar_TypeChecker_NBETerm.Constant
                          (FStar_TypeChecker_NBETerm.Bool b) ->
                          (match s1 with
                           | FStar_Const.Const_bool p1 -> b = p1
                           | uu___2 -> false)
                      | FStar_TypeChecker_NBETerm.Constant
                          (FStar_TypeChecker_NBETerm.Int i) ->
                          (match s1 with
                           | FStar_Const.Const_int
                               (p1, FStar_Pervasives_Native.None) ->
                               let uu___2 = FStar_BigInt.big_int_of_string p1 in
                               i = uu___2
                           | uu___2 -> false)
                      | FStar_TypeChecker_NBETerm.Constant
                          (FStar_TypeChecker_NBETerm.String (st, uu___2)) ->
                          (match s1 with
                           | FStar_Const.Const_string (p1, uu___3) -> st = p1
                           | uu___3 -> false)
                      | FStar_TypeChecker_NBETerm.Constant
                          (FStar_TypeChecker_NBETerm.Char c1) ->
                          (match s1 with
                           | FStar_Const.Const_char p1 -> c1 = p1
                           | uu___2 -> false)
                      | uu___2 -> false) in
                   let uu___1 = matches_const scrutinee s in
                   if uu___1
                   then FStar_Pervasives.Inl []
                   else FStar_Pervasives.Inr false
               | FStar_Syntax_Syntax.Pat_cons (fv, arg_pats) ->
                   let rec matches_args out a p1 =
                     match (a, p1) with
                     | ([], []) -> FStar_Pervasives.Inl out
                     | ((t, uu___1)::rest_a, (p2, uu___2)::rest_p) ->
                         let uu___3 = matches_pat t p2 in
                         (match uu___3 with
                          | FStar_Pervasives.Inl s ->
                              matches_args (FStar_List.append out s) rest_a
                                rest_p
                          | m -> m)
                     | uu___1 -> FStar_Pervasives.Inr false in
                   (match scrutinee.FStar_TypeChecker_NBETerm.nbe_t with
                    | FStar_TypeChecker_NBETerm.Construct
                        (fv', _us, args_rev) ->
                        let uu___1 = FStar_Syntax_Syntax.fv_eq fv fv' in
                        if uu___1
                        then
                          matches_args [] (FStar_List.rev args_rev) arg_pats
                        else FStar_Pervasives.Inr false
                    | uu___1 -> FStar_Pervasives.Inr true) in
             let res_to_string uu___1 =
               match uu___1 with
               | FStar_Pervasives.Inr b ->
                   let uu___2 = FStar_Util.string_of_bool b in
                   Prims.op_Hat "Inr " uu___2
               | FStar_Pervasives.Inl bs ->
                   let uu___2 =
                     FStar_Util.string_of_int (FStar_List.length bs) in
                   Prims.op_Hat "Inl " uu___2 in
             debug cfg
               (fun uu___2 ->
                  let uu___3 =
                    FStar_TypeChecker_NBETerm.t_to_string scrutinee in
                  let uu___4 = FStar_Syntax_Print.pat_to_string p in
                  let uu___5 = res_to_string r in
                  FStar_Util.print3 "matches_pat (%s, %s) = %s\n" uu___3
                    uu___4 uu___5);
             r) in
          match branches1 with
          | [] -> FStar_Pervasives_Native.None
          | (p, _wopt, e)::branches2 ->
              let uu___ = matches_pat scrut1 p in
              (match uu___ with
               | FStar_Pervasives.Inl matches ->
                   (debug cfg
                      (fun uu___2 ->
                         let uu___3 = FStar_Syntax_Print.pat_to_string p in
                         FStar_Util.print1 "Pattern %s matches\n" uu___3);
                    FStar_Pervasives_Native.Some (e, matches))
               | FStar_Pervasives.Inr (false) ->
                   pickBranch_aux scrut1 branches2 branches0
               | FStar_Pervasives.Inr (true) -> FStar_Pervasives_Native.None) in
        pickBranch_aux scrut branches branches
let (should_reduce_recursive_definition :
  FStar_TypeChecker_NBETerm.args ->
    Prims.bool Prims.list ->
      (Prims.bool * FStar_TypeChecker_NBETerm.args *
        FStar_TypeChecker_NBETerm.args))
  =
  fun arguments ->
    fun formals_in_decreases ->
      let rec aux ts ar_list acc =
        match (ts, ar_list) with
        | (uu___, []) -> (true, acc, ts)
        | ([], uu___::uu___1) -> (false, acc, [])
        | (t::ts1, in_decreases_clause::bs) ->
            let uu___ =
              in_decreases_clause &&
                (FStar_TypeChecker_NBETerm.isAccu
                   (FStar_Pervasives_Native.fst t)) in
            if uu___
            then (false, (FStar_List.rev_append ts1 acc), [])
            else aux ts1 bs (t :: acc) in
      aux arguments formals_in_decreases []
let (find_sigelt_in_gamma :
  config ->
    FStar_TypeChecker_Env.env ->
      FStar_Ident.lident ->
        FStar_Syntax_Syntax.sigelt FStar_Pervasives_Native.option)
  =
  fun cfg ->
    fun env ->
      fun lid ->
        let mapper uu___ =
          match uu___ with
          | (lr, rng) ->
              (match lr with
               | FStar_Pervasives.Inr (elt, FStar_Pervasives_Native.None) ->
                   FStar_Pervasives_Native.Some elt
               | FStar_Pervasives.Inr (elt, FStar_Pervasives_Native.Some us)
                   ->
                   (debug cfg
                      (fun uu___2 ->
                         let uu___3 = FStar_Syntax_Print.univs_to_string us in
                         FStar_Util.print1
                           "Universes in local declaration: %s\n" uu___3);
                    FStar_Pervasives_Native.Some elt)
               | uu___1 -> FStar_Pervasives_Native.None) in
        let uu___ = FStar_TypeChecker_Env.lookup_qname env lid in
        FStar_Util.bind_opt uu___ mapper
let (is_univ : FStar_TypeChecker_NBETerm.t -> Prims.bool) =
  fun tm ->
    match tm.FStar_TypeChecker_NBETerm.nbe_t with
    | FStar_TypeChecker_NBETerm.Univ uu___ -> true
    | uu___ -> false
let (un_univ : FStar_TypeChecker_NBETerm.t -> FStar_Syntax_Syntax.universe) =
  fun tm ->
    match tm.FStar_TypeChecker_NBETerm.nbe_t with
    | FStar_TypeChecker_NBETerm.Univ u -> u
    | uu___ ->
        let uu___1 =
          let uu___2 = FStar_TypeChecker_NBETerm.t_to_string tm in
          Prims.op_Hat "Not a universe: " uu___2 in
        failwith uu___1
let (is_constr_fv : FStar_Syntax_Syntax.fv -> Prims.bool) =
  fun fvar ->
    fvar.FStar_Syntax_Syntax.fv_qual =
      (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
let (is_constr : FStar_TypeChecker_Env.qninfo -> Prims.bool) =
  fun q ->
    match q with
    | FStar_Pervasives_Native.Some
        (FStar_Pervasives.Inr
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
              (uu___, uu___1, uu___2, uu___3, uu___4, uu___5);
            FStar_Syntax_Syntax.sigrng = uu___6;
            FStar_Syntax_Syntax.sigquals = uu___7;
            FStar_Syntax_Syntax.sigmeta = uu___8;
            FStar_Syntax_Syntax.sigattrs = uu___9;
            FStar_Syntax_Syntax.sigopts = uu___10;_},
          uu___11),
         uu___12)
        -> true
    | uu___ -> false
let (translate_univ :
  config ->
    FStar_TypeChecker_NBETerm.t Prims.list ->
      FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe)
  =
  fun cfg ->
    fun bs ->
      fun u ->
        let rec aux u1 =
          let u2 = FStar_Syntax_Subst.compress_univ u1 in
          match u2 with
          | FStar_Syntax_Syntax.U_bvar i ->
              if i < (FStar_List.length bs)
              then let u' = FStar_List.nth bs i in un_univ u'
              else
                if
                  ((cfg.core_cfg).FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.allow_unbound_universes
                then FStar_Syntax_Syntax.U_zero
                else failwith "Universe index out of bounds"
          | FStar_Syntax_Syntax.U_succ u3 ->
              let uu___ = aux u3 in FStar_Syntax_Syntax.U_succ uu___
          | FStar_Syntax_Syntax.U_max us ->
              let uu___ = FStar_List.map aux us in
              FStar_Syntax_Syntax.U_max uu___
          | FStar_Syntax_Syntax.U_unknown -> u2
          | FStar_Syntax_Syntax.U_name uu___ -> u2
          | FStar_Syntax_Syntax.U_unif uu___ -> u2
          | FStar_Syntax_Syntax.U_zero -> u2 in
        aux u
let (find_let :
  FStar_Syntax_Syntax.letbinding Prims.list ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.letbinding FStar_Pervasives_Native.option)
  =
  fun lbs ->
    fun fvar ->
      FStar_Util.find_map lbs
        (fun lb ->
           match lb.FStar_Syntax_Syntax.lbname with
           | FStar_Pervasives.Inl uu___ -> failwith "find_let : impossible"
           | FStar_Pervasives.Inr name ->
               let uu___ = FStar_Syntax_Syntax.fv_eq name fvar in
               if uu___
               then FStar_Pervasives_Native.Some lb
               else FStar_Pervasives_Native.None)
let (mk_rt :
  FStar_Range.range ->
    FStar_TypeChecker_NBETerm.t' -> FStar_TypeChecker_NBETerm.t)
  =
  fun r ->
    fun t ->
      {
        FStar_TypeChecker_NBETerm.nbe_t = t;
        FStar_TypeChecker_NBETerm.nbe_r = r
      }
let (mk_t : FStar_TypeChecker_NBETerm.t' -> FStar_TypeChecker_NBETerm.t) =
  fun t ->
    {
      FStar_TypeChecker_NBETerm.nbe_t = t;
      FStar_TypeChecker_NBETerm.nbe_r = FStar_Range.dummyRange
    }
let rec (translate :
  config ->
    FStar_TypeChecker_NBETerm.t Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_TypeChecker_NBETerm.t)
  =
  fun cfg ->
    fun bs ->
      fun e ->
        let debug1 = debug cfg in
        let mk_t1 t = mk_rt e.FStar_Syntax_Syntax.pos t in
        debug1
          (fun uu___1 ->
             let uu___2 =
               let uu___3 = FStar_Syntax_Subst.compress e in
               FStar_Syntax_Print.tag_of_term uu___3 in
             let uu___3 =
               let uu___4 = FStar_Syntax_Subst.compress e in
               FStar_Syntax_Print.term_to_string uu___4 in
             FStar_Util.print2 "Term: %s - %s\n" uu___2 uu___3);
        (let uu___1 =
           let uu___2 = FStar_Syntax_Subst.compress e in
           uu___2.FStar_Syntax_Syntax.n in
         match uu___1 with
         | FStar_Syntax_Syntax.Tm_delayed (uu___2, uu___3) ->
             failwith "Tm_delayed: Impossible"
         | FStar_Syntax_Syntax.Tm_unknown ->
             mk_t1 FStar_TypeChecker_NBETerm.Unknown
         | FStar_Syntax_Syntax.Tm_constant c ->
             let uu___2 =
               let uu___3 = translate_constant c in
               FStar_TypeChecker_NBETerm.Constant uu___3 in
             FStar_All.pipe_left mk_t1 uu___2
         | FStar_Syntax_Syntax.Tm_bvar db ->
             if db.FStar_Syntax_Syntax.index < (FStar_List.length bs)
             then
               let t = FStar_List.nth bs db.FStar_Syntax_Syntax.index in
               (debug1
                  (fun uu___3 ->
                     let uu___4 = FStar_TypeChecker_NBETerm.t_to_string t in
                     let uu___5 =
                       let uu___6 =
                         FStar_List.map FStar_TypeChecker_NBETerm.t_to_string
                           bs in
                       FStar_All.pipe_right uu___6 (FStar_String.concat "; ") in
                     FStar_Util.print2
                       "Resolved bvar to %s\n\tcontext is [%s]\n" uu___4
                       uu___5);
                t)
             else failwith "de Bruijn index out of bounds"
         | FStar_Syntax_Syntax.Tm_uinst (t, us) ->
             (debug1
                (fun uu___3 ->
                   let uu___4 = FStar_Syntax_Print.term_to_string t in
                   let uu___5 =
                     let uu___6 =
                       FStar_List.map FStar_Syntax_Print.univ_to_string us in
                     FStar_All.pipe_right uu___6 (FStar_String.concat ", ") in
                   FStar_Util.print2 "Uinst term : %s\nUnivs : %s\n" uu___4
                     uu___5);
              (let uu___3 = translate cfg bs t in
               let uu___4 =
                 FStar_List.map
                   (fun x ->
                      let uu___5 =
                        let uu___6 =
                          let uu___7 = translate_univ cfg bs x in
                          FStar_TypeChecker_NBETerm.Univ uu___7 in
                        FStar_All.pipe_left mk_t1 uu___6 in
                      FStar_TypeChecker_NBETerm.as_arg uu___5) us in
               iapp cfg uu___3 uu___4))
         | FStar_Syntax_Syntax.Tm_type u ->
             let uu___2 =
               let uu___3 = translate_univ cfg bs u in
               FStar_TypeChecker_NBETerm.Type_t uu___3 in
             FStar_All.pipe_left mk_t1 uu___2
         | FStar_Syntax_Syntax.Tm_arrow (xs, c) ->
             let norm uu___2 =
               let uu___3 =
                 FStar_List.fold_left
                   (fun uu___4 ->
                      fun b ->
                        match uu___4 with
                        | (ctx, binders_rev) ->
                            let x = b.FStar_Syntax_Syntax.binder_bv in
                            let t =
                              let uu___5 =
                                translate cfg ctx x.FStar_Syntax_Syntax.sort in
                              readback cfg uu___5 in
                            let x1 =
                              let uu___5 = FStar_Syntax_Syntax.freshen_bv x in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___5.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___5.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t
                              } in
                            let ctx1 =
                              let uu___5 =
                                FStar_TypeChecker_NBETerm.mkAccuVar x1 in
                              uu___5 :: ctx in
                            (ctx1,
                              ((let uu___5 = b in
                                {
                                  FStar_Syntax_Syntax.binder_bv = x1;
                                  FStar_Syntax_Syntax.binder_qual =
                                    (uu___5.FStar_Syntax_Syntax.binder_qual);
                                  FStar_Syntax_Syntax.binder_attrs =
                                    (uu___5.FStar_Syntax_Syntax.binder_attrs)
                                }) :: binders_rev))) (bs, []) xs in
               match uu___3 with
               | (ctx, binders_rev) ->
                   let c1 =
                     let uu___4 = translate_comp cfg ctx c in
                     readback_comp cfg uu___4 in
                   FStar_Syntax_Util.arrow (FStar_List.rev binders_rev) c1 in
             let uu___2 =
               let uu___3 =
                 let uu___4 = FStar_Thunk.mk norm in
                 FStar_Pervasives.Inl uu___4 in
               FStar_TypeChecker_NBETerm.Arrow uu___3 in
             FStar_All.pipe_left mk_t1 uu___2
         | FStar_Syntax_Syntax.Tm_refine (bv, tm) ->
             if
               ((cfg.core_cfg).FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.for_extraction
             then translate cfg bs bv.FStar_Syntax_Syntax.sort
             else
               FStar_All.pipe_left mk_t1
                 (FStar_TypeChecker_NBETerm.Refinement
                    ((fun y -> translate cfg (y :: bs) tm),
                      (fun uu___3 ->
                         let uu___4 =
                           translate cfg bs bv.FStar_Syntax_Syntax.sort in
                         FStar_TypeChecker_NBETerm.as_arg uu___4)))
         | FStar_Syntax_Syntax.Tm_ascribed (t, uu___2, uu___3) ->
             translate cfg bs t
         | FStar_Syntax_Syntax.Tm_uvar (u, (subst, set_use_range)) ->
             let norm_uvar uu___2 =
               let norm_subst_elt uu___3 =
                 match uu___3 with
                 | FStar_Syntax_Syntax.NT (x, t) ->
                     let uu___4 =
                       let uu___5 =
                         let uu___6 = translate cfg bs t in
                         readback cfg uu___6 in
                       (x, uu___5) in
                     FStar_Syntax_Syntax.NT uu___4
                 | FStar_Syntax_Syntax.NM (x, i) ->
                     let x_i =
                       FStar_Syntax_Syntax.bv_to_tm
                         (let uu___4 = x in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___4.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index = i;
                            FStar_Syntax_Syntax.sort =
                              (uu___4.FStar_Syntax_Syntax.sort)
                          }) in
                     let t =
                       let uu___4 = translate cfg bs x_i in
                       readback cfg uu___4 in
                     (match t.FStar_Syntax_Syntax.n with
                      | FStar_Syntax_Syntax.Tm_bvar x_j ->
                          FStar_Syntax_Syntax.NM
                            (x, (x_j.FStar_Syntax_Syntax.index))
                      | uu___4 -> FStar_Syntax_Syntax.NT (x, t))
                 | uu___4 ->
                     failwith "Impossible: subst invariant of uvar nodes" in
               let subst1 =
                 FStar_List.map (FStar_List.map norm_subst_elt) subst in
               let uu___3 = e in
               {
                 FStar_Syntax_Syntax.n =
                   (FStar_Syntax_Syntax.Tm_uvar (u, (subst1, set_use_range)));
                 FStar_Syntax_Syntax.pos = (uu___3.FStar_Syntax_Syntax.pos);
                 FStar_Syntax_Syntax.vars = (uu___3.FStar_Syntax_Syntax.vars)
               } in
             let uu___2 =
               let uu___3 =
                 let uu___4 =
                   let uu___5 = FStar_Thunk.mk norm_uvar in
                   FStar_TypeChecker_NBETerm.UVar uu___5 in
                 (uu___4, []) in
               FStar_TypeChecker_NBETerm.Accu uu___3 in
             FStar_All.pipe_left mk_t1 uu___2
         | FStar_Syntax_Syntax.Tm_name x ->
             FStar_TypeChecker_NBETerm.mkAccuVar x
         | FStar_Syntax_Syntax.Tm_abs ([], uu___2, uu___3) ->
             failwith "Impossible: abstraction with no binders"
         | FStar_Syntax_Syntax.Tm_abs (xs, body, resc) ->
             FStar_All.pipe_left mk_t1
               (FStar_TypeChecker_NBETerm.Lam
                  ((fun ys -> translate cfg (FStar_List.append ys bs) body),
                    (FStar_Pervasives.Inl (bs, xs, resc)),
                    (FStar_List.length xs)))
         | FStar_Syntax_Syntax.Tm_fvar fvar ->
             let uu___2 = try_in_cache cfg fvar in
             (match uu___2 with
              | FStar_Pervasives_Native.Some t -> t
              | uu___3 ->
                  let uu___4 =
                    FStar_Syntax_Syntax.set_range_of_fv fvar
                      e.FStar_Syntax_Syntax.pos in
                  translate_fv cfg bs uu___4)
         | FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                  (FStar_Const.Const_reify);
                FStar_Syntax_Syntax.pos = uu___2;
                FStar_Syntax_Syntax.vars = uu___3;_},
              arg::more::args)
             ->
             let uu___4 = FStar_Syntax_Util.head_and_args e in
             (match uu___4 with
              | (head, uu___5) ->
                  let head1 =
                    FStar_Syntax_Syntax.mk_Tm_app head [arg]
                      e.FStar_Syntax_Syntax.pos in
                  let uu___6 =
                    FStar_Syntax_Syntax.mk_Tm_app head1 (more :: args)
                      e.FStar_Syntax_Syntax.pos in
                  translate cfg bs uu___6)
         | FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                  (FStar_Const.Const_reflect uu___2);
                FStar_Syntax_Syntax.pos = uu___3;
                FStar_Syntax_Syntax.vars = uu___4;_},
              arg::more::args)
             ->
             let uu___5 = FStar_Syntax_Util.head_and_args e in
             (match uu___5 with
              | (head, uu___6) ->
                  let head1 =
                    FStar_Syntax_Syntax.mk_Tm_app head [arg]
                      e.FStar_Syntax_Syntax.pos in
                  let uu___7 =
                    FStar_Syntax_Syntax.mk_Tm_app head1 (more :: args)
                      e.FStar_Syntax_Syntax.pos in
                  translate cfg bs uu___7)
         | FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                  (FStar_Const.Const_reflect uu___2);
                FStar_Syntax_Syntax.pos = uu___3;
                FStar_Syntax_Syntax.vars = uu___4;_},
              arg::[])
             when (cfg.core_cfg).FStar_TypeChecker_Cfg.reifying ->
             let cfg1 = reifying_false cfg in
             translate cfg1 bs (FStar_Pervasives_Native.fst arg)
         | FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                  (FStar_Const.Const_reflect uu___2);
                FStar_Syntax_Syntax.pos = uu___3;
                FStar_Syntax_Syntax.vars = uu___4;_},
              arg::[])
             ->
             let uu___5 =
               let uu___6 =
                 translate cfg bs (FStar_Pervasives_Native.fst arg) in
               FStar_TypeChecker_NBETerm.Reflect uu___6 in
             FStar_All.pipe_left mk_t1 uu___5
         | FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                  (FStar_Const.Const_reify);
                FStar_Syntax_Syntax.pos = uu___2;
                FStar_Syntax_Syntax.vars = uu___3;_},
              arg::[])
             when
             ((cfg.core_cfg).FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.reify_
             ->
             let cfg1 = reifying_true cfg in
             translate cfg1 bs (FStar_Pervasives_Native.fst arg)
         | FStar_Syntax_Syntax.Tm_app (head, args) ->
             (debug1
                (fun uu___3 ->
                   let uu___4 = FStar_Syntax_Print.term_to_string head in
                   let uu___5 = FStar_Syntax_Print.args_to_string args in
                   FStar_Util.print2 "Application: %s @ %s\n" uu___4 uu___5);
              (let uu___3 = translate cfg bs head in
               let uu___4 =
                 FStar_List.map
                   (fun x ->
                      let uu___5 =
                        translate cfg bs (FStar_Pervasives_Native.fst x) in
                      (uu___5, (FStar_Pervasives_Native.snd x))) args in
               iapp cfg uu___3 uu___4))
         | FStar_Syntax_Syntax.Tm_match (scrut, ret_opt, branches) ->
             let make_returns uu___2 =
               match ret_opt with
               | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some
                   (FStar_Pervasives.Inl t, tacopt) ->
                   let uu___3 =
                     let uu___4 =
                       let uu___5 =
                         let uu___6 = translate cfg bs t in
                         readback cfg uu___6 in
                       FStar_Pervasives.Inl uu___5 in
                     (uu___4, tacopt) in
                   FStar_Pervasives_Native.Some uu___3
               | FStar_Pervasives_Native.Some
                   (FStar_Pervasives.Inr c, tacopt) ->
                   let uu___3 =
                     let uu___4 =
                       let uu___5 =
                         let uu___6 = translate_comp cfg bs c in
                         readback_comp cfg uu___6 in
                       FStar_Pervasives.Inr uu___5 in
                     (uu___4, tacopt) in
                   FStar_Pervasives_Native.Some uu___3 in
             let make_branches uu___2 =
               let cfg1 = zeta_false cfg in
               let rec process_pattern bs1 p =
                 let uu___3 =
                   match p.FStar_Syntax_Syntax.v with
                   | FStar_Syntax_Syntax.Pat_constant c ->
                       (bs1, (FStar_Syntax_Syntax.Pat_constant c))
                   | FStar_Syntax_Syntax.Pat_cons (fvar, args) ->
                       let uu___4 =
                         FStar_List.fold_left
                           (fun uu___5 ->
                              fun uu___6 ->
                                match (uu___5, uu___6) with
                                | ((bs2, args1), (arg, b)) ->
                                    let uu___7 = process_pattern bs2 arg in
                                    (match uu___7 with
                                     | (bs', arg') ->
                                         (bs', ((arg', b) :: args1))))
                           (bs1, []) args in
                       (match uu___4 with
                        | (bs', args') ->
                            (bs',
                              (FStar_Syntax_Syntax.Pat_cons
                                 (fvar, (FStar_List.rev args')))))
                   | FStar_Syntax_Syntax.Pat_var bvar ->
                       let x =
                         let uu___4 =
                           let uu___5 =
                             translate cfg1 bs1 bvar.FStar_Syntax_Syntax.sort in
                           readback cfg1 uu___5 in
                         FStar_Syntax_Syntax.new_bv
                           FStar_Pervasives_Native.None uu___4 in
                       let uu___4 =
                         let uu___5 = FStar_TypeChecker_NBETerm.mkAccuVar x in
                         uu___5 :: bs1 in
                       (uu___4, (FStar_Syntax_Syntax.Pat_var x))
                   | FStar_Syntax_Syntax.Pat_wild bvar ->
                       let x =
                         let uu___4 =
                           let uu___5 =
                             translate cfg1 bs1 bvar.FStar_Syntax_Syntax.sort in
                           readback cfg1 uu___5 in
                         FStar_Syntax_Syntax.new_bv
                           FStar_Pervasives_Native.None uu___4 in
                       let uu___4 =
                         let uu___5 = FStar_TypeChecker_NBETerm.mkAccuVar x in
                         uu___5 :: bs1 in
                       (uu___4, (FStar_Syntax_Syntax.Pat_wild x))
                   | FStar_Syntax_Syntax.Pat_dot_term (bvar, tm) ->
                       let x =
                         let uu___4 =
                           let uu___5 =
                             translate cfg1 bs1 bvar.FStar_Syntax_Syntax.sort in
                           readback cfg1 uu___5 in
                         FStar_Syntax_Syntax.new_bv
                           FStar_Pervasives_Native.None uu___4 in
                       let uu___4 =
                         let uu___5 =
                           let uu___6 =
                             let uu___7 = translate cfg1 bs1 tm in
                             readback cfg1 uu___7 in
                           (x, uu___6) in
                         FStar_Syntax_Syntax.Pat_dot_term uu___5 in
                       (bs1, uu___4) in
                 match uu___3 with
                 | (bs2, p_new) ->
                     (bs2,
                       (let uu___4 = p in
                        {
                          FStar_Syntax_Syntax.v = p_new;
                          FStar_Syntax_Syntax.p =
                            (uu___4.FStar_Syntax_Syntax.p)
                        })) in
               FStar_List.map
                 (fun uu___3 ->
                    match uu___3 with
                    | (pat, when_clause, e1) ->
                        let uu___4 = process_pattern bs pat in
                        (match uu___4 with
                         | (bs', pat') ->
                             let uu___5 =
                               let uu___6 =
                                 let uu___7 = translate cfg1 bs' e1 in
                                 readback cfg1 uu___7 in
                               (pat', when_clause, uu___6) in
                             FStar_Syntax_Util.branch uu___5)) branches in
             let scrut1 = translate cfg bs scrut in
             (debug1
                (fun uu___3 ->
                   let uu___4 =
                     FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos in
                   let uu___5 = FStar_Syntax_Print.term_to_string e in
                   FStar_Util.print2 "%s: Translating match %s\n" uu___4
                     uu___5);
              (let scrut2 = unlazy_unmeta scrut1 in
               match scrut2.FStar_TypeChecker_NBETerm.nbe_t with
               | FStar_TypeChecker_NBETerm.Construct (c, us, args) ->
                   (debug1
                      (fun uu___4 ->
                         let uu___5 =
                           let uu___6 =
                             FStar_All.pipe_right args
                               (FStar_List.map
                                  (fun uu___7 ->
                                     match uu___7 with
                                     | (x, q) ->
                                         let uu___8 =
                                           FStar_TypeChecker_NBETerm.t_to_string
                                             x in
                                         Prims.op_Hat
                                           (if FStar_Util.is_some q
                                            then "#"
                                            else "") uu___8)) in
                           FStar_All.pipe_right uu___6
                             (FStar_String.concat "; ") in
                         FStar_Util.print1 "Match args: %s\n" uu___5);
                    (let uu___4 = pickBranch cfg scrut2 branches in
                     match uu___4 with
                     | FStar_Pervasives_Native.Some (branch, args1) ->
                         let uu___5 =
                           FStar_List.fold_left
                             (fun bs1 -> fun x -> x :: bs1) bs args1 in
                         translate cfg uu___5 branch
                     | FStar_Pervasives_Native.None ->
                         FStar_TypeChecker_NBETerm.mkAccuMatch scrut2
                           make_returns make_branches))
               | FStar_TypeChecker_NBETerm.Constant c ->
                   (debug1
                      (fun uu___4 ->
                         let uu___5 =
                           FStar_TypeChecker_NBETerm.t_to_string scrut2 in
                         FStar_Util.print1 "Match constant : %s\n" uu___5);
                    (let uu___4 = pickBranch cfg scrut2 branches in
                     match uu___4 with
                     | FStar_Pervasives_Native.Some (branch, []) ->
                         translate cfg bs branch
                     | FStar_Pervasives_Native.Some (branch, arg::[]) ->
                         translate cfg (arg :: bs) branch
                     | FStar_Pervasives_Native.None ->
                         FStar_TypeChecker_NBETerm.mkAccuMatch scrut2
                           make_returns make_branches
                     | FStar_Pervasives_Native.Some (uu___5, hd::tl) ->
                         failwith
                           "Impossible: Matching on constants cannot bind more than one variable"))
               | uu___3 ->
                   FStar_TypeChecker_NBETerm.mkAccuMatch scrut2 make_returns
                     make_branches))
         | FStar_Syntax_Syntax.Tm_meta
             (e1, FStar_Syntax_Syntax.Meta_monadic (m, t)) when
             (cfg.core_cfg).FStar_TypeChecker_Cfg.reifying ->
             translate_monadic (m, t) cfg bs e1
         | FStar_Syntax_Syntax.Tm_meta
             (e1, FStar_Syntax_Syntax.Meta_monadic_lift (m, m', t)) when
             (cfg.core_cfg).FStar_TypeChecker_Cfg.reifying ->
             translate_monadic_lift (m, m', t) cfg bs e1
         | FStar_Syntax_Syntax.Tm_meta (e1, meta) ->
             let norm_meta uu___2 =
               let norm t =
                 let uu___3 = translate cfg bs t in readback cfg uu___3 in
               match meta with
               | FStar_Syntax_Syntax.Meta_named uu___3 -> meta
               | FStar_Syntax_Syntax.Meta_labeled uu___3 -> meta
               | FStar_Syntax_Syntax.Meta_desugared uu___3 -> meta
               | FStar_Syntax_Syntax.Meta_pattern (ts, args) ->
                   let uu___3 =
                     let uu___4 = FStar_List.map norm ts in
                     let uu___5 =
                       FStar_List.map
                         (FStar_List.map
                            (fun uu___6 ->
                               match uu___6 with
                               | (t, a) -> let uu___7 = norm t in (uu___7, a)))
                         args in
                     (uu___4, uu___5) in
                   FStar_Syntax_Syntax.Meta_pattern uu___3
               | FStar_Syntax_Syntax.Meta_monadic (m, t) ->
                   let uu___3 = let uu___4 = norm t in (m, uu___4) in
                   FStar_Syntax_Syntax.Meta_monadic uu___3
               | FStar_Syntax_Syntax.Meta_monadic_lift (m0, m1, t) ->
                   let uu___3 = let uu___4 = norm t in (m0, m1, uu___4) in
                   FStar_Syntax_Syntax.Meta_monadic_lift uu___3 in
             let uu___2 =
               let uu___3 =
                 let uu___4 = translate cfg bs e1 in
                 let uu___5 = FStar_Thunk.mk norm_meta in (uu___4, uu___5) in
               FStar_TypeChecker_NBETerm.Meta uu___3 in
             FStar_All.pipe_left mk_t1 uu___2
         | FStar_Syntax_Syntax.Tm_let ((false, lb::[]), body) ->
             let uu___2 =
               FStar_TypeChecker_Cfg.should_reduce_local_let cfg.core_cfg lb in
             if uu___2
             then
               let uu___3 =
                 (((cfg.core_cfg).FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.for_extraction
                    &&
                    (FStar_Syntax_Util.is_unit lb.FStar_Syntax_Syntax.lbtyp))
                   &&
                   (FStar_Syntax_Util.is_pure_or_ghost_effect
                      lb.FStar_Syntax_Syntax.lbeff) in
               (if uu___3
                then
                  let bs1 =
                    let uu___4 =
                      let uu___5 =
                        FStar_Syntax_Syntax.range_of_lbname
                          lb.FStar_Syntax_Syntax.lbname in
                      mk_rt uu___5
                        (FStar_TypeChecker_NBETerm.Constant
                           FStar_TypeChecker_NBETerm.Unit) in
                    uu___4 :: bs in
                  translate cfg bs1 body
                else
                  (let bs1 =
                     let uu___5 = translate_letbinding cfg bs lb in uu___5 ::
                       bs in
                   translate cfg bs1 body))
             else
               (let def uu___4 =
                  let uu___5 =
                    (((cfg.core_cfg).FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.for_extraction
                       &&
                       (FStar_Syntax_Util.is_unit
                          lb.FStar_Syntax_Syntax.lbtyp))
                      &&
                      (FStar_Syntax_Util.is_pure_or_ghost_effect
                         lb.FStar_Syntax_Syntax.lbeff) in
                  if uu___5
                  then
                    FStar_All.pipe_left mk_t1
                      (FStar_TypeChecker_NBETerm.Constant
                         FStar_TypeChecker_NBETerm.Unit)
                  else translate cfg bs lb.FStar_Syntax_Syntax.lbdef in
                let typ uu___4 =
                  translate cfg bs lb.FStar_Syntax_Syntax.lbtyp in
                let name =
                  let uu___4 = FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                  FStar_Syntax_Syntax.freshen_bv uu___4 in
                let bs1 =
                  let uu___4 =
                    let uu___5 = FStar_Syntax_Syntax.range_of_bv name in
                    mk_rt uu___5
                      (FStar_TypeChecker_NBETerm.Accu
                         ((FStar_TypeChecker_NBETerm.Var name), [])) in
                  uu___4 :: bs in
                let body1 uu___4 = translate cfg bs1 body in
                let uu___4 =
                  let uu___5 =
                    let uu___6 =
                      let uu___7 =
                        let uu___8 = FStar_Thunk.mk typ in
                        let uu___9 = FStar_Thunk.mk def in
                        let uu___10 = FStar_Thunk.mk body1 in
                        (name, uu___8, uu___9, uu___10, lb) in
                      FStar_TypeChecker_NBETerm.UnreducedLet uu___7 in
                    (uu___6, []) in
                  FStar_TypeChecker_NBETerm.Accu uu___5 in
                FStar_All.pipe_left mk_t1 uu___4)
         | FStar_Syntax_Syntax.Tm_let ((_rec, lbs), body) ->
             if
               (Prims.op_Negation
                  ((cfg.core_cfg).FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta)
                 &&
                 ((cfg.core_cfg).FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.pure_subterms_within_computations
             then
               let vars =
                 FStar_List.map
                   (fun lb ->
                      let uu___2 =
                        FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                      FStar_Syntax_Syntax.freshen_bv uu___2) lbs in
               let typs =
                 FStar_List.map
                   (fun lb -> translate cfg bs lb.FStar_Syntax_Syntax.lbtyp)
                   lbs in
               let rec_bs =
                 let uu___2 =
                   FStar_List.map
                     (fun v ->
                        let uu___3 =
                          let uu___4 = FStar_Syntax_Syntax.range_of_bv v in
                          mk_rt uu___4 in
                        FStar_All.pipe_left uu___3
                          (FStar_TypeChecker_NBETerm.Accu
                             ((FStar_TypeChecker_NBETerm.Var v), []))) vars in
                 FStar_List.append uu___2 bs in
               let defs =
                 FStar_List.map
                   (fun lb ->
                      translate cfg rec_bs lb.FStar_Syntax_Syntax.lbdef) lbs in
               let body1 = translate cfg rec_bs body in
               let uu___2 =
                 let uu___3 =
                   let uu___4 =
                     let uu___5 =
                       let uu___6 = FStar_List.zip3 vars typs defs in
                       (uu___6, body1, lbs) in
                     FStar_TypeChecker_NBETerm.UnreducedLetRec uu___5 in
                   (uu___4, []) in
                 FStar_TypeChecker_NBETerm.Accu uu___3 in
               FStar_All.pipe_left mk_t1 uu___2
             else
               (let uu___3 = make_rec_env lbs bs in translate cfg uu___3 body)
         | FStar_Syntax_Syntax.Tm_quoted (qt, qi) ->
             let close t =
               let bvs =
                 FStar_List.map
                   (fun uu___2 ->
                      FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                        FStar_Syntax_Syntax.tun) bs in
               let s1 =
                 FStar_List.mapi
                   (fun i -> fun bv -> FStar_Syntax_Syntax.DB (i, bv)) bvs in
               let s2 =
                 let uu___2 = FStar_List.zip bvs bs in
                 FStar_List.map
                   (fun uu___3 ->
                      match uu___3 with
                      | (bv, t1) ->
                          let uu___4 =
                            let uu___5 = readback cfg t1 in (bv, uu___5) in
                          FStar_Syntax_Syntax.NT uu___4) uu___2 in
               let uu___2 = FStar_Syntax_Subst.subst s1 t in
               FStar_Syntax_Subst.subst s2 uu___2 in
             (match qi.FStar_Syntax_Syntax.qkind with
              | FStar_Syntax_Syntax.Quote_dynamic ->
                  let qt1 = close qt in
                  FStar_All.pipe_left mk_t1
                    (FStar_TypeChecker_NBETerm.Quote (qt1, qi))
              | FStar_Syntax_Syntax.Quote_static ->
                  let qi1 = FStar_Syntax_Syntax.on_antiquoted close qi in
                  FStar_All.pipe_left mk_t1
                    (FStar_TypeChecker_NBETerm.Quote (qt, qi1)))
         | FStar_Syntax_Syntax.Tm_lazy li ->
             let f uu___2 =
               let t = FStar_Syntax_Util.unfold_lazy li in
               debug1
                 (fun uu___4 ->
                    let uu___5 = FStar_Syntax_Print.term_to_string t in
                    FStar_Util.print1 ">> Unfolding Tm_lazy to %s\n" uu___5);
               translate cfg bs t in
             let uu___2 =
               let uu___3 =
                 let uu___4 = FStar_Thunk.mk f in
                 ((FStar_Pervasives.Inl li), uu___4) in
               FStar_TypeChecker_NBETerm.Lazy uu___3 in
             FStar_All.pipe_left mk_t1 uu___2)
and (translate_comp :
  config ->
    FStar_TypeChecker_NBETerm.t Prims.list ->
      FStar_Syntax_Syntax.comp -> FStar_TypeChecker_NBETerm.comp)
  =
  fun cfg ->
    fun bs ->
      fun c ->
        match c.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total (typ, u) ->
            let uu___ =
              let uu___1 = translate cfg bs typ in
              let uu___2 = fmap_opt (translate_univ cfg bs) u in
              (uu___1, uu___2) in
            FStar_TypeChecker_NBETerm.Tot uu___
        | FStar_Syntax_Syntax.GTotal (typ, u) ->
            let uu___ =
              let uu___1 = translate cfg bs typ in
              let uu___2 = fmap_opt (translate_univ cfg bs) u in
              (uu___1, uu___2) in
            FStar_TypeChecker_NBETerm.GTot uu___
        | FStar_Syntax_Syntax.Comp ctyp ->
            let uu___ = translate_comp_typ cfg bs ctyp in
            FStar_TypeChecker_NBETerm.Comp uu___
and (iapp :
  config ->
    FStar_TypeChecker_NBETerm.t ->
      FStar_TypeChecker_NBETerm.args -> FStar_TypeChecker_NBETerm.t)
  =
  fun cfg ->
    fun f ->
      fun args ->
        let mk t = mk_rt f.FStar_TypeChecker_NBETerm.nbe_r t in
        let uu___ =
          let uu___1 = unlazy_unmeta f in
          uu___1.FStar_TypeChecker_NBETerm.nbe_t in
        match uu___ with
        | FStar_TypeChecker_NBETerm.Lam (f1, binders, n) ->
            let m = FStar_List.length args in
            if m < n
            then
              let arg_values_rev = map_rev FStar_Pervasives_Native.fst args in
              let binders1 =
                match binders with
                | FStar_Pervasives.Inr raw_args ->
                    let uu___1 = FStar_List.splitAt m raw_args in
                    (match uu___1 with
                     | (uu___2, raw_args1) -> FStar_Pervasives.Inr raw_args1)
                | FStar_Pervasives.Inl (ctx, xs, rc) ->
                    let uu___1 = FStar_List.splitAt m xs in
                    (match uu___1 with
                     | (uu___2, xs1) ->
                         let ctx1 = FStar_List.append arg_values_rev ctx in
                         FStar_Pervasives.Inl (ctx1, xs1, rc)) in
              FStar_All.pipe_left mk
                (FStar_TypeChecker_NBETerm.Lam
                   ((fun l -> f1 (FStar_List.append l arg_values_rev)),
                     binders1, (n - m)))
            else
              if m = n
              then
                (let arg_values_rev =
                   map_rev FStar_Pervasives_Native.fst args in
                 f1 arg_values_rev)
              else
                (let uu___3 = FStar_List.splitAt n args in
                 match uu___3 with
                 | (args1, args') ->
                     let uu___4 =
                       let uu___5 = map_rev FStar_Pervasives_Native.fst args1 in
                       f1 uu___5 in
                     iapp cfg uu___4 args')
        | FStar_TypeChecker_NBETerm.Accu (a, ts) ->
            FStar_All.pipe_left mk
              (FStar_TypeChecker_NBETerm.Accu
                 (a, (FStar_List.rev_append args ts)))
        | FStar_TypeChecker_NBETerm.Construct (i, us, ts) ->
            let rec aux args1 us1 ts1 =
              match args1 with
              | ({
                   FStar_TypeChecker_NBETerm.nbe_t =
                     FStar_TypeChecker_NBETerm.Univ u;
                   FStar_TypeChecker_NBETerm.nbe_r = uu___1;_},
                 uu___2)::args2 -> aux args2 (u :: us1) ts1
              | a::args2 -> aux args2 us1 (a :: ts1)
              | [] -> (us1, ts1) in
            let uu___1 = aux args us ts in
            (match uu___1 with
             | (us', ts') ->
                 FStar_All.pipe_left mk
                   (FStar_TypeChecker_NBETerm.Construct (i, us', ts')))
        | FStar_TypeChecker_NBETerm.FV (i, us, ts) ->
            let rec aux args1 us1 ts1 =
              match args1 with
              | ({
                   FStar_TypeChecker_NBETerm.nbe_t =
                     FStar_TypeChecker_NBETerm.Univ u;
                   FStar_TypeChecker_NBETerm.nbe_r = uu___1;_},
                 uu___2)::args2 -> aux args2 (u :: us1) ts1
              | a::args2 -> aux args2 us1 (a :: ts1)
              | [] -> (us1, ts1) in
            let uu___1 = aux args us ts in
            (match uu___1 with
             | (us', ts') ->
                 FStar_All.pipe_left mk
                   (FStar_TypeChecker_NBETerm.FV (i, us', ts')))
        | FStar_TypeChecker_NBETerm.TopLevelLet (lb, arity, args_rev) ->
            let args_rev1 = FStar_List.rev_append args args_rev in
            let n_args_rev = FStar_List.length args_rev1 in
            let n_univs = FStar_List.length lb.FStar_Syntax_Syntax.lbunivs in
            (debug cfg
               (fun uu___2 ->
                  let uu___3 =
                    FStar_Syntax_Print.lbname_to_string
                      lb.FStar_Syntax_Syntax.lbname in
                  let uu___4 = FStar_Util.string_of_int arity in
                  let uu___5 = FStar_Util.string_of_int n_args_rev in
                  FStar_Util.print3
                    "Reached iapp for %s with arity %s and n_args = %s\n"
                    uu___3 uu___4 uu___5);
             if n_args_rev >= arity
             then
               (let uu___2 =
                  let uu___3 =
                    let uu___4 =
                      FStar_Syntax_Util.unascribe
                        lb.FStar_Syntax_Syntax.lbdef in
                    uu___4.FStar_Syntax_Syntax.n in
                  match uu___3 with
                  | FStar_Syntax_Syntax.Tm_abs (bs, body, uu___4) ->
                      (bs, body)
                  | uu___4 -> ([], (lb.FStar_Syntax_Syntax.lbdef)) in
                match uu___2 with
                | (bs, body) ->
                    if (n_univs + (FStar_List.length bs)) = arity
                    then
                      let uu___3 =
                        FStar_Util.first_N (n_args_rev - arity) args_rev1 in
                      (match uu___3 with
                       | (extra, args_rev2) ->
                           (debug cfg
                              (fun uu___5 ->
                                 let uu___6 =
                                   FStar_Syntax_Print.lbname_to_string
                                     lb.FStar_Syntax_Syntax.lbname in
                                 let uu___7 =
                                   FStar_Syntax_Print.term_to_string body in
                                 let uu___8 =
                                   let uu___9 =
                                     FStar_List.map
                                       (fun uu___10 ->
                                          match uu___10 with
                                          | (x, uu___11) ->
                                              FStar_TypeChecker_NBETerm.t_to_string
                                                x) args_rev2 in
                                   FStar_All.pipe_right uu___9
                                     (FStar_String.concat ", ") in
                                 FStar_Util.print3
                                   "Reducing body of %s = %s,\n\twith args = %s\n"
                                   uu___6 uu___7 uu___8);
                            (let t =
                               let uu___5 =
                                 FStar_List.map FStar_Pervasives_Native.fst
                                   args_rev2 in
                               translate cfg uu___5 body in
                             match extra with
                             | [] -> t
                             | uu___5 -> iapp cfg t (FStar_List.rev extra))))
                    else
                      (let uu___4 =
                         FStar_Util.first_N (n_args_rev - n_univs) args_rev1 in
                       match uu___4 with
                       | (extra, univs) ->
                           let uu___5 =
                             let uu___6 =
                               FStar_List.map FStar_Pervasives_Native.fst
                                 univs in
                             translate cfg uu___6
                               lb.FStar_Syntax_Syntax.lbdef in
                           iapp cfg uu___5 (FStar_List.rev extra)))
             else
               FStar_All.pipe_left mk
                 (FStar_TypeChecker_NBETerm.TopLevelLet
                    (lb, arity, args_rev1)))
        | FStar_TypeChecker_NBETerm.TopLevelRec
            (lb, arity, decreases_list, args') ->
            let args1 = FStar_List.append args' args in
            if (FStar_List.length args1) >= arity
            then
              let uu___1 =
                should_reduce_recursive_definition args1 decreases_list in
              (match uu___1 with
               | (should_reduce, uu___2, uu___3) ->
                   if Prims.op_Negation should_reduce
                   then
                     let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                     (debug cfg
                        (fun uu___5 ->
                           let uu___6 = FStar_Syntax_Print.fv_to_string fv in
                           FStar_Util.print1
                             "Decided to not unfold recursive definition %s\n"
                             uu___6);
                      (let uu___5 =
                         let uu___6 = FStar_Syntax_Syntax.range_of_fv fv in
                         mk_rt uu___6
                           (FStar_TypeChecker_NBETerm.FV (fv, [], [])) in
                       iapp cfg uu___5 args1))
                   else
                     (debug cfg
                        (fun uu___6 ->
                           let uu___7 =
                             let uu___8 =
                               FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                             FStar_Syntax_Print.fv_to_string uu___8 in
                           FStar_Util.print1
                             "Yes, Decided to unfold recursive definition %s\n"
                             uu___7);
                      (let uu___6 =
                         FStar_Util.first_N
                           (FStar_List.length lb.FStar_Syntax_Syntax.lbunivs)
                           args1 in
                       match uu___6 with
                       | (univs, rest) ->
                           let uu___7 =
                             let uu___8 =
                               let uu___9 =
                                 FStar_List.map FStar_Pervasives_Native.fst
                                   univs in
                               FStar_List.rev uu___9 in
                             translate cfg uu___8
                               lb.FStar_Syntax_Syntax.lbdef in
                           iapp cfg uu___7 rest)))
            else
              FStar_All.pipe_left mk
                (FStar_TypeChecker_NBETerm.TopLevelRec
                   (lb, arity, decreases_list, args1))
        | FStar_TypeChecker_NBETerm.LocalLetRec
            (i, lb, mutual_lbs, local_env, acc_args, remaining_arity,
             decreases_list)
            ->
            if remaining_arity = Prims.int_zero
            then
              FStar_All.pipe_left mk
                (FStar_TypeChecker_NBETerm.LocalLetRec
                   (i, lb, mutual_lbs, local_env,
                     (FStar_List.append acc_args args), remaining_arity,
                     decreases_list))
            else
              (let n_args = FStar_List.length args in
               if n_args < remaining_arity
               then
                 FStar_All.pipe_left mk
                   (FStar_TypeChecker_NBETerm.LocalLetRec
                      (i, lb, mutual_lbs, local_env,
                        (FStar_List.append acc_args args),
                        (remaining_arity - n_args), decreases_list))
               else
                 (let args1 = FStar_List.append acc_args args in
                  let uu___3 =
                    should_reduce_recursive_definition args1 decreases_list in
                  match uu___3 with
                  | (should_reduce, uu___4, uu___5) ->
                      if Prims.op_Negation should_reduce
                      then
                        FStar_All.pipe_left mk
                          (FStar_TypeChecker_NBETerm.LocalLetRec
                             (i, lb, mutual_lbs, local_env, args1,
                               Prims.int_zero, decreases_list))
                      else
                        (let env = make_rec_env mutual_lbs local_env in
                         debug cfg
                           (fun uu___8 ->
                              (let uu___10 =
                                 let uu___11 =
                                   FStar_List.map
                                     FStar_TypeChecker_NBETerm.t_to_string
                                     env in
                                 FStar_String.concat ",\n\t " uu___11 in
                               FStar_Util.print1
                                 "LocalLetRec Env = {\n\t%s\n}\n" uu___10);
                              (let uu___10 =
                                 let uu___11 =
                                   FStar_List.map
                                     (fun uu___12 ->
                                        match uu___12 with
                                        | (t, uu___13) ->
                                            FStar_TypeChecker_NBETerm.t_to_string
                                              t) args1 in
                                 FStar_String.concat ",\n\t " uu___11 in
                               FStar_Util.print1
                                 "LocalLetRec Args = {\n\t%s\n}\n" uu___10));
                         (let uu___8 =
                            translate cfg env lb.FStar_Syntax_Syntax.lbdef in
                          iapp cfg uu___8 args1))))
        | FStar_TypeChecker_NBETerm.Constant
            (FStar_TypeChecker_NBETerm.SConst (FStar_Const.Const_range_of))
            ->
            (match args with
             | (a, uu___1)::[] ->
                 mk_rt a.FStar_TypeChecker_NBETerm.nbe_r
                   (FStar_TypeChecker_NBETerm.Constant
                      (FStar_TypeChecker_NBETerm.Range
                         (a.FStar_TypeChecker_NBETerm.nbe_r)))
             | uu___1 ->
                 let uu___2 =
                   let uu___3 = FStar_TypeChecker_NBETerm.t_to_string f in
                   Prims.op_Hat "NBE ill-typed application: " uu___3 in
                 failwith uu___2)
        | FStar_TypeChecker_NBETerm.Constant
            (FStar_TypeChecker_NBETerm.SConst
            (FStar_Const.Const_set_range_of)) ->
            (match args with
             | (t, uu___1)::({
                               FStar_TypeChecker_NBETerm.nbe_t =
                                 FStar_TypeChecker_NBETerm.Constant
                                 (FStar_TypeChecker_NBETerm.Range r);
                               FStar_TypeChecker_NBETerm.nbe_r = uu___2;_},
                             uu___3)::[]
                 ->
                 let uu___4 = t in
                 {
                   FStar_TypeChecker_NBETerm.nbe_t =
                     (uu___4.FStar_TypeChecker_NBETerm.nbe_t);
                   FStar_TypeChecker_NBETerm.nbe_r = r
                 }
             | uu___1 ->
                 let uu___2 =
                   let uu___3 = FStar_TypeChecker_NBETerm.t_to_string f in
                   Prims.op_Hat "NBE ill-typed application: " uu___3 in
                 failwith uu___2)
        | uu___1 ->
            let uu___2 =
              let uu___3 = FStar_TypeChecker_NBETerm.t_to_string f in
              Prims.op_Hat "NBE ill-typed application: " uu___3 in
            failwith uu___2
and (translate_fv :
  config ->
    FStar_TypeChecker_NBETerm.t Prims.list ->
      FStar_Syntax_Syntax.fv -> FStar_TypeChecker_NBETerm.t)
  =
  fun cfg ->
    fun bs ->
      fun fvar ->
        let debug1 = debug cfg in
        let qninfo =
          let uu___ = FStar_TypeChecker_Cfg.cfg_env cfg.core_cfg in
          let uu___1 = FStar_Syntax_Syntax.lid_of_fv fvar in
          FStar_TypeChecker_Env.lookup_qname uu___ uu___1 in
        let uu___ = (is_constr qninfo) || (is_constr_fv fvar) in
        if uu___
        then FStar_TypeChecker_NBETerm.mkConstruct fvar [] []
        else
          (let uu___2 =
             FStar_TypeChecker_Normalize.should_unfold cfg.core_cfg
               (fun uu___3 -> (cfg.core_cfg).FStar_TypeChecker_Cfg.reifying)
               fvar qninfo in
           match uu___2 with
           | FStar_TypeChecker_Normalize.Should_unfold_fully ->
               failwith "Not yet handled"
           | FStar_TypeChecker_Normalize.Should_unfold_no ->
               (debug1
                  (fun uu___4 ->
                     let uu___5 = FStar_Syntax_Print.fv_to_string fvar in
                     FStar_Util.print1 "(1) Decided to not unfold %s\n"
                       uu___5);
                (let uu___4 =
                   FStar_TypeChecker_Cfg.find_prim_step cfg.core_cfg fvar in
                 match uu___4 with
                 | FStar_Pervasives_Native.Some prim_step when
                     prim_step.FStar_TypeChecker_Cfg.strong_reduction_ok ->
                     let arity =
                       prim_step.FStar_TypeChecker_Cfg.arity +
                         prim_step.FStar_TypeChecker_Cfg.univ_arity in
                     (debug1
                        (fun uu___6 ->
                           let uu___7 = FStar_Syntax_Print.fv_to_string fvar in
                           FStar_Util.print1 "Found a primop %s\n" uu___7);
                      (let uu___6 =
                         let uu___7 =
                           let uu___8 =
                             let f uu___9 =
                               let uu___10 =
                                 FStar_Syntax_Syntax.new_bv
                                   FStar_Pervasives_Native.None
                                   FStar_Syntax_Syntax.t_unit in
                               FStar_Syntax_Syntax.mk_binder uu___10 in
                             let uu___9 =
                               let uu___10 = FStar_Common.tabulate arity f in
                               ([], uu___10, FStar_Pervasives_Native.None) in
                             FStar_Pervasives.Inl uu___9 in
                           ((fun args_rev ->
                               let args' =
                                 map_rev FStar_TypeChecker_NBETerm.as_arg
                                   args_rev in
                               let callbacks =
                                 {
                                   FStar_TypeChecker_NBETerm.iapp =
                                     (iapp cfg);
                                   FStar_TypeChecker_NBETerm.translate =
                                     (translate cfg bs)
                                 } in
                               let uu___9 =
                                 prim_step.FStar_TypeChecker_Cfg.interpretation_nbe
                                   callbacks args' in
                               match uu___9 with
                               | FStar_Pervasives_Native.Some x ->
                                   (debug1
                                      (fun uu___11 ->
                                         let uu___12 =
                                           FStar_Syntax_Print.fv_to_string
                                             fvar in
                                         let uu___13 =
                                           FStar_TypeChecker_NBETerm.t_to_string
                                             x in
                                         FStar_Util.print2
                                           "Primitive operator %s returned %s\n"
                                           uu___12 uu___13);
                                    x)
                               | FStar_Pervasives_Native.None ->
                                   (debug1
                                      (fun uu___11 ->
                                         let uu___12 =
                                           FStar_Syntax_Print.fv_to_string
                                             fvar in
                                         FStar_Util.print1
                                           "Primitive operator %s failed\n"
                                           uu___12);
                                    (let uu___11 =
                                       FStar_TypeChecker_NBETerm.mkFV fvar []
                                         [] in
                                     iapp cfg uu___11 args'))), uu___8,
                             arity) in
                         FStar_TypeChecker_NBETerm.Lam uu___7 in
                       FStar_All.pipe_left mk_t uu___6))
                 | FStar_Pervasives_Native.Some uu___5 ->
                     (debug1
                        (fun uu___7 ->
                           let uu___8 = FStar_Syntax_Print.fv_to_string fvar in
                           FStar_Util.print1 "(2) Decided to not unfold %s\n"
                             uu___8);
                      FStar_TypeChecker_NBETerm.mkFV fvar [] [])
                 | uu___5 ->
                     (debug1
                        (fun uu___7 ->
                           let uu___8 = FStar_Syntax_Print.fv_to_string fvar in
                           FStar_Util.print1 "(3) Decided to not unfold %s\n"
                             uu___8);
                      FStar_TypeChecker_NBETerm.mkFV fvar [] [])))
           | FStar_TypeChecker_Normalize.Should_unfold_reify ->
               let t =
                 let is_qninfo_visible =
                   let uu___3 =
                     FStar_TypeChecker_Env.lookup_definition_qninfo
                       (cfg.core_cfg).FStar_TypeChecker_Cfg.delta_level
                       (fvar.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                       qninfo in
                   FStar_Option.isSome uu___3 in
                 if is_qninfo_visible
                 then
                   match qninfo with
                   | FStar_Pervasives_Native.Some
                       (FStar_Pervasives.Inr
                        ({
                           FStar_Syntax_Syntax.sigel =
                             FStar_Syntax_Syntax.Sig_let
                             ((is_rec, lbs), names);
                           FStar_Syntax_Syntax.sigrng = uu___3;
                           FStar_Syntax_Syntax.sigquals = uu___4;
                           FStar_Syntax_Syntax.sigmeta = uu___5;
                           FStar_Syntax_Syntax.sigattrs = uu___6;
                           FStar_Syntax_Syntax.sigopts = uu___7;_},
                         _us_opt),
                        _rng)
                       ->
                       (debug1
                          (fun uu___9 ->
                             let uu___10 =
                               FStar_Syntax_Print.fv_to_string fvar in
                             FStar_Util.print1 "(1) Decided to unfold %s\n"
                               uu___10);
                        (let lbm = find_let lbs fvar in
                         match lbm with
                         | FStar_Pervasives_Native.Some lb ->
                             if
                               is_rec &&
                                 ((cfg.core_cfg).FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta
                             then
                               let uu___9 = let_rec_arity lb in
                               (match uu___9 with
                                | (ar, lst) ->
                                    let uu___10 =
                                      let uu___11 =
                                        FStar_Syntax_Syntax.range_of_fv fvar in
                                      mk_rt uu___11 in
                                    FStar_All.pipe_left uu___10
                                      (FStar_TypeChecker_NBETerm.TopLevelRec
                                         (lb, ar, lst, [])))
                             else translate_letbinding cfg bs lb
                         | FStar_Pervasives_Native.None ->
                             failwith "Could not find let binding"))
                   | uu___3 ->
                       (debug1
                          (fun uu___5 ->
                             let uu___6 =
                               FStar_Syntax_Print.fv_to_string fvar in
                             FStar_Util.print1
                               "(1) qninfo is None for (%s)\n" uu___6);
                        FStar_TypeChecker_NBETerm.mkFV fvar [] [])
                 else
                   (debug1
                      (fun uu___5 ->
                         let uu___6 = FStar_Syntax_Print.fv_to_string fvar in
                         FStar_Util.print1
                           "(1) qninfo is not visible at this level (%s)\n"
                           uu___6);
                    FStar_TypeChecker_NBETerm.mkFV fvar [] []) in
               (cache_add cfg fvar t; t)
           | FStar_TypeChecker_Normalize.Should_unfold_yes ->
               let t =
                 let is_qninfo_visible =
                   let uu___3 =
                     FStar_TypeChecker_Env.lookup_definition_qninfo
                       (cfg.core_cfg).FStar_TypeChecker_Cfg.delta_level
                       (fvar.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                       qninfo in
                   FStar_Option.isSome uu___3 in
                 if is_qninfo_visible
                 then
                   match qninfo with
                   | FStar_Pervasives_Native.Some
                       (FStar_Pervasives.Inr
                        ({
                           FStar_Syntax_Syntax.sigel =
                             FStar_Syntax_Syntax.Sig_let
                             ((is_rec, lbs), names);
                           FStar_Syntax_Syntax.sigrng = uu___3;
                           FStar_Syntax_Syntax.sigquals = uu___4;
                           FStar_Syntax_Syntax.sigmeta = uu___5;
                           FStar_Syntax_Syntax.sigattrs = uu___6;
                           FStar_Syntax_Syntax.sigopts = uu___7;_},
                         _us_opt),
                        _rng)
                       ->
                       (debug1
                          (fun uu___9 ->
                             let uu___10 =
                               FStar_Syntax_Print.fv_to_string fvar in
                             FStar_Util.print1 "(1) Decided to unfold %s\n"
                               uu___10);
                        (let lbm = find_let lbs fvar in
                         match lbm with
                         | FStar_Pervasives_Native.Some lb ->
                             if
                               is_rec &&
                                 ((cfg.core_cfg).FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta
                             then
                               let uu___9 = let_rec_arity lb in
                               (match uu___9 with
                                | (ar, lst) ->
                                    let uu___10 =
                                      let uu___11 =
                                        FStar_Syntax_Syntax.range_of_fv fvar in
                                      mk_rt uu___11 in
                                    FStar_All.pipe_left uu___10
                                      (FStar_TypeChecker_NBETerm.TopLevelRec
                                         (lb, ar, lst, [])))
                             else translate_letbinding cfg bs lb
                         | FStar_Pervasives_Native.None ->
                             failwith "Could not find let binding"))
                   | uu___3 ->
                       (debug1
                          (fun uu___5 ->
                             let uu___6 =
                               FStar_Syntax_Print.fv_to_string fvar in
                             FStar_Util.print1
                               "(1) qninfo is None for (%s)\n" uu___6);
                        FStar_TypeChecker_NBETerm.mkFV fvar [] [])
                 else
                   (debug1
                      (fun uu___5 ->
                         let uu___6 = FStar_Syntax_Print.fv_to_string fvar in
                         FStar_Util.print1
                           "(1) qninfo is not visible at this level (%s)\n"
                           uu___6);
                    FStar_TypeChecker_NBETerm.mkFV fvar [] []) in
               (cache_add cfg fvar t; t))
and (translate_letbinding :
  config ->
    FStar_TypeChecker_NBETerm.t Prims.list ->
      FStar_Syntax_Syntax.letbinding -> FStar_TypeChecker_NBETerm.t)
  =
  fun cfg ->
    fun bs ->
      fun lb ->
        let debug1 = debug cfg in
        let us = lb.FStar_Syntax_Syntax.lbunivs in
        let uu___ =
          FStar_Syntax_Util.arrow_formals lb.FStar_Syntax_Syntax.lbtyp in
        match uu___ with
        | (formals, uu___1) ->
            let arity = (FStar_List.length us) + (FStar_List.length formals) in
            if arity = Prims.int_zero
            then translate cfg bs lb.FStar_Syntax_Syntax.lbdef
            else
              (let uu___3 = FStar_Util.is_right lb.FStar_Syntax_Syntax.lbname in
               if uu___3
               then
                 (debug1
                    (fun uu___5 ->
                       let uu___6 =
                         FStar_Syntax_Print.lbname_to_string
                           lb.FStar_Syntax_Syntax.lbname in
                       let uu___7 = FStar_Util.string_of_int arity in
                       FStar_Util.print2
                         "Making TopLevelLet for %s with arity %s\n" uu___6
                         uu___7);
                  (let uu___5 =
                     let uu___6 =
                       FStar_Syntax_Syntax.range_of_lbname
                         lb.FStar_Syntax_Syntax.lbname in
                     mk_rt uu___6 in
                   FStar_All.pipe_left uu___5
                     (FStar_TypeChecker_NBETerm.TopLevelLet (lb, arity, []))))
               else translate cfg bs lb.FStar_Syntax_Syntax.lbdef)
and (mkRec :
  Prims.int ->
    FStar_Syntax_Syntax.letbinding ->
      FStar_Syntax_Syntax.letbinding Prims.list ->
        FStar_TypeChecker_NBETerm.t Prims.list -> FStar_TypeChecker_NBETerm.t)
  =
  fun i ->
    fun b ->
      fun bs ->
        fun env ->
          let uu___ = let_rec_arity b in
          match uu___ with
          | (ar, ar_lst) ->
              FStar_All.pipe_left mk_t
                (FStar_TypeChecker_NBETerm.LocalLetRec
                   (i, b, bs, env, [], ar, ar_lst))
and (make_rec_env :
  FStar_Syntax_Syntax.letbinding Prims.list ->
    FStar_TypeChecker_NBETerm.t Prims.list ->
      FStar_TypeChecker_NBETerm.t Prims.list)
  =
  fun all_lbs ->
    fun all_outer_bs ->
      let rec_bindings =
        FStar_List.mapi (fun i -> fun lb -> mkRec i lb all_lbs all_outer_bs)
          all_lbs in
      FStar_List.rev_append rec_bindings all_outer_bs
and (translate_constant :
  FStar_Syntax_Syntax.sconst -> FStar_TypeChecker_NBETerm.constant) =
  fun c ->
    match c with
    | FStar_Const.Const_unit -> FStar_TypeChecker_NBETerm.Unit
    | FStar_Const.Const_bool b -> FStar_TypeChecker_NBETerm.Bool b
    | FStar_Const.Const_int (s, FStar_Pervasives_Native.None) ->
        let uu___ = FStar_BigInt.big_int_of_string s in
        FStar_TypeChecker_NBETerm.Int uu___
    | FStar_Const.Const_string (s, r) ->
        FStar_TypeChecker_NBETerm.String (s, r)
    | FStar_Const.Const_char c1 -> FStar_TypeChecker_NBETerm.Char c1
    | FStar_Const.Const_range r -> FStar_TypeChecker_NBETerm.Range r
    | uu___ -> FStar_TypeChecker_NBETerm.SConst c
and (readback_comp :
  config -> FStar_TypeChecker_NBETerm.comp -> FStar_Syntax_Syntax.comp) =
  fun cfg ->
    fun c ->
      let c' =
        match c with
        | FStar_TypeChecker_NBETerm.Tot (typ, u) ->
            let uu___ = let uu___1 = readback cfg typ in (uu___1, u) in
            FStar_Syntax_Syntax.Total uu___
        | FStar_TypeChecker_NBETerm.GTot (typ, u) ->
            let uu___ = let uu___1 = readback cfg typ in (uu___1, u) in
            FStar_Syntax_Syntax.GTotal uu___
        | FStar_TypeChecker_NBETerm.Comp ctyp ->
            let uu___ = readback_comp_typ cfg ctyp in
            FStar_Syntax_Syntax.Comp uu___ in
      FStar_Syntax_Syntax.mk c' FStar_Range.dummyRange
and (translate_comp_typ :
  config ->
    FStar_TypeChecker_NBETerm.t Prims.list ->
      FStar_Syntax_Syntax.comp_typ -> FStar_TypeChecker_NBETerm.comp_typ)
  =
  fun cfg ->
    fun bs ->
      fun c ->
        let uu___ = c in
        match uu___ with
        | { FStar_Syntax_Syntax.comp_univs = comp_univs;
            FStar_Syntax_Syntax.effect_name = effect_name;
            FStar_Syntax_Syntax.result_typ = result_typ;
            FStar_Syntax_Syntax.effect_args = effect_args;
            FStar_Syntax_Syntax.flags = flags;_} ->
            let uu___1 = FStar_List.map (translate_univ cfg bs) comp_univs in
            let uu___2 = translate cfg bs result_typ in
            let uu___3 =
              FStar_List.map
                (fun x ->
                   let uu___4 =
                     translate cfg bs (FStar_Pervasives_Native.fst x) in
                   (uu___4, (FStar_Pervasives_Native.snd x))) effect_args in
            let uu___4 = FStar_List.map (translate_flag cfg bs) flags in
            {
              FStar_TypeChecker_NBETerm.comp_univs = uu___1;
              FStar_TypeChecker_NBETerm.effect_name = effect_name;
              FStar_TypeChecker_NBETerm.result_typ = uu___2;
              FStar_TypeChecker_NBETerm.effect_args = uu___3;
              FStar_TypeChecker_NBETerm.flags = uu___4
            }
and (readback_comp_typ :
  config ->
    FStar_TypeChecker_NBETerm.comp_typ -> FStar_Syntax_Syntax.comp_typ)
  =
  fun cfg ->
    fun c ->
      let uu___ = readback cfg c.FStar_TypeChecker_NBETerm.result_typ in
      let uu___1 =
        FStar_List.map
          (fun x ->
             let uu___2 = readback cfg (FStar_Pervasives_Native.fst x) in
             (uu___2, (FStar_Pervasives_Native.snd x)))
          c.FStar_TypeChecker_NBETerm.effect_args in
      let uu___2 =
        FStar_List.map (readback_flag cfg) c.FStar_TypeChecker_NBETerm.flags in
      {
        FStar_Syntax_Syntax.comp_univs =
          (c.FStar_TypeChecker_NBETerm.comp_univs);
        FStar_Syntax_Syntax.effect_name =
          (c.FStar_TypeChecker_NBETerm.effect_name);
        FStar_Syntax_Syntax.result_typ = uu___;
        FStar_Syntax_Syntax.effect_args = uu___1;
        FStar_Syntax_Syntax.flags = uu___2
      }
and (translate_residual_comp :
  config ->
    FStar_TypeChecker_NBETerm.t Prims.list ->
      FStar_Syntax_Syntax.residual_comp ->
        FStar_TypeChecker_NBETerm.residual_comp)
  =
  fun cfg ->
    fun bs ->
      fun c ->
        let uu___ = c in
        match uu___ with
        | { FStar_Syntax_Syntax.residual_effect = residual_effect;
            FStar_Syntax_Syntax.residual_typ = residual_typ;
            FStar_Syntax_Syntax.residual_flags = residual_flags;_} ->
            let uu___1 =
              if
                ((cfg.core_cfg).FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.for_extraction
              then FStar_Pervasives_Native.None
              else FStar_Util.map_opt residual_typ (translate cfg bs) in
            let uu___2 =
              FStar_List.map (translate_flag cfg bs) residual_flags in
            {
              FStar_TypeChecker_NBETerm.residual_effect = residual_effect;
              FStar_TypeChecker_NBETerm.residual_typ = uu___1;
              FStar_TypeChecker_NBETerm.residual_flags = uu___2
            }
and (readback_residual_comp :
  config ->
    FStar_TypeChecker_NBETerm.residual_comp ->
      FStar_Syntax_Syntax.residual_comp)
  =
  fun cfg ->
    fun c ->
      let uu___ =
        FStar_Util.map_opt c.FStar_TypeChecker_NBETerm.residual_typ
          (fun x ->
             debug cfg
               (fun uu___2 ->
                  let uu___3 = FStar_TypeChecker_NBETerm.t_to_string x in
                  FStar_Util.print1 "Reading back residualtype %s\n" uu___3);
             readback cfg x) in
      let uu___1 =
        FStar_List.map (readback_flag cfg)
          c.FStar_TypeChecker_NBETerm.residual_flags in
      {
        FStar_Syntax_Syntax.residual_effect =
          (c.FStar_TypeChecker_NBETerm.residual_effect);
        FStar_Syntax_Syntax.residual_typ = uu___;
        FStar_Syntax_Syntax.residual_flags = uu___1
      }
and (translate_flag :
  config ->
    FStar_TypeChecker_NBETerm.t Prims.list ->
      FStar_Syntax_Syntax.cflag -> FStar_TypeChecker_NBETerm.cflag)
  =
  fun cfg ->
    fun bs ->
      fun f ->
        match f with
        | FStar_Syntax_Syntax.TOTAL -> FStar_TypeChecker_NBETerm.TOTAL
        | FStar_Syntax_Syntax.MLEFFECT -> FStar_TypeChecker_NBETerm.MLEFFECT
        | FStar_Syntax_Syntax.RETURN -> FStar_TypeChecker_NBETerm.RETURN
        | FStar_Syntax_Syntax.PARTIAL_RETURN ->
            FStar_TypeChecker_NBETerm.PARTIAL_RETURN
        | FStar_Syntax_Syntax.SOMETRIVIAL ->
            FStar_TypeChecker_NBETerm.SOMETRIVIAL
        | FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION ->
            FStar_TypeChecker_NBETerm.TRIVIAL_POSTCONDITION
        | FStar_Syntax_Syntax.SHOULD_NOT_INLINE ->
            FStar_TypeChecker_NBETerm.SHOULD_NOT_INLINE
        | FStar_Syntax_Syntax.LEMMA -> FStar_TypeChecker_NBETerm.LEMMA
        | FStar_Syntax_Syntax.CPS -> FStar_TypeChecker_NBETerm.CPS
        | FStar_Syntax_Syntax.DECREASES (FStar_Syntax_Syntax.Decreases_lex l)
            ->
            let uu___ =
              FStar_All.pipe_right l (FStar_List.map (translate cfg bs)) in
            FStar_TypeChecker_NBETerm.DECREASES uu___
and (readback_flag :
  config -> FStar_TypeChecker_NBETerm.cflag -> FStar_Syntax_Syntax.cflag) =
  fun cfg ->
    fun f ->
      match f with
      | FStar_TypeChecker_NBETerm.TOTAL -> FStar_Syntax_Syntax.TOTAL
      | FStar_TypeChecker_NBETerm.MLEFFECT -> FStar_Syntax_Syntax.MLEFFECT
      | FStar_TypeChecker_NBETerm.RETURN -> FStar_Syntax_Syntax.RETURN
      | FStar_TypeChecker_NBETerm.PARTIAL_RETURN ->
          FStar_Syntax_Syntax.PARTIAL_RETURN
      | FStar_TypeChecker_NBETerm.SOMETRIVIAL ->
          FStar_Syntax_Syntax.SOMETRIVIAL
      | FStar_TypeChecker_NBETerm.TRIVIAL_POSTCONDITION ->
          FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION
      | FStar_TypeChecker_NBETerm.SHOULD_NOT_INLINE ->
          FStar_Syntax_Syntax.SHOULD_NOT_INLINE
      | FStar_TypeChecker_NBETerm.LEMMA -> FStar_Syntax_Syntax.LEMMA
      | FStar_TypeChecker_NBETerm.CPS -> FStar_Syntax_Syntax.CPS
      | FStar_TypeChecker_NBETerm.DECREASES l ->
          let uu___ =
            let uu___1 =
              FStar_All.pipe_right l (FStar_List.map (readback cfg)) in
            FStar_Syntax_Syntax.Decreases_lex uu___1 in
          FStar_Syntax_Syntax.DECREASES uu___
and (translate_monadic :
  (FStar_Syntax_Syntax.monad_name * FStar_Syntax_Syntax.term'
    FStar_Syntax_Syntax.syntax) ->
    config ->
      FStar_TypeChecker_NBETerm.t Prims.list ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
          FStar_TypeChecker_NBETerm.t)
  =
  fun uu___ ->
    fun cfg ->
      fun bs ->
        fun e ->
          match uu___ with
          | (m, ty) ->
              let e1 = FStar_Syntax_Util.unascribe e in
              (match e1.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_let ((false, lb::[]), body) ->
                   let uu___1 =
                     let uu___2 =
                       FStar_TypeChecker_Env.norm_eff_name
                         (cfg.core_cfg).FStar_TypeChecker_Cfg.tcenv m in
                     FStar_TypeChecker_Env.effect_decl_opt
                       (cfg.core_cfg).FStar_TypeChecker_Cfg.tcenv uu___2 in
                   (match uu___1 with
                    | FStar_Pervasives_Native.None ->
                        let uu___2 =
                          let uu___3 = FStar_Ident.string_of_lid m in
                          FStar_Util.format1
                            "Effect declaration not found: %s" uu___3 in
                        failwith uu___2
                    | FStar_Pervasives_Native.Some (ed, q) ->
                        let cfg' = reifying_false cfg in
                        let body_lam =
                          let body_rc =
                            {
                              FStar_Syntax_Syntax.residual_effect = m;
                              FStar_Syntax_Syntax.residual_typ =
                                (FStar_Pervasives_Native.Some ty);
                              FStar_Syntax_Syntax.residual_flags = []
                            } in
                          let uu___2 =
                            let uu___3 =
                              let uu___4 =
                                let uu___5 =
                                  let uu___6 =
                                    FStar_Util.left
                                      lb.FStar_Syntax_Syntax.lbname in
                                  FStar_Syntax_Syntax.mk_binder uu___6 in
                                [uu___5] in
                              (uu___4, body,
                                (FStar_Pervasives_Native.Some body_rc)) in
                            FStar_Syntax_Syntax.Tm_abs uu___3 in
                          FStar_Syntax_Syntax.mk uu___2
                            body.FStar_Syntax_Syntax.pos in
                        let maybe_range_arg =
                          let uu___2 =
                            FStar_Util.for_some
                              (FStar_Syntax_Util.attr_eq
                                 FStar_Syntax_Util.dm4f_bind_range_attr)
                              ed.FStar_Syntax_Syntax.eff_attrs in
                          if uu___2
                          then
                            let uu___3 =
                              let uu___4 =
                                let uu___5 =
                                  FStar_TypeChecker_Cfg.embed_simple
                                    FStar_Syntax_Embeddings.e_range
                                    lb.FStar_Syntax_Syntax.lbpos
                                    lb.FStar_Syntax_Syntax.lbpos in
                                translate cfg [] uu___5 in
                              (uu___4, FStar_Pervasives_Native.None) in
                            let uu___4 =
                              let uu___5 =
                                let uu___6 =
                                  let uu___7 =
                                    FStar_TypeChecker_Cfg.embed_simple
                                      FStar_Syntax_Embeddings.e_range
                                      body.FStar_Syntax_Syntax.pos
                                      body.FStar_Syntax_Syntax.pos in
                                  translate cfg [] uu___7 in
                                (uu___6, FStar_Pervasives_Native.None) in
                              [uu___5] in
                            uu___3 :: uu___4
                          else [] in
                        let t =
                          let uu___2 =
                            let uu___3 =
                              let uu___4 =
                                let uu___5 =
                                  let uu___6 =
                                    let uu___7 =
                                      FStar_All.pipe_right ed
                                        FStar_Syntax_Util.get_bind_repr in
                                    FStar_All.pipe_right uu___7
                                      FStar_Util.must in
                                  FStar_All.pipe_right uu___6
                                    FStar_Pervasives_Native.snd in
                                FStar_Syntax_Util.un_uinst uu___5 in
                              translate cfg' [] uu___4 in
                            let uu___4 =
                              let uu___5 =
                                let uu___6 =
                                  FStar_All.pipe_left mk_t
                                    (FStar_TypeChecker_NBETerm.Univ
                                       FStar_Syntax_Syntax.U_unknown) in
                                (uu___6, FStar_Pervasives_Native.None) in
                              let uu___6 =
                                let uu___7 =
                                  let uu___8 =
                                    FStar_All.pipe_left mk_t
                                      (FStar_TypeChecker_NBETerm.Univ
                                         FStar_Syntax_Syntax.U_unknown) in
                                  (uu___8, FStar_Pervasives_Native.None) in
                                [uu___7] in
                              uu___5 :: uu___6 in
                            iapp cfg uu___3 uu___4 in
                          let uu___3 =
                            let uu___4 =
                              let uu___5 =
                                let uu___6 =
                                  translate cfg' bs
                                    lb.FStar_Syntax_Syntax.lbtyp in
                                (uu___6, FStar_Pervasives_Native.None) in
                              let uu___6 =
                                let uu___7 =
                                  let uu___8 = translate cfg' bs ty in
                                  (uu___8, FStar_Pervasives_Native.None) in
                                [uu___7] in
                              uu___5 :: uu___6 in
                            let uu___5 =
                              let uu___6 =
                                let uu___7 =
                                  let uu___8 =
                                    let uu___9 =
                                      translate cfg bs
                                        lb.FStar_Syntax_Syntax.lbdef in
                                    (uu___9, FStar_Pervasives_Native.None) in
                                  let uu___9 =
                                    let uu___10 =
                                      let uu___11 =
                                        let uu___12 =
                                          translate cfg bs body_lam in
                                        (uu___12,
                                          FStar_Pervasives_Native.None) in
                                      [uu___11] in
                                    ((mk_t FStar_TypeChecker_NBETerm.Unknown),
                                      FStar_Pervasives_Native.None) ::
                                      uu___10 in
                                  uu___8 :: uu___9 in
                                ((mk_t FStar_TypeChecker_NBETerm.Unknown),
                                  FStar_Pervasives_Native.None) :: uu___7 in
                              FStar_List.append maybe_range_arg uu___6 in
                            FStar_List.append uu___4 uu___5 in
                          iapp cfg uu___2 uu___3 in
                        (debug cfg
                           (fun uu___3 ->
                              let uu___4 =
                                FStar_TypeChecker_NBETerm.t_to_string t in
                              FStar_Util.print1 "translate_monadic: %s\n"
                                uu___4);
                         t))
               | FStar_Syntax_Syntax.Tm_app
                   ({
                      FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                        (FStar_Const.Const_reflect uu___1);
                      FStar_Syntax_Syntax.pos = uu___2;
                      FStar_Syntax_Syntax.vars = uu___3;_},
                    (e2, uu___4)::[])
                   ->
                   let uu___5 = reifying_false cfg in translate uu___5 bs e2
               | FStar_Syntax_Syntax.Tm_app (head, args) ->
                   (debug cfg
                      (fun uu___2 ->
                         let uu___3 = FStar_Syntax_Print.term_to_string head in
                         let uu___4 = FStar_Syntax_Print.args_to_string args in
                         FStar_Util.print2
                           "translate_monadic app (%s) @ (%s)\n" uu___3
                           uu___4);
                    (let fallback1 uu___2 = translate cfg bs e1 in
                     let fallback2 uu___2 =
                       let uu___3 = reifying_false cfg in
                       let uu___4 =
                         FStar_Syntax_Syntax.mk
                           (FStar_Syntax_Syntax.Tm_meta
                              (e1,
                                (FStar_Syntax_Syntax.Meta_monadic (m, ty))))
                           e1.FStar_Syntax_Syntax.pos in
                       translate uu___3 bs uu___4 in
                     let uu___2 =
                       let uu___3 = FStar_Syntax_Util.un_uinst head in
                       uu___3.FStar_Syntax_Syntax.n in
                     match uu___2 with
                     | FStar_Syntax_Syntax.Tm_fvar fv ->
                         let lid = FStar_Syntax_Syntax.lid_of_fv fv in
                         let qninfo =
                           FStar_TypeChecker_Env.lookup_qname
                             (cfg.core_cfg).FStar_TypeChecker_Cfg.tcenv lid in
                         let uu___3 =
                           let uu___4 =
                             FStar_TypeChecker_Env.is_action
                               (cfg.core_cfg).FStar_TypeChecker_Cfg.tcenv lid in
                           Prims.op_Negation uu___4 in
                         if uu___3
                         then fallback1 ()
                         else
                           (let uu___5 =
                              let uu___6 =
                                FStar_TypeChecker_Env.lookup_definition_qninfo
                                  (cfg.core_cfg).FStar_TypeChecker_Cfg.delta_level
                                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                  qninfo in
                              FStar_Option.isNone uu___6 in
                            if uu___5
                            then fallback2 ()
                            else
                              (let e2 =
                                 let uu___7 = FStar_Syntax_Util.mk_reify head in
                                 FStar_Syntax_Syntax.mk_Tm_app uu___7 args
                                   e1.FStar_Syntax_Syntax.pos in
                               let uu___7 = reifying_false cfg in
                               translate uu___7 bs e2))
                     | uu___3 -> fallback1 ()))
               | FStar_Syntax_Syntax.Tm_match (sc, asc_opt, branches) ->
                   let branches1 =
                     FStar_All.pipe_right branches
                       (FStar_List.map
                          (fun uu___1 ->
                             match uu___1 with
                             | (pat, wopt, tm) ->
                                 let uu___2 = FStar_Syntax_Util.mk_reify tm in
                                 (pat, wopt, uu___2))) in
                   let tm =
                     FStar_Syntax_Syntax.mk
                       (FStar_Syntax_Syntax.Tm_match (sc, asc_opt, branches1))
                       e1.FStar_Syntax_Syntax.pos in
                   let uu___1 = reifying_false cfg in translate uu___1 bs tm
               | FStar_Syntax_Syntax.Tm_meta
                   (t, FStar_Syntax_Syntax.Meta_monadic uu___1) ->
                   translate_monadic (m, ty) cfg bs e1
               | FStar_Syntax_Syntax.Tm_meta
                   (t, FStar_Syntax_Syntax.Meta_monadic_lift
                    (msrc, mtgt, ty'))
                   -> translate_monadic_lift (msrc, mtgt, ty') cfg bs e1
               | uu___1 ->
                   let uu___2 =
                     let uu___3 = FStar_Syntax_Print.tag_of_term e1 in
                     FStar_Util.format1
                       "Unexpected case in translate_monadic: %s" uu___3 in
                   failwith uu___2)
and (translate_monadic_lift :
  (FStar_Syntax_Syntax.monad_name * FStar_Syntax_Syntax.monad_name *
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax) ->
    config ->
      FStar_TypeChecker_NBETerm.t Prims.list ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
          FStar_TypeChecker_NBETerm.t)
  =
  fun uu___ ->
    fun cfg ->
      fun bs ->
        fun e ->
          match uu___ with
          | (msrc, mtgt, ty) ->
              let e1 = FStar_Syntax_Util.unascribe e in
              let uu___1 =
                (FStar_Syntax_Util.is_pure_effect msrc) ||
                  (FStar_Syntax_Util.is_div_effect msrc) in
              if uu___1
              then
                let ed =
                  let uu___2 =
                    FStar_TypeChecker_Env.norm_eff_name
                      (cfg.core_cfg).FStar_TypeChecker_Cfg.tcenv mtgt in
                  FStar_TypeChecker_Env.get_effect_decl
                    (cfg.core_cfg).FStar_TypeChecker_Cfg.tcenv uu___2 in
                let ret =
                  let uu___2 =
                    let uu___3 =
                      let uu___4 =
                        let uu___5 =
                          let uu___6 =
                            FStar_All.pipe_right ed
                              FStar_Syntax_Util.get_return_repr in
                          FStar_All.pipe_right uu___6 FStar_Util.must in
                        FStar_All.pipe_right uu___5
                          FStar_Pervasives_Native.snd in
                      FStar_Syntax_Subst.compress uu___4 in
                    uu___3.FStar_Syntax_Syntax.n in
                  match uu___2 with
                  | FStar_Syntax_Syntax.Tm_uinst (ret1, uu___3::[]) ->
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_uinst
                           (ret1, [FStar_Syntax_Syntax.U_unknown]))
                        e1.FStar_Syntax_Syntax.pos
                  | uu___3 ->
                      failwith "NYI: Reification of indexed effect (NBE)" in
                let cfg' = reifying_false cfg in
                let t =
                  let uu___2 =
                    let uu___3 = translate cfg' [] ret in
                    let uu___4 =
                      let uu___5 =
                        let uu___6 =
                          FStar_All.pipe_left mk_t
                            (FStar_TypeChecker_NBETerm.Univ
                               FStar_Syntax_Syntax.U_unknown) in
                        (uu___6, FStar_Pervasives_Native.None) in
                      [uu___5] in
                    iapp cfg' uu___3 uu___4 in
                  let uu___3 =
                    let uu___4 =
                      let uu___5 = translate cfg' bs ty in
                      (uu___5, FStar_Pervasives_Native.None) in
                    let uu___5 =
                      let uu___6 =
                        let uu___7 = translate cfg' bs e1 in
                        (uu___7, FStar_Pervasives_Native.None) in
                      [uu___6] in
                    uu___4 :: uu___5 in
                  iapp cfg' uu___2 uu___3 in
                (debug cfg
                   (fun uu___3 ->
                      let uu___4 = FStar_TypeChecker_NBETerm.t_to_string t in
                      FStar_Util.print1 "translate_monadic_lift(1): %s\n"
                        uu___4);
                 t)
              else
                (let uu___3 =
                   FStar_TypeChecker_Env.monad_leq
                     (cfg.core_cfg).FStar_TypeChecker_Cfg.tcenv msrc mtgt in
                 match uu___3 with
                 | FStar_Pervasives_Native.None ->
                     let uu___4 =
                       let uu___5 = FStar_Ident.string_of_lid msrc in
                       let uu___6 = FStar_Ident.string_of_lid mtgt in
                       FStar_Util.format2
                         "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                         uu___5 uu___6 in
                     failwith uu___4
                 | FStar_Pervasives_Native.Some
                     { FStar_TypeChecker_Env.msource = uu___4;
                       FStar_TypeChecker_Env.mtarget = uu___5;
                       FStar_TypeChecker_Env.mlift =
                         { FStar_TypeChecker_Env.mlift_wp = uu___6;
                           FStar_TypeChecker_Env.mlift_term =
                             FStar_Pervasives_Native.None;_};_}
                     ->
                     let uu___7 =
                       let uu___8 = FStar_Ident.string_of_lid msrc in
                       let uu___9 = FStar_Ident.string_of_lid mtgt in
                       FStar_Util.format2
                         "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
                         uu___8 uu___9 in
                     failwith uu___7
                 | FStar_Pervasives_Native.Some
                     { FStar_TypeChecker_Env.msource = uu___4;
                       FStar_TypeChecker_Env.mtarget = uu___5;
                       FStar_TypeChecker_Env.mlift =
                         { FStar_TypeChecker_Env.mlift_wp = uu___6;
                           FStar_TypeChecker_Env.mlift_term =
                             FStar_Pervasives_Native.Some lift;_};_}
                     ->
                     let lift_lam =
                       let x =
                         FStar_Syntax_Syntax.new_bv
                           FStar_Pervasives_Native.None
                           FStar_Syntax_Syntax.tun in
                       let uu___7 =
                         let uu___8 = FStar_Syntax_Syntax.mk_binder x in
                         [uu___8] in
                       let uu___8 =
                         let uu___9 = FStar_Syntax_Syntax.bv_to_name x in
                         lift FStar_Syntax_Syntax.U_unknown ty uu___9 in
                       FStar_Syntax_Util.abs uu___7 uu___8
                         FStar_Pervasives_Native.None in
                     let cfg' = reifying_false cfg in
                     let t =
                       let uu___7 = translate cfg' [] lift_lam in
                       let uu___8 =
                         let uu___9 =
                           let uu___10 = translate cfg bs e1 in
                           (uu___10, FStar_Pervasives_Native.None) in
                         [uu___9] in
                       iapp cfg uu___7 uu___8 in
                     (debug cfg
                        (fun uu___8 ->
                           let uu___9 =
                             FStar_TypeChecker_NBETerm.t_to_string t in
                           FStar_Util.print1
                             "translate_monadic_lift(2): %s\n" uu___9);
                      t))
and (readback :
  config -> FStar_TypeChecker_NBETerm.t -> FStar_Syntax_Syntax.term) =
  fun cfg ->
    fun x ->
      let debug1 = debug cfg in
      let readback_args cfg1 args =
        map_rev
          (fun uu___ ->
             match uu___ with
             | (x1, q) -> let uu___1 = readback cfg1 x1 in (uu___1, q)) args in
      let with_range t =
        let uu___ = t in
        {
          FStar_Syntax_Syntax.n = (uu___.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = (x.FStar_TypeChecker_NBETerm.nbe_r);
          FStar_Syntax_Syntax.vars = (uu___.FStar_Syntax_Syntax.vars)
        } in
      let mk t = FStar_Syntax_Syntax.mk t x.FStar_TypeChecker_NBETerm.nbe_r in
      debug1
        (fun uu___1 ->
           let uu___2 = FStar_TypeChecker_NBETerm.t_to_string x in
           FStar_Util.print1 "Readback: %s\n" uu___2);
      (match x.FStar_TypeChecker_NBETerm.nbe_t with
       | FStar_TypeChecker_NBETerm.Univ u ->
           failwith "Readback of universes should not occur"
       | FStar_TypeChecker_NBETerm.Unknown ->
           FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
             x.FStar_TypeChecker_NBETerm.nbe_r
       | FStar_TypeChecker_NBETerm.Constant (FStar_TypeChecker_NBETerm.Unit)
           -> with_range FStar_Syntax_Syntax.unit_const
       | FStar_TypeChecker_NBETerm.Constant (FStar_TypeChecker_NBETerm.Bool
           (true)) -> with_range FStar_Syntax_Util.exp_true_bool
       | FStar_TypeChecker_NBETerm.Constant (FStar_TypeChecker_NBETerm.Bool
           (false)) -> with_range FStar_Syntax_Util.exp_false_bool
       | FStar_TypeChecker_NBETerm.Constant (FStar_TypeChecker_NBETerm.Int i)
           ->
           let uu___1 =
             let uu___2 = FStar_BigInt.string_of_big_int i in
             FStar_Syntax_Util.exp_int uu___2 in
           with_range uu___1
       | FStar_TypeChecker_NBETerm.Constant (FStar_TypeChecker_NBETerm.String
           (s, r)) ->
           mk
             (FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_string (s, r)))
       | FStar_TypeChecker_NBETerm.Constant (FStar_TypeChecker_NBETerm.Char
           c) ->
           let uu___1 = FStar_Syntax_Util.exp_char c in with_range uu___1
       | FStar_TypeChecker_NBETerm.Constant (FStar_TypeChecker_NBETerm.Range
           r) ->
           FStar_TypeChecker_Cfg.embed_simple FStar_Syntax_Embeddings.e_range
             x.FStar_TypeChecker_NBETerm.nbe_r r
       | FStar_TypeChecker_NBETerm.Constant (FStar_TypeChecker_NBETerm.SConst
           c) -> mk (FStar_Syntax_Syntax.Tm_constant c)
       | FStar_TypeChecker_NBETerm.Meta (t, m) ->
           let uu___1 =
             let uu___2 =
               let uu___3 = readback cfg t in
               let uu___4 = FStar_Thunk.force m in (uu___3, uu___4) in
             FStar_Syntax_Syntax.Tm_meta uu___2 in
           mk uu___1
       | FStar_TypeChecker_NBETerm.Type_t u ->
           mk (FStar_Syntax_Syntax.Tm_type u)
       | FStar_TypeChecker_NBETerm.Lam (f, binders, arity) ->
           let uu___1 =
             match binders with
             | FStar_Pervasives.Inl (ctx, binders1, rc) ->
                 let uu___2 =
                   FStar_List.fold_left
                     (fun uu___3 ->
                        fun b ->
                          match uu___3 with
                          | (ctx1, binders_rev, accus_rev) ->
                              let x1 = b.FStar_Syntax_Syntax.binder_bv in
                              let tnorm =
                                let uu___4 =
                                  translate cfg ctx1
                                    x1.FStar_Syntax_Syntax.sort in
                                readback cfg uu___4 in
                              let x2 =
                                let uu___4 =
                                  FStar_Syntax_Syntax.freshen_bv x1 in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___4.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___4.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = tnorm
                                } in
                              let ax = FStar_TypeChecker_NBETerm.mkAccuVar x2 in
                              let ctx2 = ax :: ctx1 in
                              (ctx2,
                                ((let uu___4 = b in
                                  {
                                    FStar_Syntax_Syntax.binder_bv = x2;
                                    FStar_Syntax_Syntax.binder_qual =
                                      (uu___4.FStar_Syntax_Syntax.binder_qual);
                                    FStar_Syntax_Syntax.binder_attrs =
                                      (uu___4.FStar_Syntax_Syntax.binder_attrs)
                                  }) :: binders_rev), (ax :: accus_rev)))
                     (ctx, [], []) binders1 in
                 (match uu___2 with
                  | (ctx1, binders_rev, accus_rev) ->
                      let rc1 =
                        match rc with
                        | FStar_Pervasives_Native.None ->
                            FStar_Pervasives_Native.None
                        | FStar_Pervasives_Native.Some rc2 ->
                            let uu___3 =
                              let uu___4 =
                                translate_residual_comp cfg ctx1 rc2 in
                              readback_residual_comp cfg uu___4 in
                            FStar_Pervasives_Native.Some uu___3 in
                      ((FStar_List.rev binders_rev), accus_rev, rc1))
             | FStar_Pervasives.Inr args ->
                 let uu___2 =
                   FStar_List.fold_right
                     (fun uu___3 ->
                        fun uu___4 ->
                          match (uu___3, uu___4) with
                          | ((t, uu___5), (binders1, accus)) ->
                              let x1 =
                                let uu___6 = readback cfg t in
                                FStar_Syntax_Syntax.new_bv
                                  FStar_Pervasives_Native.None uu___6 in
                              let uu___6 =
                                let uu___7 = FStar_Syntax_Syntax.mk_binder x1 in
                                uu___7 :: binders1 in
                              let uu___7 =
                                let uu___8 =
                                  FStar_TypeChecker_NBETerm.mkAccuVar x1 in
                                uu___8 :: accus in
                              (uu___6, uu___7)) args ([], []) in
                 (match uu___2 with
                  | (binders1, accus) ->
                      (binders1, (FStar_List.rev accus),
                        FStar_Pervasives_Native.None)) in
           (match uu___1 with
            | (binders1, accus_rev, rc) ->
                let body = let uu___2 = f accus_rev in readback cfg uu___2 in
                let uu___2 = FStar_Syntax_Util.abs binders1 body rc in
                with_range uu___2)
       | FStar_TypeChecker_NBETerm.Refinement (f, targ) ->
           if
             ((cfg.core_cfg).FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.for_extraction
           then
             let uu___1 =
               let uu___2 = targ () in FStar_Pervasives_Native.fst uu___2 in
             readback cfg uu___1
           else
             (let x1 =
                let uu___2 =
                  let uu___3 =
                    let uu___4 = targ () in
                    FStar_Pervasives_Native.fst uu___4 in
                  readback cfg uu___3 in
                FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                  uu___2 in
              let body =
                let uu___2 =
                  let uu___3 = FStar_TypeChecker_NBETerm.mkAccuVar x1 in
                  f uu___3 in
                readback cfg uu___2 in
              let refinement = FStar_Syntax_Util.refine x1 body in
              let uu___2 =
                if
                  ((cfg.core_cfg).FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.simplify
                then
                  FStar_TypeChecker_Common.simplify
                    ((cfg.core_cfg).FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                    refinement
                else refinement in
              with_range uu___2)
       | FStar_TypeChecker_NBETerm.Reflect t ->
           let tm = readback cfg t in
           let uu___1 = FStar_Syntax_Util.mk_reflect tm in with_range uu___1
       | FStar_TypeChecker_NBETerm.Arrow (FStar_Pervasives.Inl f) ->
           let uu___1 = FStar_Thunk.force f in with_range uu___1
       | FStar_TypeChecker_NBETerm.Arrow (FStar_Pervasives.Inr (args, c)) ->
           let binders =
             FStar_List.map
               (fun uu___1 ->
                  match uu___1 with
                  | (t, q) ->
                      let t1 = readback cfg t in
                      let x1 =
                        FStar_Syntax_Syntax.new_bv
                          FStar_Pervasives_Native.None t1 in
                      FStar_Syntax_Syntax.mk_binder_with_attrs x1 q []) args in
           let c1 = readback_comp cfg c in
           let uu___1 = FStar_Syntax_Util.arrow binders c1 in
           with_range uu___1
       | FStar_TypeChecker_NBETerm.Construct (fv, us, args) ->
           let args1 =
             map_rev
               (fun uu___1 ->
                  match uu___1 with
                  | (x1, q) -> let uu___2 = readback cfg x1 in (uu___2, q))
               args in
           let fv1 =
             let uu___1 = FStar_Syntax_Syntax.range_of_fv fv in
             FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv) uu___1 in
           let app =
             let uu___1 =
               FStar_Syntax_Syntax.mk_Tm_uinst fv1 (FStar_List.rev us) in
             FStar_Syntax_Util.mk_app uu___1 args1 in
           with_range app
       | FStar_TypeChecker_NBETerm.FV (fv, us, args) ->
           let args1 =
             map_rev
               (fun uu___1 ->
                  match uu___1 with
                  | (x1, q) -> let uu___2 = readback cfg x1 in (uu___2, q))
               args in
           let fv1 =
             FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
               FStar_Range.dummyRange in
           let app =
             let uu___1 =
               FStar_Syntax_Syntax.mk_Tm_uinst fv1 (FStar_List.rev us) in
             FStar_Syntax_Util.mk_app uu___1 args1 in
           let uu___1 =
             if
               ((cfg.core_cfg).FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.simplify
             then
               FStar_TypeChecker_Common.simplify
                 ((cfg.core_cfg).FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                 app
             else app in
           with_range uu___1
       | FStar_TypeChecker_NBETerm.Accu
           (FStar_TypeChecker_NBETerm.Var bv, []) ->
           let uu___1 = FStar_Syntax_Syntax.bv_to_name bv in
           with_range uu___1
       | FStar_TypeChecker_NBETerm.Accu
           (FStar_TypeChecker_NBETerm.Var bv, args) ->
           let args1 = readback_args cfg args in
           let app =
             let uu___1 = FStar_Syntax_Syntax.bv_to_name bv in
             FStar_Syntax_Util.mk_app uu___1 args1 in
           let uu___1 =
             if
               ((cfg.core_cfg).FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.simplify
             then
               FStar_TypeChecker_Common.simplify
                 ((cfg.core_cfg).FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                 app
             else app in
           with_range uu___1
       | FStar_TypeChecker_NBETerm.Accu
           (FStar_TypeChecker_NBETerm.Match
            (scrut, make_returns, make_branches), args)
           ->
           let args1 = readback_args cfg args in
           let head =
             let scrut_new = readback cfg scrut in
             let returns_new = make_returns () in
             let branches_new = make_branches () in
             FStar_Syntax_Syntax.mk
               (FStar_Syntax_Syntax.Tm_match
                  (scrut_new, returns_new, branches_new))
               scrut.FStar_TypeChecker_NBETerm.nbe_r in
           let app = FStar_Syntax_Util.mk_app head args1 in
           let uu___1 =
             if
               ((cfg.core_cfg).FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.simplify
             then
               FStar_TypeChecker_Common.simplify
                 ((cfg.core_cfg).FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                 app
             else app in
           with_range uu___1
       | FStar_TypeChecker_NBETerm.Accu
           (FStar_TypeChecker_NBETerm.UnreducedLet
            (var, typ, defn, body, lb), args)
           ->
           let typ1 =
             let uu___1 = FStar_Thunk.force typ in readback cfg uu___1 in
           let defn1 =
             let uu___1 = FStar_Thunk.force defn in readback cfg uu___1 in
           let body1 =
             let uu___1 =
               let uu___2 = FStar_Syntax_Syntax.mk_binder var in [uu___2] in
             let uu___2 =
               let uu___3 = FStar_Thunk.force body in readback cfg uu___3 in
             FStar_Syntax_Subst.close uu___1 uu___2 in
           let lbname =
             let uu___1 =
               let uu___2 = FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
               {
                 FStar_Syntax_Syntax.ppname =
                   (uu___2.FStar_Syntax_Syntax.ppname);
                 FStar_Syntax_Syntax.index =
                   (uu___2.FStar_Syntax_Syntax.index);
                 FStar_Syntax_Syntax.sort = typ1
               } in
             FStar_Pervasives.Inl uu___1 in
           let lb1 =
             let uu___1 = lb in
             {
               FStar_Syntax_Syntax.lbname = lbname;
               FStar_Syntax_Syntax.lbunivs =
                 (uu___1.FStar_Syntax_Syntax.lbunivs);
               FStar_Syntax_Syntax.lbtyp = typ1;
               FStar_Syntax_Syntax.lbeff = (uu___1.FStar_Syntax_Syntax.lbeff);
               FStar_Syntax_Syntax.lbdef = defn1;
               FStar_Syntax_Syntax.lbattrs =
                 (uu___1.FStar_Syntax_Syntax.lbattrs);
               FStar_Syntax_Syntax.lbpos = (uu___1.FStar_Syntax_Syntax.lbpos)
             } in
           let hd =
             FStar_Syntax_Syntax.mk
               (FStar_Syntax_Syntax.Tm_let ((false, [lb1]), body1))
               FStar_Range.dummyRange in
           let args1 = readback_args cfg args in
           let uu___1 = FStar_Syntax_Util.mk_app hd args1 in
           with_range uu___1
       | FStar_TypeChecker_NBETerm.Accu
           (FStar_TypeChecker_NBETerm.UnreducedLetRec
            (vars_typs_defns, body, lbs), args)
           ->
           let lbs1 =
             FStar_List.map2
               (fun uu___1 ->
                  fun lb ->
                    match uu___1 with
                    | (v, t, d) ->
                        let t1 = readback cfg t in
                        let def = readback cfg d in
                        let v1 =
                          let uu___2 = v in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___2.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___2.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t1
                          } in
                        let uu___2 = lb in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (FStar_Pervasives.Inl v1);
                          FStar_Syntax_Syntax.lbunivs =
                            (uu___2.FStar_Syntax_Syntax.lbunivs);
                          FStar_Syntax_Syntax.lbtyp = t1;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___2.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = def;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___2.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___2.FStar_Syntax_Syntax.lbpos)
                        }) vars_typs_defns lbs in
           let body1 = readback cfg body in
           let uu___1 = FStar_Syntax_Subst.close_let_rec lbs1 body1 in
           (match uu___1 with
            | (lbs2, body2) ->
                let hd =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_let ((true, lbs2), body2))
                    FStar_Range.dummyRange in
                let args1 = readback_args cfg args in
                let uu___2 = FStar_Syntax_Util.mk_app hd args1 in
                with_range uu___2)
       | FStar_TypeChecker_NBETerm.Accu
           (FStar_TypeChecker_NBETerm.UVar f, args) ->
           let hd = FStar_Thunk.force f in
           let args1 = readback_args cfg args in
           let uu___1 = FStar_Syntax_Util.mk_app hd args1 in
           with_range uu___1
       | FStar_TypeChecker_NBETerm.TopLevelLet (lb, arity, args_rev) ->
           let n_univs = FStar_List.length lb.FStar_Syntax_Syntax.lbunivs in
           let n_args = FStar_List.length args_rev in
           let uu___1 = FStar_Util.first_N (n_args - n_univs) args_rev in
           (match uu___1 with
            | (args_rev1, univs) ->
                let uu___2 =
                  let uu___3 =
                    let uu___4 =
                      FStar_List.map FStar_Pervasives_Native.fst univs in
                    translate cfg uu___4 lb.FStar_Syntax_Syntax.lbdef in
                  iapp cfg uu___3 (FStar_List.rev args_rev1) in
                readback cfg uu___2)
       | FStar_TypeChecker_NBETerm.TopLevelRec (lb, uu___1, uu___2, args) ->
           let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
           let head =
             FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
               FStar_Range.dummyRange in
           let args1 =
             FStar_List.map
               (fun uu___3 ->
                  match uu___3 with
                  | (t, q) -> let uu___4 = readback cfg t in (uu___4, q))
               args in
           let uu___3 = FStar_Syntax_Util.mk_app head args1 in
           with_range uu___3
       | FStar_TypeChecker_NBETerm.LocalLetRec
           (i, uu___1, lbs, bs, args, _ar, _ar_lst) ->
           let lbnames =
             FStar_List.map
               (fun lb ->
                  let uu___2 =
                    let uu___3 =
                      let uu___4 =
                        FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                      uu___4.FStar_Syntax_Syntax.ppname in
                    FStar_Ident.string_of_id uu___3 in
                  FStar_Syntax_Syntax.gen_bv uu___2
                    FStar_Pervasives_Native.None lb.FStar_Syntax_Syntax.lbtyp)
               lbs in
           let let_rec_env =
             let uu___2 =
               FStar_List.map
                 (fun x1 ->
                    let uu___3 = FStar_Syntax_Syntax.range_of_bv x1 in
                    mk_rt uu___3
                      (FStar_TypeChecker_NBETerm.Accu
                         ((FStar_TypeChecker_NBETerm.Var x1), []))) lbnames in
             FStar_List.rev_append uu___2 bs in
           let lbs1 =
             FStar_List.map2
               (fun lb ->
                  fun lbname ->
                    let lbdef =
                      let uu___2 =
                        translate cfg let_rec_env
                          lb.FStar_Syntax_Syntax.lbdef in
                      readback cfg uu___2 in
                    let lbtyp =
                      let uu___2 =
                        translate cfg bs lb.FStar_Syntax_Syntax.lbtyp in
                      readback cfg uu___2 in
                    let uu___2 = lb in
                    {
                      FStar_Syntax_Syntax.lbname =
                        (FStar_Pervasives.Inl lbname);
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___2.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = lbtyp;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___2.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = lbdef;
                      FStar_Syntax_Syntax.lbattrs =
                        (uu___2.FStar_Syntax_Syntax.lbattrs);
                      FStar_Syntax_Syntax.lbpos =
                        (uu___2.FStar_Syntax_Syntax.lbpos)
                    }) lbs lbnames in
           let body =
             let uu___2 = FStar_List.nth lbnames i in
             FStar_Syntax_Syntax.bv_to_name uu___2 in
           let uu___2 = FStar_Syntax_Subst.close_let_rec lbs1 body in
           (match uu___2 with
            | (lbs2, body1) ->
                let head =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_let ((true, lbs2), body1))
                    FStar_Range.dummyRange in
                let args1 =
                  FStar_List.map
                    (fun uu___3 ->
                       match uu___3 with
                       | (x1, q) ->
                           let uu___4 = readback cfg x1 in (uu___4, q)) args in
                let uu___3 = FStar_Syntax_Util.mk_app head args1 in
                with_range uu___3)
       | FStar_TypeChecker_NBETerm.Quote (qt, qi) ->
           mk (FStar_Syntax_Syntax.Tm_quoted (qt, qi))
       | FStar_TypeChecker_NBETerm.Lazy (FStar_Pervasives.Inl li, uu___1) ->
           mk (FStar_Syntax_Syntax.Tm_lazy li)
       | FStar_TypeChecker_NBETerm.Lazy (uu___1, thunk) ->
           let uu___2 = FStar_Thunk.force thunk in readback cfg uu___2)
type step =
  | Primops 
  | UnfoldUntil of FStar_Syntax_Syntax.delta_depth 
  | UnfoldOnly of FStar_Ident.lid Prims.list 
  | UnfoldAttr of FStar_Ident.lid Prims.list 
  | UnfoldTac 
  | Reify 
let (uu___is_Primops : step -> Prims.bool) =
  fun projectee -> match projectee with | Primops -> true | uu___ -> false
let (uu___is_UnfoldUntil : step -> Prims.bool) =
  fun projectee ->
    match projectee with | UnfoldUntil _0 -> true | uu___ -> false
let (__proj__UnfoldUntil__item___0 : step -> FStar_Syntax_Syntax.delta_depth)
  = fun projectee -> match projectee with | UnfoldUntil _0 -> _0
let (uu___is_UnfoldOnly : step -> Prims.bool) =
  fun projectee ->
    match projectee with | UnfoldOnly _0 -> true | uu___ -> false
let (__proj__UnfoldOnly__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee -> match projectee with | UnfoldOnly _0 -> _0
let (uu___is_UnfoldAttr : step -> Prims.bool) =
  fun projectee ->
    match projectee with | UnfoldAttr _0 -> true | uu___ -> false
let (__proj__UnfoldAttr__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee -> match projectee with | UnfoldAttr _0 -> _0
let (uu___is_UnfoldTac : step -> Prims.bool) =
  fun projectee -> match projectee with | UnfoldTac -> true | uu___ -> false
let (uu___is_Reify : step -> Prims.bool) =
  fun projectee -> match projectee with | Reify -> true | uu___ -> false
let (step_as_normalizer_step : step -> FStar_TypeChecker_Env.step) =
  fun uu___ ->
    match uu___ with
    | Primops -> FStar_TypeChecker_Env.Primops
    | UnfoldUntil d -> FStar_TypeChecker_Env.UnfoldUntil d
    | UnfoldOnly lids -> FStar_TypeChecker_Env.UnfoldOnly lids
    | UnfoldAttr lids -> FStar_TypeChecker_Env.UnfoldAttr lids
    | UnfoldTac -> FStar_TypeChecker_Env.UnfoldTac
    | Reify -> FStar_TypeChecker_Env.Reify
let (reduce_application :
  FStar_TypeChecker_Cfg.cfg ->
    FStar_TypeChecker_NBETerm.t ->
      FStar_TypeChecker_NBETerm.args -> FStar_TypeChecker_NBETerm.t)
  =
  fun cfg ->
    fun t -> fun args -> let uu___ = new_config cfg in iapp uu___ t args
let (normalize :
  FStar_TypeChecker_Cfg.primitive_step Prims.list ->
    FStar_TypeChecker_Env.step Prims.list ->
      FStar_TypeChecker_Env.env ->
        FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun psteps ->
    fun steps ->
      fun env ->
        fun e ->
          let cfg = FStar_TypeChecker_Cfg.config' psteps steps env in
          let cfg1 =
            let uu___ = cfg in
            {
              FStar_TypeChecker_Cfg.steps =
                (let uu___1 = cfg.FStar_TypeChecker_Cfg.steps in
                 {
                   FStar_TypeChecker_Cfg.beta =
                     (uu___1.FStar_TypeChecker_Cfg.beta);
                   FStar_TypeChecker_Cfg.iota =
                     (uu___1.FStar_TypeChecker_Cfg.iota);
                   FStar_TypeChecker_Cfg.zeta =
                     (uu___1.FStar_TypeChecker_Cfg.zeta);
                   FStar_TypeChecker_Cfg.zeta_full =
                     (uu___1.FStar_TypeChecker_Cfg.zeta_full);
                   FStar_TypeChecker_Cfg.weak =
                     (uu___1.FStar_TypeChecker_Cfg.weak);
                   FStar_TypeChecker_Cfg.hnf =
                     (uu___1.FStar_TypeChecker_Cfg.hnf);
                   FStar_TypeChecker_Cfg.primops =
                     (uu___1.FStar_TypeChecker_Cfg.primops);
                   FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                     (uu___1.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                   FStar_TypeChecker_Cfg.unfold_until =
                     (uu___1.FStar_TypeChecker_Cfg.unfold_until);
                   FStar_TypeChecker_Cfg.unfold_only =
                     (uu___1.FStar_TypeChecker_Cfg.unfold_only);
                   FStar_TypeChecker_Cfg.unfold_fully =
                     (uu___1.FStar_TypeChecker_Cfg.unfold_fully);
                   FStar_TypeChecker_Cfg.unfold_attr =
                     (uu___1.FStar_TypeChecker_Cfg.unfold_attr);
                   FStar_TypeChecker_Cfg.unfold_qual =
                     (uu___1.FStar_TypeChecker_Cfg.unfold_qual);
                   FStar_TypeChecker_Cfg.unfold_tac =
                     (uu___1.FStar_TypeChecker_Cfg.unfold_tac);
                   FStar_TypeChecker_Cfg.pure_subterms_within_computations =
                     (uu___1.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                   FStar_TypeChecker_Cfg.simplify =
                     (uu___1.FStar_TypeChecker_Cfg.simplify);
                   FStar_TypeChecker_Cfg.erase_universes =
                     (uu___1.FStar_TypeChecker_Cfg.erase_universes);
                   FStar_TypeChecker_Cfg.allow_unbound_universes =
                     (uu___1.FStar_TypeChecker_Cfg.allow_unbound_universes);
                   FStar_TypeChecker_Cfg.reify_ = true;
                   FStar_TypeChecker_Cfg.compress_uvars =
                     (uu___1.FStar_TypeChecker_Cfg.compress_uvars);
                   FStar_TypeChecker_Cfg.no_full_norm =
                     (uu___1.FStar_TypeChecker_Cfg.no_full_norm);
                   FStar_TypeChecker_Cfg.check_no_uvars =
                     (uu___1.FStar_TypeChecker_Cfg.check_no_uvars);
                   FStar_TypeChecker_Cfg.unmeta =
                     (uu___1.FStar_TypeChecker_Cfg.unmeta);
                   FStar_TypeChecker_Cfg.unascribe =
                     (uu___1.FStar_TypeChecker_Cfg.unascribe);
                   FStar_TypeChecker_Cfg.in_full_norm_request =
                     (uu___1.FStar_TypeChecker_Cfg.in_full_norm_request);
                   FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                     (uu___1.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                   FStar_TypeChecker_Cfg.nbe_step =
                     (uu___1.FStar_TypeChecker_Cfg.nbe_step);
                   FStar_TypeChecker_Cfg.for_extraction =
                     (uu___1.FStar_TypeChecker_Cfg.for_extraction)
                 });
              FStar_TypeChecker_Cfg.tcenv =
                (uu___.FStar_TypeChecker_Cfg.tcenv);
              FStar_TypeChecker_Cfg.debug =
                (uu___.FStar_TypeChecker_Cfg.debug);
              FStar_TypeChecker_Cfg.delta_level =
                (uu___.FStar_TypeChecker_Cfg.delta_level);
              FStar_TypeChecker_Cfg.primitive_steps =
                (uu___.FStar_TypeChecker_Cfg.primitive_steps);
              FStar_TypeChecker_Cfg.strong =
                (uu___.FStar_TypeChecker_Cfg.strong);
              FStar_TypeChecker_Cfg.memoize_lazy =
                (uu___.FStar_TypeChecker_Cfg.memoize_lazy);
              FStar_TypeChecker_Cfg.normalize_pure_lets =
                (uu___.FStar_TypeChecker_Cfg.normalize_pure_lets);
              FStar_TypeChecker_Cfg.reifying =
                (uu___.FStar_TypeChecker_Cfg.reifying)
            } in
          (let uu___1 =
             (FStar_TypeChecker_Env.debug env (FStar_Options.Other "NBETop"))
               ||
               (FStar_TypeChecker_Env.debug env (FStar_Options.Other "NBE")) in
           if uu___1
           then
             let uu___2 = FStar_Syntax_Print.term_to_string e in
             FStar_Util.print1 "Calling NBE with (%s) {\n" uu___2
           else ());
          (let cfg2 = new_config cfg1 in
           let r = let uu___1 = translate cfg2 [] e in readback cfg2 uu___1 in
           (let uu___2 =
              (FStar_TypeChecker_Env.debug env (FStar_Options.Other "NBETop"))
                ||
                (FStar_TypeChecker_Env.debug env (FStar_Options.Other "NBE")) in
            if uu___2
            then
              let uu___3 = FStar_Syntax_Print.term_to_string r in
              FStar_Util.print1 "}\nNBE returned (%s)\n" uu___3
            else ());
           r)
let (normalize_for_unit_test :
  FStar_TypeChecker_Env.step Prims.list ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun steps ->
    fun env ->
      fun e ->
        let cfg = FStar_TypeChecker_Cfg.config steps env in
        let cfg1 =
          let uu___ = cfg in
          {
            FStar_TypeChecker_Cfg.steps =
              (let uu___1 = cfg.FStar_TypeChecker_Cfg.steps in
               {
                 FStar_TypeChecker_Cfg.beta =
                   (uu___1.FStar_TypeChecker_Cfg.beta);
                 FStar_TypeChecker_Cfg.iota =
                   (uu___1.FStar_TypeChecker_Cfg.iota);
                 FStar_TypeChecker_Cfg.zeta =
                   (uu___1.FStar_TypeChecker_Cfg.zeta);
                 FStar_TypeChecker_Cfg.zeta_full =
                   (uu___1.FStar_TypeChecker_Cfg.zeta_full);
                 FStar_TypeChecker_Cfg.weak =
                   (uu___1.FStar_TypeChecker_Cfg.weak);
                 FStar_TypeChecker_Cfg.hnf =
                   (uu___1.FStar_TypeChecker_Cfg.hnf);
                 FStar_TypeChecker_Cfg.primops =
                   (uu___1.FStar_TypeChecker_Cfg.primops);
                 FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                   (uu___1.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                 FStar_TypeChecker_Cfg.unfold_until =
                   (uu___1.FStar_TypeChecker_Cfg.unfold_until);
                 FStar_TypeChecker_Cfg.unfold_only =
                   (uu___1.FStar_TypeChecker_Cfg.unfold_only);
                 FStar_TypeChecker_Cfg.unfold_fully =
                   (uu___1.FStar_TypeChecker_Cfg.unfold_fully);
                 FStar_TypeChecker_Cfg.unfold_attr =
                   (uu___1.FStar_TypeChecker_Cfg.unfold_attr);
                 FStar_TypeChecker_Cfg.unfold_qual =
                   (uu___1.FStar_TypeChecker_Cfg.unfold_qual);
                 FStar_TypeChecker_Cfg.unfold_tac =
                   (uu___1.FStar_TypeChecker_Cfg.unfold_tac);
                 FStar_TypeChecker_Cfg.pure_subterms_within_computations =
                   (uu___1.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                 FStar_TypeChecker_Cfg.simplify =
                   (uu___1.FStar_TypeChecker_Cfg.simplify);
                 FStar_TypeChecker_Cfg.erase_universes =
                   (uu___1.FStar_TypeChecker_Cfg.erase_universes);
                 FStar_TypeChecker_Cfg.allow_unbound_universes =
                   (uu___1.FStar_TypeChecker_Cfg.allow_unbound_universes);
                 FStar_TypeChecker_Cfg.reify_ = true;
                 FStar_TypeChecker_Cfg.compress_uvars =
                   (uu___1.FStar_TypeChecker_Cfg.compress_uvars);
                 FStar_TypeChecker_Cfg.no_full_norm =
                   (uu___1.FStar_TypeChecker_Cfg.no_full_norm);
                 FStar_TypeChecker_Cfg.check_no_uvars =
                   (uu___1.FStar_TypeChecker_Cfg.check_no_uvars);
                 FStar_TypeChecker_Cfg.unmeta =
                   (uu___1.FStar_TypeChecker_Cfg.unmeta);
                 FStar_TypeChecker_Cfg.unascribe =
                   (uu___1.FStar_TypeChecker_Cfg.unascribe);
                 FStar_TypeChecker_Cfg.in_full_norm_request =
                   (uu___1.FStar_TypeChecker_Cfg.in_full_norm_request);
                 FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                   (uu___1.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                 FStar_TypeChecker_Cfg.nbe_step =
                   (uu___1.FStar_TypeChecker_Cfg.nbe_step);
                 FStar_TypeChecker_Cfg.for_extraction =
                   (uu___1.FStar_TypeChecker_Cfg.for_extraction)
               });
            FStar_TypeChecker_Cfg.tcenv = (uu___.FStar_TypeChecker_Cfg.tcenv);
            FStar_TypeChecker_Cfg.debug = (uu___.FStar_TypeChecker_Cfg.debug);
            FStar_TypeChecker_Cfg.delta_level =
              (uu___.FStar_TypeChecker_Cfg.delta_level);
            FStar_TypeChecker_Cfg.primitive_steps =
              (uu___.FStar_TypeChecker_Cfg.primitive_steps);
            FStar_TypeChecker_Cfg.strong =
              (uu___.FStar_TypeChecker_Cfg.strong);
            FStar_TypeChecker_Cfg.memoize_lazy =
              (uu___.FStar_TypeChecker_Cfg.memoize_lazy);
            FStar_TypeChecker_Cfg.normalize_pure_lets =
              (uu___.FStar_TypeChecker_Cfg.normalize_pure_lets);
            FStar_TypeChecker_Cfg.reifying =
              (uu___.FStar_TypeChecker_Cfg.reifying)
          } in
        let cfg2 = new_config cfg1 in
        debug cfg2
          (fun uu___1 ->
             let uu___2 = FStar_Syntax_Print.term_to_string e in
             FStar_Util.print1 "Calling NBE with (%s) {\n" uu___2);
        (let r = let uu___1 = translate cfg2 [] e in readback cfg2 uu___1 in
         debug cfg2
           (fun uu___2 ->
              let uu___3 = FStar_Syntax_Print.term_to_string r in
              FStar_Util.print1 "}\nNBE returned (%s)\n" uu___3);
         r)