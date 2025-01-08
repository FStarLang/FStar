open Prims
let (dbg_NBE : Prims.bool FStarC_Compiler_Effect.ref) =
  FStarC_Compiler_Debug.get_toggle "NBE"
let (dbg_NBETop : Prims.bool FStarC_Compiler_Effect.ref) =
  FStarC_Compiler_Debug.get_toggle "NBETop"
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
      FStarC_Compiler_Util.bind_opt x
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
    let uu___ = drop_until (fun x -> x) (FStarC_Compiler_List.rev l) in
    FStarC_Compiler_List.rev uu___
let (implies : Prims.bool -> Prims.bool -> Prims.bool) =
  fun b1 ->
    fun b2 ->
      match (b1, b2) with | (false, uu___) -> true | (true, b21) -> b21
let (let_rec_arity :
  FStarC_Syntax_Syntax.letbinding -> (Prims.int * Prims.bool Prims.list)) =
  fun b ->
    let uu___ = FStarC_Syntax_Util.let_rec_arity b in
    match uu___ with
    | (ar, maybe_lst) ->
        (match maybe_lst with
         | FStar_Pervasives_Native.None ->
             let uu___1 = FStarC_Common.tabulate ar (fun uu___2 -> true) in
             (ar, uu___1)
         | FStar_Pervasives_Native.Some lst -> (ar, lst))
let (debug_term : FStarC_Syntax_Syntax.term -> unit) =
  fun t ->
    let uu___ = FStarC_Class_Show.show FStarC_Syntax_Print.showable_term t in
    FStarC_Compiler_Util.print1 "%s\n" uu___
let (debug_sigmap :
  FStarC_Syntax_Syntax.sigelt FStarC_Compiler_Util.smap -> unit) =
  fun m ->
    FStarC_Compiler_Util.smap_fold m
      (fun k ->
         fun v ->
           fun u ->
             let uu___ = FStarC_Syntax_Print.sigelt_to_string_short v in
             FStarC_Compiler_Util.print2 "%s -> %%s\n" k uu___) ()
type config =
  {
  core_cfg: FStarC_TypeChecker_Cfg.cfg ;
  fv_cache: FStarC_TypeChecker_NBETerm.t FStarC_Compiler_Util.smap }
let (__proj__Mkconfig__item__core_cfg : config -> FStarC_TypeChecker_Cfg.cfg)
  =
  fun projectee -> match projectee with | { core_cfg; fv_cache;_} -> core_cfg
let (__proj__Mkconfig__item__fv_cache :
  config -> FStarC_TypeChecker_NBETerm.t FStarC_Compiler_Util.smap) =
  fun projectee -> match projectee with | { core_cfg; fv_cache;_} -> fv_cache
let (new_config : FStarC_TypeChecker_Cfg.cfg -> config) =
  fun cfg ->
    let uu___ = FStarC_Compiler_Util.smap_create (Prims.of_int (51)) in
    { core_cfg = cfg; fv_cache = uu___ }
let (reifying_false : config -> config) =
  fun cfg ->
    if (cfg.core_cfg).FStarC_TypeChecker_Cfg.reifying
    then
      new_config
        (let uu___ = cfg.core_cfg in
         {
           FStarC_TypeChecker_Cfg.steps =
             (uu___.FStarC_TypeChecker_Cfg.steps);
           FStarC_TypeChecker_Cfg.tcenv =
             (uu___.FStarC_TypeChecker_Cfg.tcenv);
           FStarC_TypeChecker_Cfg.debug =
             (uu___.FStarC_TypeChecker_Cfg.debug);
           FStarC_TypeChecker_Cfg.delta_level =
             (uu___.FStarC_TypeChecker_Cfg.delta_level);
           FStarC_TypeChecker_Cfg.primitive_steps =
             (uu___.FStarC_TypeChecker_Cfg.primitive_steps);
           FStarC_TypeChecker_Cfg.strong =
             (uu___.FStarC_TypeChecker_Cfg.strong);
           FStarC_TypeChecker_Cfg.memoize_lazy =
             (uu___.FStarC_TypeChecker_Cfg.memoize_lazy);
           FStarC_TypeChecker_Cfg.normalize_pure_lets =
             (uu___.FStarC_TypeChecker_Cfg.normalize_pure_lets);
           FStarC_TypeChecker_Cfg.reifying = false;
           FStarC_TypeChecker_Cfg.compat_memo_ignore_cfg =
             (uu___.FStarC_TypeChecker_Cfg.compat_memo_ignore_cfg)
         })
    else cfg
let (reifying_true : config -> config) =
  fun cfg ->
    if Prims.op_Negation (cfg.core_cfg).FStarC_TypeChecker_Cfg.reifying
    then
      new_config
        (let uu___ = cfg.core_cfg in
         {
           FStarC_TypeChecker_Cfg.steps =
             (uu___.FStarC_TypeChecker_Cfg.steps);
           FStarC_TypeChecker_Cfg.tcenv =
             (uu___.FStarC_TypeChecker_Cfg.tcenv);
           FStarC_TypeChecker_Cfg.debug =
             (uu___.FStarC_TypeChecker_Cfg.debug);
           FStarC_TypeChecker_Cfg.delta_level =
             (uu___.FStarC_TypeChecker_Cfg.delta_level);
           FStarC_TypeChecker_Cfg.primitive_steps =
             (uu___.FStarC_TypeChecker_Cfg.primitive_steps);
           FStarC_TypeChecker_Cfg.strong =
             (uu___.FStarC_TypeChecker_Cfg.strong);
           FStarC_TypeChecker_Cfg.memoize_lazy =
             (uu___.FStarC_TypeChecker_Cfg.memoize_lazy);
           FStarC_TypeChecker_Cfg.normalize_pure_lets =
             (uu___.FStarC_TypeChecker_Cfg.normalize_pure_lets);
           FStarC_TypeChecker_Cfg.reifying = true;
           FStarC_TypeChecker_Cfg.compat_memo_ignore_cfg =
             (uu___.FStarC_TypeChecker_Cfg.compat_memo_ignore_cfg)
         })
    else cfg
let (zeta_false : config -> config) =
  fun cfg ->
    let cfg_core = cfg.core_cfg in
    if (cfg_core.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.zeta
    then
      let cfg_core' =
        {
          FStarC_TypeChecker_Cfg.steps =
            (let uu___ = cfg_core.FStarC_TypeChecker_Cfg.steps in
             {
               FStarC_TypeChecker_Cfg.beta =
                 (uu___.FStarC_TypeChecker_Cfg.beta);
               FStarC_TypeChecker_Cfg.iota =
                 (uu___.FStarC_TypeChecker_Cfg.iota);
               FStarC_TypeChecker_Cfg.zeta = false;
               FStarC_TypeChecker_Cfg.zeta_full =
                 (uu___.FStarC_TypeChecker_Cfg.zeta_full);
               FStarC_TypeChecker_Cfg.weak =
                 (uu___.FStarC_TypeChecker_Cfg.weak);
               FStarC_TypeChecker_Cfg.hnf =
                 (uu___.FStarC_TypeChecker_Cfg.hnf);
               FStarC_TypeChecker_Cfg.primops =
                 (uu___.FStarC_TypeChecker_Cfg.primops);
               FStarC_TypeChecker_Cfg.do_not_unfold_pure_lets =
                 (uu___.FStarC_TypeChecker_Cfg.do_not_unfold_pure_lets);
               FStarC_TypeChecker_Cfg.unfold_until =
                 (uu___.FStarC_TypeChecker_Cfg.unfold_until);
               FStarC_TypeChecker_Cfg.unfold_only =
                 (uu___.FStarC_TypeChecker_Cfg.unfold_only);
               FStarC_TypeChecker_Cfg.unfold_fully =
                 (uu___.FStarC_TypeChecker_Cfg.unfold_fully);
               FStarC_TypeChecker_Cfg.unfold_attr =
                 (uu___.FStarC_TypeChecker_Cfg.unfold_attr);
               FStarC_TypeChecker_Cfg.unfold_qual =
                 (uu___.FStarC_TypeChecker_Cfg.unfold_qual);
               FStarC_TypeChecker_Cfg.unfold_namespace =
                 (uu___.FStarC_TypeChecker_Cfg.unfold_namespace);
               FStarC_TypeChecker_Cfg.dont_unfold_attr =
                 (uu___.FStarC_TypeChecker_Cfg.dont_unfold_attr);
               FStarC_TypeChecker_Cfg.pure_subterms_within_computations =
                 (uu___.FStarC_TypeChecker_Cfg.pure_subterms_within_computations);
               FStarC_TypeChecker_Cfg.simplify =
                 (uu___.FStarC_TypeChecker_Cfg.simplify);
               FStarC_TypeChecker_Cfg.erase_universes =
                 (uu___.FStarC_TypeChecker_Cfg.erase_universes);
               FStarC_TypeChecker_Cfg.allow_unbound_universes =
                 (uu___.FStarC_TypeChecker_Cfg.allow_unbound_universes);
               FStarC_TypeChecker_Cfg.reify_ =
                 (uu___.FStarC_TypeChecker_Cfg.reify_);
               FStarC_TypeChecker_Cfg.compress_uvars =
                 (uu___.FStarC_TypeChecker_Cfg.compress_uvars);
               FStarC_TypeChecker_Cfg.no_full_norm =
                 (uu___.FStarC_TypeChecker_Cfg.no_full_norm);
               FStarC_TypeChecker_Cfg.check_no_uvars =
                 (uu___.FStarC_TypeChecker_Cfg.check_no_uvars);
               FStarC_TypeChecker_Cfg.unmeta =
                 (uu___.FStarC_TypeChecker_Cfg.unmeta);
               FStarC_TypeChecker_Cfg.unascribe =
                 (uu___.FStarC_TypeChecker_Cfg.unascribe);
               FStarC_TypeChecker_Cfg.in_full_norm_request =
                 (uu___.FStarC_TypeChecker_Cfg.in_full_norm_request);
               FStarC_TypeChecker_Cfg.weakly_reduce_scrutinee =
                 (uu___.FStarC_TypeChecker_Cfg.weakly_reduce_scrutinee);
               FStarC_TypeChecker_Cfg.nbe_step =
                 (uu___.FStarC_TypeChecker_Cfg.nbe_step);
               FStarC_TypeChecker_Cfg.for_extraction =
                 (uu___.FStarC_TypeChecker_Cfg.for_extraction);
               FStarC_TypeChecker_Cfg.unrefine =
                 (uu___.FStarC_TypeChecker_Cfg.unrefine);
               FStarC_TypeChecker_Cfg.default_univs_to_zero =
                 (uu___.FStarC_TypeChecker_Cfg.default_univs_to_zero);
               FStarC_TypeChecker_Cfg.tactics =
                 (uu___.FStarC_TypeChecker_Cfg.tactics)
             });
          FStarC_TypeChecker_Cfg.tcenv =
            (cfg_core.FStarC_TypeChecker_Cfg.tcenv);
          FStarC_TypeChecker_Cfg.debug =
            (cfg_core.FStarC_TypeChecker_Cfg.debug);
          FStarC_TypeChecker_Cfg.delta_level =
            (cfg_core.FStarC_TypeChecker_Cfg.delta_level);
          FStarC_TypeChecker_Cfg.primitive_steps =
            (cfg_core.FStarC_TypeChecker_Cfg.primitive_steps);
          FStarC_TypeChecker_Cfg.strong =
            (cfg_core.FStarC_TypeChecker_Cfg.strong);
          FStarC_TypeChecker_Cfg.memoize_lazy =
            (cfg_core.FStarC_TypeChecker_Cfg.memoize_lazy);
          FStarC_TypeChecker_Cfg.normalize_pure_lets =
            (cfg_core.FStarC_TypeChecker_Cfg.normalize_pure_lets);
          FStarC_TypeChecker_Cfg.reifying =
            (cfg_core.FStarC_TypeChecker_Cfg.reifying);
          FStarC_TypeChecker_Cfg.compat_memo_ignore_cfg =
            (cfg_core.FStarC_TypeChecker_Cfg.compat_memo_ignore_cfg)
        } in
      new_config cfg_core'
    else cfg
let (cache_add :
  config -> FStarC_Syntax_Syntax.fv -> FStarC_TypeChecker_NBETerm.t -> unit)
  =
  fun cfg ->
    fun fv ->
      fun v ->
        let lid = (fv.FStarC_Syntax_Syntax.fv_name).FStarC_Syntax_Syntax.v in
        let uu___ = FStarC_Ident.string_of_lid lid in
        FStarC_Compiler_Util.smap_add cfg.fv_cache uu___ v
let (try_in_cache :
  config ->
    FStarC_Syntax_Syntax.fv ->
      FStarC_TypeChecker_NBETerm.t FStar_Pervasives_Native.option)
  =
  fun cfg ->
    fun fv ->
      let lid = (fv.FStarC_Syntax_Syntax.fv_name).FStarC_Syntax_Syntax.v in
      let uu___ = FStarC_Ident.string_of_lid lid in
      FStarC_Compiler_Util.smap_try_find cfg.fv_cache uu___
let (debug : config -> (unit -> unit) -> unit) =
  fun cfg -> fun f -> FStarC_TypeChecker_Cfg.log_nbe cfg.core_cfg f
let rec (unlazy_unmeta :
  FStarC_TypeChecker_NBETerm.t -> FStarC_TypeChecker_NBETerm.t) =
  fun t ->
    match t.FStarC_TypeChecker_NBETerm.nbe_t with
    | FStarC_TypeChecker_NBETerm.Lazy (uu___, t1) ->
        let uu___1 = FStarC_Thunk.force t1 in unlazy_unmeta uu___1
    | FStarC_TypeChecker_NBETerm.Meta (t0, m) ->
        let uu___ = FStarC_Thunk.force m in
        (match uu___ with
         | FStarC_Syntax_Syntax.Meta_monadic (uu___1, uu___2) -> t
         | FStarC_Syntax_Syntax.Meta_monadic_lift (uu___1, uu___2, uu___3) ->
             t
         | uu___1 -> unlazy_unmeta t0)
    | uu___ -> t
let (pickBranch :
  config ->
    FStarC_TypeChecker_NBETerm.t ->
      FStarC_Syntax_Syntax.branch Prims.list ->
        (FStarC_Syntax_Syntax.term * FStarC_TypeChecker_NBETerm.t Prims.list)
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
                   FStarC_TypeChecker_NBETerm.t_to_string scrutinee0 in
                 let uu___3 =
                   FStarC_Class_Show.show FStarC_Syntax_Print.showable_pat p in
                 FStarC_Compiler_Util.print2 "matches_pat (%s, %s)\n" uu___2
                   uu___3);
            (let scrutinee = unlazy_unmeta scrutinee0 in
             let r =
               match p.FStarC_Syntax_Syntax.v with
               | FStarC_Syntax_Syntax.Pat_var bv ->
                   FStar_Pervasives.Inl [scrutinee0]
               | FStarC_Syntax_Syntax.Pat_dot_term uu___1 ->
                   FStar_Pervasives.Inl []
               | FStarC_Syntax_Syntax.Pat_constant s ->
                   let matches_const c s1 =
                     debug cfg
                       (fun uu___2 ->
                          let uu___3 =
                            FStarC_TypeChecker_NBETerm.t_to_string c in
                          let uu___4 =
                            FStarC_Class_Show.show
                              FStarC_Syntax_Print.showable_const s1 in
                          FStarC_Compiler_Util.print2
                            "Testing term %s against pattern %s\n" uu___3
                            uu___4);
                     (match c.FStarC_TypeChecker_NBETerm.nbe_t with
                      | FStarC_TypeChecker_NBETerm.Constant
                          (FStarC_TypeChecker_NBETerm.Unit) ->
                          s1 = FStarC_Const.Const_unit
                      | FStarC_TypeChecker_NBETerm.Constant
                          (FStarC_TypeChecker_NBETerm.Bool b) ->
                          (match s1 with
                           | FStarC_Const.Const_bool p1 -> b = p1
                           | uu___2 -> false)
                      | FStarC_TypeChecker_NBETerm.Constant
                          (FStarC_TypeChecker_NBETerm.Int i) ->
                          (match s1 with
                           | FStarC_Const.Const_int
                               (p1, FStar_Pervasives_Native.None) ->
                               let uu___2 =
                                 FStarC_BigInt.big_int_of_string p1 in
                               i = uu___2
                           | uu___2 -> false)
                      | FStarC_TypeChecker_NBETerm.Constant
                          (FStarC_TypeChecker_NBETerm.String (st, uu___2)) ->
                          (match s1 with
                           | FStarC_Const.Const_string (p1, uu___3) ->
                               st = p1
                           | uu___3 -> false)
                      | FStarC_TypeChecker_NBETerm.Constant
                          (FStarC_TypeChecker_NBETerm.Char c1) ->
                          (match s1 with
                           | FStarC_Const.Const_char p1 -> c1 = p1
                           | uu___2 -> false)
                      | uu___2 -> false) in
                   let uu___1 = matches_const scrutinee s in
                   if uu___1
                   then FStar_Pervasives.Inl []
                   else FStar_Pervasives.Inr false
               | FStarC_Syntax_Syntax.Pat_cons (fv, _us_opt, arg_pats) ->
                   let rec matches_args out a p1 =
                     match (a, p1) with
                     | ([], []) -> FStar_Pervasives.Inl out
                     | ((t, uu___1)::rest_a, (p2, uu___2)::rest_p) ->
                         let uu___3 = matches_pat t p2 in
                         (match uu___3 with
                          | FStar_Pervasives.Inl s ->
                              matches_args (FStarC_Compiler_List.op_At out s)
                                rest_a rest_p
                          | m -> m)
                     | uu___1 -> FStar_Pervasives.Inr false in
                   (match scrutinee.FStarC_TypeChecker_NBETerm.nbe_t with
                    | FStarC_TypeChecker_NBETerm.Construct
                        (fv', _us, args_rev) ->
                        let uu___1 = FStarC_Syntax_Syntax.fv_eq fv fv' in
                        if uu___1
                        then
                          matches_args [] (FStarC_Compiler_List.rev args_rev)
                            arg_pats
                        else FStar_Pervasives.Inr false
                    | uu___1 -> FStar_Pervasives.Inr true) in
             let res_to_string uu___1 =
               match uu___1 with
               | FStar_Pervasives.Inr b ->
                   let uu___2 = FStarC_Compiler_Util.string_of_bool b in
                   Prims.strcat "Inr " uu___2
               | FStar_Pervasives.Inl bs ->
                   let uu___2 =
                     FStarC_Compiler_Util.string_of_int
                       (FStarC_Compiler_List.length bs) in
                   Prims.strcat "Inl " uu___2 in
             debug cfg
               (fun uu___2 ->
                  let uu___3 =
                    FStarC_TypeChecker_NBETerm.t_to_string scrutinee in
                  let uu___4 =
                    FStarC_Class_Show.show FStarC_Syntax_Print.showable_pat p in
                  let uu___5 = res_to_string r in
                  FStarC_Compiler_Util.print3 "matches_pat (%s, %s) = %s\n"
                    uu___3 uu___4 uu___5);
             r) in
          match branches1 with
          | [] -> FStar_Pervasives_Native.None
          | (p, _wopt, e)::branches2 ->
              let uu___ = matches_pat scrut1 p in
              (match uu___ with
               | FStar_Pervasives.Inl matches ->
                   (debug cfg
                      (fun uu___2 ->
                         let uu___3 =
                           FStarC_Class_Show.show
                             FStarC_Syntax_Print.showable_pat p in
                         FStarC_Compiler_Util.print1 "Pattern %s matches\n"
                           uu___3);
                    FStar_Pervasives_Native.Some (e, matches))
               | FStar_Pervasives.Inr (false) ->
                   pickBranch_aux scrut1 branches2 branches0
               | FStar_Pervasives.Inr (true) -> FStar_Pervasives_Native.None) in
        pickBranch_aux scrut branches branches
let (should_reduce_recursive_definition :
  FStarC_TypeChecker_NBETerm.args ->
    Prims.bool Prims.list ->
      (Prims.bool * FStarC_TypeChecker_NBETerm.args *
        FStarC_TypeChecker_NBETerm.args))
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
                (FStarC_TypeChecker_NBETerm.isAccu
                   (FStar_Pervasives_Native.fst t)) in
            if uu___
            then (false, (FStarC_Compiler_List.rev_append ts1 acc), [])
            else aux ts1 bs (t :: acc) in
      aux arguments formals_in_decreases []
let (find_sigelt_in_gamma :
  config ->
    FStarC_TypeChecker_Env.env ->
      FStarC_Ident.lident ->
        FStarC_Syntax_Syntax.sigelt FStar_Pervasives_Native.option)
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
                         let uu___3 =
                           FStarC_Class_Show.show
                             (FStarC_Class_Show.show_list
                                FStarC_Syntax_Print.showable_univ) us in
                         FStarC_Compiler_Util.print1
                           "Universes in local declaration: %s\n" uu___3);
                    FStar_Pervasives_Native.Some elt)
               | uu___1 -> FStar_Pervasives_Native.None) in
        let uu___ = FStarC_TypeChecker_Env.lookup_qname env lid in
        FStarC_Compiler_Util.bind_opt uu___ mapper
let (is_univ : FStarC_TypeChecker_NBETerm.t -> Prims.bool) =
  fun tm ->
    match tm.FStarC_TypeChecker_NBETerm.nbe_t with
    | FStarC_TypeChecker_NBETerm.Univ uu___ -> true
    | uu___ -> false
let (un_univ : FStarC_TypeChecker_NBETerm.t -> FStarC_Syntax_Syntax.universe)
  =
  fun tm ->
    match tm.FStarC_TypeChecker_NBETerm.nbe_t with
    | FStarC_TypeChecker_NBETerm.Univ u -> u
    | uu___ ->
        let uu___1 =
          let uu___2 = FStarC_TypeChecker_NBETerm.t_to_string tm in
          Prims.strcat "Not a universe: " uu___2 in
        failwith uu___1
let (is_constr_fv : FStarC_Syntax_Syntax.fv -> Prims.bool) =
  fun fvar ->
    fvar.FStarC_Syntax_Syntax.fv_qual =
      (FStar_Pervasives_Native.Some FStarC_Syntax_Syntax.Data_ctor)
let (is_constr : FStarC_TypeChecker_Env.qninfo -> Prims.bool) =
  fun q ->
    match q with
    | FStar_Pervasives_Native.Some
        (FStar_Pervasives.Inr
         ({
            FStarC_Syntax_Syntax.sigel = FStarC_Syntax_Syntax.Sig_datacon
              uu___;
            FStarC_Syntax_Syntax.sigrng = uu___1;
            FStarC_Syntax_Syntax.sigquals = uu___2;
            FStarC_Syntax_Syntax.sigmeta = uu___3;
            FStarC_Syntax_Syntax.sigattrs = uu___4;
            FStarC_Syntax_Syntax.sigopens_and_abbrevs = uu___5;
            FStarC_Syntax_Syntax.sigopts = uu___6;_},
          uu___7),
         uu___8)
        -> true
    | uu___ -> false
let (translate_univ :
  config ->
    FStarC_TypeChecker_NBETerm.t Prims.list ->
      FStarC_Syntax_Syntax.universe -> FStarC_Syntax_Syntax.universe)
  =
  fun cfg ->
    fun bs ->
      fun u ->
        let rec aux u1 =
          let u2 = FStarC_Syntax_Subst.compress_univ u1 in
          match u2 with
          | FStarC_Syntax_Syntax.U_bvar i ->
              if i < (FStarC_Compiler_List.length bs)
              then let u' = FStarC_Compiler_List.nth bs i in un_univ u'
              else
                if
                  ((cfg.core_cfg).FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.allow_unbound_universes
                then FStarC_Syntax_Syntax.U_zero
                else failwith "Universe index out of bounds"
          | FStarC_Syntax_Syntax.U_succ u3 ->
              let uu___ = aux u3 in FStarC_Syntax_Syntax.U_succ uu___
          | FStarC_Syntax_Syntax.U_max us ->
              let uu___ = FStarC_Compiler_List.map aux us in
              FStarC_Syntax_Syntax.U_max uu___
          | FStarC_Syntax_Syntax.U_unknown -> u2
          | FStarC_Syntax_Syntax.U_name uu___ -> u2
          | FStarC_Syntax_Syntax.U_unif uu___ -> u2
          | FStarC_Syntax_Syntax.U_zero -> u2 in
        aux u
let (find_let :
  FStarC_Syntax_Syntax.letbinding Prims.list ->
    FStarC_Syntax_Syntax.fv ->
      FStarC_Syntax_Syntax.letbinding FStar_Pervasives_Native.option)
  =
  fun lbs ->
    fun fvar ->
      FStarC_Compiler_Util.find_map lbs
        (fun lb ->
           match lb.FStarC_Syntax_Syntax.lbname with
           | FStar_Pervasives.Inl uu___ -> failwith "find_let : impossible"
           | FStar_Pervasives.Inr name ->
               let uu___ = FStarC_Syntax_Syntax.fv_eq name fvar in
               if uu___
               then FStar_Pervasives_Native.Some lb
               else FStar_Pervasives_Native.None)
let (mk_rt :
  FStarC_Compiler_Range_Type.range ->
    FStarC_TypeChecker_NBETerm.t' -> FStarC_TypeChecker_NBETerm.t)
  =
  fun r ->
    fun t ->
      {
        FStarC_TypeChecker_NBETerm.nbe_t = t;
        FStarC_TypeChecker_NBETerm.nbe_r = r
      }
let (mk_t : FStarC_TypeChecker_NBETerm.t' -> FStarC_TypeChecker_NBETerm.t) =
  fun t ->
    {
      FStarC_TypeChecker_NBETerm.nbe_t = t;
      FStarC_TypeChecker_NBETerm.nbe_r =
        FStarC_Compiler_Range_Type.dummyRange
    }
let rec (translate :
  config ->
    FStarC_TypeChecker_NBETerm.t Prims.list ->
      FStarC_Syntax_Syntax.term -> FStarC_TypeChecker_NBETerm.t)
  =
  fun cfg ->
    fun bs ->
      fun e ->
        let debug1 = debug cfg in
        let mk_t1 t = mk_rt e.FStarC_Syntax_Syntax.pos t in
        debug1
          (fun uu___1 ->
             let uu___2 =
               let uu___3 = FStarC_Syntax_Subst.compress e in
               FStarC_Class_Tagged.tag_of FStarC_Syntax_Syntax.tagged_term
                 uu___3 in
             let uu___3 =
               let uu___4 = FStarC_Syntax_Subst.compress e in
               FStarC_Class_Show.show FStarC_Syntax_Print.showable_term
                 uu___4 in
             FStarC_Compiler_Util.print2 "Term: %s - %s\n" uu___2 uu___3);
        (let uu___1 =
           let uu___2 = FStarC_Syntax_Subst.compress e in
           uu___2.FStarC_Syntax_Syntax.n in
         match uu___1 with
         | FStarC_Syntax_Syntax.Tm_delayed uu___2 ->
             failwith "Tm_delayed: Impossible"
         | FStarC_Syntax_Syntax.Tm_unknown ->
             mk_t1 FStarC_TypeChecker_NBETerm.Unknown
         | FStarC_Syntax_Syntax.Tm_constant c ->
             let uu___2 =
               let uu___3 = translate_constant c in
               FStarC_TypeChecker_NBETerm.Constant uu___3 in
             mk_t1 uu___2
         | FStarC_Syntax_Syntax.Tm_bvar db ->
             if
               db.FStarC_Syntax_Syntax.index <
                 (FStarC_Compiler_List.length bs)
             then
               let t =
                 FStarC_Compiler_List.nth bs db.FStarC_Syntax_Syntax.index in
               (debug1
                  (fun uu___3 ->
                     let uu___4 = FStarC_TypeChecker_NBETerm.t_to_string t in
                     let uu___5 =
                       let uu___6 =
                         FStarC_Compiler_List.map
                           FStarC_TypeChecker_NBETerm.t_to_string bs in
                       FStarC_Compiler_String.concat "; " uu___6 in
                     FStarC_Compiler_Util.print2
                       "Resolved bvar to %s\n\tcontext is [%s]\n" uu___4
                       uu___5);
                t)
             else failwith "de Bruijn index out of bounds"
         | FStarC_Syntax_Syntax.Tm_uinst (t, us) ->
             (debug1
                (fun uu___3 ->
                   let uu___4 =
                     FStarC_Class_Show.show FStarC_Syntax_Print.showable_term
                       t in
                   let uu___5 =
                     let uu___6 =
                       FStarC_Compiler_List.map
                         (FStarC_Class_Show.show
                            FStarC_Syntax_Print.showable_univ) us in
                     FStarC_Compiler_String.concat ", " uu___6 in
                   FStarC_Compiler_Util.print2
                     "Uinst term : %s\nUnivs : %s\n" uu___4 uu___5);
              (let uu___3 = translate cfg bs t in
               let uu___4 =
                 FStarC_Compiler_List.map
                   (fun x ->
                      let uu___5 =
                        let uu___6 =
                          let uu___7 = translate_univ cfg bs x in
                          FStarC_TypeChecker_NBETerm.Univ uu___7 in
                        mk_t1 uu___6 in
                      FStarC_TypeChecker_NBETerm.as_arg uu___5) us in
               iapp cfg uu___3 uu___4))
         | FStarC_Syntax_Syntax.Tm_type u ->
             let uu___2 =
               let uu___3 = translate_univ cfg bs u in
               FStarC_TypeChecker_NBETerm.Type_t uu___3 in
             mk_t1 uu___2
         | FStarC_Syntax_Syntax.Tm_arrow
             { FStarC_Syntax_Syntax.bs1 = xs;
               FStarC_Syntax_Syntax.comp = c;_}
             ->
             let norm uu___2 =
               let uu___3 =
                 FStarC_Compiler_List.fold_left
                   (fun uu___4 ->
                      fun b ->
                        match uu___4 with
                        | (ctx, binders_rev) ->
                            let x = b.FStarC_Syntax_Syntax.binder_bv in
                            let t =
                              let uu___5 =
                                translate cfg ctx x.FStarC_Syntax_Syntax.sort in
                              readback cfg uu___5 in
                            let x1 =
                              let uu___5 = FStarC_Syntax_Syntax.freshen_bv x in
                              {
                                FStarC_Syntax_Syntax.ppname =
                                  (uu___5.FStarC_Syntax_Syntax.ppname);
                                FStarC_Syntax_Syntax.index =
                                  (uu___5.FStarC_Syntax_Syntax.index);
                                FStarC_Syntax_Syntax.sort = t
                              } in
                            let ctx1 =
                              let uu___5 =
                                FStarC_TypeChecker_NBETerm.mkAccuVar x1 in
                              uu___5 :: ctx in
                            (ctx1,
                              ({
                                 FStarC_Syntax_Syntax.binder_bv = x1;
                                 FStarC_Syntax_Syntax.binder_qual =
                                   (b.FStarC_Syntax_Syntax.binder_qual);
                                 FStarC_Syntax_Syntax.binder_positivity =
                                   (b.FStarC_Syntax_Syntax.binder_positivity);
                                 FStarC_Syntax_Syntax.binder_attrs =
                                   (b.FStarC_Syntax_Syntax.binder_attrs)
                               } :: binders_rev))) (bs, []) xs in
               match uu___3 with
               | (ctx, binders_rev) ->
                   let c1 =
                     let uu___4 = translate_comp cfg ctx c in
                     readback_comp cfg uu___4 in
                   FStarC_Syntax_Util.arrow
                     (FStarC_Compiler_List.rev binders_rev) c1 in
             let uu___2 =
               let uu___3 =
                 let uu___4 = FStarC_Thunk.mk norm in
                 FStar_Pervasives.Inl uu___4 in
               FStarC_TypeChecker_NBETerm.Arrow uu___3 in
             mk_t1 uu___2
         | FStarC_Syntax_Syntax.Tm_refine
             { FStarC_Syntax_Syntax.b = bv; FStarC_Syntax_Syntax.phi = tm;_}
             ->
             if
               ((cfg.core_cfg).FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.for_extraction
                 ||
                 ((cfg.core_cfg).FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.unrefine
             then translate cfg bs bv.FStarC_Syntax_Syntax.sort
             else
               mk_t1
                 (FStarC_TypeChecker_NBETerm.Refinement
                    ((fun y -> translate cfg (y :: bs) tm),
                      (fun uu___3 ->
                         let uu___4 =
                           translate cfg bs bv.FStarC_Syntax_Syntax.sort in
                         FStarC_TypeChecker_NBETerm.as_arg uu___4)))
         | FStarC_Syntax_Syntax.Tm_ascribed
             { FStarC_Syntax_Syntax.tm = t;
               FStarC_Syntax_Syntax.asc = uu___2;
               FStarC_Syntax_Syntax.eff_opt = uu___3;_}
             -> translate cfg bs t
         | FStarC_Syntax_Syntax.Tm_uvar (u, (subst, set_use_range)) ->
             let norm_uvar uu___2 =
               let norm_subst_elt uu___3 =
                 match uu___3 with
                 | FStarC_Syntax_Syntax.NT (x, t) ->
                     let uu___4 =
                       let uu___5 =
                         let uu___6 = translate cfg bs t in
                         readback cfg uu___6 in
                       (x, uu___5) in
                     FStarC_Syntax_Syntax.NT uu___4
                 | FStarC_Syntax_Syntax.NM (x, i) ->
                     let x_i =
                       FStarC_Syntax_Syntax.bv_to_tm
                         {
                           FStarC_Syntax_Syntax.ppname =
                             (x.FStarC_Syntax_Syntax.ppname);
                           FStarC_Syntax_Syntax.index = i;
                           FStarC_Syntax_Syntax.sort =
                             (x.FStarC_Syntax_Syntax.sort)
                         } in
                     let t =
                       let uu___4 = translate cfg bs x_i in
                       readback cfg uu___4 in
                     (match t.FStarC_Syntax_Syntax.n with
                      | FStarC_Syntax_Syntax.Tm_bvar x_j ->
                          FStarC_Syntax_Syntax.NM
                            (x, (x_j.FStarC_Syntax_Syntax.index))
                      | uu___4 -> FStarC_Syntax_Syntax.NT (x, t))
                 | uu___4 ->
                     failwith "Impossible: subst invariant of uvar nodes" in
               let subst1 =
                 FStarC_Compiler_List.map
                   (FStarC_Compiler_List.map norm_subst_elt) subst in
               {
                 FStarC_Syntax_Syntax.n =
                   (FStarC_Syntax_Syntax.Tm_uvar (u, (subst1, set_use_range)));
                 FStarC_Syntax_Syntax.pos = (e.FStarC_Syntax_Syntax.pos);
                 FStarC_Syntax_Syntax.vars = (e.FStarC_Syntax_Syntax.vars);
                 FStarC_Syntax_Syntax.hash_code =
                   (e.FStarC_Syntax_Syntax.hash_code)
               } in
             let uu___2 =
               let uu___3 =
                 let uu___4 =
                   let uu___5 = FStarC_Thunk.mk norm_uvar in
                   FStarC_TypeChecker_NBETerm.UVar uu___5 in
                 (uu___4, []) in
               FStarC_TypeChecker_NBETerm.Accu uu___3 in
             mk_t1 uu___2
         | FStarC_Syntax_Syntax.Tm_name x ->
             FStarC_TypeChecker_NBETerm.mkAccuVar x
         | FStarC_Syntax_Syntax.Tm_abs
             { FStarC_Syntax_Syntax.bs = [];
               FStarC_Syntax_Syntax.body = uu___2;
               FStarC_Syntax_Syntax.rc_opt = uu___3;_}
             -> failwith "Impossible: abstraction with no binders"
         | FStarC_Syntax_Syntax.Tm_abs
             { FStarC_Syntax_Syntax.bs = xs;
               FStarC_Syntax_Syntax.body = body;
               FStarC_Syntax_Syntax.rc_opt = resc;_}
             ->
             mk_t1
               (FStarC_TypeChecker_NBETerm.Lam
                  {
                    FStarC_TypeChecker_NBETerm.interp =
                      (fun ys ->
                         let uu___2 =
                           let uu___3 =
                             FStarC_Compiler_List.map
                               FStar_Pervasives_Native.fst ys in
                           FStarC_Compiler_List.append uu___3 bs in
                         translate cfg uu___2 body);
                    FStarC_TypeChecker_NBETerm.shape =
                      (FStarC_TypeChecker_NBETerm.Lam_bs (bs, xs, resc));
                    FStarC_TypeChecker_NBETerm.arity =
                      (FStarC_Compiler_List.length xs)
                  })
         | FStarC_Syntax_Syntax.Tm_fvar fvar ->
             let uu___2 = try_in_cache cfg fvar in
             (match uu___2 with
              | FStar_Pervasives_Native.Some t -> t
              | uu___3 ->
                  let uu___4 =
                    FStarC_Syntax_Syntax.set_range_of_fv fvar
                      e.FStarC_Syntax_Syntax.pos in
                  translate_fv cfg bs uu___4)
         | FStarC_Syntax_Syntax.Tm_app
             {
               FStarC_Syntax_Syntax.hd =
                 {
                   FStarC_Syntax_Syntax.n = FStarC_Syntax_Syntax.Tm_constant
                     (FStarC_Const.Const_reify uu___2);
                   FStarC_Syntax_Syntax.pos = uu___3;
                   FStarC_Syntax_Syntax.vars = uu___4;
                   FStarC_Syntax_Syntax.hash_code = uu___5;_};
               FStarC_Syntax_Syntax.args = arg::more::args;_}
             ->
             let uu___6 = FStarC_Syntax_Util.head_and_args e in
             (match uu___6 with
              | (head, uu___7) ->
                  let head1 =
                    FStarC_Syntax_Syntax.mk_Tm_app head [arg]
                      e.FStarC_Syntax_Syntax.pos in
                  let uu___8 =
                    FStarC_Syntax_Syntax.mk_Tm_app head1 (more :: args)
                      e.FStarC_Syntax_Syntax.pos in
                  translate cfg bs uu___8)
         | FStarC_Syntax_Syntax.Tm_app
             {
               FStarC_Syntax_Syntax.hd =
                 {
                   FStarC_Syntax_Syntax.n = FStarC_Syntax_Syntax.Tm_constant
                     (FStarC_Const.Const_reflect uu___2);
                   FStarC_Syntax_Syntax.pos = uu___3;
                   FStarC_Syntax_Syntax.vars = uu___4;
                   FStarC_Syntax_Syntax.hash_code = uu___5;_};
               FStarC_Syntax_Syntax.args = arg::more::args;_}
             ->
             let uu___6 = FStarC_Syntax_Util.head_and_args e in
             (match uu___6 with
              | (head, uu___7) ->
                  let head1 =
                    FStarC_Syntax_Syntax.mk_Tm_app head [arg]
                      e.FStarC_Syntax_Syntax.pos in
                  let uu___8 =
                    FStarC_Syntax_Syntax.mk_Tm_app head1 (more :: args)
                      e.FStarC_Syntax_Syntax.pos in
                  translate cfg bs uu___8)
         | FStarC_Syntax_Syntax.Tm_app
             {
               FStarC_Syntax_Syntax.hd =
                 {
                   FStarC_Syntax_Syntax.n = FStarC_Syntax_Syntax.Tm_constant
                     (FStarC_Const.Const_reflect uu___2);
                   FStarC_Syntax_Syntax.pos = uu___3;
                   FStarC_Syntax_Syntax.vars = uu___4;
                   FStarC_Syntax_Syntax.hash_code = uu___5;_};
               FStarC_Syntax_Syntax.args = arg::[];_}
             when (cfg.core_cfg).FStarC_TypeChecker_Cfg.reifying ->
             let cfg1 = reifying_false cfg in
             translate cfg1 bs (FStar_Pervasives_Native.fst arg)
         | FStarC_Syntax_Syntax.Tm_app
             {
               FStarC_Syntax_Syntax.hd =
                 {
                   FStarC_Syntax_Syntax.n = FStarC_Syntax_Syntax.Tm_constant
                     (FStarC_Const.Const_reflect uu___2);
                   FStarC_Syntax_Syntax.pos = uu___3;
                   FStarC_Syntax_Syntax.vars = uu___4;
                   FStarC_Syntax_Syntax.hash_code = uu___5;_};
               FStarC_Syntax_Syntax.args = arg::[];_}
             ->
             let uu___6 =
               let uu___7 =
                 translate cfg bs (FStar_Pervasives_Native.fst arg) in
               FStarC_TypeChecker_NBETerm.Reflect uu___7 in
             mk_t1 uu___6
         | FStarC_Syntax_Syntax.Tm_app
             {
               FStarC_Syntax_Syntax.hd =
                 {
                   FStarC_Syntax_Syntax.n = FStarC_Syntax_Syntax.Tm_constant
                     (FStarC_Const.Const_reify uu___2);
                   FStarC_Syntax_Syntax.pos = uu___3;
                   FStarC_Syntax_Syntax.vars = uu___4;
                   FStarC_Syntax_Syntax.hash_code = uu___5;_};
               FStarC_Syntax_Syntax.args = arg::[];_}
             when
             ((cfg.core_cfg).FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.reify_
             ->
             let cfg1 = reifying_true cfg in
             translate cfg1 bs (FStar_Pervasives_Native.fst arg)
         | FStarC_Syntax_Syntax.Tm_app
             {
               FStarC_Syntax_Syntax.hd =
                 {
                   FStarC_Syntax_Syntax.n = FStarC_Syntax_Syntax.Tm_constant
                     (FStarC_Const.Const_reflect uu___2);
                   FStarC_Syntax_Syntax.pos = uu___3;
                   FStarC_Syntax_Syntax.vars = uu___4;
                   FStarC_Syntax_Syntax.hash_code = uu___5;_};
               FStarC_Syntax_Syntax.args = arg::[];_}
             ->
             let uu___6 =
               let uu___7 =
                 translate cfg bs (FStar_Pervasives_Native.fst arg) in
               FStarC_TypeChecker_NBETerm.Reflect uu___7 in
             mk_t1 uu___6
         | FStarC_Syntax_Syntax.Tm_app
             {
               FStarC_Syntax_Syntax.hd =
                 { FStarC_Syntax_Syntax.n = FStarC_Syntax_Syntax.Tm_fvar fv;
                   FStarC_Syntax_Syntax.pos = uu___2;
                   FStarC_Syntax_Syntax.vars = uu___3;
                   FStarC_Syntax_Syntax.hash_code = uu___4;_};
               FStarC_Syntax_Syntax.args = uu___5::[];_}
             when
             (FStarC_Syntax_Syntax.fv_eq_lid fv
                FStarC_Parser_Const.assert_lid)
               ||
               (FStarC_Syntax_Syntax.fv_eq_lid fv
                  FStarC_Parser_Const.assert_norm_lid)
             ->
             (debug1
                (fun uu___7 ->
                   FStarC_Compiler_Util.print_string "Eliminated assertion\n");
              mk_t1
                (FStarC_TypeChecker_NBETerm.Constant
                   FStarC_TypeChecker_NBETerm.Unit))
         | FStarC_Syntax_Syntax.Tm_app
             { FStarC_Syntax_Syntax.hd = head;
               FStarC_Syntax_Syntax.args = args;_}
             when
             ((let uu___2 = FStarC_TypeChecker_Cfg.cfg_env cfg.core_cfg in
               uu___2.FStarC_TypeChecker_Env.erase_erasable_args) ||
                ((cfg.core_cfg).FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.for_extraction)
               ||
               ((cfg.core_cfg).FStarC_TypeChecker_Cfg.debug).FStarC_TypeChecker_Cfg.erase_erasable_args
             ->
             let uu___2 = translate cfg bs head in
             let uu___3 =
               FStarC_Compiler_List.map
                 (fun x ->
                    let uu___4 =
                      FStarC_Syntax_Util.aqual_is_erasable
                        (FStar_Pervasives_Native.snd x) in
                    if uu___4
                    then
                      (debug1
                         (fun uu___6 ->
                            let uu___7 =
                              FStarC_Class_Show.show
                                FStarC_Syntax_Print.showable_term
                                (FStar_Pervasives_Native.fst x) in
                            FStarC_Compiler_Util.print1 "Erasing %s\n" uu___7);
                       ((mk_t1
                           (FStarC_TypeChecker_NBETerm.Constant
                              FStarC_TypeChecker_NBETerm.Unit)),
                         (FStar_Pervasives_Native.snd x)))
                    else
                      (let uu___6 =
                         translate cfg bs (FStar_Pervasives_Native.fst x) in
                       (uu___6, (FStar_Pervasives_Native.snd x)))) args in
             iapp cfg uu___2 uu___3
         | FStarC_Syntax_Syntax.Tm_app
             { FStarC_Syntax_Syntax.hd = head;
               FStarC_Syntax_Syntax.args = args;_}
             ->
             (debug1
                (fun uu___3 ->
                   let uu___4 =
                     FStarC_Class_Show.show FStarC_Syntax_Print.showable_term
                       head in
                   let uu___5 =
                     FStarC_Class_Show.show
                       (FStarC_Class_Show.show_list
                          (FStarC_Class_Show.show_tuple2
                             FStarC_Syntax_Print.showable_term
                             FStarC_Syntax_Print.showable_aqual)) args in
                   FStarC_Compiler_Util.print2 "Application: %s @ %s\n"
                     uu___4 uu___5);
              (let uu___3 = translate cfg bs head in
               let uu___4 =
                 FStarC_Compiler_List.map
                   (fun x ->
                      let uu___5 =
                        translate cfg bs (FStar_Pervasives_Native.fst x) in
                      (uu___5, (FStar_Pervasives_Native.snd x))) args in
               iapp cfg uu___3 uu___4))
         | FStarC_Syntax_Syntax.Tm_match
             { FStarC_Syntax_Syntax.scrutinee = scrut;
               FStarC_Syntax_Syntax.ret_opt = ret_opt;
               FStarC_Syntax_Syntax.brs = branches;
               FStarC_Syntax_Syntax.rc_opt1 = rc;_}
             ->
             let make_returns uu___2 =
               match ret_opt with
               | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some (b, asc) ->
                   let uu___3 =
                     let x =
                       let uu___4 =
                         let uu___5 =
                           translate cfg bs
                             (b.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort in
                         readback cfg uu___5 in
                       FStarC_Syntax_Syntax.gen_bv'
                         (b.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.ppname
                         FStar_Pervasives_Native.None uu___4 in
                     let uu___4 = FStarC_Syntax_Syntax.mk_binder x in
                     let uu___5 =
                       let uu___6 = FStarC_TypeChecker_NBETerm.mkAccuVar x in
                       uu___6 :: bs in
                     (uu___4, uu___5) in
                   (match uu___3 with
                    | (b1, bs1) ->
                        let asc1 =
                          match asc with
                          | (FStar_Pervasives.Inl t, tacopt, use_eq) ->
                              let uu___4 =
                                let uu___5 =
                                  let uu___6 = translate cfg bs1 t in
                                  readback cfg uu___6 in
                                FStar_Pervasives.Inl uu___5 in
                              (uu___4, tacopt, use_eq)
                          | (FStar_Pervasives.Inr c, tacopt, use_eq) ->
                              let uu___4 =
                                let uu___5 =
                                  let uu___6 = translate_comp cfg bs1 c in
                                  readback_comp cfg uu___6 in
                                FStar_Pervasives.Inr uu___5 in
                              (uu___4, tacopt, use_eq) in
                        let asc2 =
                          FStarC_Syntax_Subst.close_ascription [b1] asc1 in
                        let b2 =
                          let uu___4 = FStarC_Syntax_Subst.close_binders [b1] in
                          FStarC_Compiler_List.hd uu___4 in
                        FStar_Pervasives_Native.Some (b2, asc2)) in
             let make_rc uu___2 =
               match rc with
               | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some rc1 ->
                   let uu___3 =
                     let uu___4 = translate_residual_comp cfg bs rc1 in
                     readback_residual_comp cfg uu___4 in
                   FStar_Pervasives_Native.Some uu___3 in
             let make_branches uu___2 =
               let cfg1 = zeta_false cfg in
               let rec process_pattern bs1 p =
                 let uu___3 =
                   match p.FStarC_Syntax_Syntax.v with
                   | FStarC_Syntax_Syntax.Pat_constant c ->
                       (bs1, (FStarC_Syntax_Syntax.Pat_constant c))
                   | FStarC_Syntax_Syntax.Pat_cons (fvar, us_opt, args) ->
                       let uu___4 =
                         FStarC_Compiler_List.fold_left
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
                            let us_opt1 =
                              match us_opt with
                              | FStar_Pervasives_Native.None ->
                                  FStar_Pervasives_Native.None
                              | FStar_Pervasives_Native.Some us ->
                                  let uu___5 =
                                    FStarC_Compiler_List.map
                                      (translate_univ cfg1 bs1) us in
                                  FStar_Pervasives_Native.Some uu___5 in
                            (bs',
                              (FStarC_Syntax_Syntax.Pat_cons
                                 (fvar, us_opt1,
                                   (FStarC_Compiler_List.rev args')))))
                   | FStarC_Syntax_Syntax.Pat_var bvar ->
                       let x =
                         let uu___4 =
                           let uu___5 =
                             translate cfg1 bs1
                               bvar.FStarC_Syntax_Syntax.sort in
                           readback cfg1 uu___5 in
                         FStarC_Syntax_Syntax.gen_bv'
                           bvar.FStarC_Syntax_Syntax.ppname
                           FStar_Pervasives_Native.None uu___4 in
                       let uu___4 =
                         let uu___5 = FStarC_TypeChecker_NBETerm.mkAccuVar x in
                         uu___5 :: bs1 in
                       (uu___4, (FStarC_Syntax_Syntax.Pat_var x))
                   | FStarC_Syntax_Syntax.Pat_dot_term eopt ->
                       let uu___4 =
                         let uu___5 =
                           FStarC_Compiler_Util.map_option
                             (fun e1 ->
                                let uu___6 = translate cfg1 bs1 e1 in
                                readback cfg1 uu___6) eopt in
                         FStarC_Syntax_Syntax.Pat_dot_term uu___5 in
                       (bs1, uu___4) in
                 match uu___3 with
                 | (bs2, p_new) ->
                     (bs2,
                       {
                         FStarC_Syntax_Syntax.v = p_new;
                         FStarC_Syntax_Syntax.p = (p.FStarC_Syntax_Syntax.p)
                       }) in
               FStarC_Compiler_List.map
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
                             FStarC_Syntax_Util.branch uu___5)) branches in
             let scrut1 = translate cfg bs scrut in
             (debug1
                (fun uu___3 ->
                   let uu___4 =
                     FStarC_Compiler_Range_Ops.string_of_range
                       e.FStarC_Syntax_Syntax.pos in
                   let uu___5 =
                     FStarC_Class_Show.show FStarC_Syntax_Print.showable_term
                       e in
                   FStarC_Compiler_Util.print2 "%s: Translating match %s\n"
                     uu___4 uu___5);
              (let scrut2 = unlazy_unmeta scrut1 in
               match scrut2.FStarC_TypeChecker_NBETerm.nbe_t with
               | FStarC_TypeChecker_NBETerm.Construct (c, us, args) ->
                   (debug1
                      (fun uu___4 ->
                         let uu___5 =
                           let uu___6 =
                             FStarC_Compiler_List.map
                               (fun uu___7 ->
                                  match uu___7 with
                                  | (x, q) ->
                                      let uu___8 =
                                        FStarC_TypeChecker_NBETerm.t_to_string
                                          x in
                                      Prims.strcat
                                        (if FStarC_Compiler_Util.is_some q
                                         then "#"
                                         else "") uu___8) args in
                           FStarC_Compiler_String.concat "; " uu___6 in
                         FStarC_Compiler_Util.print1 "Match args: %s\n"
                           uu___5);
                    (let uu___4 = pickBranch cfg scrut2 branches in
                     match uu___4 with
                     | FStar_Pervasives_Native.Some (branch, args1) ->
                         let uu___5 =
                           FStarC_Compiler_List.fold_left
                             (fun bs1 -> fun x -> x :: bs1) bs args1 in
                         translate cfg uu___5 branch
                     | FStar_Pervasives_Native.None ->
                         FStarC_TypeChecker_NBETerm.mkAccuMatch scrut2
                           make_returns make_branches make_rc))
               | FStarC_TypeChecker_NBETerm.Constant c ->
                   (debug1
                      (fun uu___4 ->
                         let uu___5 =
                           FStarC_TypeChecker_NBETerm.t_to_string scrut2 in
                         FStarC_Compiler_Util.print1 "Match constant : %s\n"
                           uu___5);
                    (let uu___4 = pickBranch cfg scrut2 branches in
                     match uu___4 with
                     | FStar_Pervasives_Native.Some (branch, []) ->
                         translate cfg bs branch
                     | FStar_Pervasives_Native.Some (branch, arg::[]) ->
                         translate cfg (arg :: bs) branch
                     | FStar_Pervasives_Native.None ->
                         FStarC_TypeChecker_NBETerm.mkAccuMatch scrut2
                           make_returns make_branches make_rc
                     | FStar_Pervasives_Native.Some (uu___5, hd::tl) ->
                         failwith
                           "Impossible: Matching on constants cannot bind more than one variable"))
               | uu___3 ->
                   FStarC_TypeChecker_NBETerm.mkAccuMatch scrut2 make_returns
                     make_branches make_rc))
         | FStarC_Syntax_Syntax.Tm_meta
             { FStarC_Syntax_Syntax.tm2 = e1;
               FStarC_Syntax_Syntax.meta = FStarC_Syntax_Syntax.Meta_monadic
                 (m, t);_}
             when (cfg.core_cfg).FStarC_TypeChecker_Cfg.reifying ->
             translate_monadic (m, t) cfg bs e1
         | FStarC_Syntax_Syntax.Tm_meta
             { FStarC_Syntax_Syntax.tm2 = e1;
               FStarC_Syntax_Syntax.meta =
                 FStarC_Syntax_Syntax.Meta_monadic_lift (m, m', t);_}
             when (cfg.core_cfg).FStarC_TypeChecker_Cfg.reifying ->
             translate_monadic_lift (m, m', t) cfg bs e1
         | FStarC_Syntax_Syntax.Tm_meta
             { FStarC_Syntax_Syntax.tm2 = e1;
               FStarC_Syntax_Syntax.meta = meta;_}
             ->
             let norm_meta uu___2 =
               let norm t =
                 let uu___3 = translate cfg bs t in readback cfg uu___3 in
               match meta with
               | FStarC_Syntax_Syntax.Meta_named uu___3 -> meta
               | FStarC_Syntax_Syntax.Meta_labeled uu___3 -> meta
               | FStarC_Syntax_Syntax.Meta_desugared uu___3 -> meta
               | FStarC_Syntax_Syntax.Meta_pattern (ts, args) ->
                   let uu___3 =
                     let uu___4 = FStarC_Compiler_List.map norm ts in
                     let uu___5 =
                       FStarC_Compiler_List.map
                         (FStarC_Compiler_List.map
                            (fun uu___6 ->
                               match uu___6 with
                               | (t, a) -> let uu___7 = norm t in (uu___7, a)))
                         args in
                     (uu___4, uu___5) in
                   FStarC_Syntax_Syntax.Meta_pattern uu___3
               | FStarC_Syntax_Syntax.Meta_monadic (m, t) ->
                   let uu___3 = let uu___4 = norm t in (m, uu___4) in
                   FStarC_Syntax_Syntax.Meta_monadic uu___3
               | FStarC_Syntax_Syntax.Meta_monadic_lift (m0, m1, t) ->
                   let uu___3 = let uu___4 = norm t in (m0, m1, uu___4) in
                   FStarC_Syntax_Syntax.Meta_monadic_lift uu___3 in
             let uu___2 =
               let uu___3 =
                 let uu___4 = translate cfg bs e1 in
                 let uu___5 = FStarC_Thunk.mk norm_meta in (uu___4, uu___5) in
               FStarC_TypeChecker_NBETerm.Meta uu___3 in
             mk_t1 uu___2
         | FStarC_Syntax_Syntax.Tm_let
             { FStarC_Syntax_Syntax.lbs = (false, lb::[]);
               FStarC_Syntax_Syntax.body1 = body;_}
             ->
             let uu___2 =
               FStarC_TypeChecker_Cfg.should_reduce_local_let cfg.core_cfg lb in
             if uu___2
             then
               let uu___3 =
                 (((cfg.core_cfg).FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.for_extraction
                    &&
                    (FStarC_Syntax_Util.is_unit lb.FStarC_Syntax_Syntax.lbtyp))
                   &&
                   (FStarC_Syntax_Util.is_pure_or_ghost_effect
                      lb.FStarC_Syntax_Syntax.lbeff) in
               (if uu___3
                then
                  let bs1 =
                    let uu___4 =
                      let uu___5 =
                        FStarC_Syntax_Syntax.range_of_lbname
                          lb.FStarC_Syntax_Syntax.lbname in
                      mk_rt uu___5
                        (FStarC_TypeChecker_NBETerm.Constant
                           FStarC_TypeChecker_NBETerm.Unit) in
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
                    (((cfg.core_cfg).FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.for_extraction
                       &&
                       (FStarC_Syntax_Util.is_unit
                          lb.FStarC_Syntax_Syntax.lbtyp))
                      &&
                      (FStarC_Syntax_Util.is_pure_or_ghost_effect
                         lb.FStarC_Syntax_Syntax.lbeff) in
                  if uu___5
                  then
                    mk_t1
                      (FStarC_TypeChecker_NBETerm.Constant
                         FStarC_TypeChecker_NBETerm.Unit)
                  else translate cfg bs lb.FStarC_Syntax_Syntax.lbdef in
                let typ uu___4 =
                  translate cfg bs lb.FStarC_Syntax_Syntax.lbtyp in
                let name =
                  let uu___4 =
                    FStarC_Compiler_Util.left lb.FStarC_Syntax_Syntax.lbname in
                  FStarC_Syntax_Syntax.freshen_bv uu___4 in
                let bs1 =
                  let uu___4 =
                    let uu___5 = FStarC_Syntax_Syntax.range_of_bv name in
                    mk_rt uu___5
                      (FStarC_TypeChecker_NBETerm.Accu
                         ((FStarC_TypeChecker_NBETerm.Var name), [])) in
                  uu___4 :: bs in
                let body1 uu___4 = translate cfg bs1 body in
                let uu___4 =
                  let uu___5 =
                    let uu___6 =
                      let uu___7 =
                        let uu___8 = FStarC_Thunk.mk typ in
                        let uu___9 = FStarC_Thunk.mk def in
                        let uu___10 = FStarC_Thunk.mk body1 in
                        (name, uu___8, uu___9, uu___10, lb) in
                      FStarC_TypeChecker_NBETerm.UnreducedLet uu___7 in
                    (uu___6, []) in
                  FStarC_TypeChecker_NBETerm.Accu uu___5 in
                mk_t1 uu___4)
         | FStarC_Syntax_Syntax.Tm_let
             { FStarC_Syntax_Syntax.lbs = (_rec, lbs);
               FStarC_Syntax_Syntax.body1 = body;_}
             ->
             if
               (Prims.op_Negation
                  ((cfg.core_cfg).FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.zeta)
                 &&
                 ((cfg.core_cfg).FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.pure_subterms_within_computations
             then
               let vars =
                 FStarC_Compiler_List.map
                   (fun lb ->
                      let uu___2 =
                        FStarC_Compiler_Util.left
                          lb.FStarC_Syntax_Syntax.lbname in
                      FStarC_Syntax_Syntax.freshen_bv uu___2) lbs in
               let typs =
                 FStarC_Compiler_List.map
                   (fun lb -> translate cfg bs lb.FStarC_Syntax_Syntax.lbtyp)
                   lbs in
               let rec_bs =
                 let uu___2 =
                   FStarC_Compiler_List.map
                     (fun v ->
                        let uu___3 = FStarC_Syntax_Syntax.range_of_bv v in
                        mk_rt uu___3
                          (FStarC_TypeChecker_NBETerm.Accu
                             ((FStarC_TypeChecker_NBETerm.Var v), []))) vars in
                 FStarC_Compiler_List.op_At uu___2 bs in
               let defs =
                 FStarC_Compiler_List.map
                   (fun lb ->
                      translate cfg rec_bs lb.FStarC_Syntax_Syntax.lbdef) lbs in
               let body1 = translate cfg rec_bs body in
               let uu___2 =
                 let uu___3 =
                   let uu___4 =
                     let uu___5 =
                       let uu___6 = FStarC_Compiler_List.zip3 vars typs defs in
                       (uu___6, body1, lbs) in
                     FStarC_TypeChecker_NBETerm.UnreducedLetRec uu___5 in
                   (uu___4, []) in
                 FStarC_TypeChecker_NBETerm.Accu uu___3 in
               mk_t1 uu___2
             else
               (let uu___3 = make_rec_env lbs bs in translate cfg uu___3 body)
         | FStarC_Syntax_Syntax.Tm_quoted (qt, qi) ->
             let close t =
               let bvs =
                 FStarC_Compiler_List.map
                   (fun uu___2 ->
                      FStarC_Syntax_Syntax.new_bv
                        FStar_Pervasives_Native.None FStarC_Syntax_Syntax.tun)
                   bs in
               let s1 =
                 FStarC_Compiler_List.mapi
                   (fun i -> fun bv -> FStarC_Syntax_Syntax.DB (i, bv)) bvs in
               let s2 =
                 let uu___2 = FStarC_Compiler_List.zip bvs bs in
                 FStarC_Compiler_List.map
                   (fun uu___3 ->
                      match uu___3 with
                      | (bv, t1) ->
                          let uu___4 =
                            let uu___5 = readback cfg t1 in (bv, uu___5) in
                          FStarC_Syntax_Syntax.NT uu___4) uu___2 in
               let uu___2 = FStarC_Syntax_Subst.subst s1 t in
               FStarC_Syntax_Subst.subst s2 uu___2 in
             (match qi.FStarC_Syntax_Syntax.qkind with
              | FStarC_Syntax_Syntax.Quote_dynamic ->
                  let qt1 = close qt in
                  mk_t1 (FStarC_TypeChecker_NBETerm.Quote (qt1, qi))
              | FStarC_Syntax_Syntax.Quote_static ->
                  let qi1 = FStarC_Syntax_Syntax.on_antiquoted close qi in
                  mk_t1 (FStarC_TypeChecker_NBETerm.Quote (qt, qi1)))
         | FStarC_Syntax_Syntax.Tm_lazy li ->
             let f uu___2 =
               let t = FStarC_Syntax_Util.unfold_lazy li in
               debug1
                 (fun uu___4 ->
                    let uu___5 =
                      FStarC_Class_Show.show
                        FStarC_Syntax_Print.showable_term t in
                    FStarC_Compiler_Util.print1
                      ">> Unfolding Tm_lazy to %s\n" uu___5);
               translate cfg bs t in
             let uu___2 =
               let uu___3 =
                 let uu___4 = FStarC_Thunk.mk f in
                 ((FStar_Pervasives.Inl li), uu___4) in
               FStarC_TypeChecker_NBETerm.Lazy uu___3 in
             mk_t1 uu___2)
and (translate_comp :
  config ->
    FStarC_TypeChecker_NBETerm.t Prims.list ->
      FStarC_Syntax_Syntax.comp -> FStarC_TypeChecker_NBETerm.comp)
  =
  fun cfg ->
    fun bs ->
      fun c ->
        match c.FStarC_Syntax_Syntax.n with
        | FStarC_Syntax_Syntax.Total typ ->
            let uu___ = translate cfg bs typ in
            FStarC_TypeChecker_NBETerm.Tot uu___
        | FStarC_Syntax_Syntax.GTotal typ ->
            let uu___ = translate cfg bs typ in
            FStarC_TypeChecker_NBETerm.GTot uu___
        | FStarC_Syntax_Syntax.Comp ctyp ->
            let uu___ = translate_comp_typ cfg bs ctyp in
            FStarC_TypeChecker_NBETerm.Comp uu___
and (iapp :
  config ->
    FStarC_TypeChecker_NBETerm.t ->
      FStarC_TypeChecker_NBETerm.args -> FStarC_TypeChecker_NBETerm.t)
  =
  fun cfg ->
    fun f ->
      fun args ->
        let mk t = mk_rt f.FStarC_TypeChecker_NBETerm.nbe_r t in
        let uu___ =
          let uu___1 = unlazy_unmeta f in
          uu___1.FStarC_TypeChecker_NBETerm.nbe_t in
        match uu___ with
        | FStarC_TypeChecker_NBETerm.Lam
            { FStarC_TypeChecker_NBETerm.interp = f1;
              FStarC_TypeChecker_NBETerm.shape = shape;
              FStarC_TypeChecker_NBETerm.arity = n;_}
            ->
            let m = FStarC_Compiler_List.length args in
            if m < n
            then
              let arg_values_rev = FStarC_Compiler_List.rev args in
              let shape1 =
                match shape with
                | FStarC_TypeChecker_NBETerm.Lam_args raw_args ->
                    let uu___1 = FStarC_Compiler_List.splitAt m raw_args in
                    (match uu___1 with
                     | (uu___2, raw_args1) ->
                         FStarC_TypeChecker_NBETerm.Lam_args raw_args1)
                | FStarC_TypeChecker_NBETerm.Lam_bs (ctx, xs, rc) ->
                    let uu___1 = FStarC_Compiler_List.splitAt m xs in
                    (match uu___1 with
                     | (uu___2, xs1) ->
                         let ctx1 =
                           let uu___3 =
                             FStarC_Compiler_List.map
                               FStar_Pervasives_Native.fst arg_values_rev in
                           FStarC_Compiler_List.append uu___3 ctx in
                         FStarC_TypeChecker_NBETerm.Lam_bs (ctx1, xs1, rc))
                | FStarC_TypeChecker_NBETerm.Lam_primop (f2, args_acc) ->
                    FStarC_TypeChecker_NBETerm.Lam_primop
                      (f2, (FStarC_Compiler_List.op_At args_acc args)) in
              mk
                (FStarC_TypeChecker_NBETerm.Lam
                   {
                     FStarC_TypeChecker_NBETerm.interp =
                       (fun l ->
                          f1 (FStarC_Compiler_List.append l arg_values_rev));
                     FStarC_TypeChecker_NBETerm.shape = shape1;
                     FStarC_TypeChecker_NBETerm.arity = (n - m)
                   })
            else
              if m = n
              then
                (let arg_values_rev = FStarC_Compiler_List.rev args in
                 f1 arg_values_rev)
              else
                (let uu___3 = FStarC_Compiler_List.splitAt n args in
                 match uu___3 with
                 | (args1, args') ->
                     let uu___4 = f1 (FStarC_Compiler_List.rev args1) in
                     iapp cfg uu___4 args')
        | FStarC_TypeChecker_NBETerm.Accu (a, ts) ->
            mk
              (FStarC_TypeChecker_NBETerm.Accu
                 (a, (FStarC_Compiler_List.rev_append args ts)))
        | FStarC_TypeChecker_NBETerm.Construct (i, us, ts) ->
            let rec aux args1 us1 ts1 =
              match args1 with
              | ({
                   FStarC_TypeChecker_NBETerm.nbe_t =
                     FStarC_TypeChecker_NBETerm.Univ u;
                   FStarC_TypeChecker_NBETerm.nbe_r = uu___1;_},
                 uu___2)::args2 -> aux args2 (u :: us1) ts1
              | a::args2 -> aux args2 us1 (a :: ts1)
              | [] -> (us1, ts1) in
            let uu___1 = aux args us ts in
            (match uu___1 with
             | (us', ts') ->
                 mk (FStarC_TypeChecker_NBETerm.Construct (i, us', ts')))
        | FStarC_TypeChecker_NBETerm.FV (i, us, ts) ->
            let rec aux args1 us1 ts1 =
              match args1 with
              | ({
                   FStarC_TypeChecker_NBETerm.nbe_t =
                     FStarC_TypeChecker_NBETerm.Univ u;
                   FStarC_TypeChecker_NBETerm.nbe_r = uu___1;_},
                 uu___2)::args2 -> aux args2 (u :: us1) ts1
              | a::args2 -> aux args2 us1 (a :: ts1)
              | [] -> (us1, ts1) in
            let uu___1 = aux args us ts in
            (match uu___1 with
             | (us', ts') -> mk (FStarC_TypeChecker_NBETerm.FV (i, us', ts')))
        | FStarC_TypeChecker_NBETerm.TopLevelLet (lb, arity, args_rev) ->
            let args_rev1 = FStarC_Compiler_List.rev_append args args_rev in
            let n_args_rev = FStarC_Compiler_List.length args_rev1 in
            let n_univs =
              FStarC_Compiler_List.length lb.FStarC_Syntax_Syntax.lbunivs in
            (debug cfg
               (fun uu___2 ->
                  let uu___3 =
                    FStarC_Class_Show.show
                      (FStarC_Class_Show.show_either
                         FStarC_Syntax_Print.showable_bv
                         FStarC_Syntax_Print.showable_fv)
                      lb.FStarC_Syntax_Syntax.lbname in
                  let uu___4 =
                    FStarC_Class_Show.show FStarC_Class_Show.showable_int
                      arity in
                  let uu___5 =
                    FStarC_Class_Show.show FStarC_Class_Show.showable_nat
                      n_args_rev in
                  FStarC_Compiler_Util.print3
                    "Reached iapp for %s with arity %s and n_args = %s\n"
                    uu___3 uu___4 uu___5);
             if n_args_rev >= arity
             then
               (let uu___2 =
                  let uu___3 =
                    let uu___4 =
                      FStarC_Syntax_Util.unascribe
                        lb.FStarC_Syntax_Syntax.lbdef in
                    uu___4.FStarC_Syntax_Syntax.n in
                  match uu___3 with
                  | FStarC_Syntax_Syntax.Tm_abs
                      { FStarC_Syntax_Syntax.bs = bs;
                        FStarC_Syntax_Syntax.body = body;
                        FStarC_Syntax_Syntax.rc_opt = uu___4;_}
                      -> (bs, body)
                  | uu___4 -> ([], (lb.FStarC_Syntax_Syntax.lbdef)) in
                match uu___2 with
                | (bs, body) ->
                    if (n_univs + (FStarC_Compiler_List.length bs)) = arity
                    then
                      let uu___3 =
                        FStarC_Compiler_Util.first_N (n_args_rev - arity)
                          args_rev1 in
                      (match uu___3 with
                       | (extra, args_rev2) ->
                           (debug cfg
                              (fun uu___5 ->
                                 let uu___6 =
                                   FStarC_Class_Show.show
                                     (FStarC_Class_Show.show_either
                                        FStarC_Syntax_Print.showable_bv
                                        FStarC_Syntax_Print.showable_fv)
                                     lb.FStarC_Syntax_Syntax.lbname in
                                 let uu___7 =
                                   FStarC_Class_Show.show
                                     FStarC_Syntax_Print.showable_term body in
                                 let uu___8 =
                                   FStarC_Class_Show.show
                                     FStarC_TypeChecker_NBETerm.showable_args
                                     args_rev2 in
                                 FStarC_Compiler_Util.print3
                                   "Reducing body of %s = %s,\n\twith args = %s\n"
                                   uu___6 uu___7 uu___8);
                            (let t =
                               let uu___5 =
                                 FStarC_Compiler_List.map
                                   FStar_Pervasives_Native.fst args_rev2 in
                               translate cfg uu___5 body in
                             match extra with
                             | [] -> t
                             | uu___5 ->
                                 iapp cfg t (FStarC_Compiler_List.rev extra))))
                    else
                      (let uu___4 =
                         FStarC_Compiler_Util.first_N (n_args_rev - n_univs)
                           args_rev1 in
                       match uu___4 with
                       | (extra, univs) ->
                           let uu___5 =
                             let uu___6 =
                               FStarC_Compiler_List.map
                                 FStar_Pervasives_Native.fst univs in
                             translate cfg uu___6
                               lb.FStarC_Syntax_Syntax.lbdef in
                           iapp cfg uu___5 (FStarC_Compiler_List.rev extra)))
             else
               mk
                 (FStarC_TypeChecker_NBETerm.TopLevelLet
                    (lb, arity, args_rev1)))
        | FStarC_TypeChecker_NBETerm.TopLevelRec
            (lb, arity, decreases_list, args') ->
            let args1 = FStarC_Compiler_List.append args' args in
            if (FStarC_Compiler_List.length args1) >= arity
            then
              let uu___1 =
                should_reduce_recursive_definition args1 decreases_list in
              (match uu___1 with
               | (should_reduce, uu___2, uu___3) ->
                   if Prims.op_Negation should_reduce
                   then
                     let fv =
                       FStarC_Compiler_Util.right
                         lb.FStarC_Syntax_Syntax.lbname in
                     (debug cfg
                        (fun uu___5 ->
                           let uu___6 =
                             FStarC_Class_Show.show
                               FStarC_Syntax_Print.showable_fv fv in
                           FStarC_Compiler_Util.print1
                             "Decided to not unfold recursive definition %s\n"
                             uu___6);
                      (let uu___5 =
                         let uu___6 = FStarC_Syntax_Syntax.range_of_fv fv in
                         mk_rt uu___6
                           (FStarC_TypeChecker_NBETerm.FV (fv, [], [])) in
                       iapp cfg uu___5 args1))
                   else
                     (debug cfg
                        (fun uu___6 ->
                           let uu___7 =
                             let uu___8 =
                               FStarC_Compiler_Util.right
                                 lb.FStarC_Syntax_Syntax.lbname in
                             FStarC_Class_Show.show
                               FStarC_Syntax_Print.showable_fv uu___8 in
                           FStarC_Compiler_Util.print1
                             "Yes, Decided to unfold recursive definition %s\n"
                             uu___7);
                      (let uu___6 =
                         FStarC_Compiler_Util.first_N
                           (FStarC_Compiler_List.length
                              lb.FStarC_Syntax_Syntax.lbunivs) args1 in
                       match uu___6 with
                       | (univs, rest) ->
                           let uu___7 =
                             let uu___8 =
                               let uu___9 =
                                 FStarC_Compiler_List.map
                                   FStar_Pervasives_Native.fst univs in
                               FStarC_Compiler_List.rev uu___9 in
                             translate cfg uu___8
                               lb.FStarC_Syntax_Syntax.lbdef in
                           iapp cfg uu___7 rest)))
            else
              mk
                (FStarC_TypeChecker_NBETerm.TopLevelRec
                   (lb, arity, decreases_list, args1))
        | FStarC_TypeChecker_NBETerm.LocalLetRec
            (i, lb, mutual_lbs, local_env, acc_args, remaining_arity,
             decreases_list)
            ->
            if remaining_arity = Prims.int_zero
            then
              mk
                (FStarC_TypeChecker_NBETerm.LocalLetRec
                   (i, lb, mutual_lbs, local_env,
                     (FStarC_Compiler_List.op_At acc_args args),
                     remaining_arity, decreases_list))
            else
              (let n_args = FStarC_Compiler_List.length args in
               if n_args < remaining_arity
               then
                 mk
                   (FStarC_TypeChecker_NBETerm.LocalLetRec
                      (i, lb, mutual_lbs, local_env,
                        (FStarC_Compiler_List.op_At acc_args args),
                        (remaining_arity - n_args), decreases_list))
               else
                 (let args1 = FStarC_Compiler_List.op_At acc_args args in
                  let uu___3 =
                    should_reduce_recursive_definition args1 decreases_list in
                  match uu___3 with
                  | (should_reduce, uu___4, uu___5) ->
                      if Prims.op_Negation should_reduce
                      then
                        mk
                          (FStarC_TypeChecker_NBETerm.LocalLetRec
                             (i, lb, mutual_lbs, local_env, args1,
                               Prims.int_zero, decreases_list))
                      else
                        (let env = make_rec_env mutual_lbs local_env in
                         debug cfg
                           (fun uu___8 ->
                              (let uu___10 =
                                 let uu___11 =
                                   FStarC_Compiler_List.map
                                     FStarC_TypeChecker_NBETerm.t_to_string
                                     env in
                                 FStarC_Compiler_String.concat ",\n\t "
                                   uu___11 in
                               FStarC_Compiler_Util.print1
                                 "LocalLetRec Env = {\n\t%s\n}\n" uu___10);
                              (let uu___10 =
                                 let uu___11 =
                                   FStarC_Compiler_List.map
                                     (fun uu___12 ->
                                        match uu___12 with
                                        | (t, uu___13) ->
                                            FStarC_TypeChecker_NBETerm.t_to_string
                                              t) args1 in
                                 FStarC_Compiler_String.concat ",\n\t "
                                   uu___11 in
                               FStarC_Compiler_Util.print1
                                 "LocalLetRec Args = {\n\t%s\n}\n" uu___10));
                         (let uu___8 =
                            translate cfg env lb.FStarC_Syntax_Syntax.lbdef in
                          iapp cfg uu___8 args1))))
        | FStarC_TypeChecker_NBETerm.Constant
            (FStarC_TypeChecker_NBETerm.SConst (FStarC_Const.Const_range_of))
            ->
            let callbacks =
              {
                FStarC_TypeChecker_NBETerm.iapp = (iapp cfg);
                FStarC_TypeChecker_NBETerm.translate = (translate cfg [])
              } in
            (match args with
             | (a, uu___1)::[] ->
                 FStarC_TypeChecker_NBETerm.embed
                   FStarC_TypeChecker_NBETerm.e_range callbacks
                   a.FStarC_TypeChecker_NBETerm.nbe_r
             | uu___1 ->
                 let uu___2 =
                   let uu___3 = FStarC_TypeChecker_NBETerm.t_to_string f in
                   Prims.strcat "NBE ill-typed application Const_range_of: "
                     uu___3 in
                 failwith uu___2)
        | FStarC_TypeChecker_NBETerm.Constant
            (FStarC_TypeChecker_NBETerm.SConst
            (FStarC_Const.Const_set_range_of)) ->
            let callbacks =
              {
                FStarC_TypeChecker_NBETerm.iapp = (iapp cfg);
                FStarC_TypeChecker_NBETerm.translate = (translate cfg [])
              } in
            (match args with
             | (t, uu___1)::(r, uu___2)::[] ->
                 let uu___3 =
                   FStarC_TypeChecker_NBETerm.unembed
                     FStarC_TypeChecker_NBETerm.e_range callbacks r in
                 (match uu___3 with
                  | FStar_Pervasives_Native.Some rr ->
                      {
                        FStarC_TypeChecker_NBETerm.nbe_t =
                          (t.FStarC_TypeChecker_NBETerm.nbe_t);
                        FStarC_TypeChecker_NBETerm.nbe_r = rr
                      }
                  | FStar_Pervasives_Native.None -> Prims.magic ())
             | uu___1 ->
                 let uu___2 =
                   let uu___3 = FStarC_TypeChecker_NBETerm.t_to_string f in
                   Prims.strcat
                     "NBE ill-typed application Const_set_range_of: " uu___3 in
                 failwith uu___2)
        | uu___1 ->
            let uu___2 =
              let uu___3 = FStarC_TypeChecker_NBETerm.t_to_string f in
              Prims.strcat "NBE ill-typed application: " uu___3 in
            failwith uu___2
and (translate_fv :
  config ->
    FStarC_TypeChecker_NBETerm.t Prims.list ->
      FStarC_Syntax_Syntax.fv -> FStarC_TypeChecker_NBETerm.t)
  =
  fun cfg ->
    fun bs ->
      fun fvar ->
        let debug1 = debug cfg in
        let qninfo =
          let uu___ = FStarC_TypeChecker_Cfg.cfg_env cfg.core_cfg in
          let uu___1 = FStarC_Syntax_Syntax.lid_of_fv fvar in
          FStarC_TypeChecker_Env.lookup_qname uu___ uu___1 in
        let uu___ = (is_constr qninfo) || (is_constr_fv fvar) in
        if uu___
        then FStarC_TypeChecker_NBETerm.mkConstruct fvar [] []
        else
          (let uu___2 =
             FStarC_TypeChecker_Normalize_Unfolding.should_unfold
               cfg.core_cfg
               (fun uu___3 -> (cfg.core_cfg).FStarC_TypeChecker_Cfg.reifying)
               fvar qninfo in
           match uu___2 with
           | FStarC_TypeChecker_Normalize_Unfolding.Should_unfold_fully ->
               failwith "Not yet handled"
           | FStarC_TypeChecker_Normalize_Unfolding.Should_unfold_no ->
               (debug1
                  (fun uu___4 ->
                     let uu___5 =
                       FStarC_Class_Show.show FStarC_Syntax_Print.showable_fv
                         fvar in
                     FStarC_Compiler_Util.print1
                       "(1) Decided to not unfold %s\n" uu___5);
                (let uu___4 =
                   FStarC_TypeChecker_Cfg.find_prim_step cfg.core_cfg fvar in
                 match uu___4 with
                 | FStar_Pervasives_Native.Some prim_step when
                     prim_step.FStarC_TypeChecker_Primops_Base.strong_reduction_ok
                     ->
                     let arity =
                       prim_step.FStarC_TypeChecker_Primops_Base.arity +
                         prim_step.FStarC_TypeChecker_Primops_Base.univ_arity in
                     (debug1
                        (fun uu___6 ->
                           let uu___7 =
                             FStarC_Class_Show.show
                               FStarC_Syntax_Print.showable_fv fvar in
                           FStarC_Compiler_Util.print1 "Found a primop %s\n"
                             uu___7);
                      mk_t
                        (FStarC_TypeChecker_NBETerm.Lam
                           {
                             FStarC_TypeChecker_NBETerm.interp =
                               (fun args_rev ->
                                  let args' =
                                    FStarC_Compiler_List.rev args_rev in
                                  let callbacks =
                                    {
                                      FStarC_TypeChecker_NBETerm.iapp =
                                        (iapp cfg);
                                      FStarC_TypeChecker_NBETerm.translate =
                                        (translate cfg bs)
                                    } in
                                  debug1
                                    (fun uu___7 ->
                                       let uu___8 =
                                         FStarC_Class_Show.show
                                           FStarC_TypeChecker_NBETerm.showable_args
                                           args' in
                                       FStarC_Compiler_Util.print1
                                         "Caling primop with args = [%s]\n"
                                         uu___8);
                                  (let uu___7 =
                                     FStarC_Compiler_List.span
                                       (fun uu___8 ->
                                          match uu___8 with
                                          | ({
                                               FStarC_TypeChecker_NBETerm.nbe_t
                                                 =
                                                 FStarC_TypeChecker_NBETerm.Univ
                                                 uu___9;
                                               FStarC_TypeChecker_NBETerm.nbe_r
                                                 = uu___10;_},
                                             uu___11) -> true
                                          | uu___9 -> false) args' in
                                   match uu___7 with
                                   | (univs, rest) ->
                                       let univs1 =
                                         FStarC_Compiler_List.map
                                           (fun uu___8 ->
                                              match uu___8 with
                                              | ({
                                                   FStarC_TypeChecker_NBETerm.nbe_t
                                                     =
                                                     FStarC_TypeChecker_NBETerm.Univ
                                                     u;
                                                   FStarC_TypeChecker_NBETerm.nbe_r
                                                     = uu___9;_},
                                                 uu___10) -> u
                                              | uu___9 ->
                                                  failwith "Impossible")
                                           univs in
                                       let uu___8 =
                                         prim_step.FStarC_TypeChecker_Primops_Base.interpretation_nbe
                                           callbacks univs1 rest in
                                       (match uu___8 with
                                        | FStar_Pervasives_Native.Some x ->
                                            (debug1
                                               (fun uu___10 ->
                                                  let uu___11 =
                                                    FStarC_Class_Show.show
                                                      FStarC_Syntax_Print.showable_fv
                                                      fvar in
                                                  let uu___12 =
                                                    FStarC_TypeChecker_NBETerm.t_to_string
                                                      x in
                                                  FStarC_Compiler_Util.print2
                                                    "Primitive operator %s returned %s\n"
                                                    uu___11 uu___12);
                                             x)
                                        | FStar_Pervasives_Native.None ->
                                            (debug1
                                               (fun uu___10 ->
                                                  let uu___11 =
                                                    FStarC_Class_Show.show
                                                      FStarC_Syntax_Print.showable_fv
                                                      fvar in
                                                  FStarC_Compiler_Util.print1
                                                    "Primitive operator %s failed\n"
                                                    uu___11);
                                             (let uu___10 =
                                                FStarC_TypeChecker_NBETerm.mkFV
                                                  fvar [] [] in
                                              iapp cfg uu___10 args')))));
                             FStarC_TypeChecker_NBETerm.shape =
                               (FStarC_TypeChecker_NBETerm.Lam_primop
                                  (fvar, []));
                             FStarC_TypeChecker_NBETerm.arity = arity
                           }))
                 | FStar_Pervasives_Native.Some uu___5 ->
                     (debug1
                        (fun uu___7 ->
                           let uu___8 =
                             FStarC_Class_Show.show
                               FStarC_Syntax_Print.showable_fv fvar in
                           FStarC_Compiler_Util.print1
                             "(2) Decided to not unfold %s\n" uu___8);
                      FStarC_TypeChecker_NBETerm.mkFV fvar [] [])
                 | uu___5 ->
                     (debug1
                        (fun uu___7 ->
                           let uu___8 =
                             FStarC_Class_Show.show
                               FStarC_Syntax_Print.showable_fv fvar in
                           FStarC_Compiler_Util.print1
                             "(3) Decided to not unfold %s\n" uu___8);
                      FStarC_TypeChecker_NBETerm.mkFV fvar [] [])))
           | FStarC_TypeChecker_Normalize_Unfolding.Should_unfold_reify ->
               let t =
                 let is_qninfo_visible =
                   let uu___3 =
                     FStarC_TypeChecker_Env.lookup_definition_qninfo
                       (cfg.core_cfg).FStarC_TypeChecker_Cfg.delta_level
                       (fvar.FStarC_Syntax_Syntax.fv_name).FStarC_Syntax_Syntax.v
                       qninfo in
                   FStarC_Compiler_Option.isSome uu___3 in
                 if is_qninfo_visible
                 then
                   match qninfo with
                   | FStar_Pervasives_Native.Some
                       (FStar_Pervasives.Inr
                        ({
                           FStarC_Syntax_Syntax.sigel =
                             FStarC_Syntax_Syntax.Sig_let
                             { FStarC_Syntax_Syntax.lbs1 = (is_rec, lbs);
                               FStarC_Syntax_Syntax.lids1 = names;_};
                           FStarC_Syntax_Syntax.sigrng = uu___3;
                           FStarC_Syntax_Syntax.sigquals = uu___4;
                           FStarC_Syntax_Syntax.sigmeta = uu___5;
                           FStarC_Syntax_Syntax.sigattrs = uu___6;
                           FStarC_Syntax_Syntax.sigopens_and_abbrevs = uu___7;
                           FStarC_Syntax_Syntax.sigopts = uu___8;_},
                         _us_opt),
                        _rng)
                       ->
                       (debug1
                          (fun uu___10 ->
                             let uu___11 =
                               FStarC_Class_Show.show
                                 FStarC_Syntax_Print.showable_fv fvar in
                             FStarC_Compiler_Util.print1
                               "(1) Decided to unfold %s\n" uu___11);
                        (let lbm = find_let lbs fvar in
                         match lbm with
                         | FStar_Pervasives_Native.Some lb ->
                             if
                               is_rec &&
                                 ((cfg.core_cfg).FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.zeta
                             then
                               let uu___10 = let_rec_arity lb in
                               (match uu___10 with
                                | (ar, lst) ->
                                    let uu___11 =
                                      FStarC_Syntax_Syntax.range_of_fv fvar in
                                    mk_rt uu___11
                                      (FStarC_TypeChecker_NBETerm.TopLevelRec
                                         (lb, ar, lst, [])))
                             else translate_letbinding cfg bs lb
                         | FStar_Pervasives_Native.None ->
                             failwith "Could not find let binding"))
                   | uu___3 ->
                       (debug1
                          (fun uu___5 ->
                             let uu___6 =
                               FStarC_Class_Show.show
                                 FStarC_Syntax_Print.showable_fv fvar in
                             FStarC_Compiler_Util.print1
                               "(1) qninfo is None for (%s)\n" uu___6);
                        FStarC_TypeChecker_NBETerm.mkFV fvar [] [])
                 else
                   (debug1
                      (fun uu___5 ->
                         let uu___6 =
                           FStarC_Class_Show.show
                             FStarC_Syntax_Print.showable_fv fvar in
                         FStarC_Compiler_Util.print1
                           "(1) qninfo is not visible at this level (%s)\n"
                           uu___6);
                    FStarC_TypeChecker_NBETerm.mkFV fvar [] []) in
               (cache_add cfg fvar t; t)
           | FStarC_TypeChecker_Normalize_Unfolding.Should_unfold_yes ->
               let t =
                 let is_qninfo_visible =
                   let uu___3 =
                     FStarC_TypeChecker_Env.lookup_definition_qninfo
                       (cfg.core_cfg).FStarC_TypeChecker_Cfg.delta_level
                       (fvar.FStarC_Syntax_Syntax.fv_name).FStarC_Syntax_Syntax.v
                       qninfo in
                   FStarC_Compiler_Option.isSome uu___3 in
                 if is_qninfo_visible
                 then
                   match qninfo with
                   | FStar_Pervasives_Native.Some
                       (FStar_Pervasives.Inr
                        ({
                           FStarC_Syntax_Syntax.sigel =
                             FStarC_Syntax_Syntax.Sig_let
                             { FStarC_Syntax_Syntax.lbs1 = (is_rec, lbs);
                               FStarC_Syntax_Syntax.lids1 = names;_};
                           FStarC_Syntax_Syntax.sigrng = uu___3;
                           FStarC_Syntax_Syntax.sigquals = uu___4;
                           FStarC_Syntax_Syntax.sigmeta = uu___5;
                           FStarC_Syntax_Syntax.sigattrs = uu___6;
                           FStarC_Syntax_Syntax.sigopens_and_abbrevs = uu___7;
                           FStarC_Syntax_Syntax.sigopts = uu___8;_},
                         _us_opt),
                        _rng)
                       ->
                       (debug1
                          (fun uu___10 ->
                             let uu___11 =
                               FStarC_Class_Show.show
                                 FStarC_Syntax_Print.showable_fv fvar in
                             FStarC_Compiler_Util.print1
                               "(1) Decided to unfold %s\n" uu___11);
                        (let lbm = find_let lbs fvar in
                         match lbm with
                         | FStar_Pervasives_Native.Some lb ->
                             if
                               is_rec &&
                                 ((cfg.core_cfg).FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.zeta
                             then
                               let uu___10 = let_rec_arity lb in
                               (match uu___10 with
                                | (ar, lst) ->
                                    let uu___11 =
                                      FStarC_Syntax_Syntax.range_of_fv fvar in
                                    mk_rt uu___11
                                      (FStarC_TypeChecker_NBETerm.TopLevelRec
                                         (lb, ar, lst, [])))
                             else translate_letbinding cfg bs lb
                         | FStar_Pervasives_Native.None ->
                             failwith "Could not find let binding"))
                   | uu___3 ->
                       (debug1
                          (fun uu___5 ->
                             let uu___6 =
                               FStarC_Class_Show.show
                                 FStarC_Syntax_Print.showable_fv fvar in
                             FStarC_Compiler_Util.print1
                               "(1) qninfo is None for (%s)\n" uu___6);
                        FStarC_TypeChecker_NBETerm.mkFV fvar [] [])
                 else
                   (debug1
                      (fun uu___5 ->
                         let uu___6 =
                           FStarC_Class_Show.show
                             FStarC_Syntax_Print.showable_fv fvar in
                         FStarC_Compiler_Util.print1
                           "(1) qninfo is not visible at this level (%s)\n"
                           uu___6);
                    FStarC_TypeChecker_NBETerm.mkFV fvar [] []) in
               (cache_add cfg fvar t; t))
and (translate_letbinding :
  config ->
    FStarC_TypeChecker_NBETerm.t Prims.list ->
      FStarC_Syntax_Syntax.letbinding -> FStarC_TypeChecker_NBETerm.t)
  =
  fun cfg ->
    fun bs ->
      fun lb ->
        let debug1 = debug cfg in
        let us = lb.FStarC_Syntax_Syntax.lbunivs in
        let uu___ =
          FStarC_Syntax_Util.arrow_formals lb.FStarC_Syntax_Syntax.lbtyp in
        match uu___ with
        | (formals, uu___1) ->
            let arity =
              (FStarC_Compiler_List.length us) +
                (FStarC_Compiler_List.length formals) in
            if arity = Prims.int_zero
            then translate cfg bs lb.FStarC_Syntax_Syntax.lbdef
            else
              (let uu___3 =
                 FStarC_Compiler_Util.is_right lb.FStarC_Syntax_Syntax.lbname in
               if uu___3
               then
                 (debug1
                    (fun uu___5 ->
                       let uu___6 =
                         FStarC_Class_Show.show
                           (FStarC_Class_Show.show_either
                              FStarC_Syntax_Print.showable_bv
                              FStarC_Syntax_Print.showable_fv)
                           lb.FStarC_Syntax_Syntax.lbname in
                       let uu___7 =
                         FStarC_Class_Show.show
                           FStarC_Class_Show.showable_int arity in
                       FStarC_Compiler_Util.print2
                         "Making TopLevelLet for %s with arity %s\n" uu___6
                         uu___7);
                  (let uu___5 =
                     FStarC_Syntax_Syntax.range_of_lbname
                       lb.FStarC_Syntax_Syntax.lbname in
                   mk_rt uu___5
                     (FStarC_TypeChecker_NBETerm.TopLevelLet (lb, arity, []))))
               else translate cfg bs lb.FStarC_Syntax_Syntax.lbdef)
and (mkRec :
  Prims.int ->
    FStarC_Syntax_Syntax.letbinding ->
      FStarC_Syntax_Syntax.letbinding Prims.list ->
        FStarC_TypeChecker_NBETerm.t Prims.list ->
          FStarC_TypeChecker_NBETerm.t)
  =
  fun i ->
    fun b ->
      fun bs ->
        fun env ->
          let uu___ = let_rec_arity b in
          match uu___ with
          | (ar, ar_lst) ->
              mk_t
                (FStarC_TypeChecker_NBETerm.LocalLetRec
                   (i, b, bs, env, [], ar, ar_lst))
and (make_rec_env :
  FStarC_Syntax_Syntax.letbinding Prims.list ->
    FStarC_TypeChecker_NBETerm.t Prims.list ->
      FStarC_TypeChecker_NBETerm.t Prims.list)
  =
  fun all_lbs ->
    fun all_outer_bs ->
      let rec_bindings =
        FStarC_Compiler_List.mapi
          (fun i -> fun lb -> mkRec i lb all_lbs all_outer_bs) all_lbs in
      FStarC_Compiler_List.rev_append rec_bindings all_outer_bs
and (translate_constant :
  FStarC_Syntax_Syntax.sconst -> FStarC_TypeChecker_NBETerm.constant) =
  fun c ->
    match c with
    | FStarC_Const.Const_unit -> FStarC_TypeChecker_NBETerm.Unit
    | FStarC_Const.Const_bool b -> FStarC_TypeChecker_NBETerm.Bool b
    | FStarC_Const.Const_int (s, FStar_Pervasives_Native.None) ->
        let uu___ = FStarC_BigInt.big_int_of_string s in
        FStarC_TypeChecker_NBETerm.Int uu___
    | FStarC_Const.Const_string (s, r) ->
        FStarC_TypeChecker_NBETerm.String (s, r)
    | FStarC_Const.Const_char c1 -> FStarC_TypeChecker_NBETerm.Char c1
    | FStarC_Const.Const_range r -> FStarC_TypeChecker_NBETerm.Range r
    | FStarC_Const.Const_real r -> FStarC_TypeChecker_NBETerm.Real r
    | uu___ -> FStarC_TypeChecker_NBETerm.SConst c
and (readback_comp :
  config -> FStarC_TypeChecker_NBETerm.comp -> FStarC_Syntax_Syntax.comp) =
  fun cfg ->
    fun c ->
      let c' =
        match c with
        | FStarC_TypeChecker_NBETerm.Tot typ ->
            let uu___ = readback cfg typ in FStarC_Syntax_Syntax.Total uu___
        | FStarC_TypeChecker_NBETerm.GTot typ ->
            let uu___ = readback cfg typ in FStarC_Syntax_Syntax.GTotal uu___
        | FStarC_TypeChecker_NBETerm.Comp ctyp ->
            let uu___ = readback_comp_typ cfg ctyp in
            FStarC_Syntax_Syntax.Comp uu___ in
      FStarC_Syntax_Syntax.mk c' FStarC_Compiler_Range_Type.dummyRange
and (translate_comp_typ :
  config ->
    FStarC_TypeChecker_NBETerm.t Prims.list ->
      FStarC_Syntax_Syntax.comp_typ -> FStarC_TypeChecker_NBETerm.comp_typ)
  =
  fun cfg ->
    fun bs ->
      fun c ->
        let uu___ = c in
        match uu___ with
        | { FStarC_Syntax_Syntax.comp_univs = comp_univs;
            FStarC_Syntax_Syntax.effect_name = effect_name;
            FStarC_Syntax_Syntax.result_typ = result_typ;
            FStarC_Syntax_Syntax.effect_args = effect_args;
            FStarC_Syntax_Syntax.flags = flags;_} ->
            let uu___1 =
              FStarC_Compiler_List.map (translate_univ cfg bs) comp_univs in
            let uu___2 = translate cfg bs result_typ in
            let uu___3 =
              FStarC_Compiler_List.map
                (fun x ->
                   let uu___4 =
                     translate cfg bs (FStar_Pervasives_Native.fst x) in
                   (uu___4, (FStar_Pervasives_Native.snd x))) effect_args in
            let uu___4 =
              FStarC_Compiler_List.map (translate_flag cfg bs) flags in
            {
              FStarC_TypeChecker_NBETerm.comp_univs = uu___1;
              FStarC_TypeChecker_NBETerm.effect_name = effect_name;
              FStarC_TypeChecker_NBETerm.result_typ = uu___2;
              FStarC_TypeChecker_NBETerm.effect_args = uu___3;
              FStarC_TypeChecker_NBETerm.flags = uu___4
            }
and (readback_comp_typ :
  config ->
    FStarC_TypeChecker_NBETerm.comp_typ -> FStarC_Syntax_Syntax.comp_typ)
  =
  fun cfg ->
    fun c ->
      let uu___ = readback cfg c.FStarC_TypeChecker_NBETerm.result_typ in
      let uu___1 =
        FStarC_Compiler_List.map
          (fun x ->
             let uu___2 = readback cfg (FStar_Pervasives_Native.fst x) in
             (uu___2, (FStar_Pervasives_Native.snd x)))
          c.FStarC_TypeChecker_NBETerm.effect_args in
      let uu___2 =
        FStarC_Compiler_List.map (readback_flag cfg)
          c.FStarC_TypeChecker_NBETerm.flags in
      {
        FStarC_Syntax_Syntax.comp_univs =
          (c.FStarC_TypeChecker_NBETerm.comp_univs);
        FStarC_Syntax_Syntax.effect_name =
          (c.FStarC_TypeChecker_NBETerm.effect_name);
        FStarC_Syntax_Syntax.result_typ = uu___;
        FStarC_Syntax_Syntax.effect_args = uu___1;
        FStarC_Syntax_Syntax.flags = uu___2
      }
and (translate_residual_comp :
  config ->
    FStarC_TypeChecker_NBETerm.t Prims.list ->
      FStarC_Syntax_Syntax.residual_comp ->
        FStarC_TypeChecker_NBETerm.residual_comp)
  =
  fun cfg ->
    fun bs ->
      fun c ->
        let uu___ = c in
        match uu___ with
        | { FStarC_Syntax_Syntax.residual_effect = residual_effect;
            FStarC_Syntax_Syntax.residual_typ = residual_typ;
            FStarC_Syntax_Syntax.residual_flags = residual_flags;_} ->
            let uu___1 =
              if
                ((cfg.core_cfg).FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.for_extraction
              then FStar_Pervasives_Native.None
              else
                FStarC_Compiler_Util.map_opt residual_typ (translate cfg bs) in
            let uu___2 =
              FStarC_Compiler_List.map (translate_flag cfg bs) residual_flags in
            {
              FStarC_TypeChecker_NBETerm.residual_effect = residual_effect;
              FStarC_TypeChecker_NBETerm.residual_typ = uu___1;
              FStarC_TypeChecker_NBETerm.residual_flags = uu___2
            }
and (readback_residual_comp :
  config ->
    FStarC_TypeChecker_NBETerm.residual_comp ->
      FStarC_Syntax_Syntax.residual_comp)
  =
  fun cfg ->
    fun c ->
      let uu___ =
        FStarC_Compiler_Util.map_opt
          c.FStarC_TypeChecker_NBETerm.residual_typ
          (fun x ->
             debug cfg
               (fun uu___2 ->
                  let uu___3 = FStarC_TypeChecker_NBETerm.t_to_string x in
                  FStarC_Compiler_Util.print1
                    "Reading back residualtype %s\n" uu___3);
             readback cfg x) in
      let uu___1 =
        FStarC_Compiler_List.map (readback_flag cfg)
          c.FStarC_TypeChecker_NBETerm.residual_flags in
      {
        FStarC_Syntax_Syntax.residual_effect =
          (c.FStarC_TypeChecker_NBETerm.residual_effect);
        FStarC_Syntax_Syntax.residual_typ = uu___;
        FStarC_Syntax_Syntax.residual_flags = uu___1
      }
and (translate_flag :
  config ->
    FStarC_TypeChecker_NBETerm.t Prims.list ->
      FStarC_Syntax_Syntax.cflag -> FStarC_TypeChecker_NBETerm.cflag)
  =
  fun cfg ->
    fun bs ->
      fun f ->
        match f with
        | FStarC_Syntax_Syntax.TOTAL -> FStarC_TypeChecker_NBETerm.TOTAL
        | FStarC_Syntax_Syntax.MLEFFECT ->
            FStarC_TypeChecker_NBETerm.MLEFFECT
        | FStarC_Syntax_Syntax.RETURN -> FStarC_TypeChecker_NBETerm.RETURN
        | FStarC_Syntax_Syntax.PARTIAL_RETURN ->
            FStarC_TypeChecker_NBETerm.PARTIAL_RETURN
        | FStarC_Syntax_Syntax.SOMETRIVIAL ->
            FStarC_TypeChecker_NBETerm.SOMETRIVIAL
        | FStarC_Syntax_Syntax.TRIVIAL_POSTCONDITION ->
            FStarC_TypeChecker_NBETerm.TRIVIAL_POSTCONDITION
        | FStarC_Syntax_Syntax.SHOULD_NOT_INLINE ->
            FStarC_TypeChecker_NBETerm.SHOULD_NOT_INLINE
        | FStarC_Syntax_Syntax.LEMMA -> FStarC_TypeChecker_NBETerm.LEMMA
        | FStarC_Syntax_Syntax.CPS -> FStarC_TypeChecker_NBETerm.CPS
        | FStarC_Syntax_Syntax.DECREASES (FStarC_Syntax_Syntax.Decreases_lex
            l) ->
            let uu___ = FStarC_Compiler_List.map (translate cfg bs) l in
            FStarC_TypeChecker_NBETerm.DECREASES_lex uu___
        | FStarC_Syntax_Syntax.DECREASES (FStarC_Syntax_Syntax.Decreases_wf
            (rel, e)) ->
            let uu___ =
              let uu___1 = translate cfg bs rel in
              let uu___2 = translate cfg bs e in (uu___1, uu___2) in
            FStarC_TypeChecker_NBETerm.DECREASES_wf uu___
and (readback_flag :
  config -> FStarC_TypeChecker_NBETerm.cflag -> FStarC_Syntax_Syntax.cflag) =
  fun cfg ->
    fun f ->
      match f with
      | FStarC_TypeChecker_NBETerm.TOTAL -> FStarC_Syntax_Syntax.TOTAL
      | FStarC_TypeChecker_NBETerm.MLEFFECT -> FStarC_Syntax_Syntax.MLEFFECT
      | FStarC_TypeChecker_NBETerm.RETURN -> FStarC_Syntax_Syntax.RETURN
      | FStarC_TypeChecker_NBETerm.PARTIAL_RETURN ->
          FStarC_Syntax_Syntax.PARTIAL_RETURN
      | FStarC_TypeChecker_NBETerm.SOMETRIVIAL ->
          FStarC_Syntax_Syntax.SOMETRIVIAL
      | FStarC_TypeChecker_NBETerm.TRIVIAL_POSTCONDITION ->
          FStarC_Syntax_Syntax.TRIVIAL_POSTCONDITION
      | FStarC_TypeChecker_NBETerm.SHOULD_NOT_INLINE ->
          FStarC_Syntax_Syntax.SHOULD_NOT_INLINE
      | FStarC_TypeChecker_NBETerm.LEMMA -> FStarC_Syntax_Syntax.LEMMA
      | FStarC_TypeChecker_NBETerm.CPS -> FStarC_Syntax_Syntax.CPS
      | FStarC_TypeChecker_NBETerm.DECREASES_lex l ->
          let uu___ =
            let uu___1 = FStarC_Compiler_List.map (readback cfg) l in
            FStarC_Syntax_Syntax.Decreases_lex uu___1 in
          FStarC_Syntax_Syntax.DECREASES uu___
      | FStarC_TypeChecker_NBETerm.DECREASES_wf (rel, e) ->
          let uu___ =
            let uu___1 =
              let uu___2 = readback cfg rel in
              let uu___3 = readback cfg e in (uu___2, uu___3) in
            FStarC_Syntax_Syntax.Decreases_wf uu___1 in
          FStarC_Syntax_Syntax.DECREASES uu___
and (translate_monadic :
  (FStarC_Syntax_Syntax.monad_name * FStarC_Syntax_Syntax.term'
    FStarC_Syntax_Syntax.syntax) ->
    config ->
      FStarC_TypeChecker_NBETerm.t Prims.list ->
        FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax ->
          FStarC_TypeChecker_NBETerm.t)
  =
  fun uu___ ->
    fun cfg ->
      fun bs ->
        fun e ->
          match uu___ with
          | (m, ty) ->
              let e1 = FStarC_Syntax_Util.unascribe e in
              (match e1.FStarC_Syntax_Syntax.n with
               | FStarC_Syntax_Syntax.Tm_let
                   { FStarC_Syntax_Syntax.lbs = (false, lb::[]);
                     FStarC_Syntax_Syntax.body1 = body;_}
                   ->
                   let uu___1 =
                     let uu___2 =
                       FStarC_TypeChecker_Env.norm_eff_name
                         (cfg.core_cfg).FStarC_TypeChecker_Cfg.tcenv m in
                     FStarC_TypeChecker_Env.effect_decl_opt
                       (cfg.core_cfg).FStarC_TypeChecker_Cfg.tcenv uu___2 in
                   (match uu___1 with
                    | FStar_Pervasives_Native.None ->
                        let uu___2 =
                          let uu___3 = FStarC_Ident.string_of_lid m in
                          FStarC_Compiler_Util.format1
                            "Effect declaration not found: %s" uu___3 in
                        failwith uu___2
                    | FStar_Pervasives_Native.Some (ed, q) ->
                        let cfg' = reifying_false cfg in
                        let body_lam =
                          let body_rc =
                            {
                              FStarC_Syntax_Syntax.residual_effect = m;
                              FStarC_Syntax_Syntax.residual_typ =
                                (FStar_Pervasives_Native.Some ty);
                              FStarC_Syntax_Syntax.residual_flags = []
                            } in
                          let uu___2 =
                            let uu___3 =
                              let uu___4 =
                                let uu___5 =
                                  let uu___6 =
                                    FStarC_Compiler_Util.left
                                      lb.FStarC_Syntax_Syntax.lbname in
                                  FStarC_Syntax_Syntax.mk_binder uu___6 in
                                [uu___5] in
                              {
                                FStarC_Syntax_Syntax.bs = uu___4;
                                FStarC_Syntax_Syntax.body = body;
                                FStarC_Syntax_Syntax.rc_opt =
                                  (FStar_Pervasives_Native.Some body_rc)
                              } in
                            FStarC_Syntax_Syntax.Tm_abs uu___3 in
                          FStarC_Syntax_Syntax.mk uu___2
                            body.FStarC_Syntax_Syntax.pos in
                        let maybe_range_arg =
                          let uu___2 =
                            FStarC_Compiler_Util.for_some
                              (FStarC_TypeChecker_TermEqAndSimplify.eq_tm_bool
                                 (cfg.core_cfg).FStarC_TypeChecker_Cfg.tcenv
                                 FStarC_Syntax_Util.dm4f_bind_range_attr)
                              ed.FStarC_Syntax_Syntax.eff_attrs in
                          if uu___2
                          then
                            let uu___3 =
                              let uu___4 =
                                let uu___5 =
                                  FStarC_TypeChecker_Primops_Base.embed_simple
                                    FStarC_Syntax_Embeddings.e_range
                                    lb.FStarC_Syntax_Syntax.lbpos
                                    lb.FStarC_Syntax_Syntax.lbpos in
                                translate cfg [] uu___5 in
                              (uu___4, FStar_Pervasives_Native.None) in
                            let uu___4 =
                              let uu___5 =
                                let uu___6 =
                                  let uu___7 =
                                    FStarC_TypeChecker_Primops_Base.embed_simple
                                      FStarC_Syntax_Embeddings.e_range
                                      body.FStarC_Syntax_Syntax.pos
                                      body.FStarC_Syntax_Syntax.pos in
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
                                      FStarC_Syntax_Util.get_bind_repr ed in
                                    FStarC_Compiler_Util.must uu___7 in
                                  FStar_Pervasives_Native.snd uu___6 in
                                FStarC_Syntax_Util.un_uinst uu___5 in
                              translate cfg' [] uu___4 in
                            iapp cfg uu___3
                              [((mk_t
                                   (FStarC_TypeChecker_NBETerm.Univ
                                      FStarC_Syntax_Syntax.U_unknown)),
                                 FStar_Pervasives_Native.None);
                              ((mk_t
                                  (FStarC_TypeChecker_NBETerm.Univ
                                     FStarC_Syntax_Syntax.U_unknown)),
                                FStar_Pervasives_Native.None)] in
                          let uu___3 =
                            let uu___4 =
                              let uu___5 =
                                let uu___6 =
                                  translate cfg' bs
                                    lb.FStarC_Syntax_Syntax.lbtyp in
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
                                        lb.FStarC_Syntax_Syntax.lbdef in
                                    (uu___9, FStar_Pervasives_Native.None) in
                                  let uu___9 =
                                    let uu___10 =
                                      let uu___11 =
                                        let uu___12 =
                                          translate cfg bs body_lam in
                                        (uu___12,
                                          FStar_Pervasives_Native.None) in
                                      [uu___11] in
                                    ((mk_t FStarC_TypeChecker_NBETerm.Unknown),
                                      FStar_Pervasives_Native.None) ::
                                      uu___10 in
                                  uu___8 :: uu___9 in
                                ((mk_t FStarC_TypeChecker_NBETerm.Unknown),
                                  FStar_Pervasives_Native.None) :: uu___7 in
                              FStarC_Compiler_List.op_At maybe_range_arg
                                uu___6 in
                            FStarC_Compiler_List.op_At uu___4 uu___5 in
                          iapp cfg uu___2 uu___3 in
                        (debug cfg
                           (fun uu___3 ->
                              let uu___4 =
                                FStarC_TypeChecker_NBETerm.t_to_string t in
                              FStarC_Compiler_Util.print1
                                "translate_monadic: %s\n" uu___4);
                         t))
               | FStarC_Syntax_Syntax.Tm_app
                   {
                     FStarC_Syntax_Syntax.hd =
                       {
                         FStarC_Syntax_Syntax.n =
                           FStarC_Syntax_Syntax.Tm_constant
                           (FStarC_Const.Const_reflect uu___1);
                         FStarC_Syntax_Syntax.pos = uu___2;
                         FStarC_Syntax_Syntax.vars = uu___3;
                         FStarC_Syntax_Syntax.hash_code = uu___4;_};
                     FStarC_Syntax_Syntax.args = (e2, uu___5)::[];_}
                   ->
                   let uu___6 = reifying_false cfg in translate uu___6 bs e2
               | FStarC_Syntax_Syntax.Tm_app
                   { FStarC_Syntax_Syntax.hd = head;
                     FStarC_Syntax_Syntax.args = args;_}
                   ->
                   (debug cfg
                      (fun uu___2 ->
                         let uu___3 =
                           FStarC_Class_Show.show
                             FStarC_Syntax_Print.showable_term head in
                         let uu___4 =
                           FStarC_Class_Show.show
                             (FStarC_Class_Show.show_list
                                (FStarC_Class_Show.show_tuple2
                                   FStarC_Syntax_Print.showable_term
                                   FStarC_Syntax_Print.showable_aqual)) args in
                         FStarC_Compiler_Util.print2
                           "translate_monadic app (%s) @ (%s)\n" uu___3
                           uu___4);
                    (let fallback1 uu___2 = translate cfg bs e1 in
                     let fallback2 uu___2 =
                       let uu___3 = reifying_false cfg in
                       let uu___4 =
                         FStarC_Syntax_Syntax.mk
                           (FStarC_Syntax_Syntax.Tm_meta
                              {
                                FStarC_Syntax_Syntax.tm2 = e1;
                                FStarC_Syntax_Syntax.meta =
                                  (FStarC_Syntax_Syntax.Meta_monadic (m, ty))
                              }) e1.FStarC_Syntax_Syntax.pos in
                       translate uu___3 bs uu___4 in
                     let uu___2 =
                       let uu___3 = FStarC_Syntax_Util.un_uinst head in
                       uu___3.FStarC_Syntax_Syntax.n in
                     match uu___2 with
                     | FStarC_Syntax_Syntax.Tm_fvar fv ->
                         let lid = FStarC_Syntax_Syntax.lid_of_fv fv in
                         let qninfo =
                           FStarC_TypeChecker_Env.lookup_qname
                             (cfg.core_cfg).FStarC_TypeChecker_Cfg.tcenv lid in
                         let uu___3 =
                           let uu___4 =
                             FStarC_TypeChecker_Env.is_action
                               (cfg.core_cfg).FStarC_TypeChecker_Cfg.tcenv
                               lid in
                           Prims.op_Negation uu___4 in
                         if uu___3
                         then fallback1 ()
                         else
                           (let uu___5 =
                              let uu___6 =
                                FStarC_TypeChecker_Env.lookup_definition_qninfo
                                  (cfg.core_cfg).FStarC_TypeChecker_Cfg.delta_level
                                  (fv.FStarC_Syntax_Syntax.fv_name).FStarC_Syntax_Syntax.v
                                  qninfo in
                              FStarC_Compiler_Option.isNone uu___6 in
                            if uu___5
                            then fallback2 ()
                            else
                              (let e2 =
                                 let uu___7 =
                                   FStarC_Syntax_Util.mk_reify head
                                     FStar_Pervasives_Native.None in
                                 FStarC_Syntax_Syntax.mk_Tm_app uu___7 args
                                   e1.FStarC_Syntax_Syntax.pos in
                               let uu___7 = reifying_false cfg in
                               translate uu___7 bs e2))
                     | uu___3 -> fallback1 ()))
               | FStarC_Syntax_Syntax.Tm_match
                   { FStarC_Syntax_Syntax.scrutinee = sc;
                     FStarC_Syntax_Syntax.ret_opt = asc_opt;
                     FStarC_Syntax_Syntax.brs = branches;
                     FStarC_Syntax_Syntax.rc_opt1 = lopt;_}
                   ->
                   let branches1 =
                     FStarC_Compiler_List.map
                       (fun uu___1 ->
                          match uu___1 with
                          | (pat, wopt, tm) ->
                              let uu___2 =
                                FStarC_Syntax_Util.mk_reify tm
                                  (FStar_Pervasives_Native.Some m) in
                              (pat, wopt, uu___2)) branches in
                   let tm =
                     FStarC_Syntax_Syntax.mk
                       (FStarC_Syntax_Syntax.Tm_match
                          {
                            FStarC_Syntax_Syntax.scrutinee = sc;
                            FStarC_Syntax_Syntax.ret_opt = asc_opt;
                            FStarC_Syntax_Syntax.brs = branches1;
                            FStarC_Syntax_Syntax.rc_opt1 = lopt
                          }) e1.FStarC_Syntax_Syntax.pos in
                   let uu___1 = reifying_false cfg in translate uu___1 bs tm
               | FStarC_Syntax_Syntax.Tm_meta
                   { FStarC_Syntax_Syntax.tm2 = t;
                     FStarC_Syntax_Syntax.meta =
                       FStarC_Syntax_Syntax.Meta_monadic uu___1;_}
                   -> translate_monadic (m, ty) cfg bs e1
               | FStarC_Syntax_Syntax.Tm_meta
                   { FStarC_Syntax_Syntax.tm2 = t;
                     FStarC_Syntax_Syntax.meta =
                       FStarC_Syntax_Syntax.Meta_monadic_lift
                       (msrc, mtgt, ty');_}
                   -> translate_monadic_lift (msrc, mtgt, ty') cfg bs e1
               | uu___1 ->
                   let uu___2 =
                     let uu___3 =
                       FStarC_Class_Tagged.tag_of
                         FStarC_Syntax_Syntax.tagged_term e1 in
                     FStarC_Compiler_Util.format1
                       "Unexpected case in translate_monadic: %s" uu___3 in
                   failwith uu___2)
and (translate_monadic_lift :
  (FStarC_Syntax_Syntax.monad_name * FStarC_Syntax_Syntax.monad_name *
    FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax) ->
    config ->
      FStarC_TypeChecker_NBETerm.t Prims.list ->
        FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax ->
          FStarC_TypeChecker_NBETerm.t)
  =
  fun uu___ ->
    fun cfg ->
      fun bs ->
        fun e ->
          match uu___ with
          | (msrc, mtgt, ty) ->
              let e1 = FStarC_Syntax_Util.unascribe e in
              let uu___1 =
                (FStarC_Syntax_Util.is_pure_effect msrc) ||
                  (FStarC_Syntax_Util.is_div_effect msrc) in
              if uu___1
              then
                let ed =
                  let uu___2 =
                    FStarC_TypeChecker_Env.norm_eff_name
                      (cfg.core_cfg).FStarC_TypeChecker_Cfg.tcenv mtgt in
                  FStarC_TypeChecker_Env.get_effect_decl
                    (cfg.core_cfg).FStarC_TypeChecker_Cfg.tcenv uu___2 in
                let ret =
                  let uu___2 =
                    let uu___3 =
                      let uu___4 =
                        let uu___5 =
                          let uu___6 = FStarC_Syntax_Util.get_return_repr ed in
                          FStarC_Compiler_Util.must uu___6 in
                        FStar_Pervasives_Native.snd uu___5 in
                      FStarC_Syntax_Subst.compress uu___4 in
                    uu___3.FStarC_Syntax_Syntax.n in
                  match uu___2 with
                  | FStarC_Syntax_Syntax.Tm_uinst (ret1, uu___3::[]) ->
                      FStarC_Syntax_Syntax.mk
                        (FStarC_Syntax_Syntax.Tm_uinst
                           (ret1, [FStarC_Syntax_Syntax.U_unknown]))
                        e1.FStarC_Syntax_Syntax.pos
                  | uu___3 ->
                      failwith "NYI: Reification of indexed effect (NBE)" in
                let cfg' = reifying_false cfg in
                let t =
                  let uu___2 =
                    let uu___3 = translate cfg' [] ret in
                    iapp cfg' uu___3
                      [((mk_t
                           (FStarC_TypeChecker_NBETerm.Univ
                              FStarC_Syntax_Syntax.U_unknown)),
                         FStar_Pervasives_Native.None)] in
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
                      let uu___4 = FStarC_TypeChecker_NBETerm.t_to_string t in
                      FStarC_Compiler_Util.print1
                        "translate_monadic_lift(1): %s\n" uu___4);
                 t)
              else
                (let uu___3 =
                   FStarC_TypeChecker_Env.monad_leq
                     (cfg.core_cfg).FStarC_TypeChecker_Cfg.tcenv msrc mtgt in
                 match uu___3 with
                 | FStar_Pervasives_Native.None ->
                     let uu___4 =
                       let uu___5 = FStarC_Ident.string_of_lid msrc in
                       let uu___6 = FStarC_Ident.string_of_lid mtgt in
                       FStarC_Compiler_Util.format2
                         "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                         uu___5 uu___6 in
                     failwith uu___4
                 | FStar_Pervasives_Native.Some
                     { FStarC_TypeChecker_Env.msource = uu___4;
                       FStarC_TypeChecker_Env.mtarget = uu___5;
                       FStarC_TypeChecker_Env.mlift =
                         { FStarC_TypeChecker_Env.mlift_wp = uu___6;
                           FStarC_TypeChecker_Env.mlift_term =
                             FStar_Pervasives_Native.None;_};
                       FStarC_TypeChecker_Env.mpath = uu___7;_}
                     ->
                     let uu___8 =
                       let uu___9 = FStarC_Ident.string_of_lid msrc in
                       let uu___10 = FStarC_Ident.string_of_lid mtgt in
                       FStarC_Compiler_Util.format2
                         "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
                         uu___9 uu___10 in
                     failwith uu___8
                 | FStar_Pervasives_Native.Some
                     { FStarC_TypeChecker_Env.msource = uu___4;
                       FStarC_TypeChecker_Env.mtarget = uu___5;
                       FStarC_TypeChecker_Env.mlift =
                         { FStarC_TypeChecker_Env.mlift_wp = uu___6;
                           FStarC_TypeChecker_Env.mlift_term =
                             FStar_Pervasives_Native.Some lift;_};
                       FStarC_TypeChecker_Env.mpath = uu___7;_}
                     ->
                     let lift_lam =
                       let x =
                         FStarC_Syntax_Syntax.new_bv
                           FStar_Pervasives_Native.None
                           FStarC_Syntax_Syntax.tun in
                       let uu___8 =
                         let uu___9 = FStarC_Syntax_Syntax.mk_binder x in
                         [uu___9] in
                       let uu___9 =
                         let uu___10 = FStarC_Syntax_Syntax.bv_to_name x in
                         lift FStarC_Syntax_Syntax.U_unknown ty uu___10 in
                       FStarC_Syntax_Util.abs uu___8 uu___9
                         FStar_Pervasives_Native.None in
                     let cfg' = reifying_false cfg in
                     let t =
                       let uu___8 = translate cfg' [] lift_lam in
                       let uu___9 =
                         let uu___10 =
                           let uu___11 = translate cfg bs e1 in
                           (uu___11, FStar_Pervasives_Native.None) in
                         [uu___10] in
                       iapp cfg uu___8 uu___9 in
                     (debug cfg
                        (fun uu___9 ->
                           let uu___10 =
                             FStarC_TypeChecker_NBETerm.t_to_string t in
                           FStarC_Compiler_Util.print1
                             "translate_monadic_lift(2): %s\n" uu___10);
                      t))
and (readback :
  config -> FStarC_TypeChecker_NBETerm.t -> FStarC_Syntax_Syntax.term) =
  fun cfg ->
    fun x ->
      let debug1 = debug cfg in
      let readback_args cfg1 args =
        map_rev
          (fun uu___ ->
             match uu___ with
             | (x1, q) -> let uu___1 = readback cfg1 x1 in (uu___1, q)) args in
      let with_range t =
        {
          FStarC_Syntax_Syntax.n = (t.FStarC_Syntax_Syntax.n);
          FStarC_Syntax_Syntax.pos = (x.FStarC_TypeChecker_NBETerm.nbe_r);
          FStarC_Syntax_Syntax.vars = (t.FStarC_Syntax_Syntax.vars);
          FStarC_Syntax_Syntax.hash_code = (t.FStarC_Syntax_Syntax.hash_code)
        } in
      let mk t = FStarC_Syntax_Syntax.mk t x.FStarC_TypeChecker_NBETerm.nbe_r in
      debug1
        (fun uu___1 ->
           let uu___2 = FStarC_TypeChecker_NBETerm.t_to_string x in
           FStarC_Compiler_Util.print1 "Readback: %s\n" uu___2);
      (match x.FStarC_TypeChecker_NBETerm.nbe_t with
       | FStarC_TypeChecker_NBETerm.Univ u ->
           failwith "Readback of universes should not occur"
       | FStarC_TypeChecker_NBETerm.Unknown ->
           FStarC_Syntax_Syntax.mk FStarC_Syntax_Syntax.Tm_unknown
             x.FStarC_TypeChecker_NBETerm.nbe_r
       | FStarC_TypeChecker_NBETerm.Constant
           (FStarC_TypeChecker_NBETerm.Unit) ->
           with_range FStarC_Syntax_Syntax.unit_const
       | FStarC_TypeChecker_NBETerm.Constant (FStarC_TypeChecker_NBETerm.Bool
           (true)) -> with_range FStarC_Syntax_Util.exp_true_bool
       | FStarC_TypeChecker_NBETerm.Constant (FStarC_TypeChecker_NBETerm.Bool
           (false)) -> with_range FStarC_Syntax_Util.exp_false_bool
       | FStarC_TypeChecker_NBETerm.Constant (FStarC_TypeChecker_NBETerm.Int
           i) ->
           let uu___1 =
             let uu___2 = FStarC_BigInt.string_of_big_int i in
             FStarC_Syntax_Util.exp_int uu___2 in
           with_range uu___1
       | FStarC_TypeChecker_NBETerm.Constant
           (FStarC_TypeChecker_NBETerm.String (s, r)) ->
           mk
             (FStarC_Syntax_Syntax.Tm_constant
                (FStarC_Const.Const_string (s, r)))
       | FStarC_TypeChecker_NBETerm.Constant (FStarC_TypeChecker_NBETerm.Char
           c) ->
           let uu___1 = FStarC_Syntax_Util.exp_char c in with_range uu___1
       | FStarC_TypeChecker_NBETerm.Constant
           (FStarC_TypeChecker_NBETerm.Range r) ->
           FStarC_TypeChecker_Primops_Base.embed_simple
             FStarC_Syntax_Embeddings.e___range
             x.FStarC_TypeChecker_NBETerm.nbe_r r
       | FStarC_TypeChecker_NBETerm.Constant (FStarC_TypeChecker_NBETerm.Real
           r) ->
           FStarC_TypeChecker_Primops_Base.embed_simple
             FStarC_Syntax_Embeddings.e_real
             x.FStarC_TypeChecker_NBETerm.nbe_r (FStarC_Compiler_Real.Real r)
       | FStarC_TypeChecker_NBETerm.Constant
           (FStarC_TypeChecker_NBETerm.SConst c) ->
           mk (FStarC_Syntax_Syntax.Tm_constant c)
       | FStarC_TypeChecker_NBETerm.Meta (t, m) ->
           let uu___1 =
             let uu___2 =
               let uu___3 = readback cfg t in
               let uu___4 = FStarC_Thunk.force m in
               {
                 FStarC_Syntax_Syntax.tm2 = uu___3;
                 FStarC_Syntax_Syntax.meta = uu___4
               } in
             FStarC_Syntax_Syntax.Tm_meta uu___2 in
           mk uu___1
       | FStarC_TypeChecker_NBETerm.Type_t u ->
           mk (FStarC_Syntax_Syntax.Tm_type u)
       | FStarC_TypeChecker_NBETerm.Lam
           { FStarC_TypeChecker_NBETerm.interp = f;
             FStarC_TypeChecker_NBETerm.shape = shape;
             FStarC_TypeChecker_NBETerm.arity = arity;_}
           ->
           (match shape with
            | FStarC_TypeChecker_NBETerm.Lam_bs (ctx, binders, rc) ->
                let uu___1 =
                  FStarC_Compiler_List.fold_left
                    (fun uu___2 ->
                       fun b ->
                         match uu___2 with
                         | (ctx1, binders_rev, accus_rev) ->
                             let x1 = b.FStarC_Syntax_Syntax.binder_bv in
                             let tnorm =
                               let uu___3 =
                                 translate cfg ctx1
                                   x1.FStarC_Syntax_Syntax.sort in
                               readback cfg uu___3 in
                             let x2 =
                               let uu___3 =
                                 FStarC_Syntax_Syntax.freshen_bv x1 in
                               {
                                 FStarC_Syntax_Syntax.ppname =
                                   (uu___3.FStarC_Syntax_Syntax.ppname);
                                 FStarC_Syntax_Syntax.index =
                                   (uu___3.FStarC_Syntax_Syntax.index);
                                 FStarC_Syntax_Syntax.sort = tnorm
                               } in
                             let ax = FStarC_TypeChecker_NBETerm.mkAccuVar x2 in
                             let ctx2 = ax :: ctx1 in
                             let uu___3 =
                               let uu___4 =
                                 let uu___5 =
                                   FStarC_Syntax_Util.aqual_of_binder b in
                                 (ax, uu___5) in
                               uu___4 :: accus_rev in
                             (ctx2,
                               ({
                                  FStarC_Syntax_Syntax.binder_bv = x2;
                                  FStarC_Syntax_Syntax.binder_qual =
                                    (b.FStarC_Syntax_Syntax.binder_qual);
                                  FStarC_Syntax_Syntax.binder_positivity =
                                    (b.FStarC_Syntax_Syntax.binder_positivity);
                                  FStarC_Syntax_Syntax.binder_attrs =
                                    (b.FStarC_Syntax_Syntax.binder_attrs)
                                } :: binders_rev), uu___3)) (ctx, [], [])
                    binders in
                (match uu___1 with
                 | (ctx1, binders_rev, accus_rev) ->
                     let rc1 =
                       match rc with
                       | FStar_Pervasives_Native.None ->
                           FStar_Pervasives_Native.None
                       | FStar_Pervasives_Native.Some rc2 ->
                           let uu___2 =
                             let uu___3 =
                               translate_residual_comp cfg ctx1 rc2 in
                             readback_residual_comp cfg uu___3 in
                           FStar_Pervasives_Native.Some uu___2 in
                     let binders1 = FStarC_Compiler_List.rev binders_rev in
                     let body =
                       let uu___2 = f accus_rev in readback cfg uu___2 in
                     let uu___2 = FStarC_Syntax_Util.abs binders1 body rc1 in
                     with_range uu___2)
            | FStarC_TypeChecker_NBETerm.Lam_args args ->
                let uu___1 =
                  FStarC_Compiler_List.fold_right
                    (fun uu___2 ->
                       fun uu___3 ->
                         match (uu___2, uu___3) with
                         | ((t, aq), (binders, accus)) ->
                             let uu___4 =
                               FStarC_Syntax_Util.bqual_and_attrs_of_aqual aq in
                             (match uu___4 with
                              | (bqual, battrs) ->
                                  let uu___5 =
                                    FStarC_Syntax_Util.parse_positivity_attributes
                                      battrs in
                                  (match uu___5 with
                                   | (pqual, battrs1) ->
                                       let x1 =
                                         let uu___6 = readback cfg t in
                                         FStarC_Syntax_Syntax.new_bv
                                           FStar_Pervasives_Native.None
                                           uu___6 in
                                       let uu___6 =
                                         let uu___7 =
                                           FStarC_Syntax_Syntax.mk_binder_with_attrs
                                             x1 bqual pqual battrs1 in
                                         uu___7 :: binders in
                                       let uu___7 =
                                         let uu___8 =
                                           let uu___9 =
                                             FStarC_TypeChecker_NBETerm.mkAccuVar
                                               x1 in
                                           (uu___9, aq) in
                                         uu___8 :: accus in
                                       (uu___6, uu___7)))) args ([], []) in
                (match uu___1 with
                 | (binders, accus_rev) ->
                     let accus = FStarC_Compiler_List.rev accus_rev in
                     let rc = FStar_Pervasives_Native.None in
                     let body =
                       let uu___2 = f accus_rev in readback cfg uu___2 in
                     let uu___2 = FStarC_Syntax_Util.abs binders body rc in
                     with_range uu___2)
            | FStarC_TypeChecker_NBETerm.Lam_primop (fv, args) ->
                let body =
                  let uu___1 =
                    let uu___2 = FStarC_Syntax_Syntax.range_of_fv fv in
                    FStarC_Syntax_Syntax.mk (FStarC_Syntax_Syntax.Tm_fvar fv)
                      uu___2 in
                  let uu___2 = readback_args cfg args in
                  FStarC_Syntax_Util.mk_app uu___1 uu___2 in
                with_range body)
       | FStarC_TypeChecker_NBETerm.Refinement (f, targ) ->
           if
             ((cfg.core_cfg).FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.for_extraction
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
                FStarC_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                  uu___2 in
              let body =
                let uu___2 =
                  let uu___3 = FStarC_TypeChecker_NBETerm.mkAccuVar x1 in
                  f uu___3 in
                readback cfg uu___2 in
              let refinement = FStarC_Syntax_Util.refine x1 body in
              let uu___2 =
                if
                  ((cfg.core_cfg).FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.simplify
                then
                  FStarC_TypeChecker_TermEqAndSimplify.simplify
                    ((cfg.core_cfg).FStarC_TypeChecker_Cfg.debug).FStarC_TypeChecker_Cfg.wpe
                    (cfg.core_cfg).FStarC_TypeChecker_Cfg.tcenv refinement
                else refinement in
              with_range uu___2)
       | FStarC_TypeChecker_NBETerm.Reflect t ->
           let tm = readback cfg t in
           let uu___1 = FStarC_Syntax_Util.mk_reflect tm in with_range uu___1
       | FStarC_TypeChecker_NBETerm.Arrow (FStar_Pervasives.Inl f) ->
           let uu___1 = FStarC_Thunk.force f in with_range uu___1
       | FStarC_TypeChecker_NBETerm.Arrow (FStar_Pervasives.Inr (args, c)) ->
           let binders =
             FStarC_Compiler_List.map
               (fun uu___1 ->
                  match uu___1 with
                  | (t, q) ->
                      let t1 = readback cfg t in
                      let x1 =
                        FStarC_Syntax_Syntax.new_bv
                          FStar_Pervasives_Native.None t1 in
                      let uu___2 =
                        FStarC_Syntax_Util.bqual_and_attrs_of_aqual q in
                      (match uu___2 with
                       | (q1, attrs) ->
                           let uu___3 =
                             FStarC_Syntax_Util.parse_positivity_attributes
                               attrs in
                           (match uu___3 with
                            | (pqual, attrs1) ->
                                FStarC_Syntax_Syntax.mk_binder_with_attrs x1
                                  q1 pqual attrs1))) args in
           let c1 = readback_comp cfg c in
           let uu___1 = FStarC_Syntax_Util.arrow binders c1 in
           with_range uu___1
       | FStarC_TypeChecker_NBETerm.Construct (fv, us, args) ->
           let args1 =
             map_rev
               (fun uu___1 ->
                  match uu___1 with
                  | (x1, q) -> let uu___2 = readback cfg x1 in (uu___2, q))
               args in
           let fv1 =
             let uu___1 = FStarC_Syntax_Syntax.range_of_fv fv in
             FStarC_Syntax_Syntax.mk (FStarC_Syntax_Syntax.Tm_fvar fv) uu___1 in
           let app =
             let uu___1 =
               FStarC_Syntax_Syntax.mk_Tm_uinst fv1
                 (FStarC_Compiler_List.rev us) in
             FStarC_Syntax_Util.mk_app uu___1 args1 in
           with_range app
       | FStarC_TypeChecker_NBETerm.FV (fv, us, args) ->
           let args1 =
             map_rev
               (fun uu___1 ->
                  match uu___1 with
                  | (x1, q) -> let uu___2 = readback cfg x1 in (uu___2, q))
               args in
           let fv1 =
             FStarC_Syntax_Syntax.mk (FStarC_Syntax_Syntax.Tm_fvar fv)
               FStarC_Compiler_Range_Type.dummyRange in
           let app =
             let uu___1 =
               FStarC_Syntax_Syntax.mk_Tm_uinst fv1
                 (FStarC_Compiler_List.rev us) in
             FStarC_Syntax_Util.mk_app uu___1 args1 in
           let uu___1 =
             if
               ((cfg.core_cfg).FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.simplify
             then
               FStarC_TypeChecker_TermEqAndSimplify.simplify
                 ((cfg.core_cfg).FStarC_TypeChecker_Cfg.debug).FStarC_TypeChecker_Cfg.wpe
                 (cfg.core_cfg).FStarC_TypeChecker_Cfg.tcenv app
             else app in
           with_range uu___1
       | FStarC_TypeChecker_NBETerm.Accu
           (FStarC_TypeChecker_NBETerm.Var bv, []) ->
           let uu___1 = FStarC_Syntax_Syntax.bv_to_name bv in
           with_range uu___1
       | FStarC_TypeChecker_NBETerm.Accu
           (FStarC_TypeChecker_NBETerm.Var bv, args) ->
           let args1 = readback_args cfg args in
           let app =
             let uu___1 = FStarC_Syntax_Syntax.bv_to_name bv in
             FStarC_Syntax_Util.mk_app uu___1 args1 in
           let uu___1 =
             if
               ((cfg.core_cfg).FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.simplify
             then
               FStarC_TypeChecker_TermEqAndSimplify.simplify
                 ((cfg.core_cfg).FStarC_TypeChecker_Cfg.debug).FStarC_TypeChecker_Cfg.wpe
                 (cfg.core_cfg).FStarC_TypeChecker_Cfg.tcenv app
             else app in
           with_range uu___1
       | FStarC_TypeChecker_NBETerm.Accu
           (FStarC_TypeChecker_NBETerm.Match
            (scrut, make_returns, make_branches, make_rc), args)
           ->
           let args1 = readback_args cfg args in
           let head =
             let scrut_new = readback cfg scrut in
             let returns_new = make_returns () in
             let branches_new = make_branches () in
             let rc_new = make_rc () in
             FStarC_Syntax_Syntax.mk
               (FStarC_Syntax_Syntax.Tm_match
                  {
                    FStarC_Syntax_Syntax.scrutinee = scrut_new;
                    FStarC_Syntax_Syntax.ret_opt = returns_new;
                    FStarC_Syntax_Syntax.brs = branches_new;
                    FStarC_Syntax_Syntax.rc_opt1 = rc_new
                  }) scrut.FStarC_TypeChecker_NBETerm.nbe_r in
           let app = FStarC_Syntax_Util.mk_app head args1 in
           let uu___1 =
             if
               ((cfg.core_cfg).FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.simplify
             then
               FStarC_TypeChecker_TermEqAndSimplify.simplify
                 ((cfg.core_cfg).FStarC_TypeChecker_Cfg.debug).FStarC_TypeChecker_Cfg.wpe
                 (cfg.core_cfg).FStarC_TypeChecker_Cfg.tcenv app
             else app in
           with_range uu___1
       | FStarC_TypeChecker_NBETerm.Accu
           (FStarC_TypeChecker_NBETerm.UnreducedLet
            (var, typ, defn, body, lb), args)
           ->
           let typ1 =
             let uu___1 = FStarC_Thunk.force typ in readback cfg uu___1 in
           let defn1 =
             let uu___1 = FStarC_Thunk.force defn in readback cfg uu___1 in
           let body1 =
             let uu___1 =
               let uu___2 = FStarC_Syntax_Syntax.mk_binder var in [uu___2] in
             let uu___2 =
               let uu___3 = FStarC_Thunk.force body in readback cfg uu___3 in
             FStarC_Syntax_Subst.close uu___1 uu___2 in
           let lbname =
             let uu___1 =
               let uu___2 =
                 FStarC_Compiler_Util.left lb.FStarC_Syntax_Syntax.lbname in
               {
                 FStarC_Syntax_Syntax.ppname =
                   (uu___2.FStarC_Syntax_Syntax.ppname);
                 FStarC_Syntax_Syntax.index =
                   (uu___2.FStarC_Syntax_Syntax.index);
                 FStarC_Syntax_Syntax.sort = typ1
               } in
             FStar_Pervasives.Inl uu___1 in
           let lb1 =
             {
               FStarC_Syntax_Syntax.lbname = lbname;
               FStarC_Syntax_Syntax.lbunivs =
                 (lb.FStarC_Syntax_Syntax.lbunivs);
               FStarC_Syntax_Syntax.lbtyp = typ1;
               FStarC_Syntax_Syntax.lbeff = (lb.FStarC_Syntax_Syntax.lbeff);
               FStarC_Syntax_Syntax.lbdef = defn1;
               FStarC_Syntax_Syntax.lbattrs =
                 (lb.FStarC_Syntax_Syntax.lbattrs);
               FStarC_Syntax_Syntax.lbpos = (lb.FStarC_Syntax_Syntax.lbpos)
             } in
           let hd =
             FStarC_Syntax_Syntax.mk
               (FStarC_Syntax_Syntax.Tm_let
                  {
                    FStarC_Syntax_Syntax.lbs = (false, [lb1]);
                    FStarC_Syntax_Syntax.body1 = body1
                  }) FStarC_Compiler_Range_Type.dummyRange in
           let args1 = readback_args cfg args in
           let uu___1 = FStarC_Syntax_Util.mk_app hd args1 in
           with_range uu___1
       | FStarC_TypeChecker_NBETerm.Accu
           (FStarC_TypeChecker_NBETerm.UnreducedLetRec
            (vars_typs_defns, body, lbs), args)
           ->
           let lbs1 =
             FStarC_Compiler_List.map2
               (fun uu___1 ->
                  fun lb ->
                    match uu___1 with
                    | (v, t, d) ->
                        let t1 = readback cfg t in
                        let def = readback cfg d in
                        let v1 =
                          {
                            FStarC_Syntax_Syntax.ppname =
                              (v.FStarC_Syntax_Syntax.ppname);
                            FStarC_Syntax_Syntax.index =
                              (v.FStarC_Syntax_Syntax.index);
                            FStarC_Syntax_Syntax.sort = t1
                          } in
                        {
                          FStarC_Syntax_Syntax.lbname =
                            (FStar_Pervasives.Inl v1);
                          FStarC_Syntax_Syntax.lbunivs =
                            (lb.FStarC_Syntax_Syntax.lbunivs);
                          FStarC_Syntax_Syntax.lbtyp = t1;
                          FStarC_Syntax_Syntax.lbeff =
                            (lb.FStarC_Syntax_Syntax.lbeff);
                          FStarC_Syntax_Syntax.lbdef = def;
                          FStarC_Syntax_Syntax.lbattrs =
                            (lb.FStarC_Syntax_Syntax.lbattrs);
                          FStarC_Syntax_Syntax.lbpos =
                            (lb.FStarC_Syntax_Syntax.lbpos)
                        }) vars_typs_defns lbs in
           let body1 = readback cfg body in
           let uu___1 = FStarC_Syntax_Subst.close_let_rec lbs1 body1 in
           (match uu___1 with
            | (lbs2, body2) ->
                let hd =
                  FStarC_Syntax_Syntax.mk
                    (FStarC_Syntax_Syntax.Tm_let
                       {
                         FStarC_Syntax_Syntax.lbs = (true, lbs2);
                         FStarC_Syntax_Syntax.body1 = body2
                       }) FStarC_Compiler_Range_Type.dummyRange in
                let args1 = readback_args cfg args in
                let uu___2 = FStarC_Syntax_Util.mk_app hd args1 in
                with_range uu___2)
       | FStarC_TypeChecker_NBETerm.Accu
           (FStarC_TypeChecker_NBETerm.UVar f, args) ->
           let hd = FStarC_Thunk.force f in
           let args1 = readback_args cfg args in
           let uu___1 = FStarC_Syntax_Util.mk_app hd args1 in
           with_range uu___1
       | FStarC_TypeChecker_NBETerm.TopLevelLet (lb, arity, args_rev) ->
           let n_univs =
             FStarC_Compiler_List.length lb.FStarC_Syntax_Syntax.lbunivs in
           let n_args = FStarC_Compiler_List.length args_rev in
           let uu___1 =
             FStarC_Compiler_Util.first_N (n_args - n_univs) args_rev in
           (match uu___1 with
            | (args_rev1, univs) ->
                let uu___2 =
                  let uu___3 =
                    let uu___4 =
                      FStarC_Compiler_List.map FStar_Pervasives_Native.fst
                        univs in
                    translate cfg uu___4 lb.FStarC_Syntax_Syntax.lbdef in
                  iapp cfg uu___3 (FStarC_Compiler_List.rev args_rev1) in
                readback cfg uu___2)
       | FStarC_TypeChecker_NBETerm.TopLevelRec (lb, uu___1, uu___2, args) ->
           let fv = FStarC_Compiler_Util.right lb.FStarC_Syntax_Syntax.lbname in
           let head =
             FStarC_Syntax_Syntax.mk (FStarC_Syntax_Syntax.Tm_fvar fv)
               FStarC_Compiler_Range_Type.dummyRange in
           let args1 =
             FStarC_Compiler_List.map
               (fun uu___3 ->
                  match uu___3 with
                  | (t, q) -> let uu___4 = readback cfg t in (uu___4, q))
               args in
           let uu___3 = FStarC_Syntax_Util.mk_app head args1 in
           with_range uu___3
       | FStarC_TypeChecker_NBETerm.LocalLetRec
           (i, uu___1, lbs, bs, args, _ar, _ar_lst) ->
           let lbnames =
             FStarC_Compiler_List.map
               (fun lb ->
                  let uu___2 =
                    let uu___3 =
                      let uu___4 =
                        FStarC_Compiler_Util.left
                          lb.FStarC_Syntax_Syntax.lbname in
                      uu___4.FStarC_Syntax_Syntax.ppname in
                    FStarC_Ident.string_of_id uu___3 in
                  FStarC_Syntax_Syntax.gen_bv uu___2
                    FStar_Pervasives_Native.None
                    lb.FStarC_Syntax_Syntax.lbtyp) lbs in
           let let_rec_env =
             let uu___2 =
               FStarC_Compiler_List.map
                 (fun x1 ->
                    let uu___3 = FStarC_Syntax_Syntax.range_of_bv x1 in
                    mk_rt uu___3
                      (FStarC_TypeChecker_NBETerm.Accu
                         ((FStarC_TypeChecker_NBETerm.Var x1), []))) lbnames in
             FStarC_Compiler_List.rev_append uu___2 bs in
           let lbs1 =
             FStarC_Compiler_List.map2
               (fun lb ->
                  fun lbname ->
                    let lbdef =
                      let uu___2 =
                        translate cfg let_rec_env
                          lb.FStarC_Syntax_Syntax.lbdef in
                      readback cfg uu___2 in
                    let lbtyp =
                      let uu___2 =
                        translate cfg bs lb.FStarC_Syntax_Syntax.lbtyp in
                      readback cfg uu___2 in
                    {
                      FStarC_Syntax_Syntax.lbname =
                        (FStar_Pervasives.Inl lbname);
                      FStarC_Syntax_Syntax.lbunivs =
                        (lb.FStarC_Syntax_Syntax.lbunivs);
                      FStarC_Syntax_Syntax.lbtyp = lbtyp;
                      FStarC_Syntax_Syntax.lbeff =
                        (lb.FStarC_Syntax_Syntax.lbeff);
                      FStarC_Syntax_Syntax.lbdef = lbdef;
                      FStarC_Syntax_Syntax.lbattrs =
                        (lb.FStarC_Syntax_Syntax.lbattrs);
                      FStarC_Syntax_Syntax.lbpos =
                        (lb.FStarC_Syntax_Syntax.lbpos)
                    }) lbs lbnames in
           let body =
             let uu___2 = FStarC_Compiler_List.nth lbnames i in
             FStarC_Syntax_Syntax.bv_to_name uu___2 in
           let uu___2 = FStarC_Syntax_Subst.close_let_rec lbs1 body in
           (match uu___2 with
            | (lbs2, body1) ->
                let head =
                  FStarC_Syntax_Syntax.mk
                    (FStarC_Syntax_Syntax.Tm_let
                       {
                         FStarC_Syntax_Syntax.lbs = (true, lbs2);
                         FStarC_Syntax_Syntax.body1 = body1
                       }) FStarC_Compiler_Range_Type.dummyRange in
                let args1 =
                  FStarC_Compiler_List.map
                    (fun uu___3 ->
                       match uu___3 with
                       | (x1, q) ->
                           let uu___4 = readback cfg x1 in (uu___4, q)) args in
                let uu___3 = FStarC_Syntax_Util.mk_app head args1 in
                with_range uu___3)
       | FStarC_TypeChecker_NBETerm.Quote (qt, qi) ->
           mk (FStarC_Syntax_Syntax.Tm_quoted (qt, qi))
       | FStarC_TypeChecker_NBETerm.Lazy (FStar_Pervasives.Inl li, uu___1) ->
           mk (FStarC_Syntax_Syntax.Tm_lazy li)
       | FStarC_TypeChecker_NBETerm.Lazy (uu___1, thunk) ->
           let uu___2 = FStarC_Thunk.force thunk in readback cfg uu___2)
let (reduce_application :
  FStarC_TypeChecker_Cfg.cfg ->
    FStarC_TypeChecker_NBETerm.t ->
      FStarC_TypeChecker_NBETerm.args -> FStarC_TypeChecker_NBETerm.t)
  =
  fun cfg ->
    fun t -> fun args -> let uu___ = new_config cfg in iapp uu___ t args
let (normalize :
  FStarC_TypeChecker_Primops_Base.primitive_step Prims.list ->
    FStarC_TypeChecker_Env.step Prims.list ->
      FStarC_TypeChecker_Env.env ->
        FStarC_Syntax_Syntax.term -> FStarC_Syntax_Syntax.term)
  =
  fun psteps ->
    fun steps ->
      fun env ->
        fun e ->
          let cfg = FStarC_TypeChecker_Cfg.config' psteps steps env in
          let cfg1 =
            {
              FStarC_TypeChecker_Cfg.steps =
                (let uu___ = cfg.FStarC_TypeChecker_Cfg.steps in
                 {
                   FStarC_TypeChecker_Cfg.beta =
                     (uu___.FStarC_TypeChecker_Cfg.beta);
                   FStarC_TypeChecker_Cfg.iota =
                     (uu___.FStarC_TypeChecker_Cfg.iota);
                   FStarC_TypeChecker_Cfg.zeta =
                     (uu___.FStarC_TypeChecker_Cfg.zeta);
                   FStarC_TypeChecker_Cfg.zeta_full =
                     (uu___.FStarC_TypeChecker_Cfg.zeta_full);
                   FStarC_TypeChecker_Cfg.weak =
                     (uu___.FStarC_TypeChecker_Cfg.weak);
                   FStarC_TypeChecker_Cfg.hnf =
                     (uu___.FStarC_TypeChecker_Cfg.hnf);
                   FStarC_TypeChecker_Cfg.primops =
                     (uu___.FStarC_TypeChecker_Cfg.primops);
                   FStarC_TypeChecker_Cfg.do_not_unfold_pure_lets =
                     (uu___.FStarC_TypeChecker_Cfg.do_not_unfold_pure_lets);
                   FStarC_TypeChecker_Cfg.unfold_until =
                     (uu___.FStarC_TypeChecker_Cfg.unfold_until);
                   FStarC_TypeChecker_Cfg.unfold_only =
                     (uu___.FStarC_TypeChecker_Cfg.unfold_only);
                   FStarC_TypeChecker_Cfg.unfold_fully =
                     (uu___.FStarC_TypeChecker_Cfg.unfold_fully);
                   FStarC_TypeChecker_Cfg.unfold_attr =
                     (uu___.FStarC_TypeChecker_Cfg.unfold_attr);
                   FStarC_TypeChecker_Cfg.unfold_qual =
                     (uu___.FStarC_TypeChecker_Cfg.unfold_qual);
                   FStarC_TypeChecker_Cfg.unfold_namespace =
                     (uu___.FStarC_TypeChecker_Cfg.unfold_namespace);
                   FStarC_TypeChecker_Cfg.dont_unfold_attr =
                     (uu___.FStarC_TypeChecker_Cfg.dont_unfold_attr);
                   FStarC_TypeChecker_Cfg.pure_subterms_within_computations =
                     (uu___.FStarC_TypeChecker_Cfg.pure_subterms_within_computations);
                   FStarC_TypeChecker_Cfg.simplify =
                     (uu___.FStarC_TypeChecker_Cfg.simplify);
                   FStarC_TypeChecker_Cfg.erase_universes =
                     (uu___.FStarC_TypeChecker_Cfg.erase_universes);
                   FStarC_TypeChecker_Cfg.allow_unbound_universes =
                     (uu___.FStarC_TypeChecker_Cfg.allow_unbound_universes);
                   FStarC_TypeChecker_Cfg.reify_ = true;
                   FStarC_TypeChecker_Cfg.compress_uvars =
                     (uu___.FStarC_TypeChecker_Cfg.compress_uvars);
                   FStarC_TypeChecker_Cfg.no_full_norm =
                     (uu___.FStarC_TypeChecker_Cfg.no_full_norm);
                   FStarC_TypeChecker_Cfg.check_no_uvars =
                     (uu___.FStarC_TypeChecker_Cfg.check_no_uvars);
                   FStarC_TypeChecker_Cfg.unmeta =
                     (uu___.FStarC_TypeChecker_Cfg.unmeta);
                   FStarC_TypeChecker_Cfg.unascribe =
                     (uu___.FStarC_TypeChecker_Cfg.unascribe);
                   FStarC_TypeChecker_Cfg.in_full_norm_request =
                     (uu___.FStarC_TypeChecker_Cfg.in_full_norm_request);
                   FStarC_TypeChecker_Cfg.weakly_reduce_scrutinee =
                     (uu___.FStarC_TypeChecker_Cfg.weakly_reduce_scrutinee);
                   FStarC_TypeChecker_Cfg.nbe_step =
                     (uu___.FStarC_TypeChecker_Cfg.nbe_step);
                   FStarC_TypeChecker_Cfg.for_extraction =
                     (uu___.FStarC_TypeChecker_Cfg.for_extraction);
                   FStarC_TypeChecker_Cfg.unrefine =
                     (uu___.FStarC_TypeChecker_Cfg.unrefine);
                   FStarC_TypeChecker_Cfg.default_univs_to_zero =
                     (uu___.FStarC_TypeChecker_Cfg.default_univs_to_zero);
                   FStarC_TypeChecker_Cfg.tactics =
                     (uu___.FStarC_TypeChecker_Cfg.tactics)
                 });
              FStarC_TypeChecker_Cfg.tcenv =
                (cfg.FStarC_TypeChecker_Cfg.tcenv);
              FStarC_TypeChecker_Cfg.debug =
                (cfg.FStarC_TypeChecker_Cfg.debug);
              FStarC_TypeChecker_Cfg.delta_level =
                (cfg.FStarC_TypeChecker_Cfg.delta_level);
              FStarC_TypeChecker_Cfg.primitive_steps =
                (cfg.FStarC_TypeChecker_Cfg.primitive_steps);
              FStarC_TypeChecker_Cfg.strong =
                (cfg.FStarC_TypeChecker_Cfg.strong);
              FStarC_TypeChecker_Cfg.memoize_lazy =
                (cfg.FStarC_TypeChecker_Cfg.memoize_lazy);
              FStarC_TypeChecker_Cfg.normalize_pure_lets =
                (cfg.FStarC_TypeChecker_Cfg.normalize_pure_lets);
              FStarC_TypeChecker_Cfg.reifying =
                (cfg.FStarC_TypeChecker_Cfg.reifying);
              FStarC_TypeChecker_Cfg.compat_memo_ignore_cfg =
                (cfg.FStarC_TypeChecker_Cfg.compat_memo_ignore_cfg)
            } in
          (let uu___1 =
             (FStarC_Compiler_Effect.op_Bang dbg_NBETop) ||
               (FStarC_Compiler_Effect.op_Bang dbg_NBE) in
           if uu___1
           then
             let uu___2 =
               FStarC_Class_Show.show FStarC_Syntax_Print.showable_term e in
             FStarC_Compiler_Util.print1 "Calling NBE with (%s) {\n" uu___2
           else ());
          (let cfg2 = new_config cfg1 in
           let r = let uu___1 = translate cfg2 [] e in readback cfg2 uu___1 in
           (let uu___2 =
              (FStarC_Compiler_Effect.op_Bang dbg_NBETop) ||
                (FStarC_Compiler_Effect.op_Bang dbg_NBE) in
            if uu___2
            then
              let uu___3 =
                FStarC_Class_Show.show FStarC_Syntax_Print.showable_term r in
              FStarC_Compiler_Util.print1 "}\nNBE returned (%s)\n" uu___3
            else ());
           r)
let (normalize_for_unit_test :
  FStarC_TypeChecker_Env.step Prims.list ->
    FStarC_TypeChecker_Env.env ->
      FStarC_Syntax_Syntax.term -> FStarC_Syntax_Syntax.term)
  =
  fun steps ->
    fun env ->
      fun e ->
        let cfg = FStarC_TypeChecker_Cfg.config steps env in
        let cfg1 =
          {
            FStarC_TypeChecker_Cfg.steps =
              (let uu___ = cfg.FStarC_TypeChecker_Cfg.steps in
               {
                 FStarC_TypeChecker_Cfg.beta =
                   (uu___.FStarC_TypeChecker_Cfg.beta);
                 FStarC_TypeChecker_Cfg.iota =
                   (uu___.FStarC_TypeChecker_Cfg.iota);
                 FStarC_TypeChecker_Cfg.zeta =
                   (uu___.FStarC_TypeChecker_Cfg.zeta);
                 FStarC_TypeChecker_Cfg.zeta_full =
                   (uu___.FStarC_TypeChecker_Cfg.zeta_full);
                 FStarC_TypeChecker_Cfg.weak =
                   (uu___.FStarC_TypeChecker_Cfg.weak);
                 FStarC_TypeChecker_Cfg.hnf =
                   (uu___.FStarC_TypeChecker_Cfg.hnf);
                 FStarC_TypeChecker_Cfg.primops =
                   (uu___.FStarC_TypeChecker_Cfg.primops);
                 FStarC_TypeChecker_Cfg.do_not_unfold_pure_lets =
                   (uu___.FStarC_TypeChecker_Cfg.do_not_unfold_pure_lets);
                 FStarC_TypeChecker_Cfg.unfold_until =
                   (uu___.FStarC_TypeChecker_Cfg.unfold_until);
                 FStarC_TypeChecker_Cfg.unfold_only =
                   (uu___.FStarC_TypeChecker_Cfg.unfold_only);
                 FStarC_TypeChecker_Cfg.unfold_fully =
                   (uu___.FStarC_TypeChecker_Cfg.unfold_fully);
                 FStarC_TypeChecker_Cfg.unfold_attr =
                   (uu___.FStarC_TypeChecker_Cfg.unfold_attr);
                 FStarC_TypeChecker_Cfg.unfold_qual =
                   (uu___.FStarC_TypeChecker_Cfg.unfold_qual);
                 FStarC_TypeChecker_Cfg.unfold_namespace =
                   (uu___.FStarC_TypeChecker_Cfg.unfold_namespace);
                 FStarC_TypeChecker_Cfg.dont_unfold_attr =
                   (uu___.FStarC_TypeChecker_Cfg.dont_unfold_attr);
                 FStarC_TypeChecker_Cfg.pure_subterms_within_computations =
                   (uu___.FStarC_TypeChecker_Cfg.pure_subterms_within_computations);
                 FStarC_TypeChecker_Cfg.simplify =
                   (uu___.FStarC_TypeChecker_Cfg.simplify);
                 FStarC_TypeChecker_Cfg.erase_universes =
                   (uu___.FStarC_TypeChecker_Cfg.erase_universes);
                 FStarC_TypeChecker_Cfg.allow_unbound_universes =
                   (uu___.FStarC_TypeChecker_Cfg.allow_unbound_universes);
                 FStarC_TypeChecker_Cfg.reify_ = true;
                 FStarC_TypeChecker_Cfg.compress_uvars =
                   (uu___.FStarC_TypeChecker_Cfg.compress_uvars);
                 FStarC_TypeChecker_Cfg.no_full_norm =
                   (uu___.FStarC_TypeChecker_Cfg.no_full_norm);
                 FStarC_TypeChecker_Cfg.check_no_uvars =
                   (uu___.FStarC_TypeChecker_Cfg.check_no_uvars);
                 FStarC_TypeChecker_Cfg.unmeta =
                   (uu___.FStarC_TypeChecker_Cfg.unmeta);
                 FStarC_TypeChecker_Cfg.unascribe =
                   (uu___.FStarC_TypeChecker_Cfg.unascribe);
                 FStarC_TypeChecker_Cfg.in_full_norm_request =
                   (uu___.FStarC_TypeChecker_Cfg.in_full_norm_request);
                 FStarC_TypeChecker_Cfg.weakly_reduce_scrutinee =
                   (uu___.FStarC_TypeChecker_Cfg.weakly_reduce_scrutinee);
                 FStarC_TypeChecker_Cfg.nbe_step =
                   (uu___.FStarC_TypeChecker_Cfg.nbe_step);
                 FStarC_TypeChecker_Cfg.for_extraction =
                   (uu___.FStarC_TypeChecker_Cfg.for_extraction);
                 FStarC_TypeChecker_Cfg.unrefine =
                   (uu___.FStarC_TypeChecker_Cfg.unrefine);
                 FStarC_TypeChecker_Cfg.default_univs_to_zero =
                   (uu___.FStarC_TypeChecker_Cfg.default_univs_to_zero);
                 FStarC_TypeChecker_Cfg.tactics =
                   (uu___.FStarC_TypeChecker_Cfg.tactics)
               });
            FStarC_TypeChecker_Cfg.tcenv = (cfg.FStarC_TypeChecker_Cfg.tcenv);
            FStarC_TypeChecker_Cfg.debug = (cfg.FStarC_TypeChecker_Cfg.debug);
            FStarC_TypeChecker_Cfg.delta_level =
              (cfg.FStarC_TypeChecker_Cfg.delta_level);
            FStarC_TypeChecker_Cfg.primitive_steps =
              (cfg.FStarC_TypeChecker_Cfg.primitive_steps);
            FStarC_TypeChecker_Cfg.strong =
              (cfg.FStarC_TypeChecker_Cfg.strong);
            FStarC_TypeChecker_Cfg.memoize_lazy =
              (cfg.FStarC_TypeChecker_Cfg.memoize_lazy);
            FStarC_TypeChecker_Cfg.normalize_pure_lets =
              (cfg.FStarC_TypeChecker_Cfg.normalize_pure_lets);
            FStarC_TypeChecker_Cfg.reifying =
              (cfg.FStarC_TypeChecker_Cfg.reifying);
            FStarC_TypeChecker_Cfg.compat_memo_ignore_cfg =
              (cfg.FStarC_TypeChecker_Cfg.compat_memo_ignore_cfg)
          } in
        let cfg2 = new_config cfg1 in
        debug cfg2
          (fun uu___1 ->
             let uu___2 =
               FStarC_Class_Show.show FStarC_Syntax_Print.showable_term e in
             FStarC_Compiler_Util.print1 "Calling NBE with (%s) {\n" uu___2);
        (let r = let uu___1 = translate cfg2 [] e in readback cfg2 uu___1 in
         debug cfg2
           (fun uu___2 ->
              let uu___3 =
                FStarC_Class_Show.show FStarC_Syntax_Print.showable_term r in
              FStarC_Compiler_Util.print1 "}\nNBE returned (%s)\n" uu___3);
         r)