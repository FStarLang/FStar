open Prims
type fsteps =
  {
  beta: Prims.bool ;
  iota: Prims.bool ;
  zeta: Prims.bool ;
  zeta_full: Prims.bool ;
  weak: Prims.bool ;
  hnf: Prims.bool ;
  primops: Prims.bool ;
  do_not_unfold_pure_lets: Prims.bool ;
  unfold_until:
    FStarC_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option ;
  unfold_only: FStarC_Ident.lid Prims.list FStar_Pervasives_Native.option ;
  unfold_fully: FStarC_Ident.lid Prims.list FStar_Pervasives_Native.option ;
  unfold_attr: FStarC_Ident.lid Prims.list FStar_Pervasives_Native.option ;
  unfold_qual: Prims.string Prims.list FStar_Pervasives_Native.option ;
  unfold_namespace:
    (Prims.string, Prims.bool) FStarC_Compiler_Path.forest
      FStar_Pervasives_Native.option
    ;
  dont_unfold_attr:
    FStarC_Ident.lid Prims.list FStar_Pervasives_Native.option ;
  pure_subterms_within_computations: Prims.bool ;
  simplify: Prims.bool ;
  erase_universes: Prims.bool ;
  allow_unbound_universes: Prims.bool ;
  reify_: Prims.bool ;
  compress_uvars: Prims.bool ;
  no_full_norm: Prims.bool ;
  check_no_uvars: Prims.bool ;
  unmeta: Prims.bool ;
  unascribe: Prims.bool ;
  in_full_norm_request: Prims.bool ;
  weakly_reduce_scrutinee: Prims.bool ;
  nbe_step: Prims.bool ;
  for_extraction: Prims.bool ;
  unrefine: Prims.bool ;
  default_univs_to_zero: Prims.bool ;
  tactics: Prims.bool }
let (__proj__Mkfsteps__item__beta : fsteps -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { beta; iota; zeta; zeta_full; weak; hnf; primops;
        do_not_unfold_pure_lets; unfold_until; unfold_only; unfold_fully;
        unfold_attr; unfold_qual; unfold_namespace; dont_unfold_attr;
        pure_subterms_within_computations; simplify; erase_universes;
        allow_unbound_universes; reify_; compress_uvars; no_full_norm;
        check_no_uvars; unmeta; unascribe; in_full_norm_request;
        weakly_reduce_scrutinee; nbe_step; for_extraction; unrefine;
        default_univs_to_zero; tactics;_} -> beta
let (__proj__Mkfsteps__item__iota : fsteps -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { beta; iota; zeta; zeta_full; weak; hnf; primops;
        do_not_unfold_pure_lets; unfold_until; unfold_only; unfold_fully;
        unfold_attr; unfold_qual; unfold_namespace; dont_unfold_attr;
        pure_subterms_within_computations; simplify; erase_universes;
        allow_unbound_universes; reify_; compress_uvars; no_full_norm;
        check_no_uvars; unmeta; unascribe; in_full_norm_request;
        weakly_reduce_scrutinee; nbe_step; for_extraction; unrefine;
        default_univs_to_zero; tactics;_} -> iota
let (__proj__Mkfsteps__item__zeta : fsteps -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { beta; iota; zeta; zeta_full; weak; hnf; primops;
        do_not_unfold_pure_lets; unfold_until; unfold_only; unfold_fully;
        unfold_attr; unfold_qual; unfold_namespace; dont_unfold_attr;
        pure_subterms_within_computations; simplify; erase_universes;
        allow_unbound_universes; reify_; compress_uvars; no_full_norm;
        check_no_uvars; unmeta; unascribe; in_full_norm_request;
        weakly_reduce_scrutinee; nbe_step; for_extraction; unrefine;
        default_univs_to_zero; tactics;_} -> zeta
let (__proj__Mkfsteps__item__zeta_full : fsteps -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { beta; iota; zeta; zeta_full; weak; hnf; primops;
        do_not_unfold_pure_lets; unfold_until; unfold_only; unfold_fully;
        unfold_attr; unfold_qual; unfold_namespace; dont_unfold_attr;
        pure_subterms_within_computations; simplify; erase_universes;
        allow_unbound_universes; reify_; compress_uvars; no_full_norm;
        check_no_uvars; unmeta; unascribe; in_full_norm_request;
        weakly_reduce_scrutinee; nbe_step; for_extraction; unrefine;
        default_univs_to_zero; tactics;_} -> zeta_full
let (__proj__Mkfsteps__item__weak : fsteps -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { beta; iota; zeta; zeta_full; weak; hnf; primops;
        do_not_unfold_pure_lets; unfold_until; unfold_only; unfold_fully;
        unfold_attr; unfold_qual; unfold_namespace; dont_unfold_attr;
        pure_subterms_within_computations; simplify; erase_universes;
        allow_unbound_universes; reify_; compress_uvars; no_full_norm;
        check_no_uvars; unmeta; unascribe; in_full_norm_request;
        weakly_reduce_scrutinee; nbe_step; for_extraction; unrefine;
        default_univs_to_zero; tactics;_} -> weak
let (__proj__Mkfsteps__item__hnf : fsteps -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { beta; iota; zeta; zeta_full; weak; hnf; primops;
        do_not_unfold_pure_lets; unfold_until; unfold_only; unfold_fully;
        unfold_attr; unfold_qual; unfold_namespace; dont_unfold_attr;
        pure_subterms_within_computations; simplify; erase_universes;
        allow_unbound_universes; reify_; compress_uvars; no_full_norm;
        check_no_uvars; unmeta; unascribe; in_full_norm_request;
        weakly_reduce_scrutinee; nbe_step; for_extraction; unrefine;
        default_univs_to_zero; tactics;_} -> hnf
let (__proj__Mkfsteps__item__primops : fsteps -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { beta; iota; zeta; zeta_full; weak; hnf; primops;
        do_not_unfold_pure_lets; unfold_until; unfold_only; unfold_fully;
        unfold_attr; unfold_qual; unfold_namespace; dont_unfold_attr;
        pure_subterms_within_computations; simplify; erase_universes;
        allow_unbound_universes; reify_; compress_uvars; no_full_norm;
        check_no_uvars; unmeta; unascribe; in_full_norm_request;
        weakly_reduce_scrutinee; nbe_step; for_extraction; unrefine;
        default_univs_to_zero; tactics;_} -> primops
let (__proj__Mkfsteps__item__do_not_unfold_pure_lets : fsteps -> Prims.bool)
  =
  fun projectee ->
    match projectee with
    | { beta; iota; zeta; zeta_full; weak; hnf; primops;
        do_not_unfold_pure_lets; unfold_until; unfold_only; unfold_fully;
        unfold_attr; unfold_qual; unfold_namespace; dont_unfold_attr;
        pure_subterms_within_computations; simplify; erase_universes;
        allow_unbound_universes; reify_; compress_uvars; no_full_norm;
        check_no_uvars; unmeta; unascribe; in_full_norm_request;
        weakly_reduce_scrutinee; nbe_step; for_extraction; unrefine;
        default_univs_to_zero; tactics;_} -> do_not_unfold_pure_lets
let (__proj__Mkfsteps__item__unfold_until :
  fsteps -> FStarC_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option)
  =
  fun projectee ->
    match projectee with
    | { beta; iota; zeta; zeta_full; weak; hnf; primops;
        do_not_unfold_pure_lets; unfold_until; unfold_only; unfold_fully;
        unfold_attr; unfold_qual; unfold_namespace; dont_unfold_attr;
        pure_subterms_within_computations; simplify; erase_universes;
        allow_unbound_universes; reify_; compress_uvars; no_full_norm;
        check_no_uvars; unmeta; unascribe; in_full_norm_request;
        weakly_reduce_scrutinee; nbe_step; for_extraction; unrefine;
        default_univs_to_zero; tactics;_} -> unfold_until
let (__proj__Mkfsteps__item__unfold_only :
  fsteps -> FStarC_Ident.lid Prims.list FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { beta; iota; zeta; zeta_full; weak; hnf; primops;
        do_not_unfold_pure_lets; unfold_until; unfold_only; unfold_fully;
        unfold_attr; unfold_qual; unfold_namespace; dont_unfold_attr;
        pure_subterms_within_computations; simplify; erase_universes;
        allow_unbound_universes; reify_; compress_uvars; no_full_norm;
        check_no_uvars; unmeta; unascribe; in_full_norm_request;
        weakly_reduce_scrutinee; nbe_step; for_extraction; unrefine;
        default_univs_to_zero; tactics;_} -> unfold_only
let (__proj__Mkfsteps__item__unfold_fully :
  fsteps -> FStarC_Ident.lid Prims.list FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { beta; iota; zeta; zeta_full; weak; hnf; primops;
        do_not_unfold_pure_lets; unfold_until; unfold_only; unfold_fully;
        unfold_attr; unfold_qual; unfold_namespace; dont_unfold_attr;
        pure_subterms_within_computations; simplify; erase_universes;
        allow_unbound_universes; reify_; compress_uvars; no_full_norm;
        check_no_uvars; unmeta; unascribe; in_full_norm_request;
        weakly_reduce_scrutinee; nbe_step; for_extraction; unrefine;
        default_univs_to_zero; tactics;_} -> unfold_fully
let (__proj__Mkfsteps__item__unfold_attr :
  fsteps -> FStarC_Ident.lid Prims.list FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { beta; iota; zeta; zeta_full; weak; hnf; primops;
        do_not_unfold_pure_lets; unfold_until; unfold_only; unfold_fully;
        unfold_attr; unfold_qual; unfold_namespace; dont_unfold_attr;
        pure_subterms_within_computations; simplify; erase_universes;
        allow_unbound_universes; reify_; compress_uvars; no_full_norm;
        check_no_uvars; unmeta; unascribe; in_full_norm_request;
        weakly_reduce_scrutinee; nbe_step; for_extraction; unrefine;
        default_univs_to_zero; tactics;_} -> unfold_attr
let (__proj__Mkfsteps__item__unfold_qual :
  fsteps -> Prims.string Prims.list FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { beta; iota; zeta; zeta_full; weak; hnf; primops;
        do_not_unfold_pure_lets; unfold_until; unfold_only; unfold_fully;
        unfold_attr; unfold_qual; unfold_namespace; dont_unfold_attr;
        pure_subterms_within_computations; simplify; erase_universes;
        allow_unbound_universes; reify_; compress_uvars; no_full_norm;
        check_no_uvars; unmeta; unascribe; in_full_norm_request;
        weakly_reduce_scrutinee; nbe_step; for_extraction; unrefine;
        default_univs_to_zero; tactics;_} -> unfold_qual
let (__proj__Mkfsteps__item__unfold_namespace :
  fsteps ->
    (Prims.string, Prims.bool) FStarC_Compiler_Path.forest
      FStar_Pervasives_Native.option)
  =
  fun projectee ->
    match projectee with
    | { beta; iota; zeta; zeta_full; weak; hnf; primops;
        do_not_unfold_pure_lets; unfold_until; unfold_only; unfold_fully;
        unfold_attr; unfold_qual; unfold_namespace; dont_unfold_attr;
        pure_subterms_within_computations; simplify; erase_universes;
        allow_unbound_universes; reify_; compress_uvars; no_full_norm;
        check_no_uvars; unmeta; unascribe; in_full_norm_request;
        weakly_reduce_scrutinee; nbe_step; for_extraction; unrefine;
        default_univs_to_zero; tactics;_} -> unfold_namespace
let (__proj__Mkfsteps__item__dont_unfold_attr :
  fsteps -> FStarC_Ident.lid Prims.list FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { beta; iota; zeta; zeta_full; weak; hnf; primops;
        do_not_unfold_pure_lets; unfold_until; unfold_only; unfold_fully;
        unfold_attr; unfold_qual; unfold_namespace; dont_unfold_attr;
        pure_subterms_within_computations; simplify; erase_universes;
        allow_unbound_universes; reify_; compress_uvars; no_full_norm;
        check_no_uvars; unmeta; unascribe; in_full_norm_request;
        weakly_reduce_scrutinee; nbe_step; for_extraction; unrefine;
        default_univs_to_zero; tactics;_} -> dont_unfold_attr
let (__proj__Mkfsteps__item__pure_subterms_within_computations :
  fsteps -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { beta; iota; zeta; zeta_full; weak; hnf; primops;
        do_not_unfold_pure_lets; unfold_until; unfold_only; unfold_fully;
        unfold_attr; unfold_qual; unfold_namespace; dont_unfold_attr;
        pure_subterms_within_computations; simplify; erase_universes;
        allow_unbound_universes; reify_; compress_uvars; no_full_norm;
        check_no_uvars; unmeta; unascribe; in_full_norm_request;
        weakly_reduce_scrutinee; nbe_step; for_extraction; unrefine;
        default_univs_to_zero; tactics;_} ->
        pure_subterms_within_computations
let (__proj__Mkfsteps__item__simplify : fsteps -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { beta; iota; zeta; zeta_full; weak; hnf; primops;
        do_not_unfold_pure_lets; unfold_until; unfold_only; unfold_fully;
        unfold_attr; unfold_qual; unfold_namespace; dont_unfold_attr;
        pure_subterms_within_computations; simplify; erase_universes;
        allow_unbound_universes; reify_; compress_uvars; no_full_norm;
        check_no_uvars; unmeta; unascribe; in_full_norm_request;
        weakly_reduce_scrutinee; nbe_step; for_extraction; unrefine;
        default_univs_to_zero; tactics;_} -> simplify
let (__proj__Mkfsteps__item__erase_universes : fsteps -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { beta; iota; zeta; zeta_full; weak; hnf; primops;
        do_not_unfold_pure_lets; unfold_until; unfold_only; unfold_fully;
        unfold_attr; unfold_qual; unfold_namespace; dont_unfold_attr;
        pure_subterms_within_computations; simplify; erase_universes;
        allow_unbound_universes; reify_; compress_uvars; no_full_norm;
        check_no_uvars; unmeta; unascribe; in_full_norm_request;
        weakly_reduce_scrutinee; nbe_step; for_extraction; unrefine;
        default_univs_to_zero; tactics;_} -> erase_universes
let (__proj__Mkfsteps__item__allow_unbound_universes : fsteps -> Prims.bool)
  =
  fun projectee ->
    match projectee with
    | { beta; iota; zeta; zeta_full; weak; hnf; primops;
        do_not_unfold_pure_lets; unfold_until; unfold_only; unfold_fully;
        unfold_attr; unfold_qual; unfold_namespace; dont_unfold_attr;
        pure_subterms_within_computations; simplify; erase_universes;
        allow_unbound_universes; reify_; compress_uvars; no_full_norm;
        check_no_uvars; unmeta; unascribe; in_full_norm_request;
        weakly_reduce_scrutinee; nbe_step; for_extraction; unrefine;
        default_univs_to_zero; tactics;_} -> allow_unbound_universes
let (__proj__Mkfsteps__item__reify_ : fsteps -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { beta; iota; zeta; zeta_full; weak; hnf; primops;
        do_not_unfold_pure_lets; unfold_until; unfold_only; unfold_fully;
        unfold_attr; unfold_qual; unfold_namespace; dont_unfold_attr;
        pure_subterms_within_computations; simplify; erase_universes;
        allow_unbound_universes; reify_; compress_uvars; no_full_norm;
        check_no_uvars; unmeta; unascribe; in_full_norm_request;
        weakly_reduce_scrutinee; nbe_step; for_extraction; unrefine;
        default_univs_to_zero; tactics;_} -> reify_
let (__proj__Mkfsteps__item__compress_uvars : fsteps -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { beta; iota; zeta; zeta_full; weak; hnf; primops;
        do_not_unfold_pure_lets; unfold_until; unfold_only; unfold_fully;
        unfold_attr; unfold_qual; unfold_namespace; dont_unfold_attr;
        pure_subterms_within_computations; simplify; erase_universes;
        allow_unbound_universes; reify_; compress_uvars; no_full_norm;
        check_no_uvars; unmeta; unascribe; in_full_norm_request;
        weakly_reduce_scrutinee; nbe_step; for_extraction; unrefine;
        default_univs_to_zero; tactics;_} -> compress_uvars
let (__proj__Mkfsteps__item__no_full_norm : fsteps -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { beta; iota; zeta; zeta_full; weak; hnf; primops;
        do_not_unfold_pure_lets; unfold_until; unfold_only; unfold_fully;
        unfold_attr; unfold_qual; unfold_namespace; dont_unfold_attr;
        pure_subterms_within_computations; simplify; erase_universes;
        allow_unbound_universes; reify_; compress_uvars; no_full_norm;
        check_no_uvars; unmeta; unascribe; in_full_norm_request;
        weakly_reduce_scrutinee; nbe_step; for_extraction; unrefine;
        default_univs_to_zero; tactics;_} -> no_full_norm
let (__proj__Mkfsteps__item__check_no_uvars : fsteps -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { beta; iota; zeta; zeta_full; weak; hnf; primops;
        do_not_unfold_pure_lets; unfold_until; unfold_only; unfold_fully;
        unfold_attr; unfold_qual; unfold_namespace; dont_unfold_attr;
        pure_subterms_within_computations; simplify; erase_universes;
        allow_unbound_universes; reify_; compress_uvars; no_full_norm;
        check_no_uvars; unmeta; unascribe; in_full_norm_request;
        weakly_reduce_scrutinee; nbe_step; for_extraction; unrefine;
        default_univs_to_zero; tactics;_} -> check_no_uvars
let (__proj__Mkfsteps__item__unmeta : fsteps -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { beta; iota; zeta; zeta_full; weak; hnf; primops;
        do_not_unfold_pure_lets; unfold_until; unfold_only; unfold_fully;
        unfold_attr; unfold_qual; unfold_namespace; dont_unfold_attr;
        pure_subterms_within_computations; simplify; erase_universes;
        allow_unbound_universes; reify_; compress_uvars; no_full_norm;
        check_no_uvars; unmeta; unascribe; in_full_norm_request;
        weakly_reduce_scrutinee; nbe_step; for_extraction; unrefine;
        default_univs_to_zero; tactics;_} -> unmeta
let (__proj__Mkfsteps__item__unascribe : fsteps -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { beta; iota; zeta; zeta_full; weak; hnf; primops;
        do_not_unfold_pure_lets; unfold_until; unfold_only; unfold_fully;
        unfold_attr; unfold_qual; unfold_namespace; dont_unfold_attr;
        pure_subterms_within_computations; simplify; erase_universes;
        allow_unbound_universes; reify_; compress_uvars; no_full_norm;
        check_no_uvars; unmeta; unascribe; in_full_norm_request;
        weakly_reduce_scrutinee; nbe_step; for_extraction; unrefine;
        default_univs_to_zero; tactics;_} -> unascribe
let (__proj__Mkfsteps__item__in_full_norm_request : fsteps -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { beta; iota; zeta; zeta_full; weak; hnf; primops;
        do_not_unfold_pure_lets; unfold_until; unfold_only; unfold_fully;
        unfold_attr; unfold_qual; unfold_namespace; dont_unfold_attr;
        pure_subterms_within_computations; simplify; erase_universes;
        allow_unbound_universes; reify_; compress_uvars; no_full_norm;
        check_no_uvars; unmeta; unascribe; in_full_norm_request;
        weakly_reduce_scrutinee; nbe_step; for_extraction; unrefine;
        default_univs_to_zero; tactics;_} -> in_full_norm_request
let (__proj__Mkfsteps__item__weakly_reduce_scrutinee : fsteps -> Prims.bool)
  =
  fun projectee ->
    match projectee with
    | { beta; iota; zeta; zeta_full; weak; hnf; primops;
        do_not_unfold_pure_lets; unfold_until; unfold_only; unfold_fully;
        unfold_attr; unfold_qual; unfold_namespace; dont_unfold_attr;
        pure_subterms_within_computations; simplify; erase_universes;
        allow_unbound_universes; reify_; compress_uvars; no_full_norm;
        check_no_uvars; unmeta; unascribe; in_full_norm_request;
        weakly_reduce_scrutinee; nbe_step; for_extraction; unrefine;
        default_univs_to_zero; tactics;_} -> weakly_reduce_scrutinee
let (__proj__Mkfsteps__item__nbe_step : fsteps -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { beta; iota; zeta; zeta_full; weak; hnf; primops;
        do_not_unfold_pure_lets; unfold_until; unfold_only; unfold_fully;
        unfold_attr; unfold_qual; unfold_namespace; dont_unfold_attr;
        pure_subterms_within_computations; simplify; erase_universes;
        allow_unbound_universes; reify_; compress_uvars; no_full_norm;
        check_no_uvars; unmeta; unascribe; in_full_norm_request;
        weakly_reduce_scrutinee; nbe_step; for_extraction; unrefine;
        default_univs_to_zero; tactics;_} -> nbe_step
let (__proj__Mkfsteps__item__for_extraction : fsteps -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { beta; iota; zeta; zeta_full; weak; hnf; primops;
        do_not_unfold_pure_lets; unfold_until; unfold_only; unfold_fully;
        unfold_attr; unfold_qual; unfold_namespace; dont_unfold_attr;
        pure_subterms_within_computations; simplify; erase_universes;
        allow_unbound_universes; reify_; compress_uvars; no_full_norm;
        check_no_uvars; unmeta; unascribe; in_full_norm_request;
        weakly_reduce_scrutinee; nbe_step; for_extraction; unrefine;
        default_univs_to_zero; tactics;_} -> for_extraction
let (__proj__Mkfsteps__item__unrefine : fsteps -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { beta; iota; zeta; zeta_full; weak; hnf; primops;
        do_not_unfold_pure_lets; unfold_until; unfold_only; unfold_fully;
        unfold_attr; unfold_qual; unfold_namespace; dont_unfold_attr;
        pure_subterms_within_computations; simplify; erase_universes;
        allow_unbound_universes; reify_; compress_uvars; no_full_norm;
        check_no_uvars; unmeta; unascribe; in_full_norm_request;
        weakly_reduce_scrutinee; nbe_step; for_extraction; unrefine;
        default_univs_to_zero; tactics;_} -> unrefine
let (__proj__Mkfsteps__item__default_univs_to_zero : fsteps -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { beta; iota; zeta; zeta_full; weak; hnf; primops;
        do_not_unfold_pure_lets; unfold_until; unfold_only; unfold_fully;
        unfold_attr; unfold_qual; unfold_namespace; dont_unfold_attr;
        pure_subterms_within_computations; simplify; erase_universes;
        allow_unbound_universes; reify_; compress_uvars; no_full_norm;
        check_no_uvars; unmeta; unascribe; in_full_norm_request;
        weakly_reduce_scrutinee; nbe_step; for_extraction; unrefine;
        default_univs_to_zero; tactics;_} -> default_univs_to_zero
let (__proj__Mkfsteps__item__tactics : fsteps -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { beta; iota; zeta; zeta_full; weak; hnf; primops;
        do_not_unfold_pure_lets; unfold_until; unfold_only; unfold_fully;
        unfold_attr; unfold_qual; unfold_namespace; dont_unfold_attr;
        pure_subterms_within_computations; simplify; erase_universes;
        allow_unbound_universes; reify_; compress_uvars; no_full_norm;
        check_no_uvars; unmeta; unascribe; in_full_norm_request;
        weakly_reduce_scrutinee; nbe_step; for_extraction; unrefine;
        default_univs_to_zero; tactics;_} -> tactics
let (steps_to_string : fsteps -> Prims.string) =
  fun f ->
    let format_opt f1 o =
      match o with
      | FStar_Pervasives_Native.None -> "None"
      | FStar_Pervasives_Native.Some x ->
          let uu___ =
            let uu___1 = f1 x in FStarC_Compiler_String.op_Hat uu___1 ")" in
          FStarC_Compiler_String.op_Hat "Some (" uu___ in
    let b = FStarC_Compiler_Util.string_of_bool in
    let uu___ =
      let uu___1 =
        FStarC_Class_Show.show FStarC_Class_Show.showable_bool f.beta in
      let uu___2 =
        let uu___3 =
          FStarC_Class_Show.show FStarC_Class_Show.showable_bool f.iota in
        let uu___4 =
          let uu___5 =
            FStarC_Class_Show.show FStarC_Class_Show.showable_bool f.zeta in
          let uu___6 =
            let uu___7 =
              FStarC_Class_Show.show FStarC_Class_Show.showable_bool
                f.zeta_full in
            let uu___8 =
              let uu___9 =
                FStarC_Class_Show.show FStarC_Class_Show.showable_bool f.weak in
              let uu___10 =
                let uu___11 =
                  FStarC_Class_Show.show FStarC_Class_Show.showable_bool
                    f.hnf in
                let uu___12 =
                  let uu___13 =
                    FStarC_Class_Show.show FStarC_Class_Show.showable_bool
                      f.primops in
                  let uu___14 =
                    let uu___15 =
                      FStarC_Class_Show.show FStarC_Class_Show.showable_bool
                        f.do_not_unfold_pure_lets in
                    let uu___16 =
                      let uu___17 =
                        FStarC_Class_Show.show
                          (FStarC_Class_Show.show_option
                             FStarC_Syntax_Syntax.showable_delta_depth)
                          f.unfold_until in
                      let uu___18 =
                        let uu___19 =
                          FStarC_Class_Show.show
                            (FStarC_Class_Show.show_option
                               (FStarC_Class_Show.show_list
                                  FStarC_Ident.showable_lident))
                            f.unfold_only in
                        let uu___20 =
                          let uu___21 =
                            FStarC_Class_Show.show
                              (FStarC_Class_Show.show_option
                                 (FStarC_Class_Show.show_list
                                    FStarC_Ident.showable_lident))
                              f.unfold_fully in
                          let uu___22 =
                            let uu___23 =
                              FStarC_Class_Show.show
                                (FStarC_Class_Show.show_option
                                   (FStarC_Class_Show.show_list
                                      FStarC_Ident.showable_lident))
                                f.unfold_attr in
                            let uu___24 =
                              let uu___25 =
                                FStarC_Class_Show.show
                                  (FStarC_Class_Show.show_option
                                     (FStarC_Class_Show.show_list
                                        FStarC_Class_Show.showable_string))
                                  f.unfold_qual in
                              let uu___26 =
                                let uu___27 =
                                  FStarC_Class_Show.show
                                    (FStarC_Class_Show.show_option
                                       (FStarC_Class_Show.show_tuple2
                                          (FStarC_Class_Show.show_list
                                             (FStarC_Class_Show.show_tuple2
                                                (FStarC_Class_Show.show_list
                                                   FStarC_Class_Show.showable_string)
                                                FStarC_Class_Show.showable_bool))
                                          FStarC_Class_Show.showable_bool))
                                    f.unfold_namespace in
                                let uu___28 =
                                  let uu___29 =
                                    FStarC_Class_Show.show
                                      (FStarC_Class_Show.show_option
                                         (FStarC_Class_Show.show_list
                                            FStarC_Ident.showable_lident))
                                      f.dont_unfold_attr in
                                  let uu___30 =
                                    let uu___31 =
                                      FStarC_Class_Show.show
                                        FStarC_Class_Show.showable_bool
                                        f.pure_subterms_within_computations in
                                    let uu___32 =
                                      let uu___33 =
                                        FStarC_Class_Show.show
                                          FStarC_Class_Show.showable_bool
                                          f.simplify in
                                      let uu___34 =
                                        let uu___35 =
                                          FStarC_Class_Show.show
                                            FStarC_Class_Show.showable_bool
                                            f.erase_universes in
                                        let uu___36 =
                                          let uu___37 =
                                            FStarC_Class_Show.show
                                              FStarC_Class_Show.showable_bool
                                              f.allow_unbound_universes in
                                          let uu___38 =
                                            let uu___39 =
                                              FStarC_Class_Show.show
                                                FStarC_Class_Show.showable_bool
                                                f.reify_ in
                                            let uu___40 =
                                              let uu___41 =
                                                FStarC_Class_Show.show
                                                  FStarC_Class_Show.showable_bool
                                                  f.compress_uvars in
                                              let uu___42 =
                                                let uu___43 =
                                                  FStarC_Class_Show.show
                                                    FStarC_Class_Show.showable_bool
                                                    f.no_full_norm in
                                                let uu___44 =
                                                  let uu___45 =
                                                    FStarC_Class_Show.show
                                                      FStarC_Class_Show.showable_bool
                                                      f.check_no_uvars in
                                                  let uu___46 =
                                                    let uu___47 =
                                                      FStarC_Class_Show.show
                                                        FStarC_Class_Show.showable_bool
                                                        f.unmeta in
                                                    let uu___48 =
                                                      let uu___49 =
                                                        FStarC_Class_Show.show
                                                          FStarC_Class_Show.showable_bool
                                                          f.unascribe in
                                                      let uu___50 =
                                                        let uu___51 =
                                                          FStarC_Class_Show.show
                                                            FStarC_Class_Show.showable_bool
                                                            f.in_full_norm_request in
                                                        let uu___52 =
                                                          let uu___53 =
                                                            FStarC_Class_Show.show
                                                              FStarC_Class_Show.showable_bool
                                                              f.weakly_reduce_scrutinee in
                                                          let uu___54 =
                                                            let uu___55 =
                                                              FStarC_Class_Show.show
                                                                FStarC_Class_Show.showable_bool
                                                                f.for_extraction in
                                                            let uu___56 =
                                                              let uu___57 =
                                                                FStarC_Class_Show.show
                                                                  FStarC_Class_Show.showable_bool
                                                                  f.unrefine in
                                                              let uu___58 =
                                                                let uu___59 =
                                                                  FStarC_Class_Show.show
                                                                    FStarC_Class_Show.showable_bool
                                                                    f.default_univs_to_zero in
                                                                let uu___60 =
                                                                  let uu___61
                                                                    =
                                                                    FStarC_Class_Show.show
                                                                    FStarC_Class_Show.showable_bool
                                                                    f.tactics in
                                                                  [uu___61] in
                                                                uu___59 ::
                                                                  uu___60 in
                                                              uu___57 ::
                                                                uu___58 in
                                                            uu___55 ::
                                                              uu___56 in
                                                          uu___53 :: uu___54 in
                                                        uu___51 :: uu___52 in
                                                      uu___49 :: uu___50 in
                                                    uu___47 :: uu___48 in
                                                  uu___45 :: uu___46 in
                                                uu___43 :: uu___44 in
                                              uu___41 :: uu___42 in
                                            uu___39 :: uu___40 in
                                          uu___37 :: uu___38 in
                                        uu___35 :: uu___36 in
                                      uu___33 :: uu___34 in
                                    uu___31 :: uu___32 in
                                  uu___29 :: uu___30 in
                                uu___27 :: uu___28 in
                              uu___25 :: uu___26 in
                            uu___23 :: uu___24 in
                          uu___21 :: uu___22 in
                        uu___19 :: uu___20 in
                      uu___17 :: uu___18 in
                    uu___15 :: uu___16 in
                  uu___13 :: uu___14 in
                uu___11 :: uu___12 in
              uu___9 :: uu___10 in
            uu___7 :: uu___8 in
          uu___5 :: uu___6 in
        uu___3 :: uu___4 in
      uu___1 :: uu___2 in
    FStarC_Compiler_Util.format
      "{\nbeta = %s;\niota = %s;\nzeta = %s;\nzeta_full = %s;\nweak = %s;\nhnf  = %s;\nprimops = %s;\ndo_not_unfold_pure_lets = %s;\nunfold_until = %s;\nunfold_only = %s;\nunfold_fully = %s;\nunfold_attr = %s;\nunfold_qual = %s;\nunfold_namespace = %s;\ndont_unfold_attr = %s;\npure_subterms_within_computations = %s;\nsimplify = %s;\nerase_universes = %s;\nallow_unbound_universes = %s;\nreify_ = %s;\ncompress_uvars = %s;\nno_full_norm = %s;\ncheck_no_uvars = %s;\nunmeta = %s;\nunascribe = %s;\nin_full_norm_request = %s;\nweakly_reduce_scrutinee = %s;\nfor_extraction = %s;\nunrefine = %s;\ndefault_univs_to_zero = %s;\ntactics = %s;\n}"
      uu___
let (deq_fsteps : fsteps FStarC_Class_Deq.deq) =
  {
    FStarC_Class_Deq.op_Equals_Question =
      (fun f1 ->
         fun f2 ->
           (((((((((((((((((((((((((((((((FStarC_Class_Deq.op_Equals_Question
                                            (FStarC_Class_Ord.ord_eq
                                               FStarC_Class_Ord.ord_bool)
                                            f1.beta f2.beta)
                                           &&
                                           (FStarC_Class_Deq.op_Equals_Question
                                              (FStarC_Class_Ord.ord_eq
                                                 FStarC_Class_Ord.ord_bool)
                                              f1.iota f2.iota))
                                          &&
                                          (FStarC_Class_Deq.op_Equals_Question
                                             (FStarC_Class_Ord.ord_eq
                                                FStarC_Class_Ord.ord_bool)
                                             f1.zeta f2.zeta))
                                         &&
                                         (FStarC_Class_Deq.op_Equals_Question
                                            (FStarC_Class_Ord.ord_eq
                                               FStarC_Class_Ord.ord_bool)
                                            f1.zeta_full f2.zeta_full))
                                        &&
                                        (FStarC_Class_Deq.op_Equals_Question
                                           (FStarC_Class_Ord.ord_eq
                                              FStarC_Class_Ord.ord_bool)
                                           f1.weak f2.weak))
                                       &&
                                       (FStarC_Class_Deq.op_Equals_Question
                                          (FStarC_Class_Ord.ord_eq
                                             FStarC_Class_Ord.ord_bool)
                                          f1.hnf f2.hnf))
                                      &&
                                      (FStarC_Class_Deq.op_Equals_Question
                                         (FStarC_Class_Ord.ord_eq
                                            FStarC_Class_Ord.ord_bool)
                                         f1.primops f2.primops))
                                     &&
                                     (FStarC_Class_Deq.op_Equals_Question
                                        (FStarC_Class_Ord.ord_eq
                                           FStarC_Class_Ord.ord_bool)
                                        f1.do_not_unfold_pure_lets
                                        f2.do_not_unfold_pure_lets))
                                    &&
                                    (FStarC_Class_Deq.op_Equals_Question
                                       (FStarC_Class_Deq.deq_option
                                          FStarC_Syntax_Syntax.deq_delta_depth)
                                       f1.unfold_until f2.unfold_until))
                                   &&
                                   (FStarC_Class_Deq.op_Equals_Question
                                      (FStarC_Class_Ord.ord_eq
                                         (FStarC_Class_Ord.ord_option
                                            (FStarC_Class_Ord.ord_list
                                               FStarC_Syntax_Syntax.ord_fv)))
                                      f1.unfold_only f2.unfold_only))
                                  &&
                                  (FStarC_Class_Deq.op_Equals_Question
                                     (FStarC_Class_Ord.ord_eq
                                        (FStarC_Class_Ord.ord_option
                                           (FStarC_Class_Ord.ord_list
                                              FStarC_Syntax_Syntax.ord_fv)))
                                     f1.unfold_fully f2.unfold_fully))
                                 &&
                                 (FStarC_Class_Deq.op_Equals_Question
                                    (FStarC_Class_Ord.ord_eq
                                       (FStarC_Class_Ord.ord_option
                                          (FStarC_Class_Ord.ord_list
                                             FStarC_Syntax_Syntax.ord_fv)))
                                    f1.unfold_attr f2.unfold_attr))
                                &&
                                (FStarC_Class_Deq.op_Equals_Question
                                   (FStarC_Class_Ord.ord_eq
                                      (FStarC_Class_Ord.ord_option
                                         (FStarC_Class_Ord.ord_list
                                            FStarC_Class_Ord.ord_string)))
                                   f1.unfold_qual f2.unfold_qual))
                               &&
                               (FStarC_Class_Deq.op_Equals_Question
                                  (FStarC_Class_Ord.ord_eq
                                     (FStarC_Class_Ord.ord_option
                                        (FStarC_Class_Ord.ord_tuple2
                                           (FStarC_Class_Ord.ord_list
                                              (FStarC_Class_Ord.ord_tuple2
                                                 (FStarC_Class_Ord.ord_list
                                                    FStarC_Class_Ord.ord_string)
                                                 FStarC_Class_Ord.ord_bool))
                                           FStarC_Class_Ord.ord_bool)))
                                  f1.unfold_namespace f2.unfold_namespace))
                              &&
                              (FStarC_Class_Deq.op_Equals_Question
                                 (FStarC_Class_Ord.ord_eq
                                    (FStarC_Class_Ord.ord_option
                                       (FStarC_Class_Ord.ord_list
                                          FStarC_Syntax_Syntax.ord_fv)))
                                 f1.dont_unfold_attr f2.dont_unfold_attr))
                             &&
                             (FStarC_Class_Deq.op_Equals_Question
                                (FStarC_Class_Ord.ord_eq
                                   FStarC_Class_Ord.ord_bool)
                                f1.pure_subterms_within_computations
                                f2.pure_subterms_within_computations))
                            &&
                            (FStarC_Class_Deq.op_Equals_Question
                               (FStarC_Class_Ord.ord_eq
                                  FStarC_Class_Ord.ord_bool) f1.simplify
                               f2.simplify))
                           &&
                           (FStarC_Class_Deq.op_Equals_Question
                              (FStarC_Class_Ord.ord_eq
                                 FStarC_Class_Ord.ord_bool)
                              f1.erase_universes f2.erase_universes))
                          &&
                          (FStarC_Class_Deq.op_Equals_Question
                             (FStarC_Class_Ord.ord_eq
                                FStarC_Class_Ord.ord_bool)
                             f1.allow_unbound_universes
                             f2.allow_unbound_universes))
                         &&
                         (FStarC_Class_Deq.op_Equals_Question
                            (FStarC_Class_Ord.ord_eq
                               FStarC_Class_Ord.ord_bool) f1.reify_ f2.reify_))
                        &&
                        (FStarC_Class_Deq.op_Equals_Question
                           (FStarC_Class_Ord.ord_eq FStarC_Class_Ord.ord_bool)
                           f1.compress_uvars f2.compress_uvars))
                       &&
                       (FStarC_Class_Deq.op_Equals_Question
                          (FStarC_Class_Ord.ord_eq FStarC_Class_Ord.ord_bool)
                          f1.no_full_norm f2.no_full_norm))
                      &&
                      (FStarC_Class_Deq.op_Equals_Question
                         (FStarC_Class_Ord.ord_eq FStarC_Class_Ord.ord_bool)
                         f1.check_no_uvars f2.check_no_uvars))
                     &&
                     (FStarC_Class_Deq.op_Equals_Question
                        (FStarC_Class_Ord.ord_eq FStarC_Class_Ord.ord_bool)
                        f1.unmeta f2.unmeta))
                    &&
                    (FStarC_Class_Deq.op_Equals_Question
                       (FStarC_Class_Ord.ord_eq FStarC_Class_Ord.ord_bool)
                       f1.unascribe f2.unascribe))
                   &&
                   (FStarC_Class_Deq.op_Equals_Question
                      (FStarC_Class_Ord.ord_eq FStarC_Class_Ord.ord_bool)
                      f1.in_full_norm_request f2.in_full_norm_request))
                  &&
                  (FStarC_Class_Deq.op_Equals_Question
                     (FStarC_Class_Ord.ord_eq FStarC_Class_Ord.ord_bool)
                     f1.weakly_reduce_scrutinee f2.weakly_reduce_scrutinee))
                 &&
                 (FStarC_Class_Deq.op_Equals_Question
                    (FStarC_Class_Ord.ord_eq FStarC_Class_Ord.ord_bool)
                    f1.nbe_step f2.nbe_step))
                &&
                (FStarC_Class_Deq.op_Equals_Question
                   (FStarC_Class_Ord.ord_eq FStarC_Class_Ord.ord_bool)
                   f1.for_extraction f2.for_extraction))
               &&
               (FStarC_Class_Deq.op_Equals_Question
                  (FStarC_Class_Ord.ord_eq FStarC_Class_Ord.ord_bool)
                  f1.unrefine f2.unrefine))
              &&
              (FStarC_Class_Deq.op_Equals_Question
                 (FStarC_Class_Ord.ord_eq FStarC_Class_Ord.ord_bool)
                 f1.default_univs_to_zero f2.default_univs_to_zero))
             &&
             (FStarC_Class_Deq.op_Equals_Question
                (FStarC_Class_Ord.ord_eq FStarC_Class_Ord.ord_bool)
                f1.tactics f2.tactics))
  }
let (default_steps : fsteps) =
  {
    beta = true;
    iota = true;
    zeta = true;
    zeta_full = false;
    weak = false;
    hnf = false;
    primops = false;
    do_not_unfold_pure_lets = false;
    unfold_until = FStar_Pervasives_Native.None;
    unfold_only = FStar_Pervasives_Native.None;
    unfold_fully = FStar_Pervasives_Native.None;
    unfold_attr = FStar_Pervasives_Native.None;
    unfold_qual = FStar_Pervasives_Native.None;
    unfold_namespace = FStar_Pervasives_Native.None;
    dont_unfold_attr = FStar_Pervasives_Native.None;
    pure_subterms_within_computations = false;
    simplify = false;
    erase_universes = false;
    allow_unbound_universes = false;
    reify_ = false;
    compress_uvars = false;
    no_full_norm = false;
    check_no_uvars = false;
    unmeta = false;
    unascribe = false;
    in_full_norm_request = false;
    weakly_reduce_scrutinee = true;
    nbe_step = false;
    for_extraction = false;
    unrefine = false;
    default_univs_to_zero = false;
    tactics = false
  }
let (fstep_add_one : FStarC_TypeChecker_Env.step -> fsteps -> fsteps) =
  fun s ->
    fun fs ->
      match s with
      | FStarC_TypeChecker_Env.Beta ->
          {
            beta = true;
            iota = (fs.iota);
            zeta = (fs.zeta);
            zeta_full = (fs.zeta_full);
            weak = (fs.weak);
            hnf = (fs.hnf);
            primops = (fs.primops);
            do_not_unfold_pure_lets = (fs.do_not_unfold_pure_lets);
            unfold_until = (fs.unfold_until);
            unfold_only = (fs.unfold_only);
            unfold_fully = (fs.unfold_fully);
            unfold_attr = (fs.unfold_attr);
            unfold_qual = (fs.unfold_qual);
            unfold_namespace = (fs.unfold_namespace);
            dont_unfold_attr = (fs.dont_unfold_attr);
            pure_subterms_within_computations =
              (fs.pure_subterms_within_computations);
            simplify = (fs.simplify);
            erase_universes = (fs.erase_universes);
            allow_unbound_universes = (fs.allow_unbound_universes);
            reify_ = (fs.reify_);
            compress_uvars = (fs.compress_uvars);
            no_full_norm = (fs.no_full_norm);
            check_no_uvars = (fs.check_no_uvars);
            unmeta = (fs.unmeta);
            unascribe = (fs.unascribe);
            in_full_norm_request = (fs.in_full_norm_request);
            weakly_reduce_scrutinee = (fs.weakly_reduce_scrutinee);
            nbe_step = (fs.nbe_step);
            for_extraction = (fs.for_extraction);
            unrefine = (fs.unrefine);
            default_univs_to_zero = (fs.default_univs_to_zero);
            tactics = (fs.tactics)
          }
      | FStarC_TypeChecker_Env.Iota ->
          {
            beta = (fs.beta);
            iota = true;
            zeta = (fs.zeta);
            zeta_full = (fs.zeta_full);
            weak = (fs.weak);
            hnf = (fs.hnf);
            primops = (fs.primops);
            do_not_unfold_pure_lets = (fs.do_not_unfold_pure_lets);
            unfold_until = (fs.unfold_until);
            unfold_only = (fs.unfold_only);
            unfold_fully = (fs.unfold_fully);
            unfold_attr = (fs.unfold_attr);
            unfold_qual = (fs.unfold_qual);
            unfold_namespace = (fs.unfold_namespace);
            dont_unfold_attr = (fs.dont_unfold_attr);
            pure_subterms_within_computations =
              (fs.pure_subterms_within_computations);
            simplify = (fs.simplify);
            erase_universes = (fs.erase_universes);
            allow_unbound_universes = (fs.allow_unbound_universes);
            reify_ = (fs.reify_);
            compress_uvars = (fs.compress_uvars);
            no_full_norm = (fs.no_full_norm);
            check_no_uvars = (fs.check_no_uvars);
            unmeta = (fs.unmeta);
            unascribe = (fs.unascribe);
            in_full_norm_request = (fs.in_full_norm_request);
            weakly_reduce_scrutinee = (fs.weakly_reduce_scrutinee);
            nbe_step = (fs.nbe_step);
            for_extraction = (fs.for_extraction);
            unrefine = (fs.unrefine);
            default_univs_to_zero = (fs.default_univs_to_zero);
            tactics = (fs.tactics)
          }
      | FStarC_TypeChecker_Env.Zeta ->
          {
            beta = (fs.beta);
            iota = (fs.iota);
            zeta = true;
            zeta_full = (fs.zeta_full);
            weak = (fs.weak);
            hnf = (fs.hnf);
            primops = (fs.primops);
            do_not_unfold_pure_lets = (fs.do_not_unfold_pure_lets);
            unfold_until = (fs.unfold_until);
            unfold_only = (fs.unfold_only);
            unfold_fully = (fs.unfold_fully);
            unfold_attr = (fs.unfold_attr);
            unfold_qual = (fs.unfold_qual);
            unfold_namespace = (fs.unfold_namespace);
            dont_unfold_attr = (fs.dont_unfold_attr);
            pure_subterms_within_computations =
              (fs.pure_subterms_within_computations);
            simplify = (fs.simplify);
            erase_universes = (fs.erase_universes);
            allow_unbound_universes = (fs.allow_unbound_universes);
            reify_ = (fs.reify_);
            compress_uvars = (fs.compress_uvars);
            no_full_norm = (fs.no_full_norm);
            check_no_uvars = (fs.check_no_uvars);
            unmeta = (fs.unmeta);
            unascribe = (fs.unascribe);
            in_full_norm_request = (fs.in_full_norm_request);
            weakly_reduce_scrutinee = (fs.weakly_reduce_scrutinee);
            nbe_step = (fs.nbe_step);
            for_extraction = (fs.for_extraction);
            unrefine = (fs.unrefine);
            default_univs_to_zero = (fs.default_univs_to_zero);
            tactics = (fs.tactics)
          }
      | FStarC_TypeChecker_Env.ZetaFull ->
          {
            beta = (fs.beta);
            iota = (fs.iota);
            zeta = (fs.zeta);
            zeta_full = true;
            weak = (fs.weak);
            hnf = (fs.hnf);
            primops = (fs.primops);
            do_not_unfold_pure_lets = (fs.do_not_unfold_pure_lets);
            unfold_until = (fs.unfold_until);
            unfold_only = (fs.unfold_only);
            unfold_fully = (fs.unfold_fully);
            unfold_attr = (fs.unfold_attr);
            unfold_qual = (fs.unfold_qual);
            unfold_namespace = (fs.unfold_namespace);
            dont_unfold_attr = (fs.dont_unfold_attr);
            pure_subterms_within_computations =
              (fs.pure_subterms_within_computations);
            simplify = (fs.simplify);
            erase_universes = (fs.erase_universes);
            allow_unbound_universes = (fs.allow_unbound_universes);
            reify_ = (fs.reify_);
            compress_uvars = (fs.compress_uvars);
            no_full_norm = (fs.no_full_norm);
            check_no_uvars = (fs.check_no_uvars);
            unmeta = (fs.unmeta);
            unascribe = (fs.unascribe);
            in_full_norm_request = (fs.in_full_norm_request);
            weakly_reduce_scrutinee = (fs.weakly_reduce_scrutinee);
            nbe_step = (fs.nbe_step);
            for_extraction = (fs.for_extraction);
            unrefine = (fs.unrefine);
            default_univs_to_zero = (fs.default_univs_to_zero);
            tactics = (fs.tactics)
          }
      | FStarC_TypeChecker_Env.Exclude (FStarC_TypeChecker_Env.Beta) ->
          {
            beta = false;
            iota = (fs.iota);
            zeta = (fs.zeta);
            zeta_full = (fs.zeta_full);
            weak = (fs.weak);
            hnf = (fs.hnf);
            primops = (fs.primops);
            do_not_unfold_pure_lets = (fs.do_not_unfold_pure_lets);
            unfold_until = (fs.unfold_until);
            unfold_only = (fs.unfold_only);
            unfold_fully = (fs.unfold_fully);
            unfold_attr = (fs.unfold_attr);
            unfold_qual = (fs.unfold_qual);
            unfold_namespace = (fs.unfold_namespace);
            dont_unfold_attr = (fs.dont_unfold_attr);
            pure_subterms_within_computations =
              (fs.pure_subterms_within_computations);
            simplify = (fs.simplify);
            erase_universes = (fs.erase_universes);
            allow_unbound_universes = (fs.allow_unbound_universes);
            reify_ = (fs.reify_);
            compress_uvars = (fs.compress_uvars);
            no_full_norm = (fs.no_full_norm);
            check_no_uvars = (fs.check_no_uvars);
            unmeta = (fs.unmeta);
            unascribe = (fs.unascribe);
            in_full_norm_request = (fs.in_full_norm_request);
            weakly_reduce_scrutinee = (fs.weakly_reduce_scrutinee);
            nbe_step = (fs.nbe_step);
            for_extraction = (fs.for_extraction);
            unrefine = (fs.unrefine);
            default_univs_to_zero = (fs.default_univs_to_zero);
            tactics = (fs.tactics)
          }
      | FStarC_TypeChecker_Env.Exclude (FStarC_TypeChecker_Env.Iota) ->
          {
            beta = (fs.beta);
            iota = false;
            zeta = (fs.zeta);
            zeta_full = (fs.zeta_full);
            weak = (fs.weak);
            hnf = (fs.hnf);
            primops = (fs.primops);
            do_not_unfold_pure_lets = (fs.do_not_unfold_pure_lets);
            unfold_until = (fs.unfold_until);
            unfold_only = (fs.unfold_only);
            unfold_fully = (fs.unfold_fully);
            unfold_attr = (fs.unfold_attr);
            unfold_qual = (fs.unfold_qual);
            unfold_namespace = (fs.unfold_namespace);
            dont_unfold_attr = (fs.dont_unfold_attr);
            pure_subterms_within_computations =
              (fs.pure_subterms_within_computations);
            simplify = (fs.simplify);
            erase_universes = (fs.erase_universes);
            allow_unbound_universes = (fs.allow_unbound_universes);
            reify_ = (fs.reify_);
            compress_uvars = (fs.compress_uvars);
            no_full_norm = (fs.no_full_norm);
            check_no_uvars = (fs.check_no_uvars);
            unmeta = (fs.unmeta);
            unascribe = (fs.unascribe);
            in_full_norm_request = (fs.in_full_norm_request);
            weakly_reduce_scrutinee = (fs.weakly_reduce_scrutinee);
            nbe_step = (fs.nbe_step);
            for_extraction = (fs.for_extraction);
            unrefine = (fs.unrefine);
            default_univs_to_zero = (fs.default_univs_to_zero);
            tactics = (fs.tactics)
          }
      | FStarC_TypeChecker_Env.Exclude (FStarC_TypeChecker_Env.Zeta) ->
          {
            beta = (fs.beta);
            iota = (fs.iota);
            zeta = false;
            zeta_full = (fs.zeta_full);
            weak = (fs.weak);
            hnf = (fs.hnf);
            primops = (fs.primops);
            do_not_unfold_pure_lets = (fs.do_not_unfold_pure_lets);
            unfold_until = (fs.unfold_until);
            unfold_only = (fs.unfold_only);
            unfold_fully = (fs.unfold_fully);
            unfold_attr = (fs.unfold_attr);
            unfold_qual = (fs.unfold_qual);
            unfold_namespace = (fs.unfold_namespace);
            dont_unfold_attr = (fs.dont_unfold_attr);
            pure_subterms_within_computations =
              (fs.pure_subterms_within_computations);
            simplify = (fs.simplify);
            erase_universes = (fs.erase_universes);
            allow_unbound_universes = (fs.allow_unbound_universes);
            reify_ = (fs.reify_);
            compress_uvars = (fs.compress_uvars);
            no_full_norm = (fs.no_full_norm);
            check_no_uvars = (fs.check_no_uvars);
            unmeta = (fs.unmeta);
            unascribe = (fs.unascribe);
            in_full_norm_request = (fs.in_full_norm_request);
            weakly_reduce_scrutinee = (fs.weakly_reduce_scrutinee);
            nbe_step = (fs.nbe_step);
            for_extraction = (fs.for_extraction);
            unrefine = (fs.unrefine);
            default_univs_to_zero = (fs.default_univs_to_zero);
            tactics = (fs.tactics)
          }
      | FStarC_TypeChecker_Env.Exclude uu___ -> failwith "Bad exclude"
      | FStarC_TypeChecker_Env.Weak ->
          {
            beta = (fs.beta);
            iota = (fs.iota);
            zeta = (fs.zeta);
            zeta_full = (fs.zeta_full);
            weak = true;
            hnf = (fs.hnf);
            primops = (fs.primops);
            do_not_unfold_pure_lets = (fs.do_not_unfold_pure_lets);
            unfold_until = (fs.unfold_until);
            unfold_only = (fs.unfold_only);
            unfold_fully = (fs.unfold_fully);
            unfold_attr = (fs.unfold_attr);
            unfold_qual = (fs.unfold_qual);
            unfold_namespace = (fs.unfold_namespace);
            dont_unfold_attr = (fs.dont_unfold_attr);
            pure_subterms_within_computations =
              (fs.pure_subterms_within_computations);
            simplify = (fs.simplify);
            erase_universes = (fs.erase_universes);
            allow_unbound_universes = (fs.allow_unbound_universes);
            reify_ = (fs.reify_);
            compress_uvars = (fs.compress_uvars);
            no_full_norm = (fs.no_full_norm);
            check_no_uvars = (fs.check_no_uvars);
            unmeta = (fs.unmeta);
            unascribe = (fs.unascribe);
            in_full_norm_request = (fs.in_full_norm_request);
            weakly_reduce_scrutinee = (fs.weakly_reduce_scrutinee);
            nbe_step = (fs.nbe_step);
            for_extraction = (fs.for_extraction);
            unrefine = (fs.unrefine);
            default_univs_to_zero = (fs.default_univs_to_zero);
            tactics = (fs.tactics)
          }
      | FStarC_TypeChecker_Env.HNF ->
          {
            beta = (fs.beta);
            iota = (fs.iota);
            zeta = (fs.zeta);
            zeta_full = (fs.zeta_full);
            weak = (fs.weak);
            hnf = true;
            primops = (fs.primops);
            do_not_unfold_pure_lets = (fs.do_not_unfold_pure_lets);
            unfold_until = (fs.unfold_until);
            unfold_only = (fs.unfold_only);
            unfold_fully = (fs.unfold_fully);
            unfold_attr = (fs.unfold_attr);
            unfold_qual = (fs.unfold_qual);
            unfold_namespace = (fs.unfold_namespace);
            dont_unfold_attr = (fs.dont_unfold_attr);
            pure_subterms_within_computations =
              (fs.pure_subterms_within_computations);
            simplify = (fs.simplify);
            erase_universes = (fs.erase_universes);
            allow_unbound_universes = (fs.allow_unbound_universes);
            reify_ = (fs.reify_);
            compress_uvars = (fs.compress_uvars);
            no_full_norm = (fs.no_full_norm);
            check_no_uvars = (fs.check_no_uvars);
            unmeta = (fs.unmeta);
            unascribe = (fs.unascribe);
            in_full_norm_request = (fs.in_full_norm_request);
            weakly_reduce_scrutinee = (fs.weakly_reduce_scrutinee);
            nbe_step = (fs.nbe_step);
            for_extraction = (fs.for_extraction);
            unrefine = (fs.unrefine);
            default_univs_to_zero = (fs.default_univs_to_zero);
            tactics = (fs.tactics)
          }
      | FStarC_TypeChecker_Env.Primops ->
          {
            beta = (fs.beta);
            iota = (fs.iota);
            zeta = (fs.zeta);
            zeta_full = (fs.zeta_full);
            weak = (fs.weak);
            hnf = (fs.hnf);
            primops = true;
            do_not_unfold_pure_lets = (fs.do_not_unfold_pure_lets);
            unfold_until = (fs.unfold_until);
            unfold_only = (fs.unfold_only);
            unfold_fully = (fs.unfold_fully);
            unfold_attr = (fs.unfold_attr);
            unfold_qual = (fs.unfold_qual);
            unfold_namespace = (fs.unfold_namespace);
            dont_unfold_attr = (fs.dont_unfold_attr);
            pure_subterms_within_computations =
              (fs.pure_subterms_within_computations);
            simplify = (fs.simplify);
            erase_universes = (fs.erase_universes);
            allow_unbound_universes = (fs.allow_unbound_universes);
            reify_ = (fs.reify_);
            compress_uvars = (fs.compress_uvars);
            no_full_norm = (fs.no_full_norm);
            check_no_uvars = (fs.check_no_uvars);
            unmeta = (fs.unmeta);
            unascribe = (fs.unascribe);
            in_full_norm_request = (fs.in_full_norm_request);
            weakly_reduce_scrutinee = (fs.weakly_reduce_scrutinee);
            nbe_step = (fs.nbe_step);
            for_extraction = (fs.for_extraction);
            unrefine = (fs.unrefine);
            default_univs_to_zero = (fs.default_univs_to_zero);
            tactics = (fs.tactics)
          }
      | FStarC_TypeChecker_Env.Eager_unfolding -> fs
      | FStarC_TypeChecker_Env.Inlining -> fs
      | FStarC_TypeChecker_Env.DoNotUnfoldPureLets ->
          {
            beta = (fs.beta);
            iota = (fs.iota);
            zeta = (fs.zeta);
            zeta_full = (fs.zeta_full);
            weak = (fs.weak);
            hnf = (fs.hnf);
            primops = (fs.primops);
            do_not_unfold_pure_lets = true;
            unfold_until = (fs.unfold_until);
            unfold_only = (fs.unfold_only);
            unfold_fully = (fs.unfold_fully);
            unfold_attr = (fs.unfold_attr);
            unfold_qual = (fs.unfold_qual);
            unfold_namespace = (fs.unfold_namespace);
            dont_unfold_attr = (fs.dont_unfold_attr);
            pure_subterms_within_computations =
              (fs.pure_subterms_within_computations);
            simplify = (fs.simplify);
            erase_universes = (fs.erase_universes);
            allow_unbound_universes = (fs.allow_unbound_universes);
            reify_ = (fs.reify_);
            compress_uvars = (fs.compress_uvars);
            no_full_norm = (fs.no_full_norm);
            check_no_uvars = (fs.check_no_uvars);
            unmeta = (fs.unmeta);
            unascribe = (fs.unascribe);
            in_full_norm_request = (fs.in_full_norm_request);
            weakly_reduce_scrutinee = (fs.weakly_reduce_scrutinee);
            nbe_step = (fs.nbe_step);
            for_extraction = (fs.for_extraction);
            unrefine = (fs.unrefine);
            default_univs_to_zero = (fs.default_univs_to_zero);
            tactics = (fs.tactics)
          }
      | FStarC_TypeChecker_Env.UnfoldUntil d ->
          {
            beta = (fs.beta);
            iota = (fs.iota);
            zeta = (fs.zeta);
            zeta_full = (fs.zeta_full);
            weak = (fs.weak);
            hnf = (fs.hnf);
            primops = (fs.primops);
            do_not_unfold_pure_lets = (fs.do_not_unfold_pure_lets);
            unfold_until = (FStar_Pervasives_Native.Some d);
            unfold_only = (fs.unfold_only);
            unfold_fully = (fs.unfold_fully);
            unfold_attr = (fs.unfold_attr);
            unfold_qual = (fs.unfold_qual);
            unfold_namespace = (fs.unfold_namespace);
            dont_unfold_attr = (fs.dont_unfold_attr);
            pure_subterms_within_computations =
              (fs.pure_subterms_within_computations);
            simplify = (fs.simplify);
            erase_universes = (fs.erase_universes);
            allow_unbound_universes = (fs.allow_unbound_universes);
            reify_ = (fs.reify_);
            compress_uvars = (fs.compress_uvars);
            no_full_norm = (fs.no_full_norm);
            check_no_uvars = (fs.check_no_uvars);
            unmeta = (fs.unmeta);
            unascribe = (fs.unascribe);
            in_full_norm_request = (fs.in_full_norm_request);
            weakly_reduce_scrutinee = (fs.weakly_reduce_scrutinee);
            nbe_step = (fs.nbe_step);
            for_extraction = (fs.for_extraction);
            unrefine = (fs.unrefine);
            default_univs_to_zero = (fs.default_univs_to_zero);
            tactics = (fs.tactics)
          }
      | FStarC_TypeChecker_Env.UnfoldOnly lids ->
          {
            beta = (fs.beta);
            iota = (fs.iota);
            zeta = (fs.zeta);
            zeta_full = (fs.zeta_full);
            weak = (fs.weak);
            hnf = (fs.hnf);
            primops = (fs.primops);
            do_not_unfold_pure_lets = (fs.do_not_unfold_pure_lets);
            unfold_until = (fs.unfold_until);
            unfold_only = (FStar_Pervasives_Native.Some lids);
            unfold_fully = (fs.unfold_fully);
            unfold_attr = (fs.unfold_attr);
            unfold_qual = (fs.unfold_qual);
            unfold_namespace = (fs.unfold_namespace);
            dont_unfold_attr = (fs.dont_unfold_attr);
            pure_subterms_within_computations =
              (fs.pure_subterms_within_computations);
            simplify = (fs.simplify);
            erase_universes = (fs.erase_universes);
            allow_unbound_universes = (fs.allow_unbound_universes);
            reify_ = (fs.reify_);
            compress_uvars = (fs.compress_uvars);
            no_full_norm = (fs.no_full_norm);
            check_no_uvars = (fs.check_no_uvars);
            unmeta = (fs.unmeta);
            unascribe = (fs.unascribe);
            in_full_norm_request = (fs.in_full_norm_request);
            weakly_reduce_scrutinee = (fs.weakly_reduce_scrutinee);
            nbe_step = (fs.nbe_step);
            for_extraction = (fs.for_extraction);
            unrefine = (fs.unrefine);
            default_univs_to_zero = (fs.default_univs_to_zero);
            tactics = (fs.tactics)
          }
      | FStarC_TypeChecker_Env.UnfoldFully lids ->
          {
            beta = (fs.beta);
            iota = (fs.iota);
            zeta = (fs.zeta);
            zeta_full = (fs.zeta_full);
            weak = (fs.weak);
            hnf = (fs.hnf);
            primops = (fs.primops);
            do_not_unfold_pure_lets = (fs.do_not_unfold_pure_lets);
            unfold_until = (fs.unfold_until);
            unfold_only = (fs.unfold_only);
            unfold_fully = (FStar_Pervasives_Native.Some lids);
            unfold_attr = (fs.unfold_attr);
            unfold_qual = (fs.unfold_qual);
            unfold_namespace = (fs.unfold_namespace);
            dont_unfold_attr = (fs.dont_unfold_attr);
            pure_subterms_within_computations =
              (fs.pure_subterms_within_computations);
            simplify = (fs.simplify);
            erase_universes = (fs.erase_universes);
            allow_unbound_universes = (fs.allow_unbound_universes);
            reify_ = (fs.reify_);
            compress_uvars = (fs.compress_uvars);
            no_full_norm = (fs.no_full_norm);
            check_no_uvars = (fs.check_no_uvars);
            unmeta = (fs.unmeta);
            unascribe = (fs.unascribe);
            in_full_norm_request = (fs.in_full_norm_request);
            weakly_reduce_scrutinee = (fs.weakly_reduce_scrutinee);
            nbe_step = (fs.nbe_step);
            for_extraction = (fs.for_extraction);
            unrefine = (fs.unrefine);
            default_univs_to_zero = (fs.default_univs_to_zero);
            tactics = (fs.tactics)
          }
      | FStarC_TypeChecker_Env.UnfoldAttr lids ->
          {
            beta = (fs.beta);
            iota = (fs.iota);
            zeta = (fs.zeta);
            zeta_full = (fs.zeta_full);
            weak = (fs.weak);
            hnf = (fs.hnf);
            primops = (fs.primops);
            do_not_unfold_pure_lets = (fs.do_not_unfold_pure_lets);
            unfold_until = (fs.unfold_until);
            unfold_only = (fs.unfold_only);
            unfold_fully = (fs.unfold_fully);
            unfold_attr = (FStar_Pervasives_Native.Some lids);
            unfold_qual = (fs.unfold_qual);
            unfold_namespace = (fs.unfold_namespace);
            dont_unfold_attr = (fs.dont_unfold_attr);
            pure_subterms_within_computations =
              (fs.pure_subterms_within_computations);
            simplify = (fs.simplify);
            erase_universes = (fs.erase_universes);
            allow_unbound_universes = (fs.allow_unbound_universes);
            reify_ = (fs.reify_);
            compress_uvars = (fs.compress_uvars);
            no_full_norm = (fs.no_full_norm);
            check_no_uvars = (fs.check_no_uvars);
            unmeta = (fs.unmeta);
            unascribe = (fs.unascribe);
            in_full_norm_request = (fs.in_full_norm_request);
            weakly_reduce_scrutinee = (fs.weakly_reduce_scrutinee);
            nbe_step = (fs.nbe_step);
            for_extraction = (fs.for_extraction);
            unrefine = (fs.unrefine);
            default_univs_to_zero = (fs.default_univs_to_zero);
            tactics = (fs.tactics)
          }
      | FStarC_TypeChecker_Env.UnfoldQual strs ->
          let fs1 =
            {
              beta = (fs.beta);
              iota = (fs.iota);
              zeta = (fs.zeta);
              zeta_full = (fs.zeta_full);
              weak = (fs.weak);
              hnf = (fs.hnf);
              primops = (fs.primops);
              do_not_unfold_pure_lets = (fs.do_not_unfold_pure_lets);
              unfold_until = (fs.unfold_until);
              unfold_only = (fs.unfold_only);
              unfold_fully = (fs.unfold_fully);
              unfold_attr = (fs.unfold_attr);
              unfold_qual = (FStar_Pervasives_Native.Some strs);
              unfold_namespace = (fs.unfold_namespace);
              dont_unfold_attr = (fs.dont_unfold_attr);
              pure_subterms_within_computations =
                (fs.pure_subterms_within_computations);
              simplify = (fs.simplify);
              erase_universes = (fs.erase_universes);
              allow_unbound_universes = (fs.allow_unbound_universes);
              reify_ = (fs.reify_);
              compress_uvars = (fs.compress_uvars);
              no_full_norm = (fs.no_full_norm);
              check_no_uvars = (fs.check_no_uvars);
              unmeta = (fs.unmeta);
              unascribe = (fs.unascribe);
              in_full_norm_request = (fs.in_full_norm_request);
              weakly_reduce_scrutinee = (fs.weakly_reduce_scrutinee);
              nbe_step = (fs.nbe_step);
              for_extraction = (fs.for_extraction);
              unrefine = (fs.unrefine);
              default_univs_to_zero = (fs.default_univs_to_zero);
              tactics = (fs.tactics)
            } in
          if
            FStarC_Compiler_List.contains "pure_subterms_within_computations"
              strs
          then
            {
              beta = (fs1.beta);
              iota = (fs1.iota);
              zeta = (fs1.zeta);
              zeta_full = (fs1.zeta_full);
              weak = (fs1.weak);
              hnf = (fs1.hnf);
              primops = (fs1.primops);
              do_not_unfold_pure_lets = (fs1.do_not_unfold_pure_lets);
              unfold_until = (fs1.unfold_until);
              unfold_only = (fs1.unfold_only);
              unfold_fully = (fs1.unfold_fully);
              unfold_attr = (fs1.unfold_attr);
              unfold_qual = (fs1.unfold_qual);
              unfold_namespace = (fs1.unfold_namespace);
              dont_unfold_attr = (fs1.dont_unfold_attr);
              pure_subterms_within_computations = true;
              simplify = (fs1.simplify);
              erase_universes = (fs1.erase_universes);
              allow_unbound_universes = (fs1.allow_unbound_universes);
              reify_ = (fs1.reify_);
              compress_uvars = (fs1.compress_uvars);
              no_full_norm = (fs1.no_full_norm);
              check_no_uvars = (fs1.check_no_uvars);
              unmeta = (fs1.unmeta);
              unascribe = (fs1.unascribe);
              in_full_norm_request = (fs1.in_full_norm_request);
              weakly_reduce_scrutinee = (fs1.weakly_reduce_scrutinee);
              nbe_step = (fs1.nbe_step);
              for_extraction = (fs1.for_extraction);
              unrefine = (fs1.unrefine);
              default_univs_to_zero = (fs1.default_univs_to_zero);
              tactics = (fs1.tactics)
            }
          else fs1
      | FStarC_TypeChecker_Env.UnfoldNamespace strs ->
          let uu___ =
            let uu___1 =
              let uu___2 =
                FStarC_Compiler_List.map
                  (fun s1 ->
                     let uu___3 = FStarC_Ident.path_of_text s1 in
                     (uu___3, true)) strs in
              (uu___2, false) in
            FStar_Pervasives_Native.Some uu___1 in
          {
            beta = (fs.beta);
            iota = (fs.iota);
            zeta = (fs.zeta);
            zeta_full = (fs.zeta_full);
            weak = (fs.weak);
            hnf = (fs.hnf);
            primops = (fs.primops);
            do_not_unfold_pure_lets = (fs.do_not_unfold_pure_lets);
            unfold_until = (fs.unfold_until);
            unfold_only = (fs.unfold_only);
            unfold_fully = (fs.unfold_fully);
            unfold_attr = (fs.unfold_attr);
            unfold_qual = (fs.unfold_qual);
            unfold_namespace = uu___;
            dont_unfold_attr = (fs.dont_unfold_attr);
            pure_subterms_within_computations =
              (fs.pure_subterms_within_computations);
            simplify = (fs.simplify);
            erase_universes = (fs.erase_universes);
            allow_unbound_universes = (fs.allow_unbound_universes);
            reify_ = (fs.reify_);
            compress_uvars = (fs.compress_uvars);
            no_full_norm = (fs.no_full_norm);
            check_no_uvars = (fs.check_no_uvars);
            unmeta = (fs.unmeta);
            unascribe = (fs.unascribe);
            in_full_norm_request = (fs.in_full_norm_request);
            weakly_reduce_scrutinee = (fs.weakly_reduce_scrutinee);
            nbe_step = (fs.nbe_step);
            for_extraction = (fs.for_extraction);
            unrefine = (fs.unrefine);
            default_univs_to_zero = (fs.default_univs_to_zero);
            tactics = (fs.tactics)
          }
      | FStarC_TypeChecker_Env.DontUnfoldAttr lids ->
          {
            beta = (fs.beta);
            iota = (fs.iota);
            zeta = (fs.zeta);
            zeta_full = (fs.zeta_full);
            weak = (fs.weak);
            hnf = (fs.hnf);
            primops = (fs.primops);
            do_not_unfold_pure_lets = (fs.do_not_unfold_pure_lets);
            unfold_until = (fs.unfold_until);
            unfold_only = (fs.unfold_only);
            unfold_fully = (fs.unfold_fully);
            unfold_attr = (fs.unfold_attr);
            unfold_qual = (fs.unfold_qual);
            unfold_namespace = (fs.unfold_namespace);
            dont_unfold_attr = (FStar_Pervasives_Native.Some lids);
            pure_subterms_within_computations =
              (fs.pure_subterms_within_computations);
            simplify = (fs.simplify);
            erase_universes = (fs.erase_universes);
            allow_unbound_universes = (fs.allow_unbound_universes);
            reify_ = (fs.reify_);
            compress_uvars = (fs.compress_uvars);
            no_full_norm = (fs.no_full_norm);
            check_no_uvars = (fs.check_no_uvars);
            unmeta = (fs.unmeta);
            unascribe = (fs.unascribe);
            in_full_norm_request = (fs.in_full_norm_request);
            weakly_reduce_scrutinee = (fs.weakly_reduce_scrutinee);
            nbe_step = (fs.nbe_step);
            for_extraction = (fs.for_extraction);
            unrefine = (fs.unrefine);
            default_univs_to_zero = (fs.default_univs_to_zero);
            tactics = (fs.tactics)
          }
      | FStarC_TypeChecker_Env.PureSubtermsWithinComputations ->
          {
            beta = (fs.beta);
            iota = (fs.iota);
            zeta = (fs.zeta);
            zeta_full = (fs.zeta_full);
            weak = (fs.weak);
            hnf = (fs.hnf);
            primops = (fs.primops);
            do_not_unfold_pure_lets = (fs.do_not_unfold_pure_lets);
            unfold_until = (fs.unfold_until);
            unfold_only = (fs.unfold_only);
            unfold_fully = (fs.unfold_fully);
            unfold_attr = (fs.unfold_attr);
            unfold_qual = (fs.unfold_qual);
            unfold_namespace = (fs.unfold_namespace);
            dont_unfold_attr = (fs.dont_unfold_attr);
            pure_subterms_within_computations = true;
            simplify = (fs.simplify);
            erase_universes = (fs.erase_universes);
            allow_unbound_universes = (fs.allow_unbound_universes);
            reify_ = (fs.reify_);
            compress_uvars = (fs.compress_uvars);
            no_full_norm = (fs.no_full_norm);
            check_no_uvars = (fs.check_no_uvars);
            unmeta = (fs.unmeta);
            unascribe = (fs.unascribe);
            in_full_norm_request = (fs.in_full_norm_request);
            weakly_reduce_scrutinee = (fs.weakly_reduce_scrutinee);
            nbe_step = (fs.nbe_step);
            for_extraction = (fs.for_extraction);
            unrefine = (fs.unrefine);
            default_univs_to_zero = (fs.default_univs_to_zero);
            tactics = (fs.tactics)
          }
      | FStarC_TypeChecker_Env.Simplify ->
          {
            beta = (fs.beta);
            iota = (fs.iota);
            zeta = (fs.zeta);
            zeta_full = (fs.zeta_full);
            weak = (fs.weak);
            hnf = (fs.hnf);
            primops = (fs.primops);
            do_not_unfold_pure_lets = (fs.do_not_unfold_pure_lets);
            unfold_until = (fs.unfold_until);
            unfold_only = (fs.unfold_only);
            unfold_fully = (fs.unfold_fully);
            unfold_attr = (fs.unfold_attr);
            unfold_qual = (fs.unfold_qual);
            unfold_namespace = (fs.unfold_namespace);
            dont_unfold_attr = (fs.dont_unfold_attr);
            pure_subterms_within_computations =
              (fs.pure_subterms_within_computations);
            simplify = true;
            erase_universes = (fs.erase_universes);
            allow_unbound_universes = (fs.allow_unbound_universes);
            reify_ = (fs.reify_);
            compress_uvars = (fs.compress_uvars);
            no_full_norm = (fs.no_full_norm);
            check_no_uvars = (fs.check_no_uvars);
            unmeta = (fs.unmeta);
            unascribe = (fs.unascribe);
            in_full_norm_request = (fs.in_full_norm_request);
            weakly_reduce_scrutinee = (fs.weakly_reduce_scrutinee);
            nbe_step = (fs.nbe_step);
            for_extraction = (fs.for_extraction);
            unrefine = (fs.unrefine);
            default_univs_to_zero = (fs.default_univs_to_zero);
            tactics = (fs.tactics)
          }
      | FStarC_TypeChecker_Env.EraseUniverses ->
          {
            beta = (fs.beta);
            iota = (fs.iota);
            zeta = (fs.zeta);
            zeta_full = (fs.zeta_full);
            weak = (fs.weak);
            hnf = (fs.hnf);
            primops = (fs.primops);
            do_not_unfold_pure_lets = (fs.do_not_unfold_pure_lets);
            unfold_until = (fs.unfold_until);
            unfold_only = (fs.unfold_only);
            unfold_fully = (fs.unfold_fully);
            unfold_attr = (fs.unfold_attr);
            unfold_qual = (fs.unfold_qual);
            unfold_namespace = (fs.unfold_namespace);
            dont_unfold_attr = (fs.dont_unfold_attr);
            pure_subterms_within_computations =
              (fs.pure_subterms_within_computations);
            simplify = (fs.simplify);
            erase_universes = true;
            allow_unbound_universes = (fs.allow_unbound_universes);
            reify_ = (fs.reify_);
            compress_uvars = (fs.compress_uvars);
            no_full_norm = (fs.no_full_norm);
            check_no_uvars = (fs.check_no_uvars);
            unmeta = (fs.unmeta);
            unascribe = (fs.unascribe);
            in_full_norm_request = (fs.in_full_norm_request);
            weakly_reduce_scrutinee = (fs.weakly_reduce_scrutinee);
            nbe_step = (fs.nbe_step);
            for_extraction = (fs.for_extraction);
            unrefine = (fs.unrefine);
            default_univs_to_zero = (fs.default_univs_to_zero);
            tactics = (fs.tactics)
          }
      | FStarC_TypeChecker_Env.AllowUnboundUniverses ->
          {
            beta = (fs.beta);
            iota = (fs.iota);
            zeta = (fs.zeta);
            zeta_full = (fs.zeta_full);
            weak = (fs.weak);
            hnf = (fs.hnf);
            primops = (fs.primops);
            do_not_unfold_pure_lets = (fs.do_not_unfold_pure_lets);
            unfold_until = (fs.unfold_until);
            unfold_only = (fs.unfold_only);
            unfold_fully = (fs.unfold_fully);
            unfold_attr = (fs.unfold_attr);
            unfold_qual = (fs.unfold_qual);
            unfold_namespace = (fs.unfold_namespace);
            dont_unfold_attr = (fs.dont_unfold_attr);
            pure_subterms_within_computations =
              (fs.pure_subterms_within_computations);
            simplify = (fs.simplify);
            erase_universes = (fs.erase_universes);
            allow_unbound_universes = true;
            reify_ = (fs.reify_);
            compress_uvars = (fs.compress_uvars);
            no_full_norm = (fs.no_full_norm);
            check_no_uvars = (fs.check_no_uvars);
            unmeta = (fs.unmeta);
            unascribe = (fs.unascribe);
            in_full_norm_request = (fs.in_full_norm_request);
            weakly_reduce_scrutinee = (fs.weakly_reduce_scrutinee);
            nbe_step = (fs.nbe_step);
            for_extraction = (fs.for_extraction);
            unrefine = (fs.unrefine);
            default_univs_to_zero = (fs.default_univs_to_zero);
            tactics = (fs.tactics)
          }
      | FStarC_TypeChecker_Env.Reify ->
          {
            beta = (fs.beta);
            iota = (fs.iota);
            zeta = (fs.zeta);
            zeta_full = (fs.zeta_full);
            weak = (fs.weak);
            hnf = (fs.hnf);
            primops = (fs.primops);
            do_not_unfold_pure_lets = (fs.do_not_unfold_pure_lets);
            unfold_until = (fs.unfold_until);
            unfold_only = (fs.unfold_only);
            unfold_fully = (fs.unfold_fully);
            unfold_attr = (fs.unfold_attr);
            unfold_qual = (fs.unfold_qual);
            unfold_namespace = (fs.unfold_namespace);
            dont_unfold_attr = (fs.dont_unfold_attr);
            pure_subterms_within_computations =
              (fs.pure_subterms_within_computations);
            simplify = (fs.simplify);
            erase_universes = (fs.erase_universes);
            allow_unbound_universes = (fs.allow_unbound_universes);
            reify_ = true;
            compress_uvars = (fs.compress_uvars);
            no_full_norm = (fs.no_full_norm);
            check_no_uvars = (fs.check_no_uvars);
            unmeta = (fs.unmeta);
            unascribe = (fs.unascribe);
            in_full_norm_request = (fs.in_full_norm_request);
            weakly_reduce_scrutinee = (fs.weakly_reduce_scrutinee);
            nbe_step = (fs.nbe_step);
            for_extraction = (fs.for_extraction);
            unrefine = (fs.unrefine);
            default_univs_to_zero = (fs.default_univs_to_zero);
            tactics = (fs.tactics)
          }
      | FStarC_TypeChecker_Env.CompressUvars ->
          {
            beta = (fs.beta);
            iota = (fs.iota);
            zeta = (fs.zeta);
            zeta_full = (fs.zeta_full);
            weak = (fs.weak);
            hnf = (fs.hnf);
            primops = (fs.primops);
            do_not_unfold_pure_lets = (fs.do_not_unfold_pure_lets);
            unfold_until = (fs.unfold_until);
            unfold_only = (fs.unfold_only);
            unfold_fully = (fs.unfold_fully);
            unfold_attr = (fs.unfold_attr);
            unfold_qual = (fs.unfold_qual);
            unfold_namespace = (fs.unfold_namespace);
            dont_unfold_attr = (fs.dont_unfold_attr);
            pure_subterms_within_computations =
              (fs.pure_subterms_within_computations);
            simplify = (fs.simplify);
            erase_universes = (fs.erase_universes);
            allow_unbound_universes = (fs.allow_unbound_universes);
            reify_ = (fs.reify_);
            compress_uvars = true;
            no_full_norm = (fs.no_full_norm);
            check_no_uvars = (fs.check_no_uvars);
            unmeta = (fs.unmeta);
            unascribe = (fs.unascribe);
            in_full_norm_request = (fs.in_full_norm_request);
            weakly_reduce_scrutinee = (fs.weakly_reduce_scrutinee);
            nbe_step = (fs.nbe_step);
            for_extraction = (fs.for_extraction);
            unrefine = (fs.unrefine);
            default_univs_to_zero = (fs.default_univs_to_zero);
            tactics = (fs.tactics)
          }
      | FStarC_TypeChecker_Env.NoFullNorm ->
          {
            beta = (fs.beta);
            iota = (fs.iota);
            zeta = (fs.zeta);
            zeta_full = (fs.zeta_full);
            weak = (fs.weak);
            hnf = (fs.hnf);
            primops = (fs.primops);
            do_not_unfold_pure_lets = (fs.do_not_unfold_pure_lets);
            unfold_until = (fs.unfold_until);
            unfold_only = (fs.unfold_only);
            unfold_fully = (fs.unfold_fully);
            unfold_attr = (fs.unfold_attr);
            unfold_qual = (fs.unfold_qual);
            unfold_namespace = (fs.unfold_namespace);
            dont_unfold_attr = (fs.dont_unfold_attr);
            pure_subterms_within_computations =
              (fs.pure_subterms_within_computations);
            simplify = (fs.simplify);
            erase_universes = (fs.erase_universes);
            allow_unbound_universes = (fs.allow_unbound_universes);
            reify_ = (fs.reify_);
            compress_uvars = (fs.compress_uvars);
            no_full_norm = true;
            check_no_uvars = (fs.check_no_uvars);
            unmeta = (fs.unmeta);
            unascribe = (fs.unascribe);
            in_full_norm_request = (fs.in_full_norm_request);
            weakly_reduce_scrutinee = (fs.weakly_reduce_scrutinee);
            nbe_step = (fs.nbe_step);
            for_extraction = (fs.for_extraction);
            unrefine = (fs.unrefine);
            default_univs_to_zero = (fs.default_univs_to_zero);
            tactics = (fs.tactics)
          }
      | FStarC_TypeChecker_Env.CheckNoUvars ->
          {
            beta = (fs.beta);
            iota = (fs.iota);
            zeta = (fs.zeta);
            zeta_full = (fs.zeta_full);
            weak = (fs.weak);
            hnf = (fs.hnf);
            primops = (fs.primops);
            do_not_unfold_pure_lets = (fs.do_not_unfold_pure_lets);
            unfold_until = (fs.unfold_until);
            unfold_only = (fs.unfold_only);
            unfold_fully = (fs.unfold_fully);
            unfold_attr = (fs.unfold_attr);
            unfold_qual = (fs.unfold_qual);
            unfold_namespace = (fs.unfold_namespace);
            dont_unfold_attr = (fs.dont_unfold_attr);
            pure_subterms_within_computations =
              (fs.pure_subterms_within_computations);
            simplify = (fs.simplify);
            erase_universes = (fs.erase_universes);
            allow_unbound_universes = (fs.allow_unbound_universes);
            reify_ = (fs.reify_);
            compress_uvars = (fs.compress_uvars);
            no_full_norm = (fs.no_full_norm);
            check_no_uvars = true;
            unmeta = (fs.unmeta);
            unascribe = (fs.unascribe);
            in_full_norm_request = (fs.in_full_norm_request);
            weakly_reduce_scrutinee = (fs.weakly_reduce_scrutinee);
            nbe_step = (fs.nbe_step);
            for_extraction = (fs.for_extraction);
            unrefine = (fs.unrefine);
            default_univs_to_zero = (fs.default_univs_to_zero);
            tactics = (fs.tactics)
          }
      | FStarC_TypeChecker_Env.Unmeta ->
          {
            beta = (fs.beta);
            iota = (fs.iota);
            zeta = (fs.zeta);
            zeta_full = (fs.zeta_full);
            weak = (fs.weak);
            hnf = (fs.hnf);
            primops = (fs.primops);
            do_not_unfold_pure_lets = (fs.do_not_unfold_pure_lets);
            unfold_until = (fs.unfold_until);
            unfold_only = (fs.unfold_only);
            unfold_fully = (fs.unfold_fully);
            unfold_attr = (fs.unfold_attr);
            unfold_qual = (fs.unfold_qual);
            unfold_namespace = (fs.unfold_namespace);
            dont_unfold_attr = (fs.dont_unfold_attr);
            pure_subterms_within_computations =
              (fs.pure_subterms_within_computations);
            simplify = (fs.simplify);
            erase_universes = (fs.erase_universes);
            allow_unbound_universes = (fs.allow_unbound_universes);
            reify_ = (fs.reify_);
            compress_uvars = (fs.compress_uvars);
            no_full_norm = (fs.no_full_norm);
            check_no_uvars = (fs.check_no_uvars);
            unmeta = true;
            unascribe = (fs.unascribe);
            in_full_norm_request = (fs.in_full_norm_request);
            weakly_reduce_scrutinee = (fs.weakly_reduce_scrutinee);
            nbe_step = (fs.nbe_step);
            for_extraction = (fs.for_extraction);
            unrefine = (fs.unrefine);
            default_univs_to_zero = (fs.default_univs_to_zero);
            tactics = (fs.tactics)
          }
      | FStarC_TypeChecker_Env.Unascribe ->
          {
            beta = (fs.beta);
            iota = (fs.iota);
            zeta = (fs.zeta);
            zeta_full = (fs.zeta_full);
            weak = (fs.weak);
            hnf = (fs.hnf);
            primops = (fs.primops);
            do_not_unfold_pure_lets = (fs.do_not_unfold_pure_lets);
            unfold_until = (fs.unfold_until);
            unfold_only = (fs.unfold_only);
            unfold_fully = (fs.unfold_fully);
            unfold_attr = (fs.unfold_attr);
            unfold_qual = (fs.unfold_qual);
            unfold_namespace = (fs.unfold_namespace);
            dont_unfold_attr = (fs.dont_unfold_attr);
            pure_subterms_within_computations =
              (fs.pure_subterms_within_computations);
            simplify = (fs.simplify);
            erase_universes = (fs.erase_universes);
            allow_unbound_universes = (fs.allow_unbound_universes);
            reify_ = (fs.reify_);
            compress_uvars = (fs.compress_uvars);
            no_full_norm = (fs.no_full_norm);
            check_no_uvars = (fs.check_no_uvars);
            unmeta = (fs.unmeta);
            unascribe = true;
            in_full_norm_request = (fs.in_full_norm_request);
            weakly_reduce_scrutinee = (fs.weakly_reduce_scrutinee);
            nbe_step = (fs.nbe_step);
            for_extraction = (fs.for_extraction);
            unrefine = (fs.unrefine);
            default_univs_to_zero = (fs.default_univs_to_zero);
            tactics = (fs.tactics)
          }
      | FStarC_TypeChecker_Env.NBE ->
          {
            beta = (fs.beta);
            iota = (fs.iota);
            zeta = (fs.zeta);
            zeta_full = (fs.zeta_full);
            weak = (fs.weak);
            hnf = (fs.hnf);
            primops = (fs.primops);
            do_not_unfold_pure_lets = (fs.do_not_unfold_pure_lets);
            unfold_until = (fs.unfold_until);
            unfold_only = (fs.unfold_only);
            unfold_fully = (fs.unfold_fully);
            unfold_attr = (fs.unfold_attr);
            unfold_qual = (fs.unfold_qual);
            unfold_namespace = (fs.unfold_namespace);
            dont_unfold_attr = (fs.dont_unfold_attr);
            pure_subterms_within_computations =
              (fs.pure_subterms_within_computations);
            simplify = (fs.simplify);
            erase_universes = (fs.erase_universes);
            allow_unbound_universes = (fs.allow_unbound_universes);
            reify_ = (fs.reify_);
            compress_uvars = (fs.compress_uvars);
            no_full_norm = (fs.no_full_norm);
            check_no_uvars = (fs.check_no_uvars);
            unmeta = (fs.unmeta);
            unascribe = (fs.unascribe);
            in_full_norm_request = (fs.in_full_norm_request);
            weakly_reduce_scrutinee = (fs.weakly_reduce_scrutinee);
            nbe_step = true;
            for_extraction = (fs.for_extraction);
            unrefine = (fs.unrefine);
            default_univs_to_zero = (fs.default_univs_to_zero);
            tactics = (fs.tactics)
          }
      | FStarC_TypeChecker_Env.ForExtraction ->
          {
            beta = (fs.beta);
            iota = (fs.iota);
            zeta = (fs.zeta);
            zeta_full = (fs.zeta_full);
            weak = (fs.weak);
            hnf = (fs.hnf);
            primops = (fs.primops);
            do_not_unfold_pure_lets = (fs.do_not_unfold_pure_lets);
            unfold_until = (fs.unfold_until);
            unfold_only = (fs.unfold_only);
            unfold_fully = (fs.unfold_fully);
            unfold_attr = (fs.unfold_attr);
            unfold_qual = (fs.unfold_qual);
            unfold_namespace = (fs.unfold_namespace);
            dont_unfold_attr = (fs.dont_unfold_attr);
            pure_subterms_within_computations =
              (fs.pure_subterms_within_computations);
            simplify = (fs.simplify);
            erase_universes = (fs.erase_universes);
            allow_unbound_universes = (fs.allow_unbound_universes);
            reify_ = (fs.reify_);
            compress_uvars = (fs.compress_uvars);
            no_full_norm = (fs.no_full_norm);
            check_no_uvars = (fs.check_no_uvars);
            unmeta = (fs.unmeta);
            unascribe = (fs.unascribe);
            in_full_norm_request = (fs.in_full_norm_request);
            weakly_reduce_scrutinee = (fs.weakly_reduce_scrutinee);
            nbe_step = (fs.nbe_step);
            for_extraction = true;
            unrefine = (fs.unrefine);
            default_univs_to_zero = (fs.default_univs_to_zero);
            tactics = (fs.tactics)
          }
      | FStarC_TypeChecker_Env.Unrefine ->
          {
            beta = (fs.beta);
            iota = (fs.iota);
            zeta = (fs.zeta);
            zeta_full = (fs.zeta_full);
            weak = (fs.weak);
            hnf = (fs.hnf);
            primops = (fs.primops);
            do_not_unfold_pure_lets = (fs.do_not_unfold_pure_lets);
            unfold_until = (fs.unfold_until);
            unfold_only = (fs.unfold_only);
            unfold_fully = (fs.unfold_fully);
            unfold_attr = (fs.unfold_attr);
            unfold_qual = (fs.unfold_qual);
            unfold_namespace = (fs.unfold_namespace);
            dont_unfold_attr = (fs.dont_unfold_attr);
            pure_subterms_within_computations =
              (fs.pure_subterms_within_computations);
            simplify = (fs.simplify);
            erase_universes = (fs.erase_universes);
            allow_unbound_universes = (fs.allow_unbound_universes);
            reify_ = (fs.reify_);
            compress_uvars = (fs.compress_uvars);
            no_full_norm = (fs.no_full_norm);
            check_no_uvars = (fs.check_no_uvars);
            unmeta = (fs.unmeta);
            unascribe = (fs.unascribe);
            in_full_norm_request = (fs.in_full_norm_request);
            weakly_reduce_scrutinee = (fs.weakly_reduce_scrutinee);
            nbe_step = (fs.nbe_step);
            for_extraction = (fs.for_extraction);
            unrefine = true;
            default_univs_to_zero = (fs.default_univs_to_zero);
            tactics = (fs.tactics)
          }
      | FStarC_TypeChecker_Env.NormDebug -> fs
      | FStarC_TypeChecker_Env.DefaultUnivsToZero ->
          {
            beta = (fs.beta);
            iota = (fs.iota);
            zeta = (fs.zeta);
            zeta_full = (fs.zeta_full);
            weak = (fs.weak);
            hnf = (fs.hnf);
            primops = (fs.primops);
            do_not_unfold_pure_lets = (fs.do_not_unfold_pure_lets);
            unfold_until = (fs.unfold_until);
            unfold_only = (fs.unfold_only);
            unfold_fully = (fs.unfold_fully);
            unfold_attr = (fs.unfold_attr);
            unfold_qual = (fs.unfold_qual);
            unfold_namespace = (fs.unfold_namespace);
            dont_unfold_attr = (fs.dont_unfold_attr);
            pure_subterms_within_computations =
              (fs.pure_subterms_within_computations);
            simplify = (fs.simplify);
            erase_universes = (fs.erase_universes);
            allow_unbound_universes = (fs.allow_unbound_universes);
            reify_ = (fs.reify_);
            compress_uvars = (fs.compress_uvars);
            no_full_norm = (fs.no_full_norm);
            check_no_uvars = (fs.check_no_uvars);
            unmeta = (fs.unmeta);
            unascribe = (fs.unascribe);
            in_full_norm_request = (fs.in_full_norm_request);
            weakly_reduce_scrutinee = (fs.weakly_reduce_scrutinee);
            nbe_step = (fs.nbe_step);
            for_extraction = (fs.for_extraction);
            unrefine = (fs.unrefine);
            default_univs_to_zero = true;
            tactics = (fs.tactics)
          }
      | FStarC_TypeChecker_Env.Tactics ->
          {
            beta = (fs.beta);
            iota = (fs.iota);
            zeta = (fs.zeta);
            zeta_full = (fs.zeta_full);
            weak = (fs.weak);
            hnf = (fs.hnf);
            primops = (fs.primops);
            do_not_unfold_pure_lets = (fs.do_not_unfold_pure_lets);
            unfold_until = (fs.unfold_until);
            unfold_only = (fs.unfold_only);
            unfold_fully = (fs.unfold_fully);
            unfold_attr = (fs.unfold_attr);
            unfold_qual = (fs.unfold_qual);
            unfold_namespace = (fs.unfold_namespace);
            dont_unfold_attr = (fs.dont_unfold_attr);
            pure_subterms_within_computations =
              (fs.pure_subterms_within_computations);
            simplify = (fs.simplify);
            erase_universes = (fs.erase_universes);
            allow_unbound_universes = (fs.allow_unbound_universes);
            reify_ = (fs.reify_);
            compress_uvars = (fs.compress_uvars);
            no_full_norm = (fs.no_full_norm);
            check_no_uvars = (fs.check_no_uvars);
            unmeta = (fs.unmeta);
            unascribe = (fs.unascribe);
            in_full_norm_request = (fs.in_full_norm_request);
            weakly_reduce_scrutinee = (fs.weakly_reduce_scrutinee);
            nbe_step = (fs.nbe_step);
            for_extraction = (fs.for_extraction);
            unrefine = (fs.unrefine);
            default_univs_to_zero = (fs.default_univs_to_zero);
            tactics = true
          }
let (to_fsteps : FStarC_TypeChecker_Env.step Prims.list -> fsteps) =
  fun s -> FStarC_Compiler_List.fold_right fstep_add_one s default_steps
type debug_switches =
  {
  gen: Prims.bool ;
  top: Prims.bool ;
  cfg: Prims.bool ;
  primop: Prims.bool ;
  unfolding: Prims.bool ;
  b380: Prims.bool ;
  wpe: Prims.bool ;
  norm_delayed: Prims.bool ;
  print_normalized: Prims.bool ;
  debug_nbe: Prims.bool ;
  erase_erasable_args: Prims.bool }
let (__proj__Mkdebug_switches__item__gen : debug_switches -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { gen; top; cfg; primop; unfolding; b380; wpe; norm_delayed;
        print_normalized; debug_nbe; erase_erasable_args;_} -> gen
let (__proj__Mkdebug_switches__item__top : debug_switches -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { gen; top; cfg; primop; unfolding; b380; wpe; norm_delayed;
        print_normalized; debug_nbe; erase_erasable_args;_} -> top
let (__proj__Mkdebug_switches__item__cfg : debug_switches -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { gen; top; cfg; primop; unfolding; b380; wpe; norm_delayed;
        print_normalized; debug_nbe; erase_erasable_args;_} -> cfg
let (__proj__Mkdebug_switches__item__primop : debug_switches -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { gen; top; cfg; primop; unfolding; b380; wpe; norm_delayed;
        print_normalized; debug_nbe; erase_erasable_args;_} -> primop
let (__proj__Mkdebug_switches__item__unfolding :
  debug_switches -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { gen; top; cfg; primop; unfolding; b380; wpe; norm_delayed;
        print_normalized; debug_nbe; erase_erasable_args;_} -> unfolding
let (__proj__Mkdebug_switches__item__b380 : debug_switches -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { gen; top; cfg; primop; unfolding; b380; wpe; norm_delayed;
        print_normalized; debug_nbe; erase_erasable_args;_} -> b380
let (__proj__Mkdebug_switches__item__wpe : debug_switches -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { gen; top; cfg; primop; unfolding; b380; wpe; norm_delayed;
        print_normalized; debug_nbe; erase_erasable_args;_} -> wpe
let (__proj__Mkdebug_switches__item__norm_delayed :
  debug_switches -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { gen; top; cfg; primop; unfolding; b380; wpe; norm_delayed;
        print_normalized; debug_nbe; erase_erasable_args;_} -> norm_delayed
let (__proj__Mkdebug_switches__item__print_normalized :
  debug_switches -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { gen; top; cfg; primop; unfolding; b380; wpe; norm_delayed;
        print_normalized; debug_nbe; erase_erasable_args;_} ->
        print_normalized
let (__proj__Mkdebug_switches__item__debug_nbe :
  debug_switches -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { gen; top; cfg; primop; unfolding; b380; wpe; norm_delayed;
        print_normalized; debug_nbe; erase_erasable_args;_} -> debug_nbe
let (__proj__Mkdebug_switches__item__erase_erasable_args :
  debug_switches -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { gen; top; cfg; primop; unfolding; b380; wpe; norm_delayed;
        print_normalized; debug_nbe; erase_erasable_args;_} ->
        erase_erasable_args
let (no_debug_switches : debug_switches) =
  {
    gen = false;
    top = false;
    cfg = false;
    primop = false;
    unfolding = false;
    b380 = false;
    wpe = false;
    norm_delayed = false;
    print_normalized = false;
    debug_nbe = false;
    erase_erasable_args = false
  }
type cfg =
  {
  steps: fsteps ;
  tcenv: FStarC_TypeChecker_Env.env ;
  debug: debug_switches ;
  delta_level: FStarC_TypeChecker_Env.delta_level Prims.list ;
  primitive_steps:
    FStarC_TypeChecker_Primops_Base.primitive_step FStarC_Compiler_Util.psmap ;
  strong: Prims.bool ;
  memoize_lazy: Prims.bool ;
  normalize_pure_lets: Prims.bool ;
  reifying: Prims.bool ;
  compat_memo_ignore_cfg: Prims.bool }
let (__proj__Mkcfg__item__steps : cfg -> fsteps) =
  fun projectee ->
    match projectee with
    | { steps; tcenv; debug; delta_level; primitive_steps; strong;
        memoize_lazy; normalize_pure_lets; reifying;
        compat_memo_ignore_cfg;_} -> steps
let (__proj__Mkcfg__item__tcenv : cfg -> FStarC_TypeChecker_Env.env) =
  fun projectee ->
    match projectee with
    | { steps; tcenv; debug; delta_level; primitive_steps; strong;
        memoize_lazy; normalize_pure_lets; reifying;
        compat_memo_ignore_cfg;_} -> tcenv
let (__proj__Mkcfg__item__debug : cfg -> debug_switches) =
  fun projectee ->
    match projectee with
    | { steps; tcenv; debug; delta_level; primitive_steps; strong;
        memoize_lazy; normalize_pure_lets; reifying;
        compat_memo_ignore_cfg;_} -> debug
let (__proj__Mkcfg__item__delta_level :
  cfg -> FStarC_TypeChecker_Env.delta_level Prims.list) =
  fun projectee ->
    match projectee with
    | { steps; tcenv; debug; delta_level; primitive_steps; strong;
        memoize_lazy; normalize_pure_lets; reifying;
        compat_memo_ignore_cfg;_} -> delta_level
let (__proj__Mkcfg__item__primitive_steps :
  cfg ->
    FStarC_TypeChecker_Primops_Base.primitive_step FStarC_Compiler_Util.psmap)
  =
  fun projectee ->
    match projectee with
    | { steps; tcenv; debug; delta_level; primitive_steps; strong;
        memoize_lazy; normalize_pure_lets; reifying;
        compat_memo_ignore_cfg;_} -> primitive_steps
let (__proj__Mkcfg__item__strong : cfg -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { steps; tcenv; debug; delta_level; primitive_steps; strong;
        memoize_lazy; normalize_pure_lets; reifying;
        compat_memo_ignore_cfg;_} -> strong
let (__proj__Mkcfg__item__memoize_lazy : cfg -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { steps; tcenv; debug; delta_level; primitive_steps; strong;
        memoize_lazy; normalize_pure_lets; reifying;
        compat_memo_ignore_cfg;_} -> memoize_lazy
let (__proj__Mkcfg__item__normalize_pure_lets : cfg -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { steps; tcenv; debug; delta_level; primitive_steps; strong;
        memoize_lazy; normalize_pure_lets; reifying;
        compat_memo_ignore_cfg;_} -> normalize_pure_lets
let (__proj__Mkcfg__item__reifying : cfg -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { steps; tcenv; debug; delta_level; primitive_steps; strong;
        memoize_lazy; normalize_pure_lets; reifying;
        compat_memo_ignore_cfg;_} -> reifying
let (__proj__Mkcfg__item__compat_memo_ignore_cfg : cfg -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { steps; tcenv; debug; delta_level; primitive_steps; strong;
        memoize_lazy; normalize_pure_lets; reifying;
        compat_memo_ignore_cfg;_} -> compat_memo_ignore_cfg
type prim_step_set =
  FStarC_TypeChecker_Primops_Base.primitive_step FStarC_Compiler_Util.psmap
let (empty_prim_steps : unit -> prim_step_set) =
  fun uu___ -> FStarC_Compiler_Util.psmap_empty ()
let (add_step :
  FStarC_TypeChecker_Primops_Base.primitive_step ->
    prim_step_set ->
      FStarC_TypeChecker_Primops_Base.primitive_step
        FStarC_Compiler_Util.psmap)
  =
  fun s ->
    fun ss ->
      let uu___ =
        FStarC_Ident.string_of_lid s.FStarC_TypeChecker_Primops_Base.name in
      FStarC_Compiler_Util.psmap_add ss uu___ s
let (merge_steps : prim_step_set -> prim_step_set -> prim_step_set) =
  fun s1 -> fun s2 -> FStarC_Compiler_Util.psmap_merge s1 s2
let (add_steps :
  prim_step_set ->
    FStarC_TypeChecker_Primops_Base.primitive_step Prims.list ->
      prim_step_set)
  = fun m -> fun l -> FStarC_Compiler_List.fold_right add_step l m
let (prim_from_list :
  FStarC_TypeChecker_Primops_Base.primitive_step Prims.list -> prim_step_set)
  = fun l -> let uu___ = empty_prim_steps () in add_steps uu___ l
let (built_in_primitive_steps :
  FStarC_TypeChecker_Primops_Base.primitive_step FStarC_Compiler_Util.psmap)
  = prim_from_list FStarC_TypeChecker_Primops.built_in_primitive_steps_list
let (env_dependent_ops : FStarC_TypeChecker_Env.env_t -> prim_step_set) =
  fun env ->
    let uu___ = FStarC_TypeChecker_Primops.env_dependent_ops env in
    prim_from_list uu___
let (simplification_steps :
  FStarC_TypeChecker_Env.env_t ->
    FStarC_TypeChecker_Primops_Base.primitive_step FStarC_Compiler_Util.psmap)
  =
  fun env ->
    let uu___ = FStarC_TypeChecker_Primops.simplification_ops_list env in
    prim_from_list uu___
let (showable_cfg : cfg FStarC_Class_Show.showable) =
  {
    FStarC_Class_Show.show =
      (fun cfg1 ->
         let uu___ =
           let uu___1 =
             let uu___2 =
               let uu___3 = steps_to_string cfg1.steps in
               FStarC_Compiler_Util.format1 "  steps = %s;" uu___3 in
             let uu___3 =
               let uu___4 =
                 let uu___5 =
                   FStarC_Class_Show.show
                     (FStarC_Class_Show.show_list
                        FStarC_TypeChecker_Env.showable_delta_level)
                     cfg1.delta_level in
                 FStarC_Compiler_Util.format1 "  delta_level = %s;" uu___5 in
               [uu___4; "}"] in
             uu___2 :: uu___3 in
           "{" :: uu___1 in
         FStarC_Compiler_String.concat "\n" uu___)
  }
let (cfg_env : cfg -> FStarC_TypeChecker_Env.env) = fun cfg1 -> cfg1.tcenv
let (find_prim_step :
  cfg ->
    FStarC_Syntax_Syntax.fv ->
      FStarC_TypeChecker_Primops_Base.primitive_step
        FStar_Pervasives_Native.option)
  =
  fun cfg1 ->
    fun fv ->
      let uu___ =
        FStarC_Ident.string_of_lid
          (fv.FStarC_Syntax_Syntax.fv_name).FStarC_Syntax_Syntax.v in
      FStarC_Compiler_Util.psmap_try_find cfg1.primitive_steps uu___
let (is_prim_step : cfg -> FStarC_Syntax_Syntax.fv -> Prims.bool) =
  fun cfg1 ->
    fun fv ->
      let uu___ =
        let uu___1 =
          FStarC_Ident.string_of_lid
            (fv.FStarC_Syntax_Syntax.fv_name).FStarC_Syntax_Syntax.v in
        FStarC_Compiler_Util.psmap_try_find cfg1.primitive_steps uu___1 in
      FStarC_Compiler_Util.is_some uu___
let (log : cfg -> (unit -> unit) -> unit) =
  fun cfg1 -> fun f -> if (cfg1.debug).gen then f () else ()
let (log_top : cfg -> (unit -> unit) -> unit) =
  fun cfg1 -> fun f -> if (cfg1.debug).top then f () else ()
let (log_cfg : cfg -> (unit -> unit) -> unit) =
  fun cfg1 -> fun f -> if (cfg1.debug).cfg then f () else ()
let (log_primops : cfg -> (unit -> unit) -> unit) =
  fun cfg1 -> fun f -> if (cfg1.debug).primop then f () else ()
let (dbg_unfolding : Prims.bool FStarC_Compiler_Effect.ref) =
  FStarC_Compiler_Debug.get_toggle "Unfolding"
let (log_unfolding : cfg -> (unit -> unit) -> unit) =
  fun cfg1 ->
    fun f ->
      let uu___ = FStarC_Compiler_Effect.op_Bang dbg_unfolding in
      if uu___ then f () else ()
let (log_nbe : cfg -> (unit -> unit) -> unit) =
  fun cfg1 -> fun f -> if (cfg1.debug).debug_nbe then f () else ()
let (primop_time_map : Prims.int FStarC_Compiler_Util.smap) =
  FStarC_Compiler_Util.smap_create (Prims.of_int (50))
let (primop_time_reset : unit -> unit) =
  fun uu___ -> FStarC_Compiler_Util.smap_clear primop_time_map
let (primop_time_count : Prims.string -> Prims.int -> unit) =
  fun nm ->
    fun ms ->
      let uu___ = FStarC_Compiler_Util.smap_try_find primop_time_map nm in
      match uu___ with
      | FStar_Pervasives_Native.None ->
          FStarC_Compiler_Util.smap_add primop_time_map nm ms
      | FStar_Pervasives_Native.Some ms0 ->
          FStarC_Compiler_Util.smap_add primop_time_map nm (ms0 + ms)
let (fixto : Prims.int -> Prims.string -> Prims.string) =
  fun n ->
    fun s ->
      if (FStarC_Compiler_String.length s) < n
      then
        let uu___ =
          FStarC_Compiler_String.make (n - (FStarC_Compiler_String.length s))
            32 in
        FStarC_Compiler_String.op_Hat uu___ s
      else s
let (primop_time_report : unit -> Prims.string) =
  fun uu___ ->
    let pairs =
      FStarC_Compiler_Util.smap_fold primop_time_map
        (fun nm -> fun ms -> fun rest -> (nm, ms) :: rest) [] in
    let pairs1 =
      FStarC_Compiler_Util.sort_with
        (fun uu___1 ->
           fun uu___2 ->
             match (uu___1, uu___2) with
             | ((uu___3, t1), (uu___4, t2)) -> t1 - t2) pairs in
    FStarC_Compiler_List.fold_right
      (fun uu___1 ->
         fun rest ->
           match uu___1 with
           | (nm, ms) ->
               let uu___2 =
                 let uu___3 =
                   let uu___4 = FStarC_Compiler_Util.string_of_int ms in
                   fixto (Prims.of_int (10)) uu___4 in
                 FStarC_Compiler_Util.format2 "%sms --- %s\n" uu___3 nm in
               FStarC_Compiler_String.op_Hat uu___2 rest) pairs1 ""
let (extendable_primops_dirty : Prims.bool FStarC_Compiler_Effect.ref) =
  FStarC_Compiler_Util.mk_ref true
type register_prim_step_t =
  FStarC_TypeChecker_Primops_Base.primitive_step -> unit
type retrieve_prim_step_t = unit -> prim_step_set
let (mk_extendable_primop_set :
  unit -> (register_prim_step_t * retrieve_prim_step_t)) =
  fun uu___ ->
    let steps =
      let uu___1 = empty_prim_steps () in FStarC_Compiler_Util.mk_ref uu___1 in
    let register p =
      FStarC_Compiler_Effect.op_Colon_Equals extendable_primops_dirty true;
      (let uu___2 =
         let uu___3 = FStarC_Compiler_Effect.op_Bang steps in
         add_step p uu___3 in
       FStarC_Compiler_Effect.op_Colon_Equals steps uu___2) in
    let retrieve uu___1 = FStarC_Compiler_Effect.op_Bang steps in
    (register, retrieve)
let (plugins : (register_prim_step_t * retrieve_prim_step_t)) =
  mk_extendable_primop_set ()
let (extra_steps : (register_prim_step_t * retrieve_prim_step_t)) =
  mk_extendable_primop_set ()
let (register_plugin :
  FStarC_TypeChecker_Primops_Base.primitive_step -> unit) =
  fun p -> FStar_Pervasives_Native.fst plugins p
let (retrieve_plugins : unit -> prim_step_set) =
  fun uu___ ->
    let uu___1 = FStarC_Options.no_plugins () in
    if uu___1
    then empty_prim_steps ()
    else FStar_Pervasives_Native.snd plugins ()
let (register_extra_step :
  FStarC_TypeChecker_Primops_Base.primitive_step -> unit) =
  fun p -> FStar_Pervasives_Native.fst extra_steps p
let (retrieve_extra_steps : unit -> prim_step_set) =
  fun uu___ -> FStar_Pervasives_Native.snd extra_steps ()
let (list_plugins :
  unit -> FStarC_TypeChecker_Primops_Base.primitive_step Prims.list) =
  fun uu___ ->
    let uu___1 = retrieve_plugins () in FStarC_Common.psmap_values uu___1
let (list_extra_steps :
  unit -> FStarC_TypeChecker_Primops_Base.primitive_step Prims.list) =
  fun uu___ ->
    let uu___1 = retrieve_extra_steps () in FStarC_Common.psmap_values uu___1
let (cached_steps : unit -> prim_step_set) =
  let memo =
    let uu___ = empty_prim_steps () in FStarC_Compiler_Util.mk_ref uu___ in
  fun uu___ ->
    let uu___1 = FStarC_Compiler_Effect.op_Bang extendable_primops_dirty in
    if uu___1
    then
      let steps =
        let uu___2 =
          let uu___3 = retrieve_plugins () in
          let uu___4 = retrieve_extra_steps () in merge_steps uu___3 uu___4 in
        merge_steps built_in_primitive_steps uu___2 in
      (FStarC_Compiler_Effect.op_Colon_Equals memo steps;
       FStarC_Compiler_Effect.op_Colon_Equals extendable_primops_dirty false;
       steps)
    else FStarC_Compiler_Effect.op_Bang memo
let (add_nbe : fsteps -> fsteps) =
  fun s ->
    let uu___ = FStarC_Options.use_nbe () in
    if uu___
    then
      {
        beta = (s.beta);
        iota = (s.iota);
        zeta = (s.zeta);
        zeta_full = (s.zeta_full);
        weak = (s.weak);
        hnf = (s.hnf);
        primops = (s.primops);
        do_not_unfold_pure_lets = (s.do_not_unfold_pure_lets);
        unfold_until = (s.unfold_until);
        unfold_only = (s.unfold_only);
        unfold_fully = (s.unfold_fully);
        unfold_attr = (s.unfold_attr);
        unfold_qual = (s.unfold_qual);
        unfold_namespace = (s.unfold_namespace);
        dont_unfold_attr = (s.dont_unfold_attr);
        pure_subterms_within_computations =
          (s.pure_subterms_within_computations);
        simplify = (s.simplify);
        erase_universes = (s.erase_universes);
        allow_unbound_universes = (s.allow_unbound_universes);
        reify_ = (s.reify_);
        compress_uvars = (s.compress_uvars);
        no_full_norm = (s.no_full_norm);
        check_no_uvars = (s.check_no_uvars);
        unmeta = (s.unmeta);
        unascribe = (s.unascribe);
        in_full_norm_request = (s.in_full_norm_request);
        weakly_reduce_scrutinee = (s.weakly_reduce_scrutinee);
        nbe_step = true;
        for_extraction = (s.for_extraction);
        unrefine = (s.unrefine);
        default_univs_to_zero = (s.default_univs_to_zero);
        tactics = (s.tactics)
      }
    else s
let (dbg_Norm : Prims.bool FStarC_Compiler_Effect.ref) =
  FStarC_Compiler_Debug.get_toggle "Norm"
let (dbg_NormTop : Prims.bool FStarC_Compiler_Effect.ref) =
  FStarC_Compiler_Debug.get_toggle "NormTop"
let (dbg_NormCfg : Prims.bool FStarC_Compiler_Effect.ref) =
  FStarC_Compiler_Debug.get_toggle "NormCfg"
let (dbg_Primops : Prims.bool FStarC_Compiler_Effect.ref) =
  FStarC_Compiler_Debug.get_toggle "Primops"
let (dbg_Unfolding : Prims.bool FStarC_Compiler_Effect.ref) =
  FStarC_Compiler_Debug.get_toggle "Unfolding"
let (dbg_380 : Prims.bool FStarC_Compiler_Effect.ref) =
  FStarC_Compiler_Debug.get_toggle "380"
let (dbg_WPE : Prims.bool FStarC_Compiler_Effect.ref) =
  FStarC_Compiler_Debug.get_toggle "WPE"
let (dbg_NormDelayed : Prims.bool FStarC_Compiler_Effect.ref) =
  FStarC_Compiler_Debug.get_toggle "NormDelayed"
let (dbg_print_normalized : Prims.bool FStarC_Compiler_Effect.ref) =
  FStarC_Compiler_Debug.get_toggle "print_normalized_terms"
let (dbg_NBE : Prims.bool FStarC_Compiler_Effect.ref) =
  FStarC_Compiler_Debug.get_toggle "NBE"
let (dbg_UNSOUND_EraseErasableArgs : Prims.bool FStarC_Compiler_Effect.ref) =
  FStarC_Compiler_Debug.get_toggle "UNSOUND_EraseErasableArgs"
let (config' :
  FStarC_TypeChecker_Primops_Base.primitive_step Prims.list ->
    FStarC_TypeChecker_Env.step Prims.list ->
      FStarC_TypeChecker_Env.env -> cfg)
  =
  fun psteps ->
    fun s ->
      fun e ->
        let d =
          let uu___ =
            FStarC_Compiler_List.collect
              (fun uu___1 ->
                 match uu___1 with
                 | FStarC_TypeChecker_Env.UnfoldUntil k ->
                     [FStarC_TypeChecker_Env.Unfold k]
                 | FStarC_TypeChecker_Env.Eager_unfolding ->
                     [FStarC_TypeChecker_Env.Eager_unfolding_only]
                 | FStarC_TypeChecker_Env.UnfoldQual l when
                     FStarC_Compiler_List.contains "unfold" l ->
                     [FStarC_TypeChecker_Env.Eager_unfolding_only]
                 | FStarC_TypeChecker_Env.Inlining ->
                     [FStarC_TypeChecker_Env.InliningDelta]
                 | FStarC_TypeChecker_Env.UnfoldQual l when
                     FStarC_Compiler_List.contains "inline_for_extraction" l
                     -> [FStarC_TypeChecker_Env.InliningDelta]
                 | uu___2 -> []) s in
          FStarC_Compiler_List.unique uu___ in
        let d1 =
          match d with | [] -> [FStarC_TypeChecker_Env.NoDelta] | uu___ -> d in
        let steps = let uu___ = to_fsteps s in add_nbe uu___ in
        let psteps1 =
          let uu___ =
            let uu___1 = env_dependent_ops e in
            let uu___2 = cached_steps () in merge_steps uu___1 uu___2 in
          add_steps uu___ psteps in
        let dbg_flag =
          FStarC_Compiler_List.contains FStarC_TypeChecker_Env.NormDebug s in
        let uu___ =
          let uu___1 = (FStarC_Compiler_Effect.op_Bang dbg_Norm) || dbg_flag in
          let uu___2 =
            (FStarC_Compiler_Effect.op_Bang dbg_NormTop) || dbg_flag in
          let uu___3 = FStarC_Compiler_Effect.op_Bang dbg_NormCfg in
          let uu___4 = FStarC_Compiler_Effect.op_Bang dbg_Primops in
          let uu___5 = FStarC_Compiler_Effect.op_Bang dbg_Unfolding in
          let uu___6 = FStarC_Compiler_Effect.op_Bang dbg_380 in
          let uu___7 = FStarC_Compiler_Effect.op_Bang dbg_WPE in
          let uu___8 = FStarC_Compiler_Effect.op_Bang dbg_NormDelayed in
          let uu___9 = FStarC_Compiler_Effect.op_Bang dbg_print_normalized in
          let uu___10 = FStarC_Compiler_Effect.op_Bang dbg_NBE in
          let uu___11 =
            (let uu___13 =
               FStarC_Compiler_Effect.op_Bang dbg_UNSOUND_EraseErasableArgs in
             if uu___13
             then
               FStarC_Errors.log_issue FStarC_TypeChecker_Env.hasRange_env e
                 FStarC_Errors_Codes.Warning_WarnOnUse ()
                 (Obj.magic FStarC_Errors_Msg.is_error_message_string)
                 (Obj.magic
                    "The 'UNSOUND_EraseErasableArgs' setting is for debugging only; it is not sound")
             else ());
            FStarC_Compiler_Effect.op_Bang dbg_UNSOUND_EraseErasableArgs in
          {
            gen = uu___1;
            top = uu___2;
            cfg = uu___3;
            primop = uu___4;
            unfolding = uu___5;
            b380 = uu___6;
            wpe = uu___7;
            norm_delayed = uu___8;
            print_normalized = uu___9;
            debug_nbe = uu___10;
            erase_erasable_args = uu___11
          } in
        let uu___1 =
          (Prims.op_Negation steps.pure_subterms_within_computations) ||
            (FStarC_Options.normalize_pure_terms_for_extraction ()) in
        let uu___2 =
          let uu___3 =
            FStarC_Options_Ext.get "compat:normalizer_memo_ignore_cfg" in
          uu___3 <> "" in
        {
          steps;
          tcenv = e;
          debug = uu___;
          delta_level = d1;
          primitive_steps = psteps1;
          strong = false;
          memoize_lazy = true;
          normalize_pure_lets = uu___1;
          reifying = false;
          compat_memo_ignore_cfg = uu___2
        }
let (config :
  FStarC_TypeChecker_Env.step Prims.list -> FStarC_TypeChecker_Env.env -> cfg)
  = fun s -> fun e -> config' [] s e
let (should_reduce_local_let :
  cfg -> FStarC_Syntax_Syntax.letbinding -> Prims.bool) =
  fun cfg1 ->
    fun lb ->
      if (cfg1.steps).do_not_unfold_pure_lets
      then false
      else
        (let uu___1 =
           (cfg1.steps).pure_subterms_within_computations &&
             (FStarC_Syntax_Util.has_attribute
                lb.FStarC_Syntax_Syntax.lbattrs
                FStarC_Parser_Const.inline_let_attr) in
         if uu___1
         then true
         else
           (let n =
              FStarC_TypeChecker_Env.norm_eff_name cfg1.tcenv
                lb.FStarC_Syntax_Syntax.lbeff in
            let uu___3 =
              (FStarC_Syntax_Util.is_pure_effect n) &&
                (cfg1.normalize_pure_lets ||
                   (FStarC_Syntax_Util.has_attribute
                      lb.FStarC_Syntax_Syntax.lbattrs
                      FStarC_Parser_Const.inline_let_attr)) in
            if uu___3
            then true
            else
              (FStarC_Syntax_Util.is_ghost_effect n) &&
                (Prims.op_Negation
                   (cfg1.steps).pure_subterms_within_computations)))
let (translate_norm_step :
  FStar_Pervasives.norm_step -> FStarC_TypeChecker_Env.step Prims.list) =
  fun uu___ ->
    match uu___ with
    | FStar_Pervasives.Zeta -> [FStarC_TypeChecker_Env.Zeta]
    | FStar_Pervasives.ZetaFull -> [FStarC_TypeChecker_Env.ZetaFull]
    | FStar_Pervasives.Iota -> [FStarC_TypeChecker_Env.Iota]
    | FStar_Pervasives.Delta ->
        [FStarC_TypeChecker_Env.UnfoldUntil
           FStarC_Syntax_Syntax.delta_constant]
    | FStar_Pervasives.Simpl -> [FStarC_TypeChecker_Env.Simplify]
    | FStar_Pervasives.Weak -> [FStarC_TypeChecker_Env.Weak]
    | FStar_Pervasives.HNF -> [FStarC_TypeChecker_Env.HNF]
    | FStar_Pervasives.Primops -> [FStarC_TypeChecker_Env.Primops]
    | FStar_Pervasives.Reify -> [FStarC_TypeChecker_Env.Reify]
    | FStar_Pervasives.NormDebug -> [FStarC_TypeChecker_Env.NormDebug]
    | FStar_Pervasives.UnfoldOnly names ->
        let uu___1 =
          let uu___2 =
            let uu___3 =
              FStarC_Compiler_List.map FStarC_Ident.lid_of_str names in
            FStarC_TypeChecker_Env.UnfoldOnly uu___3 in
          [uu___2] in
        (FStarC_TypeChecker_Env.UnfoldUntil
           FStarC_Syntax_Syntax.delta_constant)
          :: uu___1
    | FStar_Pervasives.UnfoldFully names ->
        let uu___1 =
          let uu___2 =
            let uu___3 =
              FStarC_Compiler_List.map FStarC_Ident.lid_of_str names in
            FStarC_TypeChecker_Env.UnfoldFully uu___3 in
          [uu___2] in
        (FStarC_TypeChecker_Env.UnfoldUntil
           FStarC_Syntax_Syntax.delta_constant)
          :: uu___1
    | FStar_Pervasives.UnfoldAttr names ->
        let uu___1 =
          let uu___2 =
            let uu___3 =
              FStarC_Compiler_List.map FStarC_Ident.lid_of_str names in
            FStarC_TypeChecker_Env.UnfoldAttr uu___3 in
          [uu___2] in
        (FStarC_TypeChecker_Env.UnfoldUntil
           FStarC_Syntax_Syntax.delta_constant)
          :: uu___1
    | FStar_Pervasives.UnfoldQual names ->
        [FStarC_TypeChecker_Env.UnfoldUntil
           FStarC_Syntax_Syntax.delta_constant;
        FStarC_TypeChecker_Env.UnfoldQual names]
    | FStar_Pervasives.UnfoldNamespace names ->
        [FStarC_TypeChecker_Env.UnfoldUntil
           FStarC_Syntax_Syntax.delta_constant;
        FStarC_TypeChecker_Env.UnfoldNamespace names]
    | FStar_Pervasives.Unascribe -> [FStarC_TypeChecker_Env.Unascribe]
    | FStar_Pervasives.NBE -> [FStarC_TypeChecker_Env.NBE]
    | FStar_Pervasives.Unmeta -> [FStarC_TypeChecker_Env.Unmeta]
let (translate_norm_steps :
  FStar_Pervasives.norm_step Prims.list ->
    FStarC_TypeChecker_Env.step Prims.list)
  =
  fun s ->
    let s1 = FStarC_Compiler_List.concatMap translate_norm_step s in
    let add_exclude s2 z =
      let uu___ =
        FStarC_Compiler_Util.for_some
          (FStarC_Class_Deq.op_Equals_Question
             FStarC_TypeChecker_Env.deq_step z) s2 in
      if uu___ then s2 else (FStarC_TypeChecker_Env.Exclude z) :: s2 in
    let s2 = FStarC_TypeChecker_Env.Beta :: s1 in
    let s3 = add_exclude s2 FStarC_TypeChecker_Env.Zeta in
    let s4 = add_exclude s3 FStarC_TypeChecker_Env.Iota in s4