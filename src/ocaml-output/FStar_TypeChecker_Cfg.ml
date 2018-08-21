open Prims
type fsteps =
  {
  beta: Prims.bool ;
  iota: Prims.bool ;
  zeta: Prims.bool ;
  weak: Prims.bool ;
  hnf: Prims.bool ;
  primops: Prims.bool ;
  do_not_unfold_pure_lets: Prims.bool ;
  unfold_until:
    FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option ;
  unfold_only: FStar_Ident.lid Prims.list FStar_Pervasives_Native.option ;
  unfold_fully: FStar_Ident.lid Prims.list FStar_Pervasives_Native.option ;
  unfold_attr: FStar_Ident.lid Prims.list FStar_Pervasives_Native.option ;
  unfold_tac: Prims.bool ;
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
  nbe_step: Prims.bool }
let (__proj__Mkfsteps__item__beta : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        do_not_unfold_pure_lets = __fname__do_not_unfold_pure_lets;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_fully = __fname__unfold_fully;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;
        in_full_norm_request = __fname__in_full_norm_request;
        weakly_reduce_scrutinee = __fname__weakly_reduce_scrutinee;
        nbe_step = __fname__nbe_step;_} -> __fname__beta
  
let (__proj__Mkfsteps__item__iota : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        do_not_unfold_pure_lets = __fname__do_not_unfold_pure_lets;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_fully = __fname__unfold_fully;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;
        in_full_norm_request = __fname__in_full_norm_request;
        weakly_reduce_scrutinee = __fname__weakly_reduce_scrutinee;
        nbe_step = __fname__nbe_step;_} -> __fname__iota
  
let (__proj__Mkfsteps__item__zeta : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        do_not_unfold_pure_lets = __fname__do_not_unfold_pure_lets;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_fully = __fname__unfold_fully;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;
        in_full_norm_request = __fname__in_full_norm_request;
        weakly_reduce_scrutinee = __fname__weakly_reduce_scrutinee;
        nbe_step = __fname__nbe_step;_} -> __fname__zeta
  
let (__proj__Mkfsteps__item__weak : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        do_not_unfold_pure_lets = __fname__do_not_unfold_pure_lets;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_fully = __fname__unfold_fully;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;
        in_full_norm_request = __fname__in_full_norm_request;
        weakly_reduce_scrutinee = __fname__weakly_reduce_scrutinee;
        nbe_step = __fname__nbe_step;_} -> __fname__weak
  
let (__proj__Mkfsteps__item__hnf : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        do_not_unfold_pure_lets = __fname__do_not_unfold_pure_lets;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_fully = __fname__unfold_fully;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;
        in_full_norm_request = __fname__in_full_norm_request;
        weakly_reduce_scrutinee = __fname__weakly_reduce_scrutinee;
        nbe_step = __fname__nbe_step;_} -> __fname__hnf
  
let (__proj__Mkfsteps__item__primops : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        do_not_unfold_pure_lets = __fname__do_not_unfold_pure_lets;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_fully = __fname__unfold_fully;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;
        in_full_norm_request = __fname__in_full_norm_request;
        weakly_reduce_scrutinee = __fname__weakly_reduce_scrutinee;
        nbe_step = __fname__nbe_step;_} -> __fname__primops
  
let (__proj__Mkfsteps__item__do_not_unfold_pure_lets : fsteps -> Prims.bool)
  =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        do_not_unfold_pure_lets = __fname__do_not_unfold_pure_lets;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_fully = __fname__unfold_fully;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;
        in_full_norm_request = __fname__in_full_norm_request;
        weakly_reduce_scrutinee = __fname__weakly_reduce_scrutinee;
        nbe_step = __fname__nbe_step;_} -> __fname__do_not_unfold_pure_lets
  
let (__proj__Mkfsteps__item__unfold_until :
  fsteps -> FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option) =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        do_not_unfold_pure_lets = __fname__do_not_unfold_pure_lets;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_fully = __fname__unfold_fully;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;
        in_full_norm_request = __fname__in_full_norm_request;
        weakly_reduce_scrutinee = __fname__weakly_reduce_scrutinee;
        nbe_step = __fname__nbe_step;_} -> __fname__unfold_until
  
let (__proj__Mkfsteps__item__unfold_only :
  fsteps -> FStar_Ident.lid Prims.list FStar_Pervasives_Native.option) =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        do_not_unfold_pure_lets = __fname__do_not_unfold_pure_lets;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_fully = __fname__unfold_fully;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;
        in_full_norm_request = __fname__in_full_norm_request;
        weakly_reduce_scrutinee = __fname__weakly_reduce_scrutinee;
        nbe_step = __fname__nbe_step;_} -> __fname__unfold_only
  
let (__proj__Mkfsteps__item__unfold_fully :
  fsteps -> FStar_Ident.lid Prims.list FStar_Pervasives_Native.option) =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        do_not_unfold_pure_lets = __fname__do_not_unfold_pure_lets;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_fully = __fname__unfold_fully;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;
        in_full_norm_request = __fname__in_full_norm_request;
        weakly_reduce_scrutinee = __fname__weakly_reduce_scrutinee;
        nbe_step = __fname__nbe_step;_} -> __fname__unfold_fully
  
let (__proj__Mkfsteps__item__unfold_attr :
  fsteps -> FStar_Ident.lid Prims.list FStar_Pervasives_Native.option) =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        do_not_unfold_pure_lets = __fname__do_not_unfold_pure_lets;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_fully = __fname__unfold_fully;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;
        in_full_norm_request = __fname__in_full_norm_request;
        weakly_reduce_scrutinee = __fname__weakly_reduce_scrutinee;
        nbe_step = __fname__nbe_step;_} -> __fname__unfold_attr
  
let (__proj__Mkfsteps__item__unfold_tac : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        do_not_unfold_pure_lets = __fname__do_not_unfold_pure_lets;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_fully = __fname__unfold_fully;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;
        in_full_norm_request = __fname__in_full_norm_request;
        weakly_reduce_scrutinee = __fname__weakly_reduce_scrutinee;
        nbe_step = __fname__nbe_step;_} -> __fname__unfold_tac
  
let (__proj__Mkfsteps__item__pure_subterms_within_computations :
  fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        do_not_unfold_pure_lets = __fname__do_not_unfold_pure_lets;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_fully = __fname__unfold_fully;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;
        in_full_norm_request = __fname__in_full_norm_request;
        weakly_reduce_scrutinee = __fname__weakly_reduce_scrutinee;
        nbe_step = __fname__nbe_step;_} ->
        __fname__pure_subterms_within_computations
  
let (__proj__Mkfsteps__item__simplify : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        do_not_unfold_pure_lets = __fname__do_not_unfold_pure_lets;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_fully = __fname__unfold_fully;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;
        in_full_norm_request = __fname__in_full_norm_request;
        weakly_reduce_scrutinee = __fname__weakly_reduce_scrutinee;
        nbe_step = __fname__nbe_step;_} -> __fname__simplify
  
let (__proj__Mkfsteps__item__erase_universes : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        do_not_unfold_pure_lets = __fname__do_not_unfold_pure_lets;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_fully = __fname__unfold_fully;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;
        in_full_norm_request = __fname__in_full_norm_request;
        weakly_reduce_scrutinee = __fname__weakly_reduce_scrutinee;
        nbe_step = __fname__nbe_step;_} -> __fname__erase_universes
  
let (__proj__Mkfsteps__item__allow_unbound_universes : fsteps -> Prims.bool)
  =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        do_not_unfold_pure_lets = __fname__do_not_unfold_pure_lets;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_fully = __fname__unfold_fully;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;
        in_full_norm_request = __fname__in_full_norm_request;
        weakly_reduce_scrutinee = __fname__weakly_reduce_scrutinee;
        nbe_step = __fname__nbe_step;_} -> __fname__allow_unbound_universes
  
let (__proj__Mkfsteps__item__reify_ : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        do_not_unfold_pure_lets = __fname__do_not_unfold_pure_lets;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_fully = __fname__unfold_fully;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;
        in_full_norm_request = __fname__in_full_norm_request;
        weakly_reduce_scrutinee = __fname__weakly_reduce_scrutinee;
        nbe_step = __fname__nbe_step;_} -> __fname__reify_
  
let (__proj__Mkfsteps__item__compress_uvars : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        do_not_unfold_pure_lets = __fname__do_not_unfold_pure_lets;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_fully = __fname__unfold_fully;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;
        in_full_norm_request = __fname__in_full_norm_request;
        weakly_reduce_scrutinee = __fname__weakly_reduce_scrutinee;
        nbe_step = __fname__nbe_step;_} -> __fname__compress_uvars
  
let (__proj__Mkfsteps__item__no_full_norm : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        do_not_unfold_pure_lets = __fname__do_not_unfold_pure_lets;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_fully = __fname__unfold_fully;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;
        in_full_norm_request = __fname__in_full_norm_request;
        weakly_reduce_scrutinee = __fname__weakly_reduce_scrutinee;
        nbe_step = __fname__nbe_step;_} -> __fname__no_full_norm
  
let (__proj__Mkfsteps__item__check_no_uvars : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        do_not_unfold_pure_lets = __fname__do_not_unfold_pure_lets;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_fully = __fname__unfold_fully;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;
        in_full_norm_request = __fname__in_full_norm_request;
        weakly_reduce_scrutinee = __fname__weakly_reduce_scrutinee;
        nbe_step = __fname__nbe_step;_} -> __fname__check_no_uvars
  
let (__proj__Mkfsteps__item__unmeta : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        do_not_unfold_pure_lets = __fname__do_not_unfold_pure_lets;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_fully = __fname__unfold_fully;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;
        in_full_norm_request = __fname__in_full_norm_request;
        weakly_reduce_scrutinee = __fname__weakly_reduce_scrutinee;
        nbe_step = __fname__nbe_step;_} -> __fname__unmeta
  
let (__proj__Mkfsteps__item__unascribe : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        do_not_unfold_pure_lets = __fname__do_not_unfold_pure_lets;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_fully = __fname__unfold_fully;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;
        in_full_norm_request = __fname__in_full_norm_request;
        weakly_reduce_scrutinee = __fname__weakly_reduce_scrutinee;
        nbe_step = __fname__nbe_step;_} -> __fname__unascribe
  
let (__proj__Mkfsteps__item__in_full_norm_request : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        do_not_unfold_pure_lets = __fname__do_not_unfold_pure_lets;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_fully = __fname__unfold_fully;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;
        in_full_norm_request = __fname__in_full_norm_request;
        weakly_reduce_scrutinee = __fname__weakly_reduce_scrutinee;
        nbe_step = __fname__nbe_step;_} -> __fname__in_full_norm_request
  
let (__proj__Mkfsteps__item__weakly_reduce_scrutinee : fsteps -> Prims.bool)
  =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        do_not_unfold_pure_lets = __fname__do_not_unfold_pure_lets;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_fully = __fname__unfold_fully;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;
        in_full_norm_request = __fname__in_full_norm_request;
        weakly_reduce_scrutinee = __fname__weakly_reduce_scrutinee;
        nbe_step = __fname__nbe_step;_} -> __fname__weakly_reduce_scrutinee
  
let (__proj__Mkfsteps__item__nbe_step : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        do_not_unfold_pure_lets = __fname__do_not_unfold_pure_lets;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_fully = __fname__unfold_fully;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;
        in_full_norm_request = __fname__in_full_norm_request;
        weakly_reduce_scrutinee = __fname__weakly_reduce_scrutinee;
        nbe_step = __fname__nbe_step;_} -> __fname__nbe_step
  
let (steps_to_string : fsteps -> Prims.string) =
  fun f  ->
    let format_opt f1 o =
      match o with
      | FStar_Pervasives_Native.None  -> "None"
      | FStar_Pervasives_Native.Some x ->
          let uu____1301 =
            let uu____1302 = f1 x  in Prims.strcat uu____1302 ")"  in
          Prims.strcat "Some (" uu____1301
       in
    let b = FStar_Util.string_of_bool  in
    let uu____1308 =
      let uu____1311 = FStar_All.pipe_right f.beta b  in
      let uu____1312 =
        let uu____1315 = FStar_All.pipe_right f.iota b  in
        let uu____1316 =
          let uu____1319 = FStar_All.pipe_right f.zeta b  in
          let uu____1320 =
            let uu____1323 = FStar_All.pipe_right f.weak b  in
            let uu____1324 =
              let uu____1327 = FStar_All.pipe_right f.hnf b  in
              let uu____1328 =
                let uu____1331 = FStar_All.pipe_right f.primops b  in
                let uu____1332 =
                  let uu____1335 =
                    FStar_All.pipe_right f.do_not_unfold_pure_lets b  in
                  let uu____1336 =
                    let uu____1339 =
                      FStar_All.pipe_right f.unfold_until
                        (format_opt FStar_Syntax_Print.delta_depth_to_string)
                       in
                    let uu____1342 =
                      let uu____1345 =
                        FStar_All.pipe_right f.unfold_only
                          (format_opt
                             (fun x  ->
                                let uu____1357 =
                                  FStar_List.map FStar_Ident.string_of_lid x
                                   in
                                FStar_All.pipe_right uu____1357
                                  (FStar_String.concat ", ")))
                         in
                      let uu____1362 =
                        let uu____1365 =
                          FStar_All.pipe_right f.unfold_fully
                            (format_opt
                               (fun x  ->
                                  let uu____1377 =
                                    FStar_List.map FStar_Ident.string_of_lid
                                      x
                                     in
                                  FStar_All.pipe_right uu____1377
                                    (FStar_String.concat ", ")))
                           in
                        let uu____1382 =
                          let uu____1385 =
                            FStar_All.pipe_right f.unfold_attr
                              (format_opt
                                 (fun x  ->
                                    let uu____1397 =
                                      FStar_List.map
                                        FStar_Ident.string_of_lid x
                                       in
                                    FStar_All.pipe_right uu____1397
                                      (FStar_String.concat ", ")))
                             in
                          let uu____1402 =
                            let uu____1405 =
                              FStar_All.pipe_right f.unfold_tac b  in
                            let uu____1406 =
                              let uu____1409 =
                                FStar_All.pipe_right
                                  f.pure_subterms_within_computations b
                                 in
                              let uu____1410 =
                                let uu____1413 =
                                  FStar_All.pipe_right f.simplify b  in
                                let uu____1414 =
                                  let uu____1417 =
                                    FStar_All.pipe_right f.erase_universes b
                                     in
                                  let uu____1418 =
                                    let uu____1421 =
                                      FStar_All.pipe_right
                                        f.allow_unbound_universes b
                                       in
                                    let uu____1422 =
                                      let uu____1425 =
                                        FStar_All.pipe_right f.reify_ b  in
                                      let uu____1426 =
                                        let uu____1429 =
                                          FStar_All.pipe_right
                                            f.compress_uvars b
                                           in
                                        let uu____1430 =
                                          let uu____1433 =
                                            FStar_All.pipe_right
                                              f.no_full_norm b
                                             in
                                          let uu____1434 =
                                            let uu____1437 =
                                              FStar_All.pipe_right
                                                f.check_no_uvars b
                                               in
                                            let uu____1438 =
                                              let uu____1441 =
                                                FStar_All.pipe_right 
                                                  f.unmeta b
                                                 in
                                              let uu____1442 =
                                                let uu____1445 =
                                                  FStar_All.pipe_right
                                                    f.unascribe b
                                                   in
                                                let uu____1446 =
                                                  let uu____1449 =
                                                    FStar_All.pipe_right
                                                      f.in_full_norm_request
                                                      b
                                                     in
                                                  let uu____1450 =
                                                    let uu____1453 =
                                                      FStar_All.pipe_right
                                                        f.weakly_reduce_scrutinee
                                                        b
                                                       in
                                                    [uu____1453]  in
                                                  uu____1449 :: uu____1450
                                                   in
                                                uu____1445 :: uu____1446  in
                                              uu____1441 :: uu____1442  in
                                            uu____1437 :: uu____1438  in
                                          uu____1433 :: uu____1434  in
                                        uu____1429 :: uu____1430  in
                                      uu____1425 :: uu____1426  in
                                    uu____1421 :: uu____1422  in
                                  uu____1417 :: uu____1418  in
                                uu____1413 :: uu____1414  in
                              uu____1409 :: uu____1410  in
                            uu____1405 :: uu____1406  in
                          uu____1385 :: uu____1402  in
                        uu____1365 :: uu____1382  in
                      uu____1345 :: uu____1362  in
                    uu____1339 :: uu____1342  in
                  uu____1335 :: uu____1336  in
                uu____1331 :: uu____1332  in
              uu____1327 :: uu____1328  in
            uu____1323 :: uu____1324  in
          uu____1319 :: uu____1320  in
        uu____1315 :: uu____1316  in
      uu____1311 :: uu____1312  in
    FStar_Util.format
      "{\nbeta = %s;\niota = %s;\nzeta = %s;\nweak = %s;\nhnf  = %s;\nprimops = %s;\ndo_not_unfold_pure_lets = %s;\nunfold_until = %s;\nunfold_only = %s;\nunfold_fully = %s;\nunfold_attr = %s;\nunfold_tac = %s;\npure_subterms_within_computations = %s;\nsimplify = %s;\nerase_universes = %s;\nallow_unbound_universes = %s;\nreify_ = %s;\ncompress_uvars = %s;\nno_full_norm = %s;\ncheck_no_uvars = %s;\nunmeta = %s;\nunascribe = %s;\nin_full_norm_request = %s;\nweakly_reduce_scrutinee = %s;\n}"
      uu____1308
  
let (default_steps : fsteps) =
  {
    beta = true;
    iota = true;
    zeta = true;
    weak = false;
    hnf = false;
    primops = false;
    do_not_unfold_pure_lets = false;
    unfold_until = FStar_Pervasives_Native.None;
    unfold_only = FStar_Pervasives_Native.None;
    unfold_fully = FStar_Pervasives_Native.None;
    unfold_attr = FStar_Pervasives_Native.None;
    unfold_tac = false;
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
    nbe_step = false
  } 
let (fstep_add_one : FStar_TypeChecker_Env.step -> fsteps -> fsteps) =
  fun s  ->
    fun fs  ->
      match s with
      | FStar_TypeChecker_Env.Beta  ->
          let uu___231_1470 = fs  in
          {
            beta = true;
            iota = (uu___231_1470.iota);
            zeta = (uu___231_1470.zeta);
            weak = (uu___231_1470.weak);
            hnf = (uu___231_1470.hnf);
            primops = (uu___231_1470.primops);
            do_not_unfold_pure_lets = (uu___231_1470.do_not_unfold_pure_lets);
            unfold_until = (uu___231_1470.unfold_until);
            unfold_only = (uu___231_1470.unfold_only);
            unfold_fully = (uu___231_1470.unfold_fully);
            unfold_attr = (uu___231_1470.unfold_attr);
            unfold_tac = (uu___231_1470.unfold_tac);
            pure_subterms_within_computations =
              (uu___231_1470.pure_subterms_within_computations);
            simplify = (uu___231_1470.simplify);
            erase_universes = (uu___231_1470.erase_universes);
            allow_unbound_universes = (uu___231_1470.allow_unbound_universes);
            reify_ = (uu___231_1470.reify_);
            compress_uvars = (uu___231_1470.compress_uvars);
            no_full_norm = (uu___231_1470.no_full_norm);
            check_no_uvars = (uu___231_1470.check_no_uvars);
            unmeta = (uu___231_1470.unmeta);
            unascribe = (uu___231_1470.unascribe);
            in_full_norm_request = (uu___231_1470.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___231_1470.weakly_reduce_scrutinee);
            nbe_step = (uu___231_1470.nbe_step)
          }
      | FStar_TypeChecker_Env.Iota  ->
          let uu___232_1471 = fs  in
          {
            beta = (uu___232_1471.beta);
            iota = true;
            zeta = (uu___232_1471.zeta);
            weak = (uu___232_1471.weak);
            hnf = (uu___232_1471.hnf);
            primops = (uu___232_1471.primops);
            do_not_unfold_pure_lets = (uu___232_1471.do_not_unfold_pure_lets);
            unfold_until = (uu___232_1471.unfold_until);
            unfold_only = (uu___232_1471.unfold_only);
            unfold_fully = (uu___232_1471.unfold_fully);
            unfold_attr = (uu___232_1471.unfold_attr);
            unfold_tac = (uu___232_1471.unfold_tac);
            pure_subterms_within_computations =
              (uu___232_1471.pure_subterms_within_computations);
            simplify = (uu___232_1471.simplify);
            erase_universes = (uu___232_1471.erase_universes);
            allow_unbound_universes = (uu___232_1471.allow_unbound_universes);
            reify_ = (uu___232_1471.reify_);
            compress_uvars = (uu___232_1471.compress_uvars);
            no_full_norm = (uu___232_1471.no_full_norm);
            check_no_uvars = (uu___232_1471.check_no_uvars);
            unmeta = (uu___232_1471.unmeta);
            unascribe = (uu___232_1471.unascribe);
            in_full_norm_request = (uu___232_1471.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___232_1471.weakly_reduce_scrutinee);
            nbe_step = (uu___232_1471.nbe_step)
          }
      | FStar_TypeChecker_Env.Zeta  ->
          let uu___233_1472 = fs  in
          {
            beta = (uu___233_1472.beta);
            iota = (uu___233_1472.iota);
            zeta = true;
            weak = (uu___233_1472.weak);
            hnf = (uu___233_1472.hnf);
            primops = (uu___233_1472.primops);
            do_not_unfold_pure_lets = (uu___233_1472.do_not_unfold_pure_lets);
            unfold_until = (uu___233_1472.unfold_until);
            unfold_only = (uu___233_1472.unfold_only);
            unfold_fully = (uu___233_1472.unfold_fully);
            unfold_attr = (uu___233_1472.unfold_attr);
            unfold_tac = (uu___233_1472.unfold_tac);
            pure_subterms_within_computations =
              (uu___233_1472.pure_subterms_within_computations);
            simplify = (uu___233_1472.simplify);
            erase_universes = (uu___233_1472.erase_universes);
            allow_unbound_universes = (uu___233_1472.allow_unbound_universes);
            reify_ = (uu___233_1472.reify_);
            compress_uvars = (uu___233_1472.compress_uvars);
            no_full_norm = (uu___233_1472.no_full_norm);
            check_no_uvars = (uu___233_1472.check_no_uvars);
            unmeta = (uu___233_1472.unmeta);
            unascribe = (uu___233_1472.unascribe);
            in_full_norm_request = (uu___233_1472.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___233_1472.weakly_reduce_scrutinee);
            nbe_step = (uu___233_1472.nbe_step)
          }
      | FStar_TypeChecker_Env.Exclude (FStar_TypeChecker_Env.Beta ) ->
          let uu___234_1473 = fs  in
          {
            beta = false;
            iota = (uu___234_1473.iota);
            zeta = (uu___234_1473.zeta);
            weak = (uu___234_1473.weak);
            hnf = (uu___234_1473.hnf);
            primops = (uu___234_1473.primops);
            do_not_unfold_pure_lets = (uu___234_1473.do_not_unfold_pure_lets);
            unfold_until = (uu___234_1473.unfold_until);
            unfold_only = (uu___234_1473.unfold_only);
            unfold_fully = (uu___234_1473.unfold_fully);
            unfold_attr = (uu___234_1473.unfold_attr);
            unfold_tac = (uu___234_1473.unfold_tac);
            pure_subterms_within_computations =
              (uu___234_1473.pure_subterms_within_computations);
            simplify = (uu___234_1473.simplify);
            erase_universes = (uu___234_1473.erase_universes);
            allow_unbound_universes = (uu___234_1473.allow_unbound_universes);
            reify_ = (uu___234_1473.reify_);
            compress_uvars = (uu___234_1473.compress_uvars);
            no_full_norm = (uu___234_1473.no_full_norm);
            check_no_uvars = (uu___234_1473.check_no_uvars);
            unmeta = (uu___234_1473.unmeta);
            unascribe = (uu___234_1473.unascribe);
            in_full_norm_request = (uu___234_1473.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___234_1473.weakly_reduce_scrutinee);
            nbe_step = (uu___234_1473.nbe_step)
          }
      | FStar_TypeChecker_Env.Exclude (FStar_TypeChecker_Env.Iota ) ->
          let uu___235_1474 = fs  in
          {
            beta = (uu___235_1474.beta);
            iota = false;
            zeta = (uu___235_1474.zeta);
            weak = (uu___235_1474.weak);
            hnf = (uu___235_1474.hnf);
            primops = (uu___235_1474.primops);
            do_not_unfold_pure_lets = (uu___235_1474.do_not_unfold_pure_lets);
            unfold_until = (uu___235_1474.unfold_until);
            unfold_only = (uu___235_1474.unfold_only);
            unfold_fully = (uu___235_1474.unfold_fully);
            unfold_attr = (uu___235_1474.unfold_attr);
            unfold_tac = (uu___235_1474.unfold_tac);
            pure_subterms_within_computations =
              (uu___235_1474.pure_subterms_within_computations);
            simplify = (uu___235_1474.simplify);
            erase_universes = (uu___235_1474.erase_universes);
            allow_unbound_universes = (uu___235_1474.allow_unbound_universes);
            reify_ = (uu___235_1474.reify_);
            compress_uvars = (uu___235_1474.compress_uvars);
            no_full_norm = (uu___235_1474.no_full_norm);
            check_no_uvars = (uu___235_1474.check_no_uvars);
            unmeta = (uu___235_1474.unmeta);
            unascribe = (uu___235_1474.unascribe);
            in_full_norm_request = (uu___235_1474.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___235_1474.weakly_reduce_scrutinee);
            nbe_step = (uu___235_1474.nbe_step)
          }
      | FStar_TypeChecker_Env.Exclude (FStar_TypeChecker_Env.Zeta ) ->
          let uu___236_1475 = fs  in
          {
            beta = (uu___236_1475.beta);
            iota = (uu___236_1475.iota);
            zeta = false;
            weak = (uu___236_1475.weak);
            hnf = (uu___236_1475.hnf);
            primops = (uu___236_1475.primops);
            do_not_unfold_pure_lets = (uu___236_1475.do_not_unfold_pure_lets);
            unfold_until = (uu___236_1475.unfold_until);
            unfold_only = (uu___236_1475.unfold_only);
            unfold_fully = (uu___236_1475.unfold_fully);
            unfold_attr = (uu___236_1475.unfold_attr);
            unfold_tac = (uu___236_1475.unfold_tac);
            pure_subterms_within_computations =
              (uu___236_1475.pure_subterms_within_computations);
            simplify = (uu___236_1475.simplify);
            erase_universes = (uu___236_1475.erase_universes);
            allow_unbound_universes = (uu___236_1475.allow_unbound_universes);
            reify_ = (uu___236_1475.reify_);
            compress_uvars = (uu___236_1475.compress_uvars);
            no_full_norm = (uu___236_1475.no_full_norm);
            check_no_uvars = (uu___236_1475.check_no_uvars);
            unmeta = (uu___236_1475.unmeta);
            unascribe = (uu___236_1475.unascribe);
            in_full_norm_request = (uu___236_1475.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___236_1475.weakly_reduce_scrutinee);
            nbe_step = (uu___236_1475.nbe_step)
          }
      | FStar_TypeChecker_Env.Exclude uu____1476 -> failwith "Bad exclude"
      | FStar_TypeChecker_Env.Weak  ->
          let uu___237_1477 = fs  in
          {
            beta = (uu___237_1477.beta);
            iota = (uu___237_1477.iota);
            zeta = (uu___237_1477.zeta);
            weak = true;
            hnf = (uu___237_1477.hnf);
            primops = (uu___237_1477.primops);
            do_not_unfold_pure_lets = (uu___237_1477.do_not_unfold_pure_lets);
            unfold_until = (uu___237_1477.unfold_until);
            unfold_only = (uu___237_1477.unfold_only);
            unfold_fully = (uu___237_1477.unfold_fully);
            unfold_attr = (uu___237_1477.unfold_attr);
            unfold_tac = (uu___237_1477.unfold_tac);
            pure_subterms_within_computations =
              (uu___237_1477.pure_subterms_within_computations);
            simplify = (uu___237_1477.simplify);
            erase_universes = (uu___237_1477.erase_universes);
            allow_unbound_universes = (uu___237_1477.allow_unbound_universes);
            reify_ = (uu___237_1477.reify_);
            compress_uvars = (uu___237_1477.compress_uvars);
            no_full_norm = (uu___237_1477.no_full_norm);
            check_no_uvars = (uu___237_1477.check_no_uvars);
            unmeta = (uu___237_1477.unmeta);
            unascribe = (uu___237_1477.unascribe);
            in_full_norm_request = (uu___237_1477.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___237_1477.weakly_reduce_scrutinee);
            nbe_step = (uu___237_1477.nbe_step)
          }
      | FStar_TypeChecker_Env.HNF  ->
          let uu___238_1478 = fs  in
          {
            beta = (uu___238_1478.beta);
            iota = (uu___238_1478.iota);
            zeta = (uu___238_1478.zeta);
            weak = (uu___238_1478.weak);
            hnf = true;
            primops = (uu___238_1478.primops);
            do_not_unfold_pure_lets = (uu___238_1478.do_not_unfold_pure_lets);
            unfold_until = (uu___238_1478.unfold_until);
            unfold_only = (uu___238_1478.unfold_only);
            unfold_fully = (uu___238_1478.unfold_fully);
            unfold_attr = (uu___238_1478.unfold_attr);
            unfold_tac = (uu___238_1478.unfold_tac);
            pure_subterms_within_computations =
              (uu___238_1478.pure_subterms_within_computations);
            simplify = (uu___238_1478.simplify);
            erase_universes = (uu___238_1478.erase_universes);
            allow_unbound_universes = (uu___238_1478.allow_unbound_universes);
            reify_ = (uu___238_1478.reify_);
            compress_uvars = (uu___238_1478.compress_uvars);
            no_full_norm = (uu___238_1478.no_full_norm);
            check_no_uvars = (uu___238_1478.check_no_uvars);
            unmeta = (uu___238_1478.unmeta);
            unascribe = (uu___238_1478.unascribe);
            in_full_norm_request = (uu___238_1478.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___238_1478.weakly_reduce_scrutinee);
            nbe_step = (uu___238_1478.nbe_step)
          }
      | FStar_TypeChecker_Env.Primops  ->
          let uu___239_1479 = fs  in
          {
            beta = (uu___239_1479.beta);
            iota = (uu___239_1479.iota);
            zeta = (uu___239_1479.zeta);
            weak = (uu___239_1479.weak);
            hnf = (uu___239_1479.hnf);
            primops = true;
            do_not_unfold_pure_lets = (uu___239_1479.do_not_unfold_pure_lets);
            unfold_until = (uu___239_1479.unfold_until);
            unfold_only = (uu___239_1479.unfold_only);
            unfold_fully = (uu___239_1479.unfold_fully);
            unfold_attr = (uu___239_1479.unfold_attr);
            unfold_tac = (uu___239_1479.unfold_tac);
            pure_subterms_within_computations =
              (uu___239_1479.pure_subterms_within_computations);
            simplify = (uu___239_1479.simplify);
            erase_universes = (uu___239_1479.erase_universes);
            allow_unbound_universes = (uu___239_1479.allow_unbound_universes);
            reify_ = (uu___239_1479.reify_);
            compress_uvars = (uu___239_1479.compress_uvars);
            no_full_norm = (uu___239_1479.no_full_norm);
            check_no_uvars = (uu___239_1479.check_no_uvars);
            unmeta = (uu___239_1479.unmeta);
            unascribe = (uu___239_1479.unascribe);
            in_full_norm_request = (uu___239_1479.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___239_1479.weakly_reduce_scrutinee);
            nbe_step = (uu___239_1479.nbe_step)
          }
      | FStar_TypeChecker_Env.Eager_unfolding  -> fs
      | FStar_TypeChecker_Env.Inlining  -> fs
      | FStar_TypeChecker_Env.DoNotUnfoldPureLets  ->
          let uu___240_1480 = fs  in
          {
            beta = (uu___240_1480.beta);
            iota = (uu___240_1480.iota);
            zeta = (uu___240_1480.zeta);
            weak = (uu___240_1480.weak);
            hnf = (uu___240_1480.hnf);
            primops = (uu___240_1480.primops);
            do_not_unfold_pure_lets = true;
            unfold_until = (uu___240_1480.unfold_until);
            unfold_only = (uu___240_1480.unfold_only);
            unfold_fully = (uu___240_1480.unfold_fully);
            unfold_attr = (uu___240_1480.unfold_attr);
            unfold_tac = (uu___240_1480.unfold_tac);
            pure_subterms_within_computations =
              (uu___240_1480.pure_subterms_within_computations);
            simplify = (uu___240_1480.simplify);
            erase_universes = (uu___240_1480.erase_universes);
            allow_unbound_universes = (uu___240_1480.allow_unbound_universes);
            reify_ = (uu___240_1480.reify_);
            compress_uvars = (uu___240_1480.compress_uvars);
            no_full_norm = (uu___240_1480.no_full_norm);
            check_no_uvars = (uu___240_1480.check_no_uvars);
            unmeta = (uu___240_1480.unmeta);
            unascribe = (uu___240_1480.unascribe);
            in_full_norm_request = (uu___240_1480.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___240_1480.weakly_reduce_scrutinee);
            nbe_step = (uu___240_1480.nbe_step)
          }
      | FStar_TypeChecker_Env.UnfoldUntil d ->
          let uu___241_1482 = fs  in
          {
            beta = (uu___241_1482.beta);
            iota = (uu___241_1482.iota);
            zeta = (uu___241_1482.zeta);
            weak = (uu___241_1482.weak);
            hnf = (uu___241_1482.hnf);
            primops = (uu___241_1482.primops);
            do_not_unfold_pure_lets = (uu___241_1482.do_not_unfold_pure_lets);
            unfold_until = (FStar_Pervasives_Native.Some d);
            unfold_only = (uu___241_1482.unfold_only);
            unfold_fully = (uu___241_1482.unfold_fully);
            unfold_attr = (uu___241_1482.unfold_attr);
            unfold_tac = (uu___241_1482.unfold_tac);
            pure_subterms_within_computations =
              (uu___241_1482.pure_subterms_within_computations);
            simplify = (uu___241_1482.simplify);
            erase_universes = (uu___241_1482.erase_universes);
            allow_unbound_universes = (uu___241_1482.allow_unbound_universes);
            reify_ = (uu___241_1482.reify_);
            compress_uvars = (uu___241_1482.compress_uvars);
            no_full_norm = (uu___241_1482.no_full_norm);
            check_no_uvars = (uu___241_1482.check_no_uvars);
            unmeta = (uu___241_1482.unmeta);
            unascribe = (uu___241_1482.unascribe);
            in_full_norm_request = (uu___241_1482.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___241_1482.weakly_reduce_scrutinee);
            nbe_step = (uu___241_1482.nbe_step)
          }
      | FStar_TypeChecker_Env.UnfoldOnly lids ->
          let uu___242_1486 = fs  in
          {
            beta = (uu___242_1486.beta);
            iota = (uu___242_1486.iota);
            zeta = (uu___242_1486.zeta);
            weak = (uu___242_1486.weak);
            hnf = (uu___242_1486.hnf);
            primops = (uu___242_1486.primops);
            do_not_unfold_pure_lets = (uu___242_1486.do_not_unfold_pure_lets);
            unfold_until = (uu___242_1486.unfold_until);
            unfold_only = (FStar_Pervasives_Native.Some lids);
            unfold_fully = (uu___242_1486.unfold_fully);
            unfold_attr = (uu___242_1486.unfold_attr);
            unfold_tac = (uu___242_1486.unfold_tac);
            pure_subterms_within_computations =
              (uu___242_1486.pure_subterms_within_computations);
            simplify = (uu___242_1486.simplify);
            erase_universes = (uu___242_1486.erase_universes);
            allow_unbound_universes = (uu___242_1486.allow_unbound_universes);
            reify_ = (uu___242_1486.reify_);
            compress_uvars = (uu___242_1486.compress_uvars);
            no_full_norm = (uu___242_1486.no_full_norm);
            check_no_uvars = (uu___242_1486.check_no_uvars);
            unmeta = (uu___242_1486.unmeta);
            unascribe = (uu___242_1486.unascribe);
            in_full_norm_request = (uu___242_1486.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___242_1486.weakly_reduce_scrutinee);
            nbe_step = (uu___242_1486.nbe_step)
          }
      | FStar_TypeChecker_Env.UnfoldFully lids ->
          let uu___243_1492 = fs  in
          {
            beta = (uu___243_1492.beta);
            iota = (uu___243_1492.iota);
            zeta = (uu___243_1492.zeta);
            weak = (uu___243_1492.weak);
            hnf = (uu___243_1492.hnf);
            primops = (uu___243_1492.primops);
            do_not_unfold_pure_lets = (uu___243_1492.do_not_unfold_pure_lets);
            unfold_until = (uu___243_1492.unfold_until);
            unfold_only = (uu___243_1492.unfold_only);
            unfold_fully = (FStar_Pervasives_Native.Some lids);
            unfold_attr = (uu___243_1492.unfold_attr);
            unfold_tac = (uu___243_1492.unfold_tac);
            pure_subterms_within_computations =
              (uu___243_1492.pure_subterms_within_computations);
            simplify = (uu___243_1492.simplify);
            erase_universes = (uu___243_1492.erase_universes);
            allow_unbound_universes = (uu___243_1492.allow_unbound_universes);
            reify_ = (uu___243_1492.reify_);
            compress_uvars = (uu___243_1492.compress_uvars);
            no_full_norm = (uu___243_1492.no_full_norm);
            check_no_uvars = (uu___243_1492.check_no_uvars);
            unmeta = (uu___243_1492.unmeta);
            unascribe = (uu___243_1492.unascribe);
            in_full_norm_request = (uu___243_1492.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___243_1492.weakly_reduce_scrutinee);
            nbe_step = (uu___243_1492.nbe_step)
          }
      | FStar_TypeChecker_Env.UnfoldAttr lids ->
          let uu___244_1498 = fs  in
          {
            beta = (uu___244_1498.beta);
            iota = (uu___244_1498.iota);
            zeta = (uu___244_1498.zeta);
            weak = (uu___244_1498.weak);
            hnf = (uu___244_1498.hnf);
            primops = (uu___244_1498.primops);
            do_not_unfold_pure_lets = (uu___244_1498.do_not_unfold_pure_lets);
            unfold_until = (uu___244_1498.unfold_until);
            unfold_only = (uu___244_1498.unfold_only);
            unfold_fully = (uu___244_1498.unfold_fully);
            unfold_attr = (FStar_Pervasives_Native.Some lids);
            unfold_tac = (uu___244_1498.unfold_tac);
            pure_subterms_within_computations =
              (uu___244_1498.pure_subterms_within_computations);
            simplify = (uu___244_1498.simplify);
            erase_universes = (uu___244_1498.erase_universes);
            allow_unbound_universes = (uu___244_1498.allow_unbound_universes);
            reify_ = (uu___244_1498.reify_);
            compress_uvars = (uu___244_1498.compress_uvars);
            no_full_norm = (uu___244_1498.no_full_norm);
            check_no_uvars = (uu___244_1498.check_no_uvars);
            unmeta = (uu___244_1498.unmeta);
            unascribe = (uu___244_1498.unascribe);
            in_full_norm_request = (uu___244_1498.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___244_1498.weakly_reduce_scrutinee);
            nbe_step = (uu___244_1498.nbe_step)
          }
      | FStar_TypeChecker_Env.UnfoldTac  ->
          let uu___245_1501 = fs  in
          {
            beta = (uu___245_1501.beta);
            iota = (uu___245_1501.iota);
            zeta = (uu___245_1501.zeta);
            weak = (uu___245_1501.weak);
            hnf = (uu___245_1501.hnf);
            primops = (uu___245_1501.primops);
            do_not_unfold_pure_lets = (uu___245_1501.do_not_unfold_pure_lets);
            unfold_until = (uu___245_1501.unfold_until);
            unfold_only = (uu___245_1501.unfold_only);
            unfold_fully = (uu___245_1501.unfold_fully);
            unfold_attr = (uu___245_1501.unfold_attr);
            unfold_tac = true;
            pure_subterms_within_computations =
              (uu___245_1501.pure_subterms_within_computations);
            simplify = (uu___245_1501.simplify);
            erase_universes = (uu___245_1501.erase_universes);
            allow_unbound_universes = (uu___245_1501.allow_unbound_universes);
            reify_ = (uu___245_1501.reify_);
            compress_uvars = (uu___245_1501.compress_uvars);
            no_full_norm = (uu___245_1501.no_full_norm);
            check_no_uvars = (uu___245_1501.check_no_uvars);
            unmeta = (uu___245_1501.unmeta);
            unascribe = (uu___245_1501.unascribe);
            in_full_norm_request = (uu___245_1501.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___245_1501.weakly_reduce_scrutinee);
            nbe_step = (uu___245_1501.nbe_step)
          }
      | FStar_TypeChecker_Env.PureSubtermsWithinComputations  ->
          let uu___246_1502 = fs  in
          {
            beta = (uu___246_1502.beta);
            iota = (uu___246_1502.iota);
            zeta = (uu___246_1502.zeta);
            weak = (uu___246_1502.weak);
            hnf = (uu___246_1502.hnf);
            primops = (uu___246_1502.primops);
            do_not_unfold_pure_lets = (uu___246_1502.do_not_unfold_pure_lets);
            unfold_until = (uu___246_1502.unfold_until);
            unfold_only = (uu___246_1502.unfold_only);
            unfold_fully = (uu___246_1502.unfold_fully);
            unfold_attr = (uu___246_1502.unfold_attr);
            unfold_tac = (uu___246_1502.unfold_tac);
            pure_subterms_within_computations = true;
            simplify = (uu___246_1502.simplify);
            erase_universes = (uu___246_1502.erase_universes);
            allow_unbound_universes = (uu___246_1502.allow_unbound_universes);
            reify_ = (uu___246_1502.reify_);
            compress_uvars = (uu___246_1502.compress_uvars);
            no_full_norm = (uu___246_1502.no_full_norm);
            check_no_uvars = (uu___246_1502.check_no_uvars);
            unmeta = (uu___246_1502.unmeta);
            unascribe = (uu___246_1502.unascribe);
            in_full_norm_request = (uu___246_1502.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___246_1502.weakly_reduce_scrutinee);
            nbe_step = (uu___246_1502.nbe_step)
          }
      | FStar_TypeChecker_Env.Simplify  ->
          let uu___247_1503 = fs  in
          {
            beta = (uu___247_1503.beta);
            iota = (uu___247_1503.iota);
            zeta = (uu___247_1503.zeta);
            weak = (uu___247_1503.weak);
            hnf = (uu___247_1503.hnf);
            primops = (uu___247_1503.primops);
            do_not_unfold_pure_lets = (uu___247_1503.do_not_unfold_pure_lets);
            unfold_until = (uu___247_1503.unfold_until);
            unfold_only = (uu___247_1503.unfold_only);
            unfold_fully = (uu___247_1503.unfold_fully);
            unfold_attr = (uu___247_1503.unfold_attr);
            unfold_tac = (uu___247_1503.unfold_tac);
            pure_subterms_within_computations =
              (uu___247_1503.pure_subterms_within_computations);
            simplify = true;
            erase_universes = (uu___247_1503.erase_universes);
            allow_unbound_universes = (uu___247_1503.allow_unbound_universes);
            reify_ = (uu___247_1503.reify_);
            compress_uvars = (uu___247_1503.compress_uvars);
            no_full_norm = (uu___247_1503.no_full_norm);
            check_no_uvars = (uu___247_1503.check_no_uvars);
            unmeta = (uu___247_1503.unmeta);
            unascribe = (uu___247_1503.unascribe);
            in_full_norm_request = (uu___247_1503.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___247_1503.weakly_reduce_scrutinee);
            nbe_step = (uu___247_1503.nbe_step)
          }
      | FStar_TypeChecker_Env.EraseUniverses  ->
          let uu___248_1504 = fs  in
          {
            beta = (uu___248_1504.beta);
            iota = (uu___248_1504.iota);
            zeta = (uu___248_1504.zeta);
            weak = (uu___248_1504.weak);
            hnf = (uu___248_1504.hnf);
            primops = (uu___248_1504.primops);
            do_not_unfold_pure_lets = (uu___248_1504.do_not_unfold_pure_lets);
            unfold_until = (uu___248_1504.unfold_until);
            unfold_only = (uu___248_1504.unfold_only);
            unfold_fully = (uu___248_1504.unfold_fully);
            unfold_attr = (uu___248_1504.unfold_attr);
            unfold_tac = (uu___248_1504.unfold_tac);
            pure_subterms_within_computations =
              (uu___248_1504.pure_subterms_within_computations);
            simplify = (uu___248_1504.simplify);
            erase_universes = true;
            allow_unbound_universes = (uu___248_1504.allow_unbound_universes);
            reify_ = (uu___248_1504.reify_);
            compress_uvars = (uu___248_1504.compress_uvars);
            no_full_norm = (uu___248_1504.no_full_norm);
            check_no_uvars = (uu___248_1504.check_no_uvars);
            unmeta = (uu___248_1504.unmeta);
            unascribe = (uu___248_1504.unascribe);
            in_full_norm_request = (uu___248_1504.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___248_1504.weakly_reduce_scrutinee);
            nbe_step = (uu___248_1504.nbe_step)
          }
      | FStar_TypeChecker_Env.AllowUnboundUniverses  ->
          let uu___249_1505 = fs  in
          {
            beta = (uu___249_1505.beta);
            iota = (uu___249_1505.iota);
            zeta = (uu___249_1505.zeta);
            weak = (uu___249_1505.weak);
            hnf = (uu___249_1505.hnf);
            primops = (uu___249_1505.primops);
            do_not_unfold_pure_lets = (uu___249_1505.do_not_unfold_pure_lets);
            unfold_until = (uu___249_1505.unfold_until);
            unfold_only = (uu___249_1505.unfold_only);
            unfold_fully = (uu___249_1505.unfold_fully);
            unfold_attr = (uu___249_1505.unfold_attr);
            unfold_tac = (uu___249_1505.unfold_tac);
            pure_subterms_within_computations =
              (uu___249_1505.pure_subterms_within_computations);
            simplify = (uu___249_1505.simplify);
            erase_universes = (uu___249_1505.erase_universes);
            allow_unbound_universes = true;
            reify_ = (uu___249_1505.reify_);
            compress_uvars = (uu___249_1505.compress_uvars);
            no_full_norm = (uu___249_1505.no_full_norm);
            check_no_uvars = (uu___249_1505.check_no_uvars);
            unmeta = (uu___249_1505.unmeta);
            unascribe = (uu___249_1505.unascribe);
            in_full_norm_request = (uu___249_1505.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___249_1505.weakly_reduce_scrutinee);
            nbe_step = (uu___249_1505.nbe_step)
          }
      | FStar_TypeChecker_Env.Reify  ->
          let uu___250_1506 = fs  in
          {
            beta = (uu___250_1506.beta);
            iota = (uu___250_1506.iota);
            zeta = (uu___250_1506.zeta);
            weak = (uu___250_1506.weak);
            hnf = (uu___250_1506.hnf);
            primops = (uu___250_1506.primops);
            do_not_unfold_pure_lets = (uu___250_1506.do_not_unfold_pure_lets);
            unfold_until = (uu___250_1506.unfold_until);
            unfold_only = (uu___250_1506.unfold_only);
            unfold_fully = (uu___250_1506.unfold_fully);
            unfold_attr = (uu___250_1506.unfold_attr);
            unfold_tac = (uu___250_1506.unfold_tac);
            pure_subterms_within_computations =
              (uu___250_1506.pure_subterms_within_computations);
            simplify = (uu___250_1506.simplify);
            erase_universes = (uu___250_1506.erase_universes);
            allow_unbound_universes = (uu___250_1506.allow_unbound_universes);
            reify_ = true;
            compress_uvars = (uu___250_1506.compress_uvars);
            no_full_norm = (uu___250_1506.no_full_norm);
            check_no_uvars = (uu___250_1506.check_no_uvars);
            unmeta = (uu___250_1506.unmeta);
            unascribe = (uu___250_1506.unascribe);
            in_full_norm_request = (uu___250_1506.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___250_1506.weakly_reduce_scrutinee);
            nbe_step = (uu___250_1506.nbe_step)
          }
      | FStar_TypeChecker_Env.CompressUvars  ->
          let uu___251_1507 = fs  in
          {
            beta = (uu___251_1507.beta);
            iota = (uu___251_1507.iota);
            zeta = (uu___251_1507.zeta);
            weak = (uu___251_1507.weak);
            hnf = (uu___251_1507.hnf);
            primops = (uu___251_1507.primops);
            do_not_unfold_pure_lets = (uu___251_1507.do_not_unfold_pure_lets);
            unfold_until = (uu___251_1507.unfold_until);
            unfold_only = (uu___251_1507.unfold_only);
            unfold_fully = (uu___251_1507.unfold_fully);
            unfold_attr = (uu___251_1507.unfold_attr);
            unfold_tac = (uu___251_1507.unfold_tac);
            pure_subterms_within_computations =
              (uu___251_1507.pure_subterms_within_computations);
            simplify = (uu___251_1507.simplify);
            erase_universes = (uu___251_1507.erase_universes);
            allow_unbound_universes = (uu___251_1507.allow_unbound_universes);
            reify_ = (uu___251_1507.reify_);
            compress_uvars = true;
            no_full_norm = (uu___251_1507.no_full_norm);
            check_no_uvars = (uu___251_1507.check_no_uvars);
            unmeta = (uu___251_1507.unmeta);
            unascribe = (uu___251_1507.unascribe);
            in_full_norm_request = (uu___251_1507.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___251_1507.weakly_reduce_scrutinee);
            nbe_step = (uu___251_1507.nbe_step)
          }
      | FStar_TypeChecker_Env.NoFullNorm  ->
          let uu___252_1508 = fs  in
          {
            beta = (uu___252_1508.beta);
            iota = (uu___252_1508.iota);
            zeta = (uu___252_1508.zeta);
            weak = (uu___252_1508.weak);
            hnf = (uu___252_1508.hnf);
            primops = (uu___252_1508.primops);
            do_not_unfold_pure_lets = (uu___252_1508.do_not_unfold_pure_lets);
            unfold_until = (uu___252_1508.unfold_until);
            unfold_only = (uu___252_1508.unfold_only);
            unfold_fully = (uu___252_1508.unfold_fully);
            unfold_attr = (uu___252_1508.unfold_attr);
            unfold_tac = (uu___252_1508.unfold_tac);
            pure_subterms_within_computations =
              (uu___252_1508.pure_subterms_within_computations);
            simplify = (uu___252_1508.simplify);
            erase_universes = (uu___252_1508.erase_universes);
            allow_unbound_universes = (uu___252_1508.allow_unbound_universes);
            reify_ = (uu___252_1508.reify_);
            compress_uvars = (uu___252_1508.compress_uvars);
            no_full_norm = true;
            check_no_uvars = (uu___252_1508.check_no_uvars);
            unmeta = (uu___252_1508.unmeta);
            unascribe = (uu___252_1508.unascribe);
            in_full_norm_request = (uu___252_1508.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___252_1508.weakly_reduce_scrutinee);
            nbe_step = (uu___252_1508.nbe_step)
          }
      | FStar_TypeChecker_Env.CheckNoUvars  ->
          let uu___253_1509 = fs  in
          {
            beta = (uu___253_1509.beta);
            iota = (uu___253_1509.iota);
            zeta = (uu___253_1509.zeta);
            weak = (uu___253_1509.weak);
            hnf = (uu___253_1509.hnf);
            primops = (uu___253_1509.primops);
            do_not_unfold_pure_lets = (uu___253_1509.do_not_unfold_pure_lets);
            unfold_until = (uu___253_1509.unfold_until);
            unfold_only = (uu___253_1509.unfold_only);
            unfold_fully = (uu___253_1509.unfold_fully);
            unfold_attr = (uu___253_1509.unfold_attr);
            unfold_tac = (uu___253_1509.unfold_tac);
            pure_subterms_within_computations =
              (uu___253_1509.pure_subterms_within_computations);
            simplify = (uu___253_1509.simplify);
            erase_universes = (uu___253_1509.erase_universes);
            allow_unbound_universes = (uu___253_1509.allow_unbound_universes);
            reify_ = (uu___253_1509.reify_);
            compress_uvars = (uu___253_1509.compress_uvars);
            no_full_norm = (uu___253_1509.no_full_norm);
            check_no_uvars = true;
            unmeta = (uu___253_1509.unmeta);
            unascribe = (uu___253_1509.unascribe);
            in_full_norm_request = (uu___253_1509.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___253_1509.weakly_reduce_scrutinee);
            nbe_step = (uu___253_1509.nbe_step)
          }
      | FStar_TypeChecker_Env.Unmeta  ->
          let uu___254_1510 = fs  in
          {
            beta = (uu___254_1510.beta);
            iota = (uu___254_1510.iota);
            zeta = (uu___254_1510.zeta);
            weak = (uu___254_1510.weak);
            hnf = (uu___254_1510.hnf);
            primops = (uu___254_1510.primops);
            do_not_unfold_pure_lets = (uu___254_1510.do_not_unfold_pure_lets);
            unfold_until = (uu___254_1510.unfold_until);
            unfold_only = (uu___254_1510.unfold_only);
            unfold_fully = (uu___254_1510.unfold_fully);
            unfold_attr = (uu___254_1510.unfold_attr);
            unfold_tac = (uu___254_1510.unfold_tac);
            pure_subterms_within_computations =
              (uu___254_1510.pure_subterms_within_computations);
            simplify = (uu___254_1510.simplify);
            erase_universes = (uu___254_1510.erase_universes);
            allow_unbound_universes = (uu___254_1510.allow_unbound_universes);
            reify_ = (uu___254_1510.reify_);
            compress_uvars = (uu___254_1510.compress_uvars);
            no_full_norm = (uu___254_1510.no_full_norm);
            check_no_uvars = (uu___254_1510.check_no_uvars);
            unmeta = true;
            unascribe = (uu___254_1510.unascribe);
            in_full_norm_request = (uu___254_1510.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___254_1510.weakly_reduce_scrutinee);
            nbe_step = (uu___254_1510.nbe_step)
          }
      | FStar_TypeChecker_Env.Unascribe  ->
          let uu___255_1511 = fs  in
          {
            beta = (uu___255_1511.beta);
            iota = (uu___255_1511.iota);
            zeta = (uu___255_1511.zeta);
            weak = (uu___255_1511.weak);
            hnf = (uu___255_1511.hnf);
            primops = (uu___255_1511.primops);
            do_not_unfold_pure_lets = (uu___255_1511.do_not_unfold_pure_lets);
            unfold_until = (uu___255_1511.unfold_until);
            unfold_only = (uu___255_1511.unfold_only);
            unfold_fully = (uu___255_1511.unfold_fully);
            unfold_attr = (uu___255_1511.unfold_attr);
            unfold_tac = (uu___255_1511.unfold_tac);
            pure_subterms_within_computations =
              (uu___255_1511.pure_subterms_within_computations);
            simplify = (uu___255_1511.simplify);
            erase_universes = (uu___255_1511.erase_universes);
            allow_unbound_universes = (uu___255_1511.allow_unbound_universes);
            reify_ = (uu___255_1511.reify_);
            compress_uvars = (uu___255_1511.compress_uvars);
            no_full_norm = (uu___255_1511.no_full_norm);
            check_no_uvars = (uu___255_1511.check_no_uvars);
            unmeta = (uu___255_1511.unmeta);
            unascribe = true;
            in_full_norm_request = (uu___255_1511.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___255_1511.weakly_reduce_scrutinee);
            nbe_step = (uu___255_1511.nbe_step)
          }
      | FStar_TypeChecker_Env.NBE  ->
          let uu___256_1512 = fs  in
          {
            beta = (uu___256_1512.beta);
            iota = (uu___256_1512.iota);
            zeta = (uu___256_1512.zeta);
            weak = (uu___256_1512.weak);
            hnf = (uu___256_1512.hnf);
            primops = (uu___256_1512.primops);
            do_not_unfold_pure_lets = (uu___256_1512.do_not_unfold_pure_lets);
            unfold_until = (uu___256_1512.unfold_until);
            unfold_only = (uu___256_1512.unfold_only);
            unfold_fully = (uu___256_1512.unfold_fully);
            unfold_attr = (uu___256_1512.unfold_attr);
            unfold_tac = (uu___256_1512.unfold_tac);
            pure_subterms_within_computations =
              (uu___256_1512.pure_subterms_within_computations);
            simplify = (uu___256_1512.simplify);
            erase_universes = (uu___256_1512.erase_universes);
            allow_unbound_universes = (uu___256_1512.allow_unbound_universes);
            reify_ = (uu___256_1512.reify_);
            compress_uvars = (uu___256_1512.compress_uvars);
            no_full_norm = (uu___256_1512.no_full_norm);
            check_no_uvars = (uu___256_1512.check_no_uvars);
            unmeta = (uu___256_1512.unmeta);
            unascribe = (uu___256_1512.unascribe);
            in_full_norm_request = (uu___256_1512.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___256_1512.weakly_reduce_scrutinee);
            nbe_step = true
          }
  
let (to_fsteps : FStar_TypeChecker_Env.step Prims.list -> fsteps) =
  fun s  -> FStar_List.fold_right fstep_add_one s default_steps 
type psc =
  {
  psc_range: FStar_Range.range ;
  psc_subst: unit -> FStar_Syntax_Syntax.subst_t }
let (__proj__Mkpsc__item__psc_range : psc -> FStar_Range.range) =
  fun projectee  ->
    match projectee with
    | { psc_range = __fname__psc_range; psc_subst = __fname__psc_subst;_} ->
        __fname__psc_range
  
let (__proj__Mkpsc__item__psc_subst :
  psc -> unit -> FStar_Syntax_Syntax.subst_t) =
  fun projectee  ->
    match projectee with
    | { psc_range = __fname__psc_range; psc_subst = __fname__psc_subst;_} ->
        __fname__psc_subst
  
let (null_psc : psc) =
  { psc_range = FStar_Range.dummyRange; psc_subst = (fun uu____1565  -> []) } 
let (psc_range : psc -> FStar_Range.range) = fun psc  -> psc.psc_range 
let (psc_subst : psc -> FStar_Syntax_Syntax.subst_t) =
  fun psc  -> psc.psc_subst () 
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
  print_normalized: Prims.bool }
let (__proj__Mkdebug_switches__item__gen : debug_switches -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { gen = __fname__gen; top = __fname__top; cfg = __fname__cfg;
        primop = __fname__primop; unfolding = __fname__unfolding;
        b380 = __fname__b380; wpe = __fname__wpe;
        norm_delayed = __fname__norm_delayed;
        print_normalized = __fname__print_normalized;_} -> __fname__gen
  
let (__proj__Mkdebug_switches__item__top : debug_switches -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { gen = __fname__gen; top = __fname__top; cfg = __fname__cfg;
        primop = __fname__primop; unfolding = __fname__unfolding;
        b380 = __fname__b380; wpe = __fname__wpe;
        norm_delayed = __fname__norm_delayed;
        print_normalized = __fname__print_normalized;_} -> __fname__top
  
let (__proj__Mkdebug_switches__item__cfg : debug_switches -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { gen = __fname__gen; top = __fname__top; cfg = __fname__cfg;
        primop = __fname__primop; unfolding = __fname__unfolding;
        b380 = __fname__b380; wpe = __fname__wpe;
        norm_delayed = __fname__norm_delayed;
        print_normalized = __fname__print_normalized;_} -> __fname__cfg
  
let (__proj__Mkdebug_switches__item__primop : debug_switches -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { gen = __fname__gen; top = __fname__top; cfg = __fname__cfg;
        primop = __fname__primop; unfolding = __fname__unfolding;
        b380 = __fname__b380; wpe = __fname__wpe;
        norm_delayed = __fname__norm_delayed;
        print_normalized = __fname__print_normalized;_} -> __fname__primop
  
let (__proj__Mkdebug_switches__item__unfolding :
  debug_switches -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { gen = __fname__gen; top = __fname__top; cfg = __fname__cfg;
        primop = __fname__primop; unfolding = __fname__unfolding;
        b380 = __fname__b380; wpe = __fname__wpe;
        norm_delayed = __fname__norm_delayed;
        print_normalized = __fname__print_normalized;_} -> __fname__unfolding
  
let (__proj__Mkdebug_switches__item__b380 : debug_switches -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { gen = __fname__gen; top = __fname__top; cfg = __fname__cfg;
        primop = __fname__primop; unfolding = __fname__unfolding;
        b380 = __fname__b380; wpe = __fname__wpe;
        norm_delayed = __fname__norm_delayed;
        print_normalized = __fname__print_normalized;_} -> __fname__b380
  
let (__proj__Mkdebug_switches__item__wpe : debug_switches -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { gen = __fname__gen; top = __fname__top; cfg = __fname__cfg;
        primop = __fname__primop; unfolding = __fname__unfolding;
        b380 = __fname__b380; wpe = __fname__wpe;
        norm_delayed = __fname__norm_delayed;
        print_normalized = __fname__print_normalized;_} -> __fname__wpe
  
let (__proj__Mkdebug_switches__item__norm_delayed :
  debug_switches -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { gen = __fname__gen; top = __fname__top; cfg = __fname__cfg;
        primop = __fname__primop; unfolding = __fname__unfolding;
        b380 = __fname__b380; wpe = __fname__wpe;
        norm_delayed = __fname__norm_delayed;
        print_normalized = __fname__print_normalized;_} ->
        __fname__norm_delayed
  
let (__proj__Mkdebug_switches__item__print_normalized :
  debug_switches -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { gen = __fname__gen; top = __fname__top; cfg = __fname__cfg;
        primop = __fname__primop; unfolding = __fname__unfolding;
        b380 = __fname__b380; wpe = __fname__wpe;
        norm_delayed = __fname__norm_delayed;
        print_normalized = __fname__print_normalized;_} ->
        __fname__print_normalized
  
type primitive_step =
  {
  name: FStar_Ident.lid ;
  arity: Prims.int ;
  univ_arity: Prims.int ;
  auto_reflect: Prims.int FStar_Pervasives_Native.option ;
  strong_reduction_ok: Prims.bool ;
  requires_binder_substitution: Prims.bool ;
  interpretation:
    psc ->
      FStar_Syntax_Embeddings.norm_cb ->
        FStar_Syntax_Syntax.args ->
          FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
    ;
  interpretation_nbe:
    FStar_TypeChecker_NBETerm.nbe_cbs ->
      FStar_TypeChecker_NBETerm.args ->
        FStar_TypeChecker_NBETerm.t FStar_Pervasives_Native.option
    }
let (__proj__Mkprimitive_step__item__name :
  primitive_step -> FStar_Ident.lid) =
  fun projectee  ->
    match projectee with
    | { name = __fname__name; arity = __fname__arity;
        univ_arity = __fname__univ_arity;
        auto_reflect = __fname__auto_reflect;
        strong_reduction_ok = __fname__strong_reduction_ok;
        requires_binder_substitution = __fname__requires_binder_substitution;
        interpretation = __fname__interpretation;
        interpretation_nbe = __fname__interpretation_nbe;_} -> __fname__name
  
let (__proj__Mkprimitive_step__item__arity : primitive_step -> Prims.int) =
  fun projectee  ->
    match projectee with
    | { name = __fname__name; arity = __fname__arity;
        univ_arity = __fname__univ_arity;
        auto_reflect = __fname__auto_reflect;
        strong_reduction_ok = __fname__strong_reduction_ok;
        requires_binder_substitution = __fname__requires_binder_substitution;
        interpretation = __fname__interpretation;
        interpretation_nbe = __fname__interpretation_nbe;_} -> __fname__arity
  
let (__proj__Mkprimitive_step__item__univ_arity :
  primitive_step -> Prims.int) =
  fun projectee  ->
    match projectee with
    | { name = __fname__name; arity = __fname__arity;
        univ_arity = __fname__univ_arity;
        auto_reflect = __fname__auto_reflect;
        strong_reduction_ok = __fname__strong_reduction_ok;
        requires_binder_substitution = __fname__requires_binder_substitution;
        interpretation = __fname__interpretation;
        interpretation_nbe = __fname__interpretation_nbe;_} ->
        __fname__univ_arity
  
let (__proj__Mkprimitive_step__item__auto_reflect :
  primitive_step -> Prims.int FStar_Pervasives_Native.option) =
  fun projectee  ->
    match projectee with
    | { name = __fname__name; arity = __fname__arity;
        univ_arity = __fname__univ_arity;
        auto_reflect = __fname__auto_reflect;
        strong_reduction_ok = __fname__strong_reduction_ok;
        requires_binder_substitution = __fname__requires_binder_substitution;
        interpretation = __fname__interpretation;
        interpretation_nbe = __fname__interpretation_nbe;_} ->
        __fname__auto_reflect
  
let (__proj__Mkprimitive_step__item__strong_reduction_ok :
  primitive_step -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { name = __fname__name; arity = __fname__arity;
        univ_arity = __fname__univ_arity;
        auto_reflect = __fname__auto_reflect;
        strong_reduction_ok = __fname__strong_reduction_ok;
        requires_binder_substitution = __fname__requires_binder_substitution;
        interpretation = __fname__interpretation;
        interpretation_nbe = __fname__interpretation_nbe;_} ->
        __fname__strong_reduction_ok
  
let (__proj__Mkprimitive_step__item__requires_binder_substitution :
  primitive_step -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { name = __fname__name; arity = __fname__arity;
        univ_arity = __fname__univ_arity;
        auto_reflect = __fname__auto_reflect;
        strong_reduction_ok = __fname__strong_reduction_ok;
        requires_binder_substitution = __fname__requires_binder_substitution;
        interpretation = __fname__interpretation;
        interpretation_nbe = __fname__interpretation_nbe;_} ->
        __fname__requires_binder_substitution
  
let (__proj__Mkprimitive_step__item__interpretation :
  primitive_step ->
    psc ->
      FStar_Syntax_Embeddings.norm_cb ->
        FStar_Syntax_Syntax.args ->
          FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun projectee  ->
    match projectee with
    | { name = __fname__name; arity = __fname__arity;
        univ_arity = __fname__univ_arity;
        auto_reflect = __fname__auto_reflect;
        strong_reduction_ok = __fname__strong_reduction_ok;
        requires_binder_substitution = __fname__requires_binder_substitution;
        interpretation = __fname__interpretation;
        interpretation_nbe = __fname__interpretation_nbe;_} ->
        __fname__interpretation
  
let (__proj__Mkprimitive_step__item__interpretation_nbe :
  primitive_step ->
    FStar_TypeChecker_NBETerm.nbe_cbs ->
      FStar_TypeChecker_NBETerm.args ->
        FStar_TypeChecker_NBETerm.t FStar_Pervasives_Native.option)
  =
  fun projectee  ->
    match projectee with
    | { name = __fname__name; arity = __fname__arity;
        univ_arity = __fname__univ_arity;
        auto_reflect = __fname__auto_reflect;
        strong_reduction_ok = __fname__strong_reduction_ok;
        requires_binder_substitution = __fname__requires_binder_substitution;
        interpretation = __fname__interpretation;
        interpretation_nbe = __fname__interpretation_nbe;_} ->
        __fname__interpretation_nbe
  
type cfg =
  {
  steps: fsteps ;
  tcenv: FStar_TypeChecker_Env.env ;
  debug: debug_switches ;
  delta_level: FStar_TypeChecker_Env.delta_level Prims.list ;
  primitive_steps: primitive_step FStar_Util.psmap ;
  strong: Prims.bool ;
  memoize_lazy: Prims.bool ;
  normalize_pure_lets: Prims.bool ;
  reifying: Prims.bool }
let (__proj__Mkcfg__item__steps : cfg -> fsteps) =
  fun projectee  ->
    match projectee with
    | { steps = __fname__steps; tcenv = __fname__tcenv;
        debug = __fname__debug; delta_level = __fname__delta_level;
        primitive_steps = __fname__primitive_steps; strong = __fname__strong;
        memoize_lazy = __fname__memoize_lazy;
        normalize_pure_lets = __fname__normalize_pure_lets;
        reifying = __fname__reifying;_} -> __fname__steps
  
let (__proj__Mkcfg__item__tcenv : cfg -> FStar_TypeChecker_Env.env) =
  fun projectee  ->
    match projectee with
    | { steps = __fname__steps; tcenv = __fname__tcenv;
        debug = __fname__debug; delta_level = __fname__delta_level;
        primitive_steps = __fname__primitive_steps; strong = __fname__strong;
        memoize_lazy = __fname__memoize_lazy;
        normalize_pure_lets = __fname__normalize_pure_lets;
        reifying = __fname__reifying;_} -> __fname__tcenv
  
let (__proj__Mkcfg__item__debug : cfg -> debug_switches) =
  fun projectee  ->
    match projectee with
    | { steps = __fname__steps; tcenv = __fname__tcenv;
        debug = __fname__debug; delta_level = __fname__delta_level;
        primitive_steps = __fname__primitive_steps; strong = __fname__strong;
        memoize_lazy = __fname__memoize_lazy;
        normalize_pure_lets = __fname__normalize_pure_lets;
        reifying = __fname__reifying;_} -> __fname__debug
  
let (__proj__Mkcfg__item__delta_level :
  cfg -> FStar_TypeChecker_Env.delta_level Prims.list) =
  fun projectee  ->
    match projectee with
    | { steps = __fname__steps; tcenv = __fname__tcenv;
        debug = __fname__debug; delta_level = __fname__delta_level;
        primitive_steps = __fname__primitive_steps; strong = __fname__strong;
        memoize_lazy = __fname__memoize_lazy;
        normalize_pure_lets = __fname__normalize_pure_lets;
        reifying = __fname__reifying;_} -> __fname__delta_level
  
let (__proj__Mkcfg__item__primitive_steps :
  cfg -> primitive_step FStar_Util.psmap) =
  fun projectee  ->
    match projectee with
    | { steps = __fname__steps; tcenv = __fname__tcenv;
        debug = __fname__debug; delta_level = __fname__delta_level;
        primitive_steps = __fname__primitive_steps; strong = __fname__strong;
        memoize_lazy = __fname__memoize_lazy;
        normalize_pure_lets = __fname__normalize_pure_lets;
        reifying = __fname__reifying;_} -> __fname__primitive_steps
  
let (__proj__Mkcfg__item__strong : cfg -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { steps = __fname__steps; tcenv = __fname__tcenv;
        debug = __fname__debug; delta_level = __fname__delta_level;
        primitive_steps = __fname__primitive_steps; strong = __fname__strong;
        memoize_lazy = __fname__memoize_lazy;
        normalize_pure_lets = __fname__normalize_pure_lets;
        reifying = __fname__reifying;_} -> __fname__strong
  
let (__proj__Mkcfg__item__memoize_lazy : cfg -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { steps = __fname__steps; tcenv = __fname__tcenv;
        debug = __fname__debug; delta_level = __fname__delta_level;
        primitive_steps = __fname__primitive_steps; strong = __fname__strong;
        memoize_lazy = __fname__memoize_lazy;
        normalize_pure_lets = __fname__normalize_pure_lets;
        reifying = __fname__reifying;_} -> __fname__memoize_lazy
  
let (__proj__Mkcfg__item__normalize_pure_lets : cfg -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { steps = __fname__steps; tcenv = __fname__tcenv;
        debug = __fname__debug; delta_level = __fname__delta_level;
        primitive_steps = __fname__primitive_steps; strong = __fname__strong;
        memoize_lazy = __fname__memoize_lazy;
        normalize_pure_lets = __fname__normalize_pure_lets;
        reifying = __fname__reifying;_} -> __fname__normalize_pure_lets
  
let (__proj__Mkcfg__item__reifying : cfg -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { steps = __fname__steps; tcenv = __fname__tcenv;
        debug = __fname__debug; delta_level = __fname__delta_level;
        primitive_steps = __fname__primitive_steps; strong = __fname__strong;
        memoize_lazy = __fname__memoize_lazy;
        normalize_pure_lets = __fname__normalize_pure_lets;
        reifying = __fname__reifying;_} -> __fname__reifying
  
let (cfg_to_string : cfg -> Prims.string) =
  fun cfg  ->
    let uu____2384 =
      let uu____2387 =
        let uu____2390 =
          let uu____2391 = steps_to_string cfg.steps  in
          FStar_Util.format1 "  steps = %s" uu____2391  in
        [uu____2390; "}"]  in
      "{" :: uu____2387  in
    FStar_String.concat "\n" uu____2384
  
let (cfg_env : cfg -> FStar_TypeChecker_Env.env) = fun cfg  -> cfg.tcenv 
let (add_steps :
  primitive_step FStar_Util.psmap ->
    primitive_step Prims.list -> primitive_step FStar_Util.psmap)
  =
  fun m  ->
    fun l  ->
      FStar_List.fold_right
        (fun p  ->
           fun m1  ->
             let uu____2428 = FStar_Ident.text_of_lid p.name  in
             FStar_Util.psmap_add m1 uu____2428 p) l m
  
let (prim_from_list :
  primitive_step Prims.list -> primitive_step FStar_Util.psmap) =
  fun l  ->
    let uu____2442 = FStar_Util.psmap_empty ()  in add_steps uu____2442 l
  
let (find_prim_step :
  cfg ->
    FStar_Syntax_Syntax.fv -> primitive_step FStar_Pervasives_Native.option)
  =
  fun cfg  ->
    fun fv  ->
      let uu____2457 =
        FStar_Ident.text_of_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
         in
      FStar_Util.psmap_try_find cfg.primitive_steps uu____2457
  
let (is_prim_step : cfg -> FStar_Syntax_Syntax.fv -> Prims.bool) =
  fun cfg  ->
    fun fv  ->
      let uu____2468 =
        let uu____2471 =
          FStar_Ident.text_of_lid
            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
           in
        FStar_Util.psmap_try_find cfg.primitive_steps uu____2471  in
      FStar_Util.is_some uu____2468
  
let (log : cfg -> (unit -> unit) -> unit) =
  fun cfg  -> fun f  -> if (cfg.debug).gen then f () else () 
let (log_top : cfg -> (unit -> unit) -> unit) =
  fun cfg  -> fun f  -> if (cfg.debug).top then f () else () 
let (log_cfg : cfg -> (unit -> unit) -> unit) =
  fun cfg  -> fun f  -> if (cfg.debug).cfg then f () else () 
let (log_primops : cfg -> (unit -> unit) -> unit) =
  fun cfg  -> fun f  -> if (cfg.debug).primop then f () else () 
let (log_unfolding : cfg -> (unit -> unit) -> unit) =
  fun cfg  -> fun f  -> if (cfg.debug).unfolding then f () else () 
let (log_nbe : cfg -> (unit -> unit) -> unit) =
  fun cfg  ->
    fun f  ->
      let uu____2567 =
        FStar_All.pipe_left (FStar_TypeChecker_Env.debug cfg.tcenv)
          (FStar_Options.Other "NBE")
         in
      if uu____2567 then f () else ()
  
let embed_simple :
  'a .
    'a FStar_Syntax_Embeddings.embedding ->
      FStar_Range.range -> 'a -> FStar_Syntax_Syntax.term
  =
  fun emb  ->
    fun r  ->
      fun x  ->
        let uu____2597 = FStar_Syntax_Embeddings.embed emb x  in
        uu____2597 r FStar_Pervasives_Native.None
          FStar_Syntax_Embeddings.id_norm_cb
  
let try_unembed_simple :
  'a .
    'a FStar_Syntax_Embeddings.embedding ->
      FStar_Syntax_Syntax.term -> 'a FStar_Pervasives_Native.option
  =
  fun emb  ->
    fun x  ->
      let uu____2652 = FStar_Syntax_Embeddings.unembed emb x  in
      uu____2652 false FStar_Syntax_Embeddings.id_norm_cb
  
let mk :
  'Auu____2669 .
    'Auu____2669 ->
      FStar_Range.range -> 'Auu____2669 FStar_Syntax_Syntax.syntax
  =
  fun t  -> fun r  -> FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None r 
let (built_in_primitive_steps : primitive_step FStar_Util.psmap) =
  let arg_as_int1 a =
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a)
      (try_unembed_simple FStar_Syntax_Embeddings.e_int)
     in
  let arg_as_bool1 a =
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a)
      (try_unembed_simple FStar_Syntax_Embeddings.e_bool)
     in
  let arg_as_char1 a =
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a)
      (try_unembed_simple FStar_Syntax_Embeddings.e_char)
     in
  let arg_as_string1 a =
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a)
      (try_unembed_simple FStar_Syntax_Embeddings.e_string)
     in
  let arg_as_list1 e a =
    let uu____2783 =
      let uu____2792 = FStar_Syntax_Embeddings.e_list e  in
      try_unembed_simple uu____2792  in
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a) uu____2783  in
  let arg_as_bounded_int1 uu____2822 =
    match uu____2822 with
    | (a,uu____2836) ->
        let uu____2847 = FStar_Syntax_Util.head_and_args' a  in
        (match uu____2847 with
         | (hd1,args) ->
             let a1 = FStar_Syntax_Util.unlazy_emb a  in
             let uu____2891 =
               let uu____2906 =
                 let uu____2907 = FStar_Syntax_Subst.compress hd1  in
                 uu____2907.FStar_Syntax_Syntax.n  in
               (uu____2906, args)  in
             (match uu____2891 with
              | (FStar_Syntax_Syntax.Tm_fvar fv1,(arg,uu____2928)::[]) when
                  let uu____2963 =
                    FStar_Ident.text_of_lid
                      (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                     in
                  FStar_Util.ends_with uu____2963 "int_to_t" ->
                  let arg1 = FStar_Syntax_Util.unlazy_emb arg  in
                  let uu____2965 =
                    let uu____2966 = FStar_Syntax_Subst.compress arg1  in
                    uu____2966.FStar_Syntax_Syntax.n  in
                  (match uu____2965 with
                   | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
                       (i,FStar_Pervasives_Native.None )) ->
                       let uu____2986 =
                         let uu____2991 = FStar_BigInt.big_int_of_string i
                            in
                         (fv1, uu____2991)  in
                       FStar_Pervasives_Native.Some uu____2986
                   | uu____2996 -> FStar_Pervasives_Native.None)
              | uu____3001 -> FStar_Pervasives_Native.None))
     in
  let lift_unary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a)::[] ->
        let uu____3063 = f a  in FStar_Pervasives_Native.Some uu____3063
    | uu____3064 -> FStar_Pervasives_Native.None  in
  let lift_binary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a0)::(FStar_Pervasives_Native.Some
        a1)::[] ->
        let uu____3120 = f a0 a1  in FStar_Pervasives_Native.Some uu____3120
    | uu____3121 -> FStar_Pervasives_Native.None  in
  let unary_op1 as_a f res norm_cb args =
    let uu____3190 = FStar_List.map as_a args  in
    lift_unary (f res.psc_range) uu____3190  in
  let binary_op1 as_a f res n1 args =
    let uu____3274 = FStar_List.map as_a args  in
    lift_binary (f res.psc_range) uu____3274  in
  let as_primitive_step is_strong uu____3327 =
    match uu____3327 with
    | (l,arity,u_arity,f,f_nbe) ->
        {
          name = l;
          arity;
          univ_arity = u_arity;
          auto_reflect = FStar_Pervasives_Native.None;
          strong_reduction_ok = is_strong;
          requires_binder_substitution = false;
          interpretation = f;
          interpretation_nbe = ((fun _cb  -> f_nbe))
        }
     in
  let unary_int_op1 f =
    unary_op1 arg_as_int1
      (fun r  ->
         fun x  ->
           let uu____3430 = f x  in
           embed_simple FStar_Syntax_Embeddings.e_int r uu____3430)
     in
  let binary_int_op1 f =
    binary_op1 arg_as_int1
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____3473 = f x y  in
             embed_simple FStar_Syntax_Embeddings.e_int r uu____3473)
     in
  let unary_bool_op1 f =
    unary_op1 arg_as_bool1
      (fun r  ->
         fun x  ->
           let uu____3509 = f x  in
           embed_simple FStar_Syntax_Embeddings.e_bool r uu____3509)
     in
  let binary_bool_op1 f =
    binary_op1 arg_as_bool1
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____3552 = f x y  in
             embed_simple FStar_Syntax_Embeddings.e_bool r uu____3552)
     in
  let binary_string_op1 f =
    binary_op1 arg_as_string1
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____3595 = f x y  in
             embed_simple FStar_Syntax_Embeddings.e_string r uu____3595)
     in
  let mixed_binary_op1 as_a as_b embed_c f res _norm_cb args =
    match args with
    | a::b::[] ->
        let uu____3748 =
          let uu____3757 = as_a a  in
          let uu____3760 = as_b b  in (uu____3757, uu____3760)  in
        (match uu____3748 with
         | (FStar_Pervasives_Native.Some a1,FStar_Pervasives_Native.Some b1)
             ->
             let uu____3775 =
               let uu____3776 = f res.psc_range a1 b1  in
               embed_c res.psc_range uu____3776  in
             FStar_Pervasives_Native.Some uu____3775
         | uu____3777 -> FStar_Pervasives_Native.None)
    | uu____3786 -> FStar_Pervasives_Native.None  in
  let list_of_string'1 rng s =
    let name l =
      let uu____3806 =
        let uu____3807 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
            FStar_Pervasives_Native.None
           in
        FStar_Syntax_Syntax.Tm_fvar uu____3807  in
      mk uu____3806 rng  in
    let char_t = name FStar_Parser_Const.char_lid  in
    let charterm c =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c)) rng  in
    let uu____3821 =
      let uu____3824 = FStar_String.list_of_string s  in
      FStar_List.map charterm uu____3824  in
    FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu____3821  in
  let string_of_list'1 rng l =
    let s = FStar_String.string_of_list l  in FStar_Syntax_Util.exp_string s
     in
  let string_compare'1 rng s1 s2 =
    let r = FStar_String.compare s1 s2  in
    let uu____3866 =
      let uu____3867 = FStar_Util.string_of_int r  in
      FStar_BigInt.big_int_of_string uu____3867  in
    embed_simple FStar_Syntax_Embeddings.e_int rng uu____3866  in
  let string_concat'1 psc _n args =
    match args with
    | a1::a2::[] ->
        let uu____3954 = arg_as_string1 a1  in
        (match uu____3954 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____3960 =
               arg_as_list1 FStar_Syntax_Embeddings.e_string a2  in
             (match uu____3960 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2  in
                  let uu____3973 =
                    embed_simple FStar_Syntax_Embeddings.e_string
                      psc.psc_range r
                     in
                  FStar_Pervasives_Native.Some uu____3973
              | uu____3974 -> FStar_Pervasives_Native.None)
         | uu____3979 -> FStar_Pervasives_Native.None)
    | uu____3982 -> FStar_Pervasives_Native.None  in
  let string_split'1 psc _norm_cb args =
    match args with
    | a1::a2::[] ->
        let uu____4065 = arg_as_list1 FStar_Syntax_Embeddings.e_char a1  in
        (match uu____4065 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____4081 = arg_as_string1 a2  in
             (match uu____4081 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.split s1 s2  in
                  let uu____4090 =
                    let uu____4091 =
                      FStar_Syntax_Embeddings.e_list
                        FStar_Syntax_Embeddings.e_string
                       in
                    embed_simple uu____4091 psc.psc_range r  in
                  FStar_Pervasives_Native.Some uu____4090
              | uu____4098 -> FStar_Pervasives_Native.None)
         | uu____4101 -> FStar_Pervasives_Native.None)
    | uu____4107 -> FStar_Pervasives_Native.None  in
  let string_substring'1 psc _norm_cb args =
    match args with
    | a1::a2::a3::[] ->
        let uu____4147 =
          let uu____4160 = arg_as_string1 a1  in
          let uu____4163 = arg_as_int1 a2  in
          let uu____4166 = arg_as_int1 a3  in
          (uu____4160, uu____4163, uu____4166)  in
        (match uu____4147 with
         | (FStar_Pervasives_Native.Some s1,FStar_Pervasives_Native.Some
            n1,FStar_Pervasives_Native.Some n2) ->
             let n11 = FStar_BigInt.to_int_fs n1  in
             let n21 = FStar_BigInt.to_int_fs n2  in
             (try
                (fun uu___258_4193  ->
                   match () with
                   | () ->
                       let r = FStar_String.substring s1 n11 n21  in
                       let uu____4197 =
                         embed_simple FStar_Syntax_Embeddings.e_string
                           psc.psc_range r
                          in
                       FStar_Pervasives_Native.Some uu____4197) ()
              with | uu___257_4199 -> FStar_Pervasives_Native.None)
         | uu____4202 -> FStar_Pervasives_Native.None)
    | uu____4215 -> FStar_Pervasives_Native.None  in
  let string_of_int1 rng i =
    let uu____4229 = FStar_BigInt.string_of_big_int i  in
    embed_simple FStar_Syntax_Embeddings.e_string rng uu____4229  in
  let string_of_bool1 rng b =
    embed_simple FStar_Syntax_Embeddings.e_string rng
      (if b then "true" else "false")
     in
  let mk_range1 psc _norm_cb args =
    match args with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____4275 =
          let uu____4296 = arg_as_string1 fn  in
          let uu____4299 = arg_as_int1 from_line  in
          let uu____4302 = arg_as_int1 from_col  in
          let uu____4305 = arg_as_int1 to_line  in
          let uu____4308 = arg_as_int1 to_col  in
          (uu____4296, uu____4299, uu____4302, uu____4305, uu____4308)  in
        (match uu____4275 with
         | (FStar_Pervasives_Native.Some fn1,FStar_Pervasives_Native.Some
            from_l,FStar_Pervasives_Native.Some
            from_c,FStar_Pervasives_Native.Some
            to_l,FStar_Pervasives_Native.Some to_c) ->
             let r =
               let uu____4339 =
                 let uu____4340 = FStar_BigInt.to_int_fs from_l  in
                 let uu____4341 = FStar_BigInt.to_int_fs from_c  in
                 FStar_Range.mk_pos uu____4340 uu____4341  in
               let uu____4342 =
                 let uu____4343 = FStar_BigInt.to_int_fs to_l  in
                 let uu____4344 = FStar_BigInt.to_int_fs to_c  in
                 FStar_Range.mk_pos uu____4343 uu____4344  in
               FStar_Range.mk_range fn1 uu____4339 uu____4342  in
             let uu____4345 =
               embed_simple FStar_Syntax_Embeddings.e_range psc.psc_range r
                in
             FStar_Pervasives_Native.Some uu____4345
         | uu____4346 -> FStar_Pervasives_Native.None)
    | uu____4367 -> FStar_Pervasives_Native.None  in
  let decidable_eq1 neg psc _norm_cb args =
    let r = psc.psc_range  in
    let tru =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool true)) r
       in
    let fal =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool false)) r
       in
    match args with
    | (_typ,uu____4409)::(a1,uu____4411)::(a2,uu____4413)::[] ->
        let uu____4470 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____4470 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some (if neg then fal else tru)
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some (if neg then tru else fal)
         | uu____4475 -> FStar_Pervasives_Native.None)
    | uu____4476 -> failwith "Unexpected number of arguments"  in
  let prims_to_fstar_range_step1 psc _norm_cb args =
    match args with
    | (a1,uu____4520)::[] ->
        let uu____4537 =
          try_unembed_simple FStar_Syntax_Embeddings.e_range a1  in
        (match uu____4537 with
         | FStar_Pervasives_Native.Some r ->
             let uu____4543 =
               embed_simple FStar_Syntax_Embeddings.e_range psc.psc_range r
                in
             FStar_Pervasives_Native.Some uu____4543
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
    | uu____4544 -> failwith "Unexpected number of arguments"  in
  let bogus_cbs =
    {
      FStar_TypeChecker_NBETerm.iapp = (fun h  -> fun _args  -> h);
      FStar_TypeChecker_NBETerm.translate =
        (fun uu____4563  -> failwith "bogus_cbs translate")
    }  in
  let basic_ops =
    let uu____4595 =
      let uu____4624 =
        FStar_TypeChecker_NBETerm.unary_int_op
          (fun x  -> FStar_BigInt.minus_big_int x)
         in
      (FStar_Parser_Const.op_Minus, (Prims.parse_int "1"),
        (Prims.parse_int "0"),
        (unary_int_op1 (fun x  -> FStar_BigInt.minus_big_int x)), uu____4624)
       in
    let uu____4655 =
      let uu____4686 =
        let uu____4715 =
          FStar_TypeChecker_NBETerm.binary_int_op
            (fun x  -> fun y  -> FStar_BigInt.add_big_int x y)
           in
        (FStar_Parser_Const.op_Addition, (Prims.parse_int "2"),
          (Prims.parse_int "0"),
          (binary_int_op1 (fun x  -> fun y  -> FStar_BigInt.add_big_int x y)),
          uu____4715)
         in
      let uu____4752 =
        let uu____4783 =
          let uu____4812 =
            FStar_TypeChecker_NBETerm.binary_int_op
              (fun x  -> fun y  -> FStar_BigInt.sub_big_int x y)
             in
          (FStar_Parser_Const.op_Subtraction, (Prims.parse_int "2"),
            (Prims.parse_int "0"),
            (binary_int_op1
               (fun x  -> fun y  -> FStar_BigInt.sub_big_int x y)),
            uu____4812)
           in
        let uu____4849 =
          let uu____4880 =
            let uu____4909 =
              FStar_TypeChecker_NBETerm.binary_int_op
                (fun x  -> fun y  -> FStar_BigInt.mult_big_int x y)
               in
            (FStar_Parser_Const.op_Multiply, (Prims.parse_int "2"),
              (Prims.parse_int "0"),
              (binary_int_op1
                 (fun x  -> fun y  -> FStar_BigInt.mult_big_int x y)),
              uu____4909)
             in
          let uu____4946 =
            let uu____4977 =
              let uu____5006 =
                FStar_TypeChecker_NBETerm.binary_int_op
                  (fun x  -> fun y  -> FStar_BigInt.div_big_int x y)
                 in
              (FStar_Parser_Const.op_Division, (Prims.parse_int "2"),
                (Prims.parse_int "0"),
                (binary_int_op1
                   (fun x  -> fun y  -> FStar_BigInt.div_big_int x y)),
                uu____5006)
               in
            let uu____5043 =
              let uu____5074 =
                let uu____5103 =
                  FStar_TypeChecker_NBETerm.binary_op
                    FStar_TypeChecker_NBETerm.arg_as_int
                    (fun x  ->
                       fun y  ->
                         let uu____5115 = FStar_BigInt.lt_big_int x y  in
                         FStar_TypeChecker_NBETerm.embed
                           FStar_TypeChecker_NBETerm.e_bool bogus_cbs
                           uu____5115)
                   in
                (FStar_Parser_Const.op_LT, (Prims.parse_int "2"),
                  (Prims.parse_int "0"),
                  (binary_op1 arg_as_int1
                     (fun r  ->
                        fun x  ->
                          fun y  ->
                            let uu____5141 = FStar_BigInt.lt_big_int x y  in
                            embed_simple FStar_Syntax_Embeddings.e_bool r
                              uu____5141)), uu____5103)
                 in
              let uu____5142 =
                let uu____5173 =
                  let uu____5202 =
                    FStar_TypeChecker_NBETerm.binary_op
                      FStar_TypeChecker_NBETerm.arg_as_int
                      (fun x  ->
                         fun y  ->
                           let uu____5214 = FStar_BigInt.le_big_int x y  in
                           FStar_TypeChecker_NBETerm.embed
                             FStar_TypeChecker_NBETerm.e_bool bogus_cbs
                             uu____5214)
                     in
                  (FStar_Parser_Const.op_LTE, (Prims.parse_int "2"),
                    (Prims.parse_int "0"),
                    (binary_op1 arg_as_int1
                       (fun r  ->
                          fun x  ->
                            fun y  ->
                              let uu____5240 = FStar_BigInt.le_big_int x y
                                 in
                              embed_simple FStar_Syntax_Embeddings.e_bool r
                                uu____5240)), uu____5202)
                   in
                let uu____5241 =
                  let uu____5272 =
                    let uu____5301 =
                      FStar_TypeChecker_NBETerm.binary_op
                        FStar_TypeChecker_NBETerm.arg_as_int
                        (fun x  ->
                           fun y  ->
                             let uu____5313 = FStar_BigInt.gt_big_int x y  in
                             FStar_TypeChecker_NBETerm.embed
                               FStar_TypeChecker_NBETerm.e_bool bogus_cbs
                               uu____5313)
                       in
                    (FStar_Parser_Const.op_GT, (Prims.parse_int "2"),
                      (Prims.parse_int "0"),
                      (binary_op1 arg_as_int1
                         (fun r  ->
                            fun x  ->
                              fun y  ->
                                let uu____5339 = FStar_BigInt.gt_big_int x y
                                   in
                                embed_simple FStar_Syntax_Embeddings.e_bool r
                                  uu____5339)), uu____5301)
                     in
                  let uu____5340 =
                    let uu____5371 =
                      let uu____5400 =
                        FStar_TypeChecker_NBETerm.binary_op
                          FStar_TypeChecker_NBETerm.arg_as_int
                          (fun x  ->
                             fun y  ->
                               let uu____5412 = FStar_BigInt.ge_big_int x y
                                  in
                               FStar_TypeChecker_NBETerm.embed
                                 FStar_TypeChecker_NBETerm.e_bool bogus_cbs
                                 uu____5412)
                         in
                      (FStar_Parser_Const.op_GTE, (Prims.parse_int "2"),
                        (Prims.parse_int "0"),
                        (binary_op1 arg_as_int1
                           (fun r  ->
                              fun x  ->
                                fun y  ->
                                  let uu____5438 =
                                    FStar_BigInt.ge_big_int x y  in
                                  embed_simple FStar_Syntax_Embeddings.e_bool
                                    r uu____5438)), uu____5400)
                       in
                    let uu____5439 =
                      let uu____5470 =
                        let uu____5499 =
                          FStar_TypeChecker_NBETerm.binary_int_op
                            (fun x  -> fun y  -> FStar_BigInt.mod_big_int x y)
                           in
                        (FStar_Parser_Const.op_Modulus,
                          (Prims.parse_int "2"), (Prims.parse_int "0"),
                          (binary_int_op1
                             (fun x  ->
                                fun y  -> FStar_BigInt.mod_big_int x y)),
                          uu____5499)
                         in
                      let uu____5536 =
                        let uu____5567 =
                          let uu____5596 =
                            FStar_TypeChecker_NBETerm.unary_bool_op
                              (fun x  -> Prims.op_Negation x)
                             in
                          (FStar_Parser_Const.op_Negation,
                            (Prims.parse_int "1"), (Prims.parse_int "0"),
                            (unary_bool_op1 (fun x  -> Prims.op_Negation x)),
                            uu____5596)
                           in
                        let uu____5627 =
                          let uu____5658 =
                            let uu____5687 =
                              FStar_TypeChecker_NBETerm.binary_bool_op
                                (fun x  -> fun y  -> x && y)
                               in
                            (FStar_Parser_Const.op_And,
                              (Prims.parse_int "2"), (Prims.parse_int "0"),
                              (binary_bool_op1 (fun x  -> fun y  -> x && y)),
                              uu____5687)
                             in
                          let uu____5724 =
                            let uu____5755 =
                              let uu____5784 =
                                FStar_TypeChecker_NBETerm.binary_bool_op
                                  (fun x  -> fun y  -> x || y)
                                 in
                              (FStar_Parser_Const.op_Or,
                                (Prims.parse_int "2"), (Prims.parse_int "0"),
                                (binary_bool_op1 (fun x  -> fun y  -> x || y)),
                                uu____5784)
                               in
                            let uu____5821 =
                              let uu____5852 =
                                let uu____5881 =
                                  FStar_TypeChecker_NBETerm.binary_string_op
                                    (fun x  -> fun y  -> Prims.strcat x y)
                                   in
                                (FStar_Parser_Const.strcat_lid,
                                  (Prims.parse_int "2"),
                                  (Prims.parse_int "0"),
                                  (binary_string_op1
                                     (fun x  -> fun y  -> Prims.strcat x y)),
                                  uu____5881)
                                 in
                              let uu____5918 =
                                let uu____5949 =
                                  let uu____5978 =
                                    FStar_TypeChecker_NBETerm.binary_string_op
                                      (fun x  -> fun y  -> Prims.strcat x y)
                                     in
                                  (FStar_Parser_Const.strcat_lid',
                                    (Prims.parse_int "2"),
                                    (Prims.parse_int "0"),
                                    (binary_string_op1
                                       (fun x  -> fun y  -> Prims.strcat x y)),
                                    uu____5978)
                                   in
                                let uu____6015 =
                                  let uu____6046 =
                                    let uu____6077 =
                                      let uu____6106 =
                                        FStar_TypeChecker_NBETerm.unary_op
                                          FStar_TypeChecker_NBETerm.arg_as_int
                                          FStar_TypeChecker_NBETerm.string_of_int
                                         in
                                      (FStar_Parser_Const.string_of_int_lid,
                                        (Prims.parse_int "1"),
                                        (Prims.parse_int "0"),
                                        (unary_op1 arg_as_int1 string_of_int1),
                                        uu____6106)
                                       in
                                    let uu____6131 =
                                      let uu____6162 =
                                        let uu____6191 =
                                          FStar_TypeChecker_NBETerm.unary_op
                                            FStar_TypeChecker_NBETerm.arg_as_bool
                                            FStar_TypeChecker_NBETerm.string_of_bool
                                           in
                                        (FStar_Parser_Const.string_of_bool_lid,
                                          (Prims.parse_int "1"),
                                          (Prims.parse_int "0"),
                                          (unary_op1 arg_as_bool1
                                             string_of_bool1), uu____6191)
                                         in
                                      let uu____6216 =
                                        let uu____6247 =
                                          let uu____6276 =
                                            FStar_TypeChecker_NBETerm.binary_op
                                              FStar_TypeChecker_NBETerm.arg_as_string
                                              FStar_TypeChecker_NBETerm.string_compare'
                                             in
                                          (FStar_Parser_Const.string_compare,
                                            (Prims.parse_int "2"),
                                            (Prims.parse_int "0"),
                                            (binary_op1 arg_as_string1
                                               string_compare'1), uu____6276)
                                           in
                                        let uu____6301 =
                                          let uu____6332 =
                                            let uu____6363 =
                                              let uu____6394 =
                                                let uu____6423 =
                                                  FStar_Parser_Const.p2l
                                                    ["FStar";
                                                    "String";
                                                    "list_of_string"]
                                                   in
                                                let uu____6424 =
                                                  FStar_TypeChecker_NBETerm.unary_op
                                                    FStar_TypeChecker_NBETerm.arg_as_string
                                                    FStar_TypeChecker_NBETerm.list_of_string'
                                                   in
                                                (uu____6423,
                                                  (Prims.parse_int "1"),
                                                  (Prims.parse_int "0"),
                                                  (unary_op1 arg_as_string1
                                                     list_of_string'1),
                                                  uu____6424)
                                                 in
                                              let uu____6449 =
                                                let uu____6480 =
                                                  let uu____6509 =
                                                    FStar_Parser_Const.p2l
                                                      ["FStar";
                                                      "String";
                                                      "string_of_list"]
                                                     in
                                                  let uu____6510 =
                                                    FStar_TypeChecker_NBETerm.unary_op
                                                      (FStar_TypeChecker_NBETerm.arg_as_list
                                                         FStar_TypeChecker_NBETerm.e_char)
                                                      FStar_TypeChecker_NBETerm.string_of_list'
                                                     in
                                                  (uu____6509,
                                                    (Prims.parse_int "1"),
                                                    (Prims.parse_int "0"),
                                                    (unary_op1
                                                       (arg_as_list1
                                                          FStar_Syntax_Embeddings.e_char)
                                                       string_of_list'1),
                                                    uu____6510)
                                                   in
                                                let uu____6543 =
                                                  let uu____6574 =
                                                    let uu____6603 =
                                                      FStar_Parser_Const.p2l
                                                        ["FStar";
                                                        "String";
                                                        "split"]
                                                       in
                                                    (uu____6603,
                                                      (Prims.parse_int "2"),
                                                      (Prims.parse_int "0"),
                                                      string_split'1,
                                                      FStar_TypeChecker_NBETerm.string_split')
                                                     in
                                                  let uu____6622 =
                                                    let uu____6653 =
                                                      let uu____6682 =
                                                        FStar_Parser_Const.p2l
                                                          ["FStar";
                                                          "String";
                                                          "substring"]
                                                         in
                                                      (uu____6682,
                                                        (Prims.parse_int "3"),
                                                        (Prims.parse_int "0"),
                                                        string_substring'1,
                                                        FStar_TypeChecker_NBETerm.string_substring')
                                                       in
                                                    let uu____6701 =
                                                      let uu____6732 =
                                                        let uu____6761 =
                                                          FStar_Parser_Const.p2l
                                                            ["FStar";
                                                            "String";
                                                            "concat"]
                                                           in
                                                        (uu____6761,
                                                          (Prims.parse_int "2"),
                                                          (Prims.parse_int "0"),
                                                          string_concat'1,
                                                          FStar_TypeChecker_NBETerm.string_concat')
                                                         in
                                                      let uu____6780 =
                                                        let uu____6811 =
                                                          let uu____6840 =
                                                            FStar_Parser_Const.p2l
                                                              ["Prims";
                                                              "mk_range"]
                                                             in
                                                          (uu____6840,
                                                            (Prims.parse_int "5"),
                                                            (Prims.parse_int "0"),
                                                            mk_range1,
                                                            FStar_TypeChecker_NBETerm.mk_range)
                                                           in
                                                        let uu____6859 =
                                                          let uu____6890 =
                                                            let uu____6919 =
                                                              FStar_Parser_Const.p2l
                                                                ["FStar";
                                                                "Range";
                                                                "prims_to_fstar_range"]
                                                               in
                                                            (uu____6919,
                                                              (Prims.parse_int "1"),
                                                              (Prims.parse_int "0"),
                                                              prims_to_fstar_range_step1,
                                                              FStar_TypeChecker_NBETerm.prims_to_fstar_range_step)
                                                             in
                                                          [uu____6890]  in
                                                        uu____6811 ::
                                                          uu____6859
                                                         in
                                                      uu____6732 ::
                                                        uu____6780
                                                       in
                                                    uu____6653 :: uu____6701
                                                     in
                                                  uu____6574 :: uu____6622
                                                   in
                                                uu____6480 :: uu____6543  in
                                              uu____6394 :: uu____6449  in
                                            (FStar_Parser_Const.op_notEq,
                                              (Prims.parse_int "3"),
                                              (Prims.parse_int "0"),
                                              (decidable_eq1 true),
                                              (FStar_TypeChecker_NBETerm.decidable_eq
                                                 true))
                                              :: uu____6363
                                             in
                                          (FStar_Parser_Const.op_Eq,
                                            (Prims.parse_int "3"),
                                            (Prims.parse_int "0"),
                                            (decidable_eq1 false),
                                            (FStar_TypeChecker_NBETerm.decidable_eq
                                               false))
                                            :: uu____6332
                                           in
                                        uu____6247 :: uu____6301  in
                                      uu____6162 :: uu____6216  in
                                    uu____6077 :: uu____6131  in
                                  (FStar_Parser_Const.str_make_lid,
                                    (Prims.parse_int "2"),
                                    (Prims.parse_int "0"),
                                    (mixed_binary_op1 arg_as_int1
                                       arg_as_char1
                                       (embed_simple
                                          FStar_Syntax_Embeddings.e_string)
                                       (fun r  ->
                                          fun x  ->
                                            fun y  ->
                                              let uu____7393 =
                                                FStar_BigInt.to_int_fs x  in
                                              FStar_String.make uu____7393 y)),
                                    (FStar_TypeChecker_NBETerm.mixed_binary_op
                                       FStar_TypeChecker_NBETerm.arg_as_int
                                       FStar_TypeChecker_NBETerm.arg_as_char
                                       (FStar_TypeChecker_NBETerm.embed
                                          FStar_TypeChecker_NBETerm.e_string
                                          bogus_cbs)
                                       (fun x  ->
                                          fun y  ->
                                            let uu____7401 =
                                              FStar_BigInt.to_int_fs x  in
                                            FStar_String.make uu____7401 y)))
                                    :: uu____6046
                                   in
                                uu____5949 :: uu____6015  in
                              uu____5852 :: uu____5918  in
                            uu____5755 :: uu____5821  in
                          uu____5658 :: uu____5724  in
                        uu____5567 :: uu____5627  in
                      uu____5470 :: uu____5536  in
                    uu____5371 :: uu____5439  in
                  uu____5272 :: uu____5340  in
                uu____5173 :: uu____5241  in
              uu____5074 :: uu____5142  in
            uu____4977 :: uu____5043  in
          uu____4880 :: uu____4946  in
        uu____4783 :: uu____4849  in
      uu____4686 :: uu____4752  in
    uu____4595 :: uu____4655  in
  let weak_ops = []  in
  let bounded_arith_ops =
    let bounded_signed_int_types = ["Int8"; "Int16"; "Int32"; "Int64"]  in
    let bounded_unsigned_int_types =
      ["UInt8"; "UInt16"; "UInt32"; "UInt64"; "UInt128"]  in
    let int_as_bounded1 r int_to_t1 n1 =
      let c = embed_simple FStar_Syntax_Embeddings.e_int r n1  in
      let int_to_t2 = FStar_Syntax_Syntax.fv_to_tm int_to_t1  in
      let uu____7938 =
        let uu____7943 =
          let uu____7944 = FStar_Syntax_Syntax.as_arg c  in [uu____7944]  in
        FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____7943  in
      uu____7938 FStar_Pervasives_Native.None r  in
    let add_sub_mul_v =
      FStar_All.pipe_right
        (FStar_List.append bounded_signed_int_types
           bounded_unsigned_int_types)
        (FStar_List.collect
           (fun m  ->
              let uu____8066 =
                let uu____8095 = FStar_Parser_Const.p2l ["FStar"; m; "add"]
                   in
                let uu____8096 =
                  FStar_TypeChecker_NBETerm.binary_op
                    FStar_TypeChecker_NBETerm.arg_as_bounded_int
                    (fun uu____8114  ->
                       fun uu____8115  ->
                         match (uu____8114, uu____8115) with
                         | ((int_to_t1,x),(uu____8134,y)) ->
                             let uu____8144 = FStar_BigInt.add_big_int x y
                                in
                             FStar_TypeChecker_NBETerm.int_as_bounded
                               int_to_t1 uu____8144)
                   in
                (uu____8095, (Prims.parse_int "2"), (Prims.parse_int "0"),
                  (binary_op1 arg_as_bounded_int1
                     (fun r  ->
                        fun uu____8176  ->
                          fun uu____8177  ->
                            match (uu____8176, uu____8177) with
                            | ((int_to_t1,x),(uu____8196,y)) ->
                                let uu____8206 = FStar_BigInt.add_big_int x y
                                   in
                                int_as_bounded1 r int_to_t1 uu____8206)),
                  uu____8096)
                 in
              let uu____8207 =
                let uu____8238 =
                  let uu____8267 = FStar_Parser_Const.p2l ["FStar"; m; "sub"]
                     in
                  let uu____8268 =
                    FStar_TypeChecker_NBETerm.binary_op
                      FStar_TypeChecker_NBETerm.arg_as_bounded_int
                      (fun uu____8286  ->
                         fun uu____8287  ->
                           match (uu____8286, uu____8287) with
                           | ((int_to_t1,x),(uu____8306,y)) ->
                               let uu____8316 = FStar_BigInt.sub_big_int x y
                                  in
                               FStar_TypeChecker_NBETerm.int_as_bounded
                                 int_to_t1 uu____8316)
                     in
                  (uu____8267, (Prims.parse_int "2"), (Prims.parse_int "0"),
                    (binary_op1 arg_as_bounded_int1
                       (fun r  ->
                          fun uu____8348  ->
                            fun uu____8349  ->
                              match (uu____8348, uu____8349) with
                              | ((int_to_t1,x),(uu____8368,y)) ->
                                  let uu____8378 =
                                    FStar_BigInt.sub_big_int x y  in
                                  int_as_bounded1 r int_to_t1 uu____8378)),
                    uu____8268)
                   in
                let uu____8379 =
                  let uu____8410 =
                    let uu____8439 =
                      FStar_Parser_Const.p2l ["FStar"; m; "mul"]  in
                    let uu____8440 =
                      FStar_TypeChecker_NBETerm.binary_op
                        FStar_TypeChecker_NBETerm.arg_as_bounded_int
                        (fun uu____8458  ->
                           fun uu____8459  ->
                             match (uu____8458, uu____8459) with
                             | ((int_to_t1,x),(uu____8478,y)) ->
                                 let uu____8488 =
                                   FStar_BigInt.mult_big_int x y  in
                                 FStar_TypeChecker_NBETerm.int_as_bounded
                                   int_to_t1 uu____8488)
                       in
                    (uu____8439, (Prims.parse_int "2"),
                      (Prims.parse_int "0"),
                      (binary_op1 arg_as_bounded_int1
                         (fun r  ->
                            fun uu____8520  ->
                              fun uu____8521  ->
                                match (uu____8520, uu____8521) with
                                | ((int_to_t1,x),(uu____8540,y)) ->
                                    let uu____8550 =
                                      FStar_BigInt.mult_big_int x y  in
                                    int_as_bounded1 r int_to_t1 uu____8550)),
                      uu____8440)
                     in
                  let uu____8551 =
                    let uu____8582 =
                      let uu____8611 =
                        FStar_Parser_Const.p2l ["FStar"; m; "v"]  in
                      let uu____8612 =
                        FStar_TypeChecker_NBETerm.unary_op
                          FStar_TypeChecker_NBETerm.arg_as_bounded_int
                          (fun uu____8626  ->
                             match uu____8626 with
                             | (int_to_t1,x) ->
                                 FStar_TypeChecker_NBETerm.embed
                                   FStar_TypeChecker_NBETerm.e_int bogus_cbs
                                   x)
                         in
                      (uu____8611, (Prims.parse_int "1"),
                        (Prims.parse_int "0"),
                        (unary_op1 arg_as_bounded_int1
                           (fun r  ->
                              fun uu____8660  ->
                                match uu____8660 with
                                | (int_to_t1,x) ->
                                    embed_simple
                                      FStar_Syntax_Embeddings.e_int r x)),
                        uu____8612)
                       in
                    [uu____8582]  in
                  uu____8410 :: uu____8551  in
                uu____8238 :: uu____8379  in
              uu____8066 :: uu____8207))
       in
    let div_mod_unsigned =
      FStar_All.pipe_right bounded_unsigned_int_types
        (FStar_List.collect
           (fun m  ->
              let uu____8902 =
                let uu____8931 = FStar_Parser_Const.p2l ["FStar"; m; "div"]
                   in
                let uu____8932 =
                  FStar_TypeChecker_NBETerm.binary_op
                    FStar_TypeChecker_NBETerm.arg_as_bounded_int
                    (fun uu____8950  ->
                       fun uu____8951  ->
                         match (uu____8950, uu____8951) with
                         | ((int_to_t1,x),(uu____8970,y)) ->
                             let uu____8980 = FStar_BigInt.div_big_int x y
                                in
                             FStar_TypeChecker_NBETerm.int_as_bounded
                               int_to_t1 uu____8980)
                   in
                (uu____8931, (Prims.parse_int "2"), (Prims.parse_int "0"),
                  (binary_op1 arg_as_bounded_int1
                     (fun r  ->
                        fun uu____9012  ->
                          fun uu____9013  ->
                            match (uu____9012, uu____9013) with
                            | ((int_to_t1,x),(uu____9032,y)) ->
                                let uu____9042 = FStar_BigInt.div_big_int x y
                                   in
                                int_as_bounded1 r int_to_t1 uu____9042)),
                  uu____8932)
                 in
              let uu____9043 =
                let uu____9074 =
                  let uu____9103 = FStar_Parser_Const.p2l ["FStar"; m; "rem"]
                     in
                  let uu____9104 =
                    FStar_TypeChecker_NBETerm.binary_op
                      FStar_TypeChecker_NBETerm.arg_as_bounded_int
                      (fun uu____9122  ->
                         fun uu____9123  ->
                           match (uu____9122, uu____9123) with
                           | ((int_to_t1,x),(uu____9142,y)) ->
                               let uu____9152 = FStar_BigInt.mod_big_int x y
                                  in
                               FStar_TypeChecker_NBETerm.int_as_bounded
                                 int_to_t1 uu____9152)
                     in
                  (uu____9103, (Prims.parse_int "2"), (Prims.parse_int "0"),
                    (binary_op1 arg_as_bounded_int1
                       (fun r  ->
                          fun uu____9184  ->
                            fun uu____9185  ->
                              match (uu____9184, uu____9185) with
                              | ((int_to_t1,x),(uu____9204,y)) ->
                                  let uu____9214 =
                                    FStar_BigInt.mod_big_int x y  in
                                  int_as_bounded1 r int_to_t1 uu____9214)),
                    uu____9104)
                   in
                [uu____9074]  in
              uu____8902 :: uu____9043))
       in
    let bitwise =
      FStar_All.pipe_right bounded_unsigned_int_types
        (FStar_List.collect
           (fun m  ->
              let uu____9394 =
                let uu____9423 = FStar_Parser_Const.p2l ["FStar"; m; "logor"]
                   in
                let uu____9424 =
                  FStar_TypeChecker_NBETerm.binary_op
                    FStar_TypeChecker_NBETerm.arg_as_bounded_int
                    (fun uu____9442  ->
                       fun uu____9443  ->
                         match (uu____9442, uu____9443) with
                         | ((int_to_t1,x),(uu____9462,y)) ->
                             let uu____9472 = FStar_BigInt.logor_big_int x y
                                in
                             FStar_TypeChecker_NBETerm.int_as_bounded
                               int_to_t1 uu____9472)
                   in
                (uu____9423, (Prims.parse_int "2"), (Prims.parse_int "0"),
                  (binary_op1 arg_as_bounded_int1
                     (fun r  ->
                        fun uu____9504  ->
                          fun uu____9505  ->
                            match (uu____9504, uu____9505) with
                            | ((int_to_t1,x),(uu____9524,y)) ->
                                let uu____9534 =
                                  FStar_BigInt.logor_big_int x y  in
                                int_as_bounded1 r int_to_t1 uu____9534)),
                  uu____9424)
                 in
              let uu____9535 =
                let uu____9566 =
                  let uu____9595 =
                    FStar_Parser_Const.p2l ["FStar"; m; "logand"]  in
                  let uu____9596 =
                    FStar_TypeChecker_NBETerm.binary_op
                      FStar_TypeChecker_NBETerm.arg_as_bounded_int
                      (fun uu____9614  ->
                         fun uu____9615  ->
                           match (uu____9614, uu____9615) with
                           | ((int_to_t1,x),(uu____9634,y)) ->
                               let uu____9644 =
                                 FStar_BigInt.logand_big_int x y  in
                               FStar_TypeChecker_NBETerm.int_as_bounded
                                 int_to_t1 uu____9644)
                     in
                  (uu____9595, (Prims.parse_int "2"), (Prims.parse_int "0"),
                    (binary_op1 arg_as_bounded_int1
                       (fun r  ->
                          fun uu____9676  ->
                            fun uu____9677  ->
                              match (uu____9676, uu____9677) with
                              | ((int_to_t1,x),(uu____9696,y)) ->
                                  let uu____9706 =
                                    FStar_BigInt.logand_big_int x y  in
                                  int_as_bounded1 r int_to_t1 uu____9706)),
                    uu____9596)
                   in
                let uu____9707 =
                  let uu____9738 =
                    let uu____9767 =
                      FStar_Parser_Const.p2l ["FStar"; m; "logxor"]  in
                    let uu____9768 =
                      FStar_TypeChecker_NBETerm.binary_op
                        FStar_TypeChecker_NBETerm.arg_as_bounded_int
                        (fun uu____9786  ->
                           fun uu____9787  ->
                             match (uu____9786, uu____9787) with
                             | ((int_to_t1,x),(uu____9806,y)) ->
                                 let uu____9816 =
                                   FStar_BigInt.logxor_big_int x y  in
                                 FStar_TypeChecker_NBETerm.int_as_bounded
                                   int_to_t1 uu____9816)
                       in
                    (uu____9767, (Prims.parse_int "2"),
                      (Prims.parse_int "0"),
                      (binary_op1 arg_as_bounded_int1
                         (fun r  ->
                            fun uu____9848  ->
                              fun uu____9849  ->
                                match (uu____9848, uu____9849) with
                                | ((int_to_t1,x),(uu____9868,y)) ->
                                    let uu____9878 =
                                      FStar_BigInt.logxor_big_int x y  in
                                    int_as_bounded1 r int_to_t1 uu____9878)),
                      uu____9768)
                     in
                  let uu____9879 =
                    let uu____9910 =
                      let uu____9939 =
                        FStar_Parser_Const.p2l ["FStar"; m; "lognot"]  in
                      let uu____9940 =
                        FStar_TypeChecker_NBETerm.unary_op
                          FStar_TypeChecker_NBETerm.arg_as_bounded_int
                          (fun uu____9955  ->
                             match uu____9955 with
                             | (int_to_t1,x) ->
                                 let uu____9962 =
                                   FStar_BigInt.lognot_big_int x  in
                                 FStar_TypeChecker_NBETerm.int_as_bounded
                                   int_to_t1 uu____9962)
                         in
                      (uu____9939, (Prims.parse_int "1"),
                        (Prims.parse_int "0"),
                        (unary_op1 arg_as_bounded_int1
                           (fun r  ->
                              fun uu____9991  ->
                                match uu____9991 with
                                | (int_to_t1,x) ->
                                    let uu____9998 =
                                      FStar_BigInt.lognot_big_int x  in
                                    int_as_bounded1 r int_to_t1 uu____9998)),
                        uu____9940)
                       in
                    [uu____9910]  in
                  uu____9738 :: uu____9879  in
                uu____9566 :: uu____9707  in
              uu____9394 :: uu____9535))
       in
    FStar_List.append add_sub_mul_v div_mod_unsigned  in
  let strong_steps =
    FStar_List.map (as_primitive_step true)
      (FStar_List.append basic_ops bounded_arith_ops)
     in
  let weak_steps = FStar_List.map (as_primitive_step false) weak_ops  in
  FStar_All.pipe_left prim_from_list
    (FStar_List.append strong_steps weak_steps)
  
let (equality_ops : primitive_step FStar_Util.psmap) =
  let interp_prop1 psc _norm_cb args =
    let r = psc.psc_range  in
    match args with
    | (_typ,uu____10293)::(a1,uu____10295)::(a2,uu____10297)::[] ->
        let uu____10354 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____10354 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___259_10358 = FStar_Syntax_Util.t_true  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___259_10358.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___259_10358.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___260_10360 = FStar_Syntax_Util.t_false  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___260_10360.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___260_10360.FStar_Syntax_Syntax.vars)
                })
         | uu____10361 -> FStar_Pervasives_Native.None)
    | (_typ,uu____10363)::uu____10364::(a1,uu____10366)::(a2,uu____10368)::[]
        ->
        let uu____10441 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____10441 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___259_10445 = FStar_Syntax_Util.t_true  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___259_10445.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___259_10445.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___260_10447 = FStar_Syntax_Util.t_false  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___260_10447.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___260_10447.FStar_Syntax_Syntax.vars)
                })
         | uu____10448 -> FStar_Pervasives_Native.None)
    | uu____10449 -> failwith "Unexpected number of arguments"  in
  let propositional_equality =
    {
      name = FStar_Parser_Const.eq2_lid;
      arity = (Prims.parse_int "3");
      univ_arity = (Prims.parse_int "1");
      auto_reflect = FStar_Pervasives_Native.None;
      strong_reduction_ok = true;
      requires_binder_substitution = false;
      interpretation = interp_prop1;
      interpretation_nbe =
        (fun _cb  -> FStar_TypeChecker_NBETerm.interp_prop)
    }  in
  let hetero_propositional_equality =
    {
      name = FStar_Parser_Const.eq3_lid;
      arity = (Prims.parse_int "4");
      univ_arity = (Prims.parse_int "2");
      auto_reflect = FStar_Pervasives_Native.None;
      strong_reduction_ok = true;
      requires_binder_substitution = false;
      interpretation = interp_prop1;
      interpretation_nbe =
        (fun _cb  -> FStar_TypeChecker_NBETerm.interp_prop)
    }  in
  prim_from_list [propositional_equality; hetero_propositional_equality] 
let (primop_time_map : Prims.int FStar_Util.smap) =
  FStar_Util.smap_create (Prims.parse_int "50") 
let (primop_time_reset : unit -> unit) =
  fun uu____10464  -> FStar_Util.smap_clear primop_time_map 
let (primop_time_count : Prims.string -> Prims.int -> unit) =
  fun nm  ->
    fun ms  ->
      let uu____10475 = FStar_Util.smap_try_find primop_time_map nm  in
      match uu____10475 with
      | FStar_Pervasives_Native.None  ->
          FStar_Util.smap_add primop_time_map nm ms
      | FStar_Pervasives_Native.Some ms0 ->
          FStar_Util.smap_add primop_time_map nm (ms0 + ms)
  
let (fixto : Prims.int -> Prims.string -> Prims.string) =
  fun n1  ->
    fun s  ->
      if (FStar_String.length s) < n1
      then
        let uu____10489 = FStar_String.make (n1 - (FStar_String.length s)) 32
           in
        Prims.strcat uu____10489 s
      else s
  
let (primop_time_report : unit -> Prims.string) =
  fun uu____10496  ->
    let pairs =
      FStar_Util.smap_fold primop_time_map
        (fun nm  -> fun ms  -> fun rest  -> (nm, ms) :: rest) []
       in
    let pairs1 =
      FStar_Util.sort_with
        (fun uu____10547  ->
           fun uu____10548  ->
             match (uu____10547, uu____10548) with
             | ((uu____10565,t1),(uu____10567,t2)) -> t1 - t2) pairs
       in
    FStar_List.fold_right
      (fun uu____10586  ->
         fun rest  ->
           match uu____10586 with
           | (nm,ms) ->
               let uu____10594 =
                 let uu____10595 =
                   let uu____10596 = FStar_Util.string_of_int ms  in
                   fixto (Prims.parse_int "10") uu____10596  in
                 FStar_Util.format2 "%sms --- %s\n" uu____10595 nm  in
               Prims.strcat uu____10594 rest) pairs1 ""
  
let (plugins :
  (primitive_step -> unit,unit -> primitive_step Prims.list)
    FStar_Pervasives_Native.tuple2)
  =
  let plugins = FStar_Util.mk_ref []  in
  let register p =
    let uu____10622 =
      let uu____10625 = FStar_ST.op_Bang plugins  in p :: uu____10625  in
    FStar_ST.op_Colon_Equals plugins uu____10622  in
  let retrieve uu____10725 = FStar_ST.op_Bang plugins  in
  (register, retrieve) 
let (register_plugin : primitive_step -> unit) =
  fun p  -> FStar_Pervasives_Native.fst plugins p 
let (retrieve_plugins : unit -> primitive_step Prims.list) =
  fun uu____10798  ->
    let uu____10799 = FStar_Options.no_plugins ()  in
    if uu____10799 then [] else FStar_Pervasives_Native.snd plugins ()
  
let (config' :
  primitive_step Prims.list ->
    FStar_TypeChecker_Env.step Prims.list -> FStar_TypeChecker_Env.env -> cfg)
  =
  fun psteps  ->
    fun s  ->
      fun e  ->
        let d =
          FStar_All.pipe_right s
            (FStar_List.collect
               (fun uu___230_10843  ->
                  match uu___230_10843 with
                  | FStar_TypeChecker_Env.UnfoldUntil k ->
                      [FStar_TypeChecker_Env.Unfold k]
                  | FStar_TypeChecker_Env.Eager_unfolding  ->
                      [FStar_TypeChecker_Env.Eager_unfolding_only]
                  | FStar_TypeChecker_Env.Inlining  ->
                      [FStar_TypeChecker_Env.InliningDelta]
                  | uu____10847 -> []))
           in
        let d1 =
          match d with
          | [] -> [FStar_TypeChecker_Env.NoDelta]
          | uu____10853 -> d  in
        let uu____10856 = to_fsteps s  in
        let uu____10857 =
          let uu____10858 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Norm")  in
          let uu____10859 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "NormTop")  in
          let uu____10860 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "NormCfg")  in
          let uu____10861 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Primops")  in
          let uu____10862 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Unfolding")
             in
          let uu____10863 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "380")  in
          let uu____10864 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "WPE")  in
          let uu____10865 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "NormDelayed")
             in
          let uu____10866 =
            FStar_TypeChecker_Env.debug e
              (FStar_Options.Other "print_normalized_terms")
             in
          {
            gen = uu____10858;
            top = uu____10859;
            cfg = uu____10860;
            primop = uu____10861;
            unfolding = uu____10862;
            b380 = uu____10863;
            wpe = uu____10864;
            norm_delayed = uu____10865;
            print_normalized = uu____10866
          }  in
        let uu____10867 =
          let uu____10870 =
            let uu____10873 = retrieve_plugins ()  in
            FStar_List.append uu____10873 psteps  in
          add_steps built_in_primitive_steps uu____10870  in
        let uu____10876 =
          (FStar_Options.normalize_pure_terms_for_extraction ()) ||
            (let uu____10878 =
               FStar_All.pipe_right s
                 (FStar_Util.for_some
                    (FStar_TypeChecker_Env.eq_step
                       FStar_TypeChecker_Env.PureSubtermsWithinComputations))
                in
             Prims.op_Negation uu____10878)
           in
        {
          steps = uu____10856;
          tcenv = e;
          debug = uu____10857;
          delta_level = d1;
          primitive_steps = uu____10867;
          strong = false;
          memoize_lazy = true;
          normalize_pure_lets = uu____10876;
          reifying = false
        }
  
let (config :
  FStar_TypeChecker_Env.step Prims.list -> FStar_TypeChecker_Env.env -> cfg)
  = fun s  -> fun e  -> config' [] s e 