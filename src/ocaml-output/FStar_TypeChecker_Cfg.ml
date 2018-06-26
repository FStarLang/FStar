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
  unfold_attr:
    FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option ;
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
  fsteps ->
    FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
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
      let add_opt x uu___220_1302 =
        match uu___220_1302 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.Some [x]
        | FStar_Pervasives_Native.Some xs ->
            FStar_Pervasives_Native.Some (x :: xs)
         in
      match s with
      | FStar_TypeChecker_Env.Beta  ->
          let uu___222_1322 = fs  in
          {
            beta = true;
            iota = (uu___222_1322.iota);
            zeta = (uu___222_1322.zeta);
            weak = (uu___222_1322.weak);
            hnf = (uu___222_1322.hnf);
            primops = (uu___222_1322.primops);
            do_not_unfold_pure_lets = (uu___222_1322.do_not_unfold_pure_lets);
            unfold_until = (uu___222_1322.unfold_until);
            unfold_only = (uu___222_1322.unfold_only);
            unfold_fully = (uu___222_1322.unfold_fully);
            unfold_attr = (uu___222_1322.unfold_attr);
            unfold_tac = (uu___222_1322.unfold_tac);
            pure_subterms_within_computations =
              (uu___222_1322.pure_subterms_within_computations);
            simplify = (uu___222_1322.simplify);
            erase_universes = (uu___222_1322.erase_universes);
            allow_unbound_universes = (uu___222_1322.allow_unbound_universes);
            reify_ = (uu___222_1322.reify_);
            compress_uvars = (uu___222_1322.compress_uvars);
            no_full_norm = (uu___222_1322.no_full_norm);
            check_no_uvars = (uu___222_1322.check_no_uvars);
            unmeta = (uu___222_1322.unmeta);
            unascribe = (uu___222_1322.unascribe);
            in_full_norm_request = (uu___222_1322.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___222_1322.weakly_reduce_scrutinee);
            nbe_step = (uu___222_1322.nbe_step)
          }
      | FStar_TypeChecker_Env.Iota  ->
          let uu___223_1323 = fs  in
          {
            beta = (uu___223_1323.beta);
            iota = true;
            zeta = (uu___223_1323.zeta);
            weak = (uu___223_1323.weak);
            hnf = (uu___223_1323.hnf);
            primops = (uu___223_1323.primops);
            do_not_unfold_pure_lets = (uu___223_1323.do_not_unfold_pure_lets);
            unfold_until = (uu___223_1323.unfold_until);
            unfold_only = (uu___223_1323.unfold_only);
            unfold_fully = (uu___223_1323.unfold_fully);
            unfold_attr = (uu___223_1323.unfold_attr);
            unfold_tac = (uu___223_1323.unfold_tac);
            pure_subterms_within_computations =
              (uu___223_1323.pure_subterms_within_computations);
            simplify = (uu___223_1323.simplify);
            erase_universes = (uu___223_1323.erase_universes);
            allow_unbound_universes = (uu___223_1323.allow_unbound_universes);
            reify_ = (uu___223_1323.reify_);
            compress_uvars = (uu___223_1323.compress_uvars);
            no_full_norm = (uu___223_1323.no_full_norm);
            check_no_uvars = (uu___223_1323.check_no_uvars);
            unmeta = (uu___223_1323.unmeta);
            unascribe = (uu___223_1323.unascribe);
            in_full_norm_request = (uu___223_1323.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___223_1323.weakly_reduce_scrutinee);
            nbe_step = (uu___223_1323.nbe_step)
          }
      | FStar_TypeChecker_Env.Zeta  ->
          let uu___224_1324 = fs  in
          {
            beta = (uu___224_1324.beta);
            iota = (uu___224_1324.iota);
            zeta = true;
            weak = (uu___224_1324.weak);
            hnf = (uu___224_1324.hnf);
            primops = (uu___224_1324.primops);
            do_not_unfold_pure_lets = (uu___224_1324.do_not_unfold_pure_lets);
            unfold_until = (uu___224_1324.unfold_until);
            unfold_only = (uu___224_1324.unfold_only);
            unfold_fully = (uu___224_1324.unfold_fully);
            unfold_attr = (uu___224_1324.unfold_attr);
            unfold_tac = (uu___224_1324.unfold_tac);
            pure_subterms_within_computations =
              (uu___224_1324.pure_subterms_within_computations);
            simplify = (uu___224_1324.simplify);
            erase_universes = (uu___224_1324.erase_universes);
            allow_unbound_universes = (uu___224_1324.allow_unbound_universes);
            reify_ = (uu___224_1324.reify_);
            compress_uvars = (uu___224_1324.compress_uvars);
            no_full_norm = (uu___224_1324.no_full_norm);
            check_no_uvars = (uu___224_1324.check_no_uvars);
            unmeta = (uu___224_1324.unmeta);
            unascribe = (uu___224_1324.unascribe);
            in_full_norm_request = (uu___224_1324.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___224_1324.weakly_reduce_scrutinee);
            nbe_step = (uu___224_1324.nbe_step)
          }
      | FStar_TypeChecker_Env.Exclude (FStar_TypeChecker_Env.Beta ) ->
          let uu___225_1325 = fs  in
          {
            beta = false;
            iota = (uu___225_1325.iota);
            zeta = (uu___225_1325.zeta);
            weak = (uu___225_1325.weak);
            hnf = (uu___225_1325.hnf);
            primops = (uu___225_1325.primops);
            do_not_unfold_pure_lets = (uu___225_1325.do_not_unfold_pure_lets);
            unfold_until = (uu___225_1325.unfold_until);
            unfold_only = (uu___225_1325.unfold_only);
            unfold_fully = (uu___225_1325.unfold_fully);
            unfold_attr = (uu___225_1325.unfold_attr);
            unfold_tac = (uu___225_1325.unfold_tac);
            pure_subterms_within_computations =
              (uu___225_1325.pure_subterms_within_computations);
            simplify = (uu___225_1325.simplify);
            erase_universes = (uu___225_1325.erase_universes);
            allow_unbound_universes = (uu___225_1325.allow_unbound_universes);
            reify_ = (uu___225_1325.reify_);
            compress_uvars = (uu___225_1325.compress_uvars);
            no_full_norm = (uu___225_1325.no_full_norm);
            check_no_uvars = (uu___225_1325.check_no_uvars);
            unmeta = (uu___225_1325.unmeta);
            unascribe = (uu___225_1325.unascribe);
            in_full_norm_request = (uu___225_1325.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___225_1325.weakly_reduce_scrutinee);
            nbe_step = (uu___225_1325.nbe_step)
          }
      | FStar_TypeChecker_Env.Exclude (FStar_TypeChecker_Env.Iota ) ->
          let uu___226_1326 = fs  in
          {
            beta = (uu___226_1326.beta);
            iota = false;
            zeta = (uu___226_1326.zeta);
            weak = (uu___226_1326.weak);
            hnf = (uu___226_1326.hnf);
            primops = (uu___226_1326.primops);
            do_not_unfold_pure_lets = (uu___226_1326.do_not_unfold_pure_lets);
            unfold_until = (uu___226_1326.unfold_until);
            unfold_only = (uu___226_1326.unfold_only);
            unfold_fully = (uu___226_1326.unfold_fully);
            unfold_attr = (uu___226_1326.unfold_attr);
            unfold_tac = (uu___226_1326.unfold_tac);
            pure_subterms_within_computations =
              (uu___226_1326.pure_subterms_within_computations);
            simplify = (uu___226_1326.simplify);
            erase_universes = (uu___226_1326.erase_universes);
            allow_unbound_universes = (uu___226_1326.allow_unbound_universes);
            reify_ = (uu___226_1326.reify_);
            compress_uvars = (uu___226_1326.compress_uvars);
            no_full_norm = (uu___226_1326.no_full_norm);
            check_no_uvars = (uu___226_1326.check_no_uvars);
            unmeta = (uu___226_1326.unmeta);
            unascribe = (uu___226_1326.unascribe);
            in_full_norm_request = (uu___226_1326.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___226_1326.weakly_reduce_scrutinee);
            nbe_step = (uu___226_1326.nbe_step)
          }
      | FStar_TypeChecker_Env.Exclude (FStar_TypeChecker_Env.Zeta ) ->
          let uu___227_1327 = fs  in
          {
            beta = (uu___227_1327.beta);
            iota = (uu___227_1327.iota);
            zeta = false;
            weak = (uu___227_1327.weak);
            hnf = (uu___227_1327.hnf);
            primops = (uu___227_1327.primops);
            do_not_unfold_pure_lets = (uu___227_1327.do_not_unfold_pure_lets);
            unfold_until = (uu___227_1327.unfold_until);
            unfold_only = (uu___227_1327.unfold_only);
            unfold_fully = (uu___227_1327.unfold_fully);
            unfold_attr = (uu___227_1327.unfold_attr);
            unfold_tac = (uu___227_1327.unfold_tac);
            pure_subterms_within_computations =
              (uu___227_1327.pure_subterms_within_computations);
            simplify = (uu___227_1327.simplify);
            erase_universes = (uu___227_1327.erase_universes);
            allow_unbound_universes = (uu___227_1327.allow_unbound_universes);
            reify_ = (uu___227_1327.reify_);
            compress_uvars = (uu___227_1327.compress_uvars);
            no_full_norm = (uu___227_1327.no_full_norm);
            check_no_uvars = (uu___227_1327.check_no_uvars);
            unmeta = (uu___227_1327.unmeta);
            unascribe = (uu___227_1327.unascribe);
            in_full_norm_request = (uu___227_1327.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___227_1327.weakly_reduce_scrutinee);
            nbe_step = (uu___227_1327.nbe_step)
          }
      | FStar_TypeChecker_Env.Exclude uu____1328 -> failwith "Bad exclude"
      | FStar_TypeChecker_Env.Weak  ->
          let uu___228_1329 = fs  in
          {
            beta = (uu___228_1329.beta);
            iota = (uu___228_1329.iota);
            zeta = (uu___228_1329.zeta);
            weak = true;
            hnf = (uu___228_1329.hnf);
            primops = (uu___228_1329.primops);
            do_not_unfold_pure_lets = (uu___228_1329.do_not_unfold_pure_lets);
            unfold_until = (uu___228_1329.unfold_until);
            unfold_only = (uu___228_1329.unfold_only);
            unfold_fully = (uu___228_1329.unfold_fully);
            unfold_attr = (uu___228_1329.unfold_attr);
            unfold_tac = (uu___228_1329.unfold_tac);
            pure_subterms_within_computations =
              (uu___228_1329.pure_subterms_within_computations);
            simplify = (uu___228_1329.simplify);
            erase_universes = (uu___228_1329.erase_universes);
            allow_unbound_universes = (uu___228_1329.allow_unbound_universes);
            reify_ = (uu___228_1329.reify_);
            compress_uvars = (uu___228_1329.compress_uvars);
            no_full_norm = (uu___228_1329.no_full_norm);
            check_no_uvars = (uu___228_1329.check_no_uvars);
            unmeta = (uu___228_1329.unmeta);
            unascribe = (uu___228_1329.unascribe);
            in_full_norm_request = (uu___228_1329.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___228_1329.weakly_reduce_scrutinee);
            nbe_step = (uu___228_1329.nbe_step)
          }
      | FStar_TypeChecker_Env.HNF  ->
          let uu___229_1330 = fs  in
          {
            beta = (uu___229_1330.beta);
            iota = (uu___229_1330.iota);
            zeta = (uu___229_1330.zeta);
            weak = (uu___229_1330.weak);
            hnf = true;
            primops = (uu___229_1330.primops);
            do_not_unfold_pure_lets = (uu___229_1330.do_not_unfold_pure_lets);
            unfold_until = (uu___229_1330.unfold_until);
            unfold_only = (uu___229_1330.unfold_only);
            unfold_fully = (uu___229_1330.unfold_fully);
            unfold_attr = (uu___229_1330.unfold_attr);
            unfold_tac = (uu___229_1330.unfold_tac);
            pure_subterms_within_computations =
              (uu___229_1330.pure_subterms_within_computations);
            simplify = (uu___229_1330.simplify);
            erase_universes = (uu___229_1330.erase_universes);
            allow_unbound_universes = (uu___229_1330.allow_unbound_universes);
            reify_ = (uu___229_1330.reify_);
            compress_uvars = (uu___229_1330.compress_uvars);
            no_full_norm = (uu___229_1330.no_full_norm);
            check_no_uvars = (uu___229_1330.check_no_uvars);
            unmeta = (uu___229_1330.unmeta);
            unascribe = (uu___229_1330.unascribe);
            in_full_norm_request = (uu___229_1330.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___229_1330.weakly_reduce_scrutinee);
            nbe_step = (uu___229_1330.nbe_step)
          }
      | FStar_TypeChecker_Env.Primops  ->
          let uu___230_1331 = fs  in
          {
            beta = (uu___230_1331.beta);
            iota = (uu___230_1331.iota);
            zeta = (uu___230_1331.zeta);
            weak = (uu___230_1331.weak);
            hnf = (uu___230_1331.hnf);
            primops = true;
            do_not_unfold_pure_lets = (uu___230_1331.do_not_unfold_pure_lets);
            unfold_until = (uu___230_1331.unfold_until);
            unfold_only = (uu___230_1331.unfold_only);
            unfold_fully = (uu___230_1331.unfold_fully);
            unfold_attr = (uu___230_1331.unfold_attr);
            unfold_tac = (uu___230_1331.unfold_tac);
            pure_subterms_within_computations =
              (uu___230_1331.pure_subterms_within_computations);
            simplify = (uu___230_1331.simplify);
            erase_universes = (uu___230_1331.erase_universes);
            allow_unbound_universes = (uu___230_1331.allow_unbound_universes);
            reify_ = (uu___230_1331.reify_);
            compress_uvars = (uu___230_1331.compress_uvars);
            no_full_norm = (uu___230_1331.no_full_norm);
            check_no_uvars = (uu___230_1331.check_no_uvars);
            unmeta = (uu___230_1331.unmeta);
            unascribe = (uu___230_1331.unascribe);
            in_full_norm_request = (uu___230_1331.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___230_1331.weakly_reduce_scrutinee);
            nbe_step = (uu___230_1331.nbe_step)
          }
      | FStar_TypeChecker_Env.Eager_unfolding  -> fs
      | FStar_TypeChecker_Env.Inlining  -> fs
      | FStar_TypeChecker_Env.DoNotUnfoldPureLets  ->
          let uu___231_1332 = fs  in
          {
            beta = (uu___231_1332.beta);
            iota = (uu___231_1332.iota);
            zeta = (uu___231_1332.zeta);
            weak = (uu___231_1332.weak);
            hnf = (uu___231_1332.hnf);
            primops = (uu___231_1332.primops);
            do_not_unfold_pure_lets = true;
            unfold_until = (uu___231_1332.unfold_until);
            unfold_only = (uu___231_1332.unfold_only);
            unfold_fully = (uu___231_1332.unfold_fully);
            unfold_attr = (uu___231_1332.unfold_attr);
            unfold_tac = (uu___231_1332.unfold_tac);
            pure_subterms_within_computations =
              (uu___231_1332.pure_subterms_within_computations);
            simplify = (uu___231_1332.simplify);
            erase_universes = (uu___231_1332.erase_universes);
            allow_unbound_universes = (uu___231_1332.allow_unbound_universes);
            reify_ = (uu___231_1332.reify_);
            compress_uvars = (uu___231_1332.compress_uvars);
            no_full_norm = (uu___231_1332.no_full_norm);
            check_no_uvars = (uu___231_1332.check_no_uvars);
            unmeta = (uu___231_1332.unmeta);
            unascribe = (uu___231_1332.unascribe);
            in_full_norm_request = (uu___231_1332.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___231_1332.weakly_reduce_scrutinee);
            nbe_step = (uu___231_1332.nbe_step)
          }
      | FStar_TypeChecker_Env.UnfoldUntil d ->
          let uu___232_1334 = fs  in
          {
            beta = (uu___232_1334.beta);
            iota = (uu___232_1334.iota);
            zeta = (uu___232_1334.zeta);
            weak = (uu___232_1334.weak);
            hnf = (uu___232_1334.hnf);
            primops = (uu___232_1334.primops);
            do_not_unfold_pure_lets = (uu___232_1334.do_not_unfold_pure_lets);
            unfold_until = (FStar_Pervasives_Native.Some d);
            unfold_only = (uu___232_1334.unfold_only);
            unfold_fully = (uu___232_1334.unfold_fully);
            unfold_attr = (uu___232_1334.unfold_attr);
            unfold_tac = (uu___232_1334.unfold_tac);
            pure_subterms_within_computations =
              (uu___232_1334.pure_subterms_within_computations);
            simplify = (uu___232_1334.simplify);
            erase_universes = (uu___232_1334.erase_universes);
            allow_unbound_universes = (uu___232_1334.allow_unbound_universes);
            reify_ = (uu___232_1334.reify_);
            compress_uvars = (uu___232_1334.compress_uvars);
            no_full_norm = (uu___232_1334.no_full_norm);
            check_no_uvars = (uu___232_1334.check_no_uvars);
            unmeta = (uu___232_1334.unmeta);
            unascribe = (uu___232_1334.unascribe);
            in_full_norm_request = (uu___232_1334.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___232_1334.weakly_reduce_scrutinee);
            nbe_step = (uu___232_1334.nbe_step)
          }
      | FStar_TypeChecker_Env.UnfoldOnly lids ->
          let uu___233_1338 = fs  in
          {
            beta = (uu___233_1338.beta);
            iota = (uu___233_1338.iota);
            zeta = (uu___233_1338.zeta);
            weak = (uu___233_1338.weak);
            hnf = (uu___233_1338.hnf);
            primops = (uu___233_1338.primops);
            do_not_unfold_pure_lets = (uu___233_1338.do_not_unfold_pure_lets);
            unfold_until = (uu___233_1338.unfold_until);
            unfold_only = (FStar_Pervasives_Native.Some lids);
            unfold_fully = (uu___233_1338.unfold_fully);
            unfold_attr = (uu___233_1338.unfold_attr);
            unfold_tac = (uu___233_1338.unfold_tac);
            pure_subterms_within_computations =
              (uu___233_1338.pure_subterms_within_computations);
            simplify = (uu___233_1338.simplify);
            erase_universes = (uu___233_1338.erase_universes);
            allow_unbound_universes = (uu___233_1338.allow_unbound_universes);
            reify_ = (uu___233_1338.reify_);
            compress_uvars = (uu___233_1338.compress_uvars);
            no_full_norm = (uu___233_1338.no_full_norm);
            check_no_uvars = (uu___233_1338.check_no_uvars);
            unmeta = (uu___233_1338.unmeta);
            unascribe = (uu___233_1338.unascribe);
            in_full_norm_request = (uu___233_1338.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___233_1338.weakly_reduce_scrutinee);
            nbe_step = (uu___233_1338.nbe_step)
          }
      | FStar_TypeChecker_Env.UnfoldFully lids ->
          let uu___234_1344 = fs  in
          {
            beta = (uu___234_1344.beta);
            iota = (uu___234_1344.iota);
            zeta = (uu___234_1344.zeta);
            weak = (uu___234_1344.weak);
            hnf = (uu___234_1344.hnf);
            primops = (uu___234_1344.primops);
            do_not_unfold_pure_lets = (uu___234_1344.do_not_unfold_pure_lets);
            unfold_until = (uu___234_1344.unfold_until);
            unfold_only = (uu___234_1344.unfold_only);
            unfold_fully = (FStar_Pervasives_Native.Some lids);
            unfold_attr = (uu___234_1344.unfold_attr);
            unfold_tac = (uu___234_1344.unfold_tac);
            pure_subterms_within_computations =
              (uu___234_1344.pure_subterms_within_computations);
            simplify = (uu___234_1344.simplify);
            erase_universes = (uu___234_1344.erase_universes);
            allow_unbound_universes = (uu___234_1344.allow_unbound_universes);
            reify_ = (uu___234_1344.reify_);
            compress_uvars = (uu___234_1344.compress_uvars);
            no_full_norm = (uu___234_1344.no_full_norm);
            check_no_uvars = (uu___234_1344.check_no_uvars);
            unmeta = (uu___234_1344.unmeta);
            unascribe = (uu___234_1344.unascribe);
            in_full_norm_request = (uu___234_1344.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___234_1344.weakly_reduce_scrutinee);
            nbe_step = (uu___234_1344.nbe_step)
          }
      | FStar_TypeChecker_Env.UnfoldAttr attr ->
          let uu___235_1348 = fs  in
          {
            beta = (uu___235_1348.beta);
            iota = (uu___235_1348.iota);
            zeta = (uu___235_1348.zeta);
            weak = (uu___235_1348.weak);
            hnf = (uu___235_1348.hnf);
            primops = (uu___235_1348.primops);
            do_not_unfold_pure_lets = (uu___235_1348.do_not_unfold_pure_lets);
            unfold_until = (uu___235_1348.unfold_until);
            unfold_only = (uu___235_1348.unfold_only);
            unfold_fully = (uu___235_1348.unfold_fully);
            unfold_attr = (add_opt attr fs.unfold_attr);
            unfold_tac = (uu___235_1348.unfold_tac);
            pure_subterms_within_computations =
              (uu___235_1348.pure_subterms_within_computations);
            simplify = (uu___235_1348.simplify);
            erase_universes = (uu___235_1348.erase_universes);
            allow_unbound_universes = (uu___235_1348.allow_unbound_universes);
            reify_ = (uu___235_1348.reify_);
            compress_uvars = (uu___235_1348.compress_uvars);
            no_full_norm = (uu___235_1348.no_full_norm);
            check_no_uvars = (uu___235_1348.check_no_uvars);
            unmeta = (uu___235_1348.unmeta);
            unascribe = (uu___235_1348.unascribe);
            in_full_norm_request = (uu___235_1348.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___235_1348.weakly_reduce_scrutinee);
            nbe_step = (uu___235_1348.nbe_step)
          }
      | FStar_TypeChecker_Env.UnfoldTac  ->
          let uu___236_1349 = fs  in
          {
            beta = (uu___236_1349.beta);
            iota = (uu___236_1349.iota);
            zeta = (uu___236_1349.zeta);
            weak = (uu___236_1349.weak);
            hnf = (uu___236_1349.hnf);
            primops = (uu___236_1349.primops);
            do_not_unfold_pure_lets = (uu___236_1349.do_not_unfold_pure_lets);
            unfold_until = (uu___236_1349.unfold_until);
            unfold_only = (uu___236_1349.unfold_only);
            unfold_fully = (uu___236_1349.unfold_fully);
            unfold_attr = (uu___236_1349.unfold_attr);
            unfold_tac = true;
            pure_subterms_within_computations =
              (uu___236_1349.pure_subterms_within_computations);
            simplify = (uu___236_1349.simplify);
            erase_universes = (uu___236_1349.erase_universes);
            allow_unbound_universes = (uu___236_1349.allow_unbound_universes);
            reify_ = (uu___236_1349.reify_);
            compress_uvars = (uu___236_1349.compress_uvars);
            no_full_norm = (uu___236_1349.no_full_norm);
            check_no_uvars = (uu___236_1349.check_no_uvars);
            unmeta = (uu___236_1349.unmeta);
            unascribe = (uu___236_1349.unascribe);
            in_full_norm_request = (uu___236_1349.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___236_1349.weakly_reduce_scrutinee);
            nbe_step = (uu___236_1349.nbe_step)
          }
      | FStar_TypeChecker_Env.PureSubtermsWithinComputations  ->
          let uu___237_1350 = fs  in
          {
            beta = (uu___237_1350.beta);
            iota = (uu___237_1350.iota);
            zeta = (uu___237_1350.zeta);
            weak = (uu___237_1350.weak);
            hnf = (uu___237_1350.hnf);
            primops = (uu___237_1350.primops);
            do_not_unfold_pure_lets = (uu___237_1350.do_not_unfold_pure_lets);
            unfold_until = (uu___237_1350.unfold_until);
            unfold_only = (uu___237_1350.unfold_only);
            unfold_fully = (uu___237_1350.unfold_fully);
            unfold_attr = (uu___237_1350.unfold_attr);
            unfold_tac = (uu___237_1350.unfold_tac);
            pure_subterms_within_computations = true;
            simplify = (uu___237_1350.simplify);
            erase_universes = (uu___237_1350.erase_universes);
            allow_unbound_universes = (uu___237_1350.allow_unbound_universes);
            reify_ = (uu___237_1350.reify_);
            compress_uvars = (uu___237_1350.compress_uvars);
            no_full_norm = (uu___237_1350.no_full_norm);
            check_no_uvars = (uu___237_1350.check_no_uvars);
            unmeta = (uu___237_1350.unmeta);
            unascribe = (uu___237_1350.unascribe);
            in_full_norm_request = (uu___237_1350.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___237_1350.weakly_reduce_scrutinee);
            nbe_step = (uu___237_1350.nbe_step)
          }
      | FStar_TypeChecker_Env.Simplify  ->
          let uu___238_1351 = fs  in
          {
            beta = (uu___238_1351.beta);
            iota = (uu___238_1351.iota);
            zeta = (uu___238_1351.zeta);
            weak = (uu___238_1351.weak);
            hnf = (uu___238_1351.hnf);
            primops = (uu___238_1351.primops);
            do_not_unfold_pure_lets = (uu___238_1351.do_not_unfold_pure_lets);
            unfold_until = (uu___238_1351.unfold_until);
            unfold_only = (uu___238_1351.unfold_only);
            unfold_fully = (uu___238_1351.unfold_fully);
            unfold_attr = (uu___238_1351.unfold_attr);
            unfold_tac = (uu___238_1351.unfold_tac);
            pure_subterms_within_computations =
              (uu___238_1351.pure_subterms_within_computations);
            simplify = true;
            erase_universes = (uu___238_1351.erase_universes);
            allow_unbound_universes = (uu___238_1351.allow_unbound_universes);
            reify_ = (uu___238_1351.reify_);
            compress_uvars = (uu___238_1351.compress_uvars);
            no_full_norm = (uu___238_1351.no_full_norm);
            check_no_uvars = (uu___238_1351.check_no_uvars);
            unmeta = (uu___238_1351.unmeta);
            unascribe = (uu___238_1351.unascribe);
            in_full_norm_request = (uu___238_1351.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___238_1351.weakly_reduce_scrutinee);
            nbe_step = (uu___238_1351.nbe_step)
          }
      | FStar_TypeChecker_Env.EraseUniverses  ->
          let uu___239_1352 = fs  in
          {
            beta = (uu___239_1352.beta);
            iota = (uu___239_1352.iota);
            zeta = (uu___239_1352.zeta);
            weak = (uu___239_1352.weak);
            hnf = (uu___239_1352.hnf);
            primops = (uu___239_1352.primops);
            do_not_unfold_pure_lets = (uu___239_1352.do_not_unfold_pure_lets);
            unfold_until = (uu___239_1352.unfold_until);
            unfold_only = (uu___239_1352.unfold_only);
            unfold_fully = (uu___239_1352.unfold_fully);
            unfold_attr = (uu___239_1352.unfold_attr);
            unfold_tac = (uu___239_1352.unfold_tac);
            pure_subterms_within_computations =
              (uu___239_1352.pure_subterms_within_computations);
            simplify = (uu___239_1352.simplify);
            erase_universes = true;
            allow_unbound_universes = (uu___239_1352.allow_unbound_universes);
            reify_ = (uu___239_1352.reify_);
            compress_uvars = (uu___239_1352.compress_uvars);
            no_full_norm = (uu___239_1352.no_full_norm);
            check_no_uvars = (uu___239_1352.check_no_uvars);
            unmeta = (uu___239_1352.unmeta);
            unascribe = (uu___239_1352.unascribe);
            in_full_norm_request = (uu___239_1352.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___239_1352.weakly_reduce_scrutinee);
            nbe_step = (uu___239_1352.nbe_step)
          }
      | FStar_TypeChecker_Env.AllowUnboundUniverses  ->
          let uu___240_1353 = fs  in
          {
            beta = (uu___240_1353.beta);
            iota = (uu___240_1353.iota);
            zeta = (uu___240_1353.zeta);
            weak = (uu___240_1353.weak);
            hnf = (uu___240_1353.hnf);
            primops = (uu___240_1353.primops);
            do_not_unfold_pure_lets = (uu___240_1353.do_not_unfold_pure_lets);
            unfold_until = (uu___240_1353.unfold_until);
            unfold_only = (uu___240_1353.unfold_only);
            unfold_fully = (uu___240_1353.unfold_fully);
            unfold_attr = (uu___240_1353.unfold_attr);
            unfold_tac = (uu___240_1353.unfold_tac);
            pure_subterms_within_computations =
              (uu___240_1353.pure_subterms_within_computations);
            simplify = (uu___240_1353.simplify);
            erase_universes = (uu___240_1353.erase_universes);
            allow_unbound_universes = true;
            reify_ = (uu___240_1353.reify_);
            compress_uvars = (uu___240_1353.compress_uvars);
            no_full_norm = (uu___240_1353.no_full_norm);
            check_no_uvars = (uu___240_1353.check_no_uvars);
            unmeta = (uu___240_1353.unmeta);
            unascribe = (uu___240_1353.unascribe);
            in_full_norm_request = (uu___240_1353.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___240_1353.weakly_reduce_scrutinee);
            nbe_step = (uu___240_1353.nbe_step)
          }
      | FStar_TypeChecker_Env.Reify  ->
          let uu___241_1354 = fs  in
          {
            beta = (uu___241_1354.beta);
            iota = (uu___241_1354.iota);
            zeta = (uu___241_1354.zeta);
            weak = (uu___241_1354.weak);
            hnf = (uu___241_1354.hnf);
            primops = (uu___241_1354.primops);
            do_not_unfold_pure_lets = (uu___241_1354.do_not_unfold_pure_lets);
            unfold_until = (uu___241_1354.unfold_until);
            unfold_only = (uu___241_1354.unfold_only);
            unfold_fully = (uu___241_1354.unfold_fully);
            unfold_attr = (uu___241_1354.unfold_attr);
            unfold_tac = (uu___241_1354.unfold_tac);
            pure_subterms_within_computations =
              (uu___241_1354.pure_subterms_within_computations);
            simplify = (uu___241_1354.simplify);
            erase_universes = (uu___241_1354.erase_universes);
            allow_unbound_universes = (uu___241_1354.allow_unbound_universes);
            reify_ = true;
            compress_uvars = (uu___241_1354.compress_uvars);
            no_full_norm = (uu___241_1354.no_full_norm);
            check_no_uvars = (uu___241_1354.check_no_uvars);
            unmeta = (uu___241_1354.unmeta);
            unascribe = (uu___241_1354.unascribe);
            in_full_norm_request = (uu___241_1354.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___241_1354.weakly_reduce_scrutinee);
            nbe_step = (uu___241_1354.nbe_step)
          }
      | FStar_TypeChecker_Env.CompressUvars  ->
          let uu___242_1355 = fs  in
          {
            beta = (uu___242_1355.beta);
            iota = (uu___242_1355.iota);
            zeta = (uu___242_1355.zeta);
            weak = (uu___242_1355.weak);
            hnf = (uu___242_1355.hnf);
            primops = (uu___242_1355.primops);
            do_not_unfold_pure_lets = (uu___242_1355.do_not_unfold_pure_lets);
            unfold_until = (uu___242_1355.unfold_until);
            unfold_only = (uu___242_1355.unfold_only);
            unfold_fully = (uu___242_1355.unfold_fully);
            unfold_attr = (uu___242_1355.unfold_attr);
            unfold_tac = (uu___242_1355.unfold_tac);
            pure_subterms_within_computations =
              (uu___242_1355.pure_subterms_within_computations);
            simplify = (uu___242_1355.simplify);
            erase_universes = (uu___242_1355.erase_universes);
            allow_unbound_universes = (uu___242_1355.allow_unbound_universes);
            reify_ = (uu___242_1355.reify_);
            compress_uvars = true;
            no_full_norm = (uu___242_1355.no_full_norm);
            check_no_uvars = (uu___242_1355.check_no_uvars);
            unmeta = (uu___242_1355.unmeta);
            unascribe = (uu___242_1355.unascribe);
            in_full_norm_request = (uu___242_1355.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___242_1355.weakly_reduce_scrutinee);
            nbe_step = (uu___242_1355.nbe_step)
          }
      | FStar_TypeChecker_Env.NoFullNorm  ->
          let uu___243_1356 = fs  in
          {
            beta = (uu___243_1356.beta);
            iota = (uu___243_1356.iota);
            zeta = (uu___243_1356.zeta);
            weak = (uu___243_1356.weak);
            hnf = (uu___243_1356.hnf);
            primops = (uu___243_1356.primops);
            do_not_unfold_pure_lets = (uu___243_1356.do_not_unfold_pure_lets);
            unfold_until = (uu___243_1356.unfold_until);
            unfold_only = (uu___243_1356.unfold_only);
            unfold_fully = (uu___243_1356.unfold_fully);
            unfold_attr = (uu___243_1356.unfold_attr);
            unfold_tac = (uu___243_1356.unfold_tac);
            pure_subterms_within_computations =
              (uu___243_1356.pure_subterms_within_computations);
            simplify = (uu___243_1356.simplify);
            erase_universes = (uu___243_1356.erase_universes);
            allow_unbound_universes = (uu___243_1356.allow_unbound_universes);
            reify_ = (uu___243_1356.reify_);
            compress_uvars = (uu___243_1356.compress_uvars);
            no_full_norm = true;
            check_no_uvars = (uu___243_1356.check_no_uvars);
            unmeta = (uu___243_1356.unmeta);
            unascribe = (uu___243_1356.unascribe);
            in_full_norm_request = (uu___243_1356.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___243_1356.weakly_reduce_scrutinee);
            nbe_step = (uu___243_1356.nbe_step)
          }
      | FStar_TypeChecker_Env.CheckNoUvars  ->
          let uu___244_1357 = fs  in
          {
            beta = (uu___244_1357.beta);
            iota = (uu___244_1357.iota);
            zeta = (uu___244_1357.zeta);
            weak = (uu___244_1357.weak);
            hnf = (uu___244_1357.hnf);
            primops = (uu___244_1357.primops);
            do_not_unfold_pure_lets = (uu___244_1357.do_not_unfold_pure_lets);
            unfold_until = (uu___244_1357.unfold_until);
            unfold_only = (uu___244_1357.unfold_only);
            unfold_fully = (uu___244_1357.unfold_fully);
            unfold_attr = (uu___244_1357.unfold_attr);
            unfold_tac = (uu___244_1357.unfold_tac);
            pure_subterms_within_computations =
              (uu___244_1357.pure_subterms_within_computations);
            simplify = (uu___244_1357.simplify);
            erase_universes = (uu___244_1357.erase_universes);
            allow_unbound_universes = (uu___244_1357.allow_unbound_universes);
            reify_ = (uu___244_1357.reify_);
            compress_uvars = (uu___244_1357.compress_uvars);
            no_full_norm = (uu___244_1357.no_full_norm);
            check_no_uvars = true;
            unmeta = (uu___244_1357.unmeta);
            unascribe = (uu___244_1357.unascribe);
            in_full_norm_request = (uu___244_1357.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___244_1357.weakly_reduce_scrutinee);
            nbe_step = (uu___244_1357.nbe_step)
          }
      | FStar_TypeChecker_Env.Unmeta  ->
          let uu___245_1358 = fs  in
          {
            beta = (uu___245_1358.beta);
            iota = (uu___245_1358.iota);
            zeta = (uu___245_1358.zeta);
            weak = (uu___245_1358.weak);
            hnf = (uu___245_1358.hnf);
            primops = (uu___245_1358.primops);
            do_not_unfold_pure_lets = (uu___245_1358.do_not_unfold_pure_lets);
            unfold_until = (uu___245_1358.unfold_until);
            unfold_only = (uu___245_1358.unfold_only);
            unfold_fully = (uu___245_1358.unfold_fully);
            unfold_attr = (uu___245_1358.unfold_attr);
            unfold_tac = (uu___245_1358.unfold_tac);
            pure_subterms_within_computations =
              (uu___245_1358.pure_subterms_within_computations);
            simplify = (uu___245_1358.simplify);
            erase_universes = (uu___245_1358.erase_universes);
            allow_unbound_universes = (uu___245_1358.allow_unbound_universes);
            reify_ = (uu___245_1358.reify_);
            compress_uvars = (uu___245_1358.compress_uvars);
            no_full_norm = (uu___245_1358.no_full_norm);
            check_no_uvars = (uu___245_1358.check_no_uvars);
            unmeta = true;
            unascribe = (uu___245_1358.unascribe);
            in_full_norm_request = (uu___245_1358.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___245_1358.weakly_reduce_scrutinee);
            nbe_step = (uu___245_1358.nbe_step)
          }
      | FStar_TypeChecker_Env.Unascribe  ->
          let uu___246_1359 = fs  in
          {
            beta = (uu___246_1359.beta);
            iota = (uu___246_1359.iota);
            zeta = (uu___246_1359.zeta);
            weak = (uu___246_1359.weak);
            hnf = (uu___246_1359.hnf);
            primops = (uu___246_1359.primops);
            do_not_unfold_pure_lets = (uu___246_1359.do_not_unfold_pure_lets);
            unfold_until = (uu___246_1359.unfold_until);
            unfold_only = (uu___246_1359.unfold_only);
            unfold_fully = (uu___246_1359.unfold_fully);
            unfold_attr = (uu___246_1359.unfold_attr);
            unfold_tac = (uu___246_1359.unfold_tac);
            pure_subterms_within_computations =
              (uu___246_1359.pure_subterms_within_computations);
            simplify = (uu___246_1359.simplify);
            erase_universes = (uu___246_1359.erase_universes);
            allow_unbound_universes = (uu___246_1359.allow_unbound_universes);
            reify_ = (uu___246_1359.reify_);
            compress_uvars = (uu___246_1359.compress_uvars);
            no_full_norm = (uu___246_1359.no_full_norm);
            check_no_uvars = (uu___246_1359.check_no_uvars);
            unmeta = (uu___246_1359.unmeta);
            unascribe = true;
            in_full_norm_request = (uu___246_1359.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___246_1359.weakly_reduce_scrutinee);
            nbe_step = (uu___246_1359.nbe_step)
          }
      | FStar_TypeChecker_Env.NBE  ->
          let uu___247_1360 = fs  in
          {
            beta = (uu___247_1360.beta);
            iota = (uu___247_1360.iota);
            zeta = (uu___247_1360.zeta);
            weak = (uu___247_1360.weak);
            hnf = (uu___247_1360.hnf);
            primops = (uu___247_1360.primops);
            do_not_unfold_pure_lets = (uu___247_1360.do_not_unfold_pure_lets);
            unfold_until = (uu___247_1360.unfold_until);
            unfold_only = (uu___247_1360.unfold_only);
            unfold_fully = (uu___247_1360.unfold_fully);
            unfold_attr = (uu___247_1360.unfold_attr);
            unfold_tac = (uu___247_1360.unfold_tac);
            pure_subterms_within_computations =
              (uu___247_1360.pure_subterms_within_computations);
            simplify = (uu___247_1360.simplify);
            erase_universes = (uu___247_1360.erase_universes);
            allow_unbound_universes = (uu___247_1360.allow_unbound_universes);
            reify_ = (uu___247_1360.reify_);
            compress_uvars = (uu___247_1360.compress_uvars);
            no_full_norm = (uu___247_1360.no_full_norm);
            check_no_uvars = (uu___247_1360.check_no_uvars);
            unmeta = (uu___247_1360.unmeta);
            unascribe = (uu___247_1360.unascribe);
            in_full_norm_request = (uu___247_1360.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___247_1360.weakly_reduce_scrutinee);
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
  { psc_range = FStar_Range.dummyRange; psc_subst = (fun uu____1413  -> []) } 
let (psc_range : psc -> FStar_Range.range) = fun psc  -> psc.psc_range 
let (psc_subst : psc -> FStar_Syntax_Syntax.subst_t) =
  fun psc  -> psc.psc_subst () 
type debug_switches =
  {
  gen: Prims.bool ;
  primop: Prims.bool ;
  unfolding: Prims.bool ;
  b380: Prims.bool ;
  wpe: Prims.bool ;
  norm_delayed: Prims.bool ;
  print_normalized: Prims.bool }
let (__proj__Mkdebug_switches__item__gen : debug_switches -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { gen = __fname__gen; primop = __fname__primop;
        unfolding = __fname__unfolding; b380 = __fname__b380;
        wpe = __fname__wpe; norm_delayed = __fname__norm_delayed;
        print_normalized = __fname__print_normalized;_} -> __fname__gen
  
let (__proj__Mkdebug_switches__item__primop : debug_switches -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { gen = __fname__gen; primop = __fname__primop;
        unfolding = __fname__unfolding; b380 = __fname__b380;
        wpe = __fname__wpe; norm_delayed = __fname__norm_delayed;
        print_normalized = __fname__print_normalized;_} -> __fname__primop
  
let (__proj__Mkdebug_switches__item__unfolding :
  debug_switches -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { gen = __fname__gen; primop = __fname__primop;
        unfolding = __fname__unfolding; b380 = __fname__b380;
        wpe = __fname__wpe; norm_delayed = __fname__norm_delayed;
        print_normalized = __fname__print_normalized;_} -> __fname__unfolding
  
let (__proj__Mkdebug_switches__item__b380 : debug_switches -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { gen = __fname__gen; primop = __fname__primop;
        unfolding = __fname__unfolding; b380 = __fname__b380;
        wpe = __fname__wpe; norm_delayed = __fname__norm_delayed;
        print_normalized = __fname__print_normalized;_} -> __fname__b380
  
let (__proj__Mkdebug_switches__item__wpe : debug_switches -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { gen = __fname__gen; primop = __fname__primop;
        unfolding = __fname__unfolding; b380 = __fname__b380;
        wpe = __fname__wpe; norm_delayed = __fname__norm_delayed;
        print_normalized = __fname__print_normalized;_} -> __fname__wpe
  
let (__proj__Mkdebug_switches__item__norm_delayed :
  debug_switches -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { gen = __fname__gen; primop = __fname__primop;
        unfolding = __fname__unfolding; b380 = __fname__b380;
        wpe = __fname__wpe; norm_delayed = __fname__norm_delayed;
        print_normalized = __fname__print_normalized;_} ->
        __fname__norm_delayed
  
let (__proj__Mkdebug_switches__item__print_normalized :
  debug_switches -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { gen = __fname__gen; primop = __fname__primop;
        unfolding = __fname__unfolding; b380 = __fname__b380;
        wpe = __fname__wpe; norm_delayed = __fname__norm_delayed;
        print_normalized = __fname__print_normalized;_} ->
        __fname__print_normalized
  
type primitive_step =
  {
  name: FStar_Ident.lid ;
  arity: Prims.int ;
  auto_reflect: Prims.int FStar_Pervasives_Native.option ;
  strong_reduction_ok: Prims.bool ;
  requires_binder_substitution: Prims.bool ;
  interpretation:
    psc ->
      FStar_Syntax_Syntax.args ->
        FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
    }
let (__proj__Mkprimitive_step__item__name :
  primitive_step -> FStar_Ident.lid) =
  fun projectee  ->
    match projectee with
    | { name = __fname__name; arity = __fname__arity;
        auto_reflect = __fname__auto_reflect;
        strong_reduction_ok = __fname__strong_reduction_ok;
        requires_binder_substitution = __fname__requires_binder_substitution;
        interpretation = __fname__interpretation;_} -> __fname__name
  
let (__proj__Mkprimitive_step__item__arity : primitive_step -> Prims.int) =
  fun projectee  ->
    match projectee with
    | { name = __fname__name; arity = __fname__arity;
        auto_reflect = __fname__auto_reflect;
        strong_reduction_ok = __fname__strong_reduction_ok;
        requires_binder_substitution = __fname__requires_binder_substitution;
        interpretation = __fname__interpretation;_} -> __fname__arity
  
let (__proj__Mkprimitive_step__item__auto_reflect :
  primitive_step -> Prims.int FStar_Pervasives_Native.option) =
  fun projectee  ->
    match projectee with
    | { name = __fname__name; arity = __fname__arity;
        auto_reflect = __fname__auto_reflect;
        strong_reduction_ok = __fname__strong_reduction_ok;
        requires_binder_substitution = __fname__requires_binder_substitution;
        interpretation = __fname__interpretation;_} -> __fname__auto_reflect
  
let (__proj__Mkprimitive_step__item__strong_reduction_ok :
  primitive_step -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { name = __fname__name; arity = __fname__arity;
        auto_reflect = __fname__auto_reflect;
        strong_reduction_ok = __fname__strong_reduction_ok;
        requires_binder_substitution = __fname__requires_binder_substitution;
        interpretation = __fname__interpretation;_} ->
        __fname__strong_reduction_ok
  
let (__proj__Mkprimitive_step__item__requires_binder_substitution :
  primitive_step -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { name = __fname__name; arity = __fname__arity;
        auto_reflect = __fname__auto_reflect;
        strong_reduction_ok = __fname__strong_reduction_ok;
        requires_binder_substitution = __fname__requires_binder_substitution;
        interpretation = __fname__interpretation;_} ->
        __fname__requires_binder_substitution
  
let (__proj__Mkprimitive_step__item__interpretation :
  primitive_step ->
    psc ->
      FStar_Syntax_Syntax.args ->
        FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun projectee  ->
    match projectee with
    | { name = __fname__name; arity = __fname__arity;
        auto_reflect = __fname__auto_reflect;
        strong_reduction_ok = __fname__strong_reduction_ok;
        requires_binder_substitution = __fname__requires_binder_substitution;
        interpretation = __fname__interpretation;_} ->
        __fname__interpretation
  
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
             let uu____1990 = FStar_Ident.text_of_lid p.name  in
             FStar_Util.psmap_add m1 uu____1990 p) l m
  
let (prim_from_list :
  primitive_step Prims.list -> primitive_step FStar_Util.psmap) =
  fun l  ->
    let uu____2004 = FStar_Util.psmap_empty ()  in add_steps uu____2004 l
  
let (find_prim_step :
  cfg ->
    FStar_Syntax_Syntax.fv -> primitive_step FStar_Pervasives_Native.option)
  =
  fun cfg  ->
    fun fv  ->
      let uu____2019 =
        FStar_Ident.text_of_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
         in
      FStar_Util.psmap_try_find cfg.primitive_steps uu____2019
  
let (is_prim_step : cfg -> FStar_Syntax_Syntax.fv -> Prims.bool) =
  fun cfg  ->
    fun fv  ->
      let uu____2030 =
        let uu____2033 =
          FStar_Ident.text_of_lid
            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
           in
        FStar_Util.psmap_try_find cfg.primitive_steps uu____2033  in
      FStar_Util.is_some uu____2030
  
let (log : cfg -> (unit -> unit) -> unit) =
  fun cfg  -> fun f  -> if (cfg.debug).gen then f () else () 
let (log_primops : cfg -> (unit -> unit) -> unit) =
  fun cfg  -> fun f  -> if (cfg.debug).primop then f () else () 
let (log_unfolding : cfg -> (unit -> unit) -> unit) =
  fun cfg  -> fun f  -> if (cfg.debug).unfolding then f () else () 
let (log_nbe : cfg -> (unit -> unit) -> unit) =
  fun cfg  ->
    fun f  ->
      let uu____2097 =
        FStar_All.pipe_left (FStar_TypeChecker_Env.debug cfg.tcenv)
          (FStar_Options.Other "NBE")
         in
      if uu____2097 then f () else ()
  
let mk :
  'Auu____2105 .
    'Auu____2105 ->
      FStar_Range.range -> 'Auu____2105 FStar_Syntax_Syntax.syntax
  =
  fun t  -> fun r  -> FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None r 
let (built_in_primitive_steps : primitive_step FStar_Util.psmap) =
  let arg_as_int a =
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a)
      (FStar_Syntax_Embeddings.try_unembed FStar_Syntax_Embeddings.e_int)
     in
  let arg_as_bool a =
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a)
      (FStar_Syntax_Embeddings.try_unembed FStar_Syntax_Embeddings.e_bool)
     in
  let arg_as_char a =
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a)
      (FStar_Syntax_Embeddings.try_unembed FStar_Syntax_Embeddings.e_char)
     in
  let arg_as_string a =
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a)
      (FStar_Syntax_Embeddings.try_unembed FStar_Syntax_Embeddings.e_string)
     in
  let arg_as_list e a =
    let uu____2207 =
      let uu____2216 = FStar_Syntax_Embeddings.e_list e  in
      FStar_Syntax_Embeddings.try_unembed uu____2216  in
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a) uu____2207  in
  let arg_as_bounded_int uu____2242 =
    match uu____2242 with
    | (a,uu____2254) ->
        let uu____2261 =
          let uu____2262 = FStar_Syntax_Subst.compress a  in
          uu____2262.FStar_Syntax_Syntax.n  in
        (match uu____2261 with
         | FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv1;
                FStar_Syntax_Syntax.pos = uu____2272;
                FStar_Syntax_Syntax.vars = uu____2273;_},({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_constant
                                                              (FStar_Const.Const_int
                                                              (i,FStar_Pervasives_Native.None
                                                               ));
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____2275;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____2276;_},uu____2277)::[])
             when
             let uu____2316 =
               FStar_Ident.text_of_lid
                 (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                in
             FStar_Util.ends_with uu____2316 "int_to_t" ->
             let uu____2317 =
               let uu____2322 = FStar_BigInt.big_int_of_string i  in
               (fv1, uu____2322)  in
             FStar_Pervasives_Native.Some uu____2317
         | uu____2327 -> FStar_Pervasives_Native.None)
     in
  let lift_unary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a)::[] ->
        let uu____2375 = f a  in FStar_Pervasives_Native.Some uu____2375
    | uu____2376 -> FStar_Pervasives_Native.None  in
  let lift_binary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a0)::(FStar_Pervasives_Native.Some
        a1)::[] ->
        let uu____2432 = f a0 a1  in FStar_Pervasives_Native.Some uu____2432
    | uu____2433 -> FStar_Pervasives_Native.None  in
  let unary_op as_a f res args =
    let uu____2491 = FStar_List.map as_a args  in
    lift_unary (f res.psc_range) uu____2491  in
  let binary_op as_a f res args =
    let uu____2562 = FStar_List.map as_a args  in
    lift_binary (f res.psc_range) uu____2562  in
  let as_primitive_step is_strong uu____2599 =
    match uu____2599 with
    | (l,arity,f) ->
        {
          name = l;
          arity;
          auto_reflect = FStar_Pervasives_Native.None;
          strong_reduction_ok = is_strong;
          requires_binder_substitution = false;
          interpretation = f
        }
     in
  let unary_int_op f =
    unary_op arg_as_int
      (fun r  ->
         fun x  ->
           let uu____2659 = f x  in
           FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_int r
             uu____2659)
     in
  let binary_int_op f =
    binary_op arg_as_int
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____2695 = f x y  in
             FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_int r
               uu____2695)
     in
  let unary_bool_op f =
    unary_op arg_as_bool
      (fun r  ->
         fun x  ->
           let uu____2724 = f x  in
           FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_bool r
             uu____2724)
     in
  let binary_bool_op f =
    binary_op arg_as_bool
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____2760 = f x y  in
             FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_bool r
               uu____2760)
     in
  let binary_string_op f =
    binary_op arg_as_string
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____2796 = f x y  in
             FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_string r
               uu____2796)
     in
  let mixed_binary_op as_a as_b embed_c f res args =
    match args with
    | a::b::[] ->
        let uu____2928 =
          let uu____2937 = as_a a  in
          let uu____2940 = as_b b  in (uu____2937, uu____2940)  in
        (match uu____2928 with
         | (FStar_Pervasives_Native.Some a1,FStar_Pervasives_Native.Some b1)
             ->
             let uu____2955 =
               let uu____2956 = f res.psc_range a1 b1  in
               embed_c res.psc_range uu____2956  in
             FStar_Pervasives_Native.Some uu____2955
         | uu____2957 -> FStar_Pervasives_Native.None)
    | uu____2966 -> FStar_Pervasives_Native.None  in
  let list_of_string' rng s =
    let name l =
      let uu____2986 =
        let uu____2987 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
            FStar_Pervasives_Native.None
           in
        FStar_Syntax_Syntax.Tm_fvar uu____2987  in
      mk uu____2986 rng  in
    let char_t = name FStar_Parser_Const.char_lid  in
    let charterm c =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c)) rng  in
    let uu____3001 =
      let uu____3004 = FStar_String.list_of_string s  in
      FStar_List.map charterm uu____3004  in
    FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu____3001  in
  let string_of_list' rng l =
    let s = FStar_String.string_of_list l  in FStar_Syntax_Util.exp_string s
     in
  let string_compare' rng s1 s2 =
    let r = FStar_String.compare s1 s2  in
    let uu____3046 =
      let uu____3047 = FStar_Util.string_of_int r  in
      FStar_BigInt.big_int_of_string uu____3047  in
    FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_int rng
      uu____3046
     in
  let string_concat' psc args =
    match args with
    | a1::a2::[] ->
        let uu____3111 = arg_as_string a1  in
        (match uu____3111 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____3117 = arg_as_list FStar_Syntax_Embeddings.e_string a2
                in
             (match uu____3117 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2  in
                  let uu____3130 =
                    FStar_Syntax_Embeddings.embed
                      FStar_Syntax_Embeddings.e_string psc.psc_range r
                     in
                  FStar_Pervasives_Native.Some uu____3130
              | uu____3131 -> FStar_Pervasives_Native.None)
         | uu____3136 -> FStar_Pervasives_Native.None)
    | uu____3139 -> FStar_Pervasives_Native.None  in
  let string_of_int1 rng i =
    let uu____3159 = FStar_BigInt.string_of_big_int i  in
    FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_string rng
      uu____3159
     in
  let string_of_bool1 rng b =
    FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_string rng
      (if b then "true" else "false")
     in
  let mk_range1 psc args =
    match args with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____3196 =
          let uu____3217 = arg_as_string fn  in
          let uu____3220 = arg_as_int from_line  in
          let uu____3223 = arg_as_int from_col  in
          let uu____3226 = arg_as_int to_line  in
          let uu____3229 = arg_as_int to_col  in
          (uu____3217, uu____3220, uu____3223, uu____3226, uu____3229)  in
        (match uu____3196 with
         | (FStar_Pervasives_Native.Some fn1,FStar_Pervasives_Native.Some
            from_l,FStar_Pervasives_Native.Some
            from_c,FStar_Pervasives_Native.Some
            to_l,FStar_Pervasives_Native.Some to_c) ->
             let r =
               let uu____3260 =
                 let uu____3261 = FStar_BigInt.to_int_fs from_l  in
                 let uu____3262 = FStar_BigInt.to_int_fs from_c  in
                 FStar_Range.mk_pos uu____3261 uu____3262  in
               let uu____3263 =
                 let uu____3264 = FStar_BigInt.to_int_fs to_l  in
                 let uu____3265 = FStar_BigInt.to_int_fs to_c  in
                 FStar_Range.mk_pos uu____3264 uu____3265  in
               FStar_Range.mk_range fn1 uu____3260 uu____3263  in
             let uu____3266 =
               FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_range
                 psc.psc_range r
                in
             FStar_Pervasives_Native.Some uu____3266
         | uu____3267 -> FStar_Pervasives_Native.None)
    | uu____3288 -> FStar_Pervasives_Native.None  in
  let decidable_eq neg psc args =
    let r = psc.psc_range  in
    let tru =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool true)) r
       in
    let fal =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool false)) r
       in
    match args with
    | (_typ,uu____3321)::(a1,uu____3323)::(a2,uu____3325)::[] ->
        let uu____3362 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____3362 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some (if neg then fal else tru)
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some (if neg then tru else fal)
         | uu____3367 -> FStar_Pervasives_Native.None)
    | uu____3368 -> failwith "Unexpected number of arguments"  in
  let prims_to_fstar_range_step psc args =
    match args with
    | (a1,uu____3399)::[] ->
        let uu____3408 =
          FStar_Syntax_Embeddings.try_unembed FStar_Syntax_Embeddings.e_range
            a1
           in
        (match uu____3408 with
         | FStar_Pervasives_Native.Some r ->
             let uu____3414 =
               FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_range
                 psc.psc_range r
                in
             FStar_Pervasives_Native.Some uu____3414
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
    | uu____3415 -> failwith "Unexpected number of arguments"  in
  let basic_ops =
    let uu____3441 =
      let uu____3458 =
        let uu____3475 =
          let uu____3492 =
            let uu____3509 =
              let uu____3526 =
                let uu____3543 =
                  let uu____3560 =
                    let uu____3577 =
                      let uu____3594 =
                        let uu____3611 =
                          let uu____3628 =
                            let uu____3645 =
                              let uu____3662 =
                                let uu____3679 =
                                  let uu____3696 =
                                    let uu____3713 =
                                      let uu____3730 =
                                        let uu____3747 =
                                          let uu____3764 =
                                            let uu____3781 =
                                              let uu____3798 =
                                                let uu____3813 =
                                                  FStar_Parser_Const.p2l
                                                    ["FStar";
                                                    "String";
                                                    "list_of_string"]
                                                   in
                                                (uu____3813,
                                                  (Prims.parse_int "1"),
                                                  (unary_op arg_as_string
                                                     list_of_string'))
                                                 in
                                              let uu____3822 =
                                                let uu____3839 =
                                                  let uu____3854 =
                                                    FStar_Parser_Const.p2l
                                                      ["FStar";
                                                      "String";
                                                      "string_of_list"]
                                                     in
                                                  (uu____3854,
                                                    (Prims.parse_int "1"),
                                                    (unary_op
                                                       (arg_as_list
                                                          FStar_Syntax_Embeddings.e_char)
                                                       string_of_list'))
                                                   in
                                                let uu____3867 =
                                                  let uu____3884 =
                                                    let uu____3899 =
                                                      FStar_Parser_Const.p2l
                                                        ["FStar";
                                                        "String";
                                                        "concat"]
                                                       in
                                                    (uu____3899,
                                                      (Prims.parse_int "2"),
                                                      string_concat')
                                                     in
                                                  let uu____3908 =
                                                    let uu____3925 =
                                                      let uu____3940 =
                                                        FStar_Parser_Const.p2l
                                                          ["Prims";
                                                          "mk_range"]
                                                         in
                                                      (uu____3940,
                                                        (Prims.parse_int "5"),
                                                        mk_range1)
                                                       in
                                                    [uu____3925]  in
                                                  uu____3884 :: uu____3908
                                                   in
                                                uu____3839 :: uu____3867  in
                                              uu____3798 :: uu____3822  in
                                            (FStar_Parser_Const.op_notEq,
                                              (Prims.parse_int "3"),
                                              (decidable_eq true)) ::
                                              uu____3781
                                             in
                                          (FStar_Parser_Const.op_Eq,
                                            (Prims.parse_int "3"),
                                            (decidable_eq false)) ::
                                            uu____3764
                                           in
                                        (FStar_Parser_Const.string_compare,
                                          (Prims.parse_int "2"),
                                          (binary_op arg_as_string
                                             string_compare'))
                                          :: uu____3747
                                         in
                                      (FStar_Parser_Const.string_of_bool_lid,
                                        (Prims.parse_int "1"),
                                        (unary_op arg_as_bool string_of_bool1))
                                        :: uu____3730
                                       in
                                    (FStar_Parser_Const.string_of_int_lid,
                                      (Prims.parse_int "1"),
                                      (unary_op arg_as_int string_of_int1))
                                      :: uu____3713
                                     in
                                  (FStar_Parser_Const.str_make_lid,
                                    (Prims.parse_int "2"),
                                    (mixed_binary_op arg_as_int arg_as_char
                                       (FStar_Syntax_Embeddings.embed
                                          FStar_Syntax_Embeddings.e_string)
                                       (fun r  ->
                                          fun x  ->
                                            fun y  ->
                                              let uu____4160 =
                                                FStar_BigInt.to_int_fs x  in
                                              FStar_String.make uu____4160 y)))
                                    :: uu____3696
                                   in
                                (FStar_Parser_Const.strcat_lid',
                                  (Prims.parse_int "2"),
                                  (binary_string_op
                                     (fun x  -> fun y  -> Prims.strcat x y)))
                                  :: uu____3679
                                 in
                              (FStar_Parser_Const.strcat_lid,
                                (Prims.parse_int "2"),
                                (binary_string_op
                                   (fun x  -> fun y  -> Prims.strcat x y)))
                                :: uu____3662
                               in
                            (FStar_Parser_Const.op_Or, (Prims.parse_int "2"),
                              (binary_bool_op (fun x  -> fun y  -> x || y)))
                              :: uu____3645
                             in
                          (FStar_Parser_Const.op_And, (Prims.parse_int "2"),
                            (binary_bool_op (fun x  -> fun y  -> x && y))) ::
                            uu____3628
                           in
                        (FStar_Parser_Const.op_Negation,
                          (Prims.parse_int "1"),
                          (unary_bool_op (fun x  -> Prims.op_Negation x))) ::
                          uu____3611
                         in
                      (FStar_Parser_Const.op_Modulus, (Prims.parse_int "2"),
                        (binary_int_op
                           (fun x  -> fun y  -> FStar_BigInt.mod_big_int x y)))
                        :: uu____3594
                       in
                    (FStar_Parser_Const.op_GTE, (Prims.parse_int "2"),
                      (binary_op arg_as_int
                         (fun r  ->
                            fun x  ->
                              fun y  ->
                                let uu____4355 = FStar_BigInt.ge_big_int x y
                                   in
                                FStar_Syntax_Embeddings.embed
                                  FStar_Syntax_Embeddings.e_bool r uu____4355)))
                      :: uu____3577
                     in
                  (FStar_Parser_Const.op_GT, (Prims.parse_int "2"),
                    (binary_op arg_as_int
                       (fun r  ->
                          fun x  ->
                            fun y  ->
                              let uu____4385 = FStar_BigInt.gt_big_int x y
                                 in
                              FStar_Syntax_Embeddings.embed
                                FStar_Syntax_Embeddings.e_bool r uu____4385)))
                    :: uu____3560
                   in
                (FStar_Parser_Const.op_LTE, (Prims.parse_int "2"),
                  (binary_op arg_as_int
                     (fun r  ->
                        fun x  ->
                          fun y  ->
                            let uu____4415 = FStar_BigInt.le_big_int x y  in
                            FStar_Syntax_Embeddings.embed
                              FStar_Syntax_Embeddings.e_bool r uu____4415)))
                  :: uu____3543
                 in
              (FStar_Parser_Const.op_LT, (Prims.parse_int "2"),
                (binary_op arg_as_int
                   (fun r  ->
                      fun x  ->
                        fun y  ->
                          let uu____4445 = FStar_BigInt.lt_big_int x y  in
                          FStar_Syntax_Embeddings.embed
                            FStar_Syntax_Embeddings.e_bool r uu____4445)))
                :: uu____3526
               in
            (FStar_Parser_Const.op_Division, (Prims.parse_int "2"),
              (binary_int_op
                 (fun x  -> fun y  -> FStar_BigInt.div_big_int x y)))
              :: uu____3509
             in
          (FStar_Parser_Const.op_Multiply, (Prims.parse_int "2"),
            (binary_int_op
               (fun x  -> fun y  -> FStar_BigInt.mult_big_int x y)))
            :: uu____3492
           in
        (FStar_Parser_Const.op_Subtraction, (Prims.parse_int "2"),
          (binary_int_op (fun x  -> fun y  -> FStar_BigInt.sub_big_int x y)))
          :: uu____3475
         in
      (FStar_Parser_Const.op_Addition, (Prims.parse_int "2"),
        (binary_int_op (fun x  -> fun y  -> FStar_BigInt.add_big_int x y)))
        :: uu____3458
       in
    (FStar_Parser_Const.op_Minus, (Prims.parse_int "1"),
      (unary_int_op (fun x  -> FStar_BigInt.minus_big_int x))) :: uu____3441
     in
  let weak_ops =
    let uu____4600 =
      let uu____4615 =
        FStar_Parser_Const.p2l ["FStar"; "Range"; "prims_to_fstar_range"]  in
      (uu____4615, (Prims.parse_int "1"), prims_to_fstar_range_step)  in
    [uu____4600]  in
  let bounded_arith_ops =
    let bounded_signed_int_types = ["Int8"; "Int16"; "Int32"; "Int64"]  in
    let bounded_unsigned_int_types =
      ["UInt8"; "UInt16"; "UInt32"; "UInt64"; "UInt128"]  in
    let int_as_bounded r int_to_t1 n1 =
      let c =
        FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_int r n1  in
      let int_to_t2 = FStar_Syntax_Syntax.fv_to_tm int_to_t1  in
      let uu____4695 =
        let uu____4700 =
          let uu____4701 = FStar_Syntax_Syntax.as_arg c  in [uu____4701]  in
        FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____4700  in
      uu____4695 FStar_Pervasives_Native.None r  in
    let add_sub_mul_v =
      FStar_All.pipe_right
        (FStar_List.append bounded_signed_int_types
           bounded_unsigned_int_types)
        (FStar_List.collect
           (fun m  ->
              let uu____4775 =
                let uu____4790 = FStar_Parser_Const.p2l ["FStar"; m; "add"]
                   in
                (uu____4790, (Prims.parse_int "2"),
                  (binary_op arg_as_bounded_int
                     (fun r  ->
                        fun uu____4812  ->
                          fun uu____4813  ->
                            match (uu____4812, uu____4813) with
                            | ((int_to_t1,x),(uu____4832,y)) ->
                                let uu____4842 = FStar_BigInt.add_big_int x y
                                   in
                                int_as_bounded r int_to_t1 uu____4842)))
                 in
              let uu____4843 =
                let uu____4860 =
                  let uu____4875 = FStar_Parser_Const.p2l ["FStar"; m; "sub"]
                     in
                  (uu____4875, (Prims.parse_int "2"),
                    (binary_op arg_as_bounded_int
                       (fun r  ->
                          fun uu____4897  ->
                            fun uu____4898  ->
                              match (uu____4897, uu____4898) with
                              | ((int_to_t1,x),(uu____4917,y)) ->
                                  let uu____4927 =
                                    FStar_BigInt.sub_big_int x y  in
                                  int_as_bounded r int_to_t1 uu____4927)))
                   in
                let uu____4928 =
                  let uu____4945 =
                    let uu____4960 =
                      FStar_Parser_Const.p2l ["FStar"; m; "mul"]  in
                    (uu____4960, (Prims.parse_int "2"),
                      (binary_op arg_as_bounded_int
                         (fun r  ->
                            fun uu____4982  ->
                              fun uu____4983  ->
                                match (uu____4982, uu____4983) with
                                | ((int_to_t1,x),(uu____5002,y)) ->
                                    let uu____5012 =
                                      FStar_BigInt.mult_big_int x y  in
                                    int_as_bounded r int_to_t1 uu____5012)))
                     in
                  let uu____5013 =
                    let uu____5030 =
                      let uu____5045 =
                        FStar_Parser_Const.p2l ["FStar"; m; "v"]  in
                      (uu____5045, (Prims.parse_int "1"),
                        (unary_op arg_as_bounded_int
                           (fun r  ->
                              fun uu____5063  ->
                                match uu____5063 with
                                | (int_to_t1,x) ->
                                    FStar_Syntax_Embeddings.embed
                                      FStar_Syntax_Embeddings.e_int r x)))
                       in
                    [uu____5030]  in
                  uu____4945 :: uu____5013  in
                uu____4860 :: uu____4928  in
              uu____4775 :: uu____4843))
       in
    let div_mod_unsigned =
      FStar_All.pipe_right bounded_unsigned_int_types
        (FStar_List.collect
           (fun m  ->
              let uu____5193 =
                let uu____5208 = FStar_Parser_Const.p2l ["FStar"; m; "div"]
                   in
                (uu____5208, (Prims.parse_int "2"),
                  (binary_op arg_as_bounded_int
                     (fun r  ->
                        fun uu____5230  ->
                          fun uu____5231  ->
                            match (uu____5230, uu____5231) with
                            | ((int_to_t1,x),(uu____5250,y)) ->
                                let uu____5260 = FStar_BigInt.div_big_int x y
                                   in
                                int_as_bounded r int_to_t1 uu____5260)))
                 in
              let uu____5261 =
                let uu____5278 =
                  let uu____5293 = FStar_Parser_Const.p2l ["FStar"; m; "rem"]
                     in
                  (uu____5293, (Prims.parse_int "2"),
                    (binary_op arg_as_bounded_int
                       (fun r  ->
                          fun uu____5315  ->
                            fun uu____5316  ->
                              match (uu____5315, uu____5316) with
                              | ((int_to_t1,x),(uu____5335,y)) ->
                                  let uu____5345 =
                                    FStar_BigInt.mod_big_int x y  in
                                  int_as_bounded r int_to_t1 uu____5345)))
                   in
                [uu____5278]  in
              uu____5193 :: uu____5261))
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
  let interp_prop psc args =
    let r = psc.psc_range  in
    match args with
    | (_typ,uu____5477)::(a1,uu____5479)::(a2,uu____5481)::[] ->
        let uu____5518 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____5518 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___248_5522 = FStar_Syntax_Util.t_true  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___248_5522.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___248_5522.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___249_5524 = FStar_Syntax_Util.t_false  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___249_5524.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___249_5524.FStar_Syntax_Syntax.vars)
                })
         | uu____5525 -> FStar_Pervasives_Native.None)
    | (_typ,uu____5527)::uu____5528::(a1,uu____5530)::(a2,uu____5532)::[] ->
        let uu____5581 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____5581 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___248_5585 = FStar_Syntax_Util.t_true  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___248_5585.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___248_5585.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___249_5587 = FStar_Syntax_Util.t_false  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___249_5587.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___249_5587.FStar_Syntax_Syntax.vars)
                })
         | uu____5588 -> FStar_Pervasives_Native.None)
    | uu____5589 -> failwith "Unexpected number of arguments"  in
  let propositional_equality =
    {
      name = FStar_Parser_Const.eq2_lid;
      arity = (Prims.parse_int "3");
      auto_reflect = FStar_Pervasives_Native.None;
      strong_reduction_ok = true;
      requires_binder_substitution = false;
      interpretation = interp_prop
    }  in
  let hetero_propositional_equality =
    {
      name = FStar_Parser_Const.eq3_lid;
      arity = (Prims.parse_int "4");
      auto_reflect = FStar_Pervasives_Native.None;
      strong_reduction_ok = true;
      requires_binder_substitution = false;
      interpretation = interp_prop
    }  in
  prim_from_list [propositional_equality; hetero_propositional_equality] 
let (plugins :
  (primitive_step -> unit,unit -> primitive_step Prims.list)
    FStar_Pervasives_Native.tuple2)
  =
  let plugins = FStar_Util.mk_ref []  in
  let register p =
    let uu____5619 =
      let uu____5622 = FStar_ST.op_Bang plugins  in p :: uu____5622  in
    FStar_ST.op_Colon_Equals plugins uu____5619  in
  let retrieve uu____5730 = FStar_ST.op_Bang plugins  in (register, retrieve) 
let (register_plugin : primitive_step -> unit) =
  fun p  -> FStar_Pervasives_Native.fst plugins p 
let (retrieve_plugins : unit -> primitive_step Prims.list) =
  fun uu____5807  -> FStar_Pervasives_Native.snd plugins () 
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
               (fun uu___221_5848  ->
                  match uu___221_5848 with
                  | FStar_TypeChecker_Env.UnfoldUntil k ->
                      [FStar_TypeChecker_Env.Unfold k]
                  | FStar_TypeChecker_Env.Eager_unfolding  ->
                      [FStar_TypeChecker_Env.Eager_unfolding_only]
                  | FStar_TypeChecker_Env.Inlining  ->
                      [FStar_TypeChecker_Env.InliningDelta]
                  | FStar_TypeChecker_Env.UnfoldTac  ->
                      [FStar_TypeChecker_Env.UnfoldTacDelta]
                  | uu____5852 -> []))
           in
        let d1 =
          match d with
          | [] -> [FStar_TypeChecker_Env.NoDelta]
          | uu____5858 -> d  in
        let uu____5861 = to_fsteps s  in
        let uu____5862 =
          let uu____5863 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Norm")  in
          let uu____5864 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Primops")  in
          let uu____5865 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Unfolding")
             in
          let uu____5866 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "380")  in
          let uu____5867 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "WPE")  in
          let uu____5868 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "NormDelayed")
             in
          let uu____5869 =
            FStar_TypeChecker_Env.debug e
              (FStar_Options.Other "print_normalized_terms")
             in
          {
            gen = uu____5863;
            primop = uu____5864;
            unfolding = uu____5865;
            b380 = uu____5866;
            wpe = uu____5867;
            norm_delayed = uu____5868;
            print_normalized = uu____5869
          }  in
        let uu____5870 =
          let uu____5873 =
            let uu____5876 = retrieve_plugins ()  in
            FStar_List.append uu____5876 psteps  in
          add_steps built_in_primitive_steps uu____5873  in
        let uu____5879 =
          (FStar_Options.normalize_pure_terms_for_extraction ()) ||
            (let uu____5881 =
               FStar_All.pipe_right s
                 (FStar_List.contains
                    FStar_TypeChecker_Env.PureSubtermsWithinComputations)
                in
             Prims.op_Negation uu____5881)
           in
        {
          steps = uu____5861;
          tcenv = e;
          debug = uu____5862;
          delta_level = d1;
          primitive_steps = uu____5870;
          strong = false;
          memoize_lazy = true;
          normalize_pure_lets = uu____5879;
          reifying = false
        }
  
let (config :
  FStar_TypeChecker_Env.step Prims.list -> FStar_TypeChecker_Env.env -> cfg)
  = fun s  -> fun e  -> config' [] s e 