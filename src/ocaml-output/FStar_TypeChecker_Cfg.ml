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
  
let (steps_to_string : fsteps -> Prims.string) =
  fun steps  ->
    let uu____1273 =
      let uu____1276 =
        let uu____1279 =
          let uu____1280 = FStar_Util.string_of_bool steps.beta  in
          FStar_Util.format1 "    beta = %s;" uu____1280  in
        let uu____1281 =
          let uu____1284 =
            let uu____1285 = FStar_Util.string_of_bool steps.iota  in
            FStar_Util.format1 "    iota = %s;" uu____1285  in
          let uu____1286 =
            let uu____1289 =
              let uu____1290 = FStar_Util.string_of_bool steps.zeta  in
              FStar_Util.format1 "    zeta = %s;" uu____1290  in
            let uu____1291 =
              let uu____1294 =
                let uu____1295 = FStar_Util.string_of_bool steps.weak  in
                FStar_Util.format1 "    weak = %s;" uu____1295  in
              let uu____1296 =
                let uu____1299 =
                  let uu____1300 = FStar_Util.string_of_bool steps.hnf  in
                  FStar_Util.format1 "    hnf = %s;" uu____1300  in
                let uu____1301 =
                  let uu____1304 =
                    let uu____1305 = FStar_Util.string_of_bool steps.primops
                       in
                    FStar_Util.format1 "    primops = %s;" uu____1305  in
                  let uu____1306 =
                    let uu____1309 =
                      let uu____1310 =
                        FStar_Util.string_of_bool
                          steps.do_not_unfold_pure_lets
                         in
                      FStar_Util.format1 "    do_not_unfold_pure_lets = %s;"
                        uu____1310
                       in
                    let uu____1311 =
                      let uu____1314 =
                        let uu____1315 =
                          FStar_Util.string_of_bool steps.unfold_tac  in
                        FStar_Util.format1 "    unfold_tac = %s;" uu____1315
                         in
                      let uu____1316 =
                        let uu____1319 =
                          let uu____1320 =
                            FStar_Util.string_of_bool
                              steps.pure_subterms_within_computations
                             in
                          FStar_Util.format1
                            "    pure_subterms_within_computations = %s;"
                            uu____1320
                           in
                        let uu____1321 =
                          let uu____1324 =
                            let uu____1325 =
                              FStar_Util.string_of_bool steps.simplify  in
                            FStar_Util.format1 "    simplify = %s;"
                              uu____1325
                             in
                          let uu____1326 =
                            let uu____1329 =
                              let uu____1330 =
                                FStar_Util.string_of_bool
                                  steps.erase_universes
                                 in
                              FStar_Util.format1 "    erase_universes = %s;"
                                uu____1330
                               in
                            let uu____1331 =
                              let uu____1334 =
                                let uu____1335 =
                                  FStar_Util.string_of_bool
                                    steps.allow_unbound_universes
                                   in
                                FStar_Util.format1
                                  "    allow_unbound_universes = %s;"
                                  uu____1335
                                 in
                              let uu____1336 =
                                let uu____1339 =
                                  let uu____1340 =
                                    FStar_Util.string_of_bool steps.reify_
                                     in
                                  FStar_Util.format1 "    reify_ = %s;"
                                    uu____1340
                                   in
                                let uu____1341 =
                                  let uu____1344 =
                                    let uu____1345 =
                                      FStar_Util.string_of_bool
                                        steps.compress_uvars
                                       in
                                    FStar_Util.format1
                                      "    compress_uvars = %s;" uu____1345
                                     in
                                  let uu____1346 =
                                    let uu____1349 =
                                      let uu____1350 =
                                        FStar_Util.string_of_bool
                                          steps.no_full_norm
                                         in
                                      FStar_Util.format1
                                        "    no_full_norm = %s;" uu____1350
                                       in
                                    let uu____1351 =
                                      let uu____1354 =
                                        let uu____1355 =
                                          FStar_Util.string_of_bool
                                            steps.check_no_uvars
                                           in
                                        FStar_Util.format1
                                          "    check_no_uvars = %s;"
                                          uu____1355
                                         in
                                      let uu____1356 =
                                        let uu____1359 =
                                          let uu____1360 =
                                            FStar_Util.string_of_bool
                                              steps.unmeta
                                             in
                                          FStar_Util.format1
                                            "    unmeta = %s;" uu____1360
                                           in
                                        let uu____1361 =
                                          let uu____1364 =
                                            let uu____1365 =
                                              FStar_Util.string_of_bool
                                                steps.unascribe
                                               in
                                            FStar_Util.format1
                                              "    unascribe = %s;"
                                              uu____1365
                                             in
                                          let uu____1366 =
                                            let uu____1369 =
                                              let uu____1370 =
                                                FStar_Util.string_of_bool
                                                  steps.in_full_norm_request
                                                 in
                                              FStar_Util.format1
                                                "    in_full_norm_request = %s;"
                                                uu____1370
                                               in
                                            let uu____1371 =
                                              let uu____1374 =
                                                let uu____1375 =
                                                  FStar_Util.string_of_bool
                                                    steps.weakly_reduce_scrutinee
                                                   in
                                                FStar_Util.format1
                                                  "    weakly_reduce_scrutinee = %s;"
                                                  uu____1375
                                                 in
                                              let uu____1376 =
                                                let uu____1379 =
                                                  let uu____1380 =
                                                    FStar_Util.string_of_bool
                                                      steps.nbe_step
                                                     in
                                                  FStar_Util.format1
                                                    "    nbe_step = %s;"
                                                    uu____1380
                                                   in
                                                [uu____1379; "  }"]  in
                                              uu____1374 :: uu____1376  in
                                            uu____1369 :: uu____1371  in
                                          uu____1364 :: uu____1366  in
                                        uu____1359 :: uu____1361  in
                                      uu____1354 :: uu____1356  in
                                    uu____1349 :: uu____1351  in
                                  uu____1344 :: uu____1346  in
                                uu____1339 :: uu____1341  in
                              uu____1334 :: uu____1336  in
                            uu____1329 :: uu____1331  in
                          uu____1324 :: uu____1326  in
                        uu____1319 :: uu____1321  in
                      uu____1314 :: uu____1316  in
                    uu____1309 :: uu____1311  in
                  uu____1304 :: uu____1306  in
                uu____1299 :: uu____1301  in
              uu____1294 :: uu____1296  in
            uu____1289 :: uu____1291  in
          uu____1284 :: uu____1286  in
        uu____1279 :: uu____1281  in
      "{" :: uu____1276  in
    FStar_String.concat "\n" uu____1273
  
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
      let add_opt x uu___224_1415 =
        match uu___224_1415 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.Some [x]
        | FStar_Pervasives_Native.Some xs ->
            FStar_Pervasives_Native.Some (x :: xs)
         in
      match s with
      | FStar_TypeChecker_Env.Beta  ->
          let uu___226_1435 = fs  in
          {
            beta = true;
            iota = (uu___226_1435.iota);
            zeta = (uu___226_1435.zeta);
            weak = (uu___226_1435.weak);
            hnf = (uu___226_1435.hnf);
            primops = (uu___226_1435.primops);
            do_not_unfold_pure_lets = (uu___226_1435.do_not_unfold_pure_lets);
            unfold_until = (uu___226_1435.unfold_until);
            unfold_only = (uu___226_1435.unfold_only);
            unfold_fully = (uu___226_1435.unfold_fully);
            unfold_attr = (uu___226_1435.unfold_attr);
            unfold_tac = (uu___226_1435.unfold_tac);
            pure_subterms_within_computations =
              (uu___226_1435.pure_subterms_within_computations);
            simplify = (uu___226_1435.simplify);
            erase_universes = (uu___226_1435.erase_universes);
            allow_unbound_universes = (uu___226_1435.allow_unbound_universes);
            reify_ = (uu___226_1435.reify_);
            compress_uvars = (uu___226_1435.compress_uvars);
            no_full_norm = (uu___226_1435.no_full_norm);
            check_no_uvars = (uu___226_1435.check_no_uvars);
            unmeta = (uu___226_1435.unmeta);
            unascribe = (uu___226_1435.unascribe);
            in_full_norm_request = (uu___226_1435.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___226_1435.weakly_reduce_scrutinee);
            nbe_step = (uu___226_1435.nbe_step)
          }
      | FStar_TypeChecker_Env.Iota  ->
          let uu___227_1436 = fs  in
          {
            beta = (uu___227_1436.beta);
            iota = true;
            zeta = (uu___227_1436.zeta);
            weak = (uu___227_1436.weak);
            hnf = (uu___227_1436.hnf);
            primops = (uu___227_1436.primops);
            do_not_unfold_pure_lets = (uu___227_1436.do_not_unfold_pure_lets);
            unfold_until = (uu___227_1436.unfold_until);
            unfold_only = (uu___227_1436.unfold_only);
            unfold_fully = (uu___227_1436.unfold_fully);
            unfold_attr = (uu___227_1436.unfold_attr);
            unfold_tac = (uu___227_1436.unfold_tac);
            pure_subterms_within_computations =
              (uu___227_1436.pure_subterms_within_computations);
            simplify = (uu___227_1436.simplify);
            erase_universes = (uu___227_1436.erase_universes);
            allow_unbound_universes = (uu___227_1436.allow_unbound_universes);
            reify_ = (uu___227_1436.reify_);
            compress_uvars = (uu___227_1436.compress_uvars);
            no_full_norm = (uu___227_1436.no_full_norm);
            check_no_uvars = (uu___227_1436.check_no_uvars);
            unmeta = (uu___227_1436.unmeta);
            unascribe = (uu___227_1436.unascribe);
            in_full_norm_request = (uu___227_1436.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___227_1436.weakly_reduce_scrutinee);
            nbe_step = (uu___227_1436.nbe_step)
          }
      | FStar_TypeChecker_Env.Zeta  ->
          let uu___228_1437 = fs  in
          {
            beta = (uu___228_1437.beta);
            iota = (uu___228_1437.iota);
            zeta = true;
            weak = (uu___228_1437.weak);
            hnf = (uu___228_1437.hnf);
            primops = (uu___228_1437.primops);
            do_not_unfold_pure_lets = (uu___228_1437.do_not_unfold_pure_lets);
            unfold_until = (uu___228_1437.unfold_until);
            unfold_only = (uu___228_1437.unfold_only);
            unfold_fully = (uu___228_1437.unfold_fully);
            unfold_attr = (uu___228_1437.unfold_attr);
            unfold_tac = (uu___228_1437.unfold_tac);
            pure_subterms_within_computations =
              (uu___228_1437.pure_subterms_within_computations);
            simplify = (uu___228_1437.simplify);
            erase_universes = (uu___228_1437.erase_universes);
            allow_unbound_universes = (uu___228_1437.allow_unbound_universes);
            reify_ = (uu___228_1437.reify_);
            compress_uvars = (uu___228_1437.compress_uvars);
            no_full_norm = (uu___228_1437.no_full_norm);
            check_no_uvars = (uu___228_1437.check_no_uvars);
            unmeta = (uu___228_1437.unmeta);
            unascribe = (uu___228_1437.unascribe);
            in_full_norm_request = (uu___228_1437.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___228_1437.weakly_reduce_scrutinee);
            nbe_step = (uu___228_1437.nbe_step)
          }
      | FStar_TypeChecker_Env.Exclude (FStar_TypeChecker_Env.Beta ) ->
          let uu___229_1438 = fs  in
          {
            beta = false;
            iota = (uu___229_1438.iota);
            zeta = (uu___229_1438.zeta);
            weak = (uu___229_1438.weak);
            hnf = (uu___229_1438.hnf);
            primops = (uu___229_1438.primops);
            do_not_unfold_pure_lets = (uu___229_1438.do_not_unfold_pure_lets);
            unfold_until = (uu___229_1438.unfold_until);
            unfold_only = (uu___229_1438.unfold_only);
            unfold_fully = (uu___229_1438.unfold_fully);
            unfold_attr = (uu___229_1438.unfold_attr);
            unfold_tac = (uu___229_1438.unfold_tac);
            pure_subterms_within_computations =
              (uu___229_1438.pure_subterms_within_computations);
            simplify = (uu___229_1438.simplify);
            erase_universes = (uu___229_1438.erase_universes);
            allow_unbound_universes = (uu___229_1438.allow_unbound_universes);
            reify_ = (uu___229_1438.reify_);
            compress_uvars = (uu___229_1438.compress_uvars);
            no_full_norm = (uu___229_1438.no_full_norm);
            check_no_uvars = (uu___229_1438.check_no_uvars);
            unmeta = (uu___229_1438.unmeta);
            unascribe = (uu___229_1438.unascribe);
            in_full_norm_request = (uu___229_1438.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___229_1438.weakly_reduce_scrutinee);
            nbe_step = (uu___229_1438.nbe_step)
          }
      | FStar_TypeChecker_Env.Exclude (FStar_TypeChecker_Env.Iota ) ->
          let uu___230_1439 = fs  in
          {
            beta = (uu___230_1439.beta);
            iota = false;
            zeta = (uu___230_1439.zeta);
            weak = (uu___230_1439.weak);
            hnf = (uu___230_1439.hnf);
            primops = (uu___230_1439.primops);
            do_not_unfold_pure_lets = (uu___230_1439.do_not_unfold_pure_lets);
            unfold_until = (uu___230_1439.unfold_until);
            unfold_only = (uu___230_1439.unfold_only);
            unfold_fully = (uu___230_1439.unfold_fully);
            unfold_attr = (uu___230_1439.unfold_attr);
            unfold_tac = (uu___230_1439.unfold_tac);
            pure_subterms_within_computations =
              (uu___230_1439.pure_subterms_within_computations);
            simplify = (uu___230_1439.simplify);
            erase_universes = (uu___230_1439.erase_universes);
            allow_unbound_universes = (uu___230_1439.allow_unbound_universes);
            reify_ = (uu___230_1439.reify_);
            compress_uvars = (uu___230_1439.compress_uvars);
            no_full_norm = (uu___230_1439.no_full_norm);
            check_no_uvars = (uu___230_1439.check_no_uvars);
            unmeta = (uu___230_1439.unmeta);
            unascribe = (uu___230_1439.unascribe);
            in_full_norm_request = (uu___230_1439.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___230_1439.weakly_reduce_scrutinee);
            nbe_step = (uu___230_1439.nbe_step)
          }
      | FStar_TypeChecker_Env.Exclude (FStar_TypeChecker_Env.Zeta ) ->
          let uu___231_1440 = fs  in
          {
            beta = (uu___231_1440.beta);
            iota = (uu___231_1440.iota);
            zeta = false;
            weak = (uu___231_1440.weak);
            hnf = (uu___231_1440.hnf);
            primops = (uu___231_1440.primops);
            do_not_unfold_pure_lets = (uu___231_1440.do_not_unfold_pure_lets);
            unfold_until = (uu___231_1440.unfold_until);
            unfold_only = (uu___231_1440.unfold_only);
            unfold_fully = (uu___231_1440.unfold_fully);
            unfold_attr = (uu___231_1440.unfold_attr);
            unfold_tac = (uu___231_1440.unfold_tac);
            pure_subterms_within_computations =
              (uu___231_1440.pure_subterms_within_computations);
            simplify = (uu___231_1440.simplify);
            erase_universes = (uu___231_1440.erase_universes);
            allow_unbound_universes = (uu___231_1440.allow_unbound_universes);
            reify_ = (uu___231_1440.reify_);
            compress_uvars = (uu___231_1440.compress_uvars);
            no_full_norm = (uu___231_1440.no_full_norm);
            check_no_uvars = (uu___231_1440.check_no_uvars);
            unmeta = (uu___231_1440.unmeta);
            unascribe = (uu___231_1440.unascribe);
            in_full_norm_request = (uu___231_1440.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___231_1440.weakly_reduce_scrutinee);
            nbe_step = (uu___231_1440.nbe_step)
          }
      | FStar_TypeChecker_Env.Exclude uu____1441 -> failwith "Bad exclude"
      | FStar_TypeChecker_Env.Weak  ->
          let uu___232_1442 = fs  in
          {
            beta = (uu___232_1442.beta);
            iota = (uu___232_1442.iota);
            zeta = (uu___232_1442.zeta);
            weak = true;
            hnf = (uu___232_1442.hnf);
            primops = (uu___232_1442.primops);
            do_not_unfold_pure_lets = (uu___232_1442.do_not_unfold_pure_lets);
            unfold_until = (uu___232_1442.unfold_until);
            unfold_only = (uu___232_1442.unfold_only);
            unfold_fully = (uu___232_1442.unfold_fully);
            unfold_attr = (uu___232_1442.unfold_attr);
            unfold_tac = (uu___232_1442.unfold_tac);
            pure_subterms_within_computations =
              (uu___232_1442.pure_subterms_within_computations);
            simplify = (uu___232_1442.simplify);
            erase_universes = (uu___232_1442.erase_universes);
            allow_unbound_universes = (uu___232_1442.allow_unbound_universes);
            reify_ = (uu___232_1442.reify_);
            compress_uvars = (uu___232_1442.compress_uvars);
            no_full_norm = (uu___232_1442.no_full_norm);
            check_no_uvars = (uu___232_1442.check_no_uvars);
            unmeta = (uu___232_1442.unmeta);
            unascribe = (uu___232_1442.unascribe);
            in_full_norm_request = (uu___232_1442.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___232_1442.weakly_reduce_scrutinee);
            nbe_step = (uu___232_1442.nbe_step)
          }
      | FStar_TypeChecker_Env.HNF  ->
          let uu___233_1443 = fs  in
          {
            beta = (uu___233_1443.beta);
            iota = (uu___233_1443.iota);
            zeta = (uu___233_1443.zeta);
            weak = (uu___233_1443.weak);
            hnf = true;
            primops = (uu___233_1443.primops);
            do_not_unfold_pure_lets = (uu___233_1443.do_not_unfold_pure_lets);
            unfold_until = (uu___233_1443.unfold_until);
            unfold_only = (uu___233_1443.unfold_only);
            unfold_fully = (uu___233_1443.unfold_fully);
            unfold_attr = (uu___233_1443.unfold_attr);
            unfold_tac = (uu___233_1443.unfold_tac);
            pure_subterms_within_computations =
              (uu___233_1443.pure_subterms_within_computations);
            simplify = (uu___233_1443.simplify);
            erase_universes = (uu___233_1443.erase_universes);
            allow_unbound_universes = (uu___233_1443.allow_unbound_universes);
            reify_ = (uu___233_1443.reify_);
            compress_uvars = (uu___233_1443.compress_uvars);
            no_full_norm = (uu___233_1443.no_full_norm);
            check_no_uvars = (uu___233_1443.check_no_uvars);
            unmeta = (uu___233_1443.unmeta);
            unascribe = (uu___233_1443.unascribe);
            in_full_norm_request = (uu___233_1443.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___233_1443.weakly_reduce_scrutinee);
            nbe_step = (uu___233_1443.nbe_step)
          }
      | FStar_TypeChecker_Env.Primops  ->
          let uu___234_1444 = fs  in
          {
            beta = (uu___234_1444.beta);
            iota = (uu___234_1444.iota);
            zeta = (uu___234_1444.zeta);
            weak = (uu___234_1444.weak);
            hnf = (uu___234_1444.hnf);
            primops = true;
            do_not_unfold_pure_lets = (uu___234_1444.do_not_unfold_pure_lets);
            unfold_until = (uu___234_1444.unfold_until);
            unfold_only = (uu___234_1444.unfold_only);
            unfold_fully = (uu___234_1444.unfold_fully);
            unfold_attr = (uu___234_1444.unfold_attr);
            unfold_tac = (uu___234_1444.unfold_tac);
            pure_subterms_within_computations =
              (uu___234_1444.pure_subterms_within_computations);
            simplify = (uu___234_1444.simplify);
            erase_universes = (uu___234_1444.erase_universes);
            allow_unbound_universes = (uu___234_1444.allow_unbound_universes);
            reify_ = (uu___234_1444.reify_);
            compress_uvars = (uu___234_1444.compress_uvars);
            no_full_norm = (uu___234_1444.no_full_norm);
            check_no_uvars = (uu___234_1444.check_no_uvars);
            unmeta = (uu___234_1444.unmeta);
            unascribe = (uu___234_1444.unascribe);
            in_full_norm_request = (uu___234_1444.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___234_1444.weakly_reduce_scrutinee);
            nbe_step = (uu___234_1444.nbe_step)
          }
      | FStar_TypeChecker_Env.Eager_unfolding  -> fs
      | FStar_TypeChecker_Env.Inlining  -> fs
      | FStar_TypeChecker_Env.DoNotUnfoldPureLets  ->
          let uu___235_1445 = fs  in
          {
            beta = (uu___235_1445.beta);
            iota = (uu___235_1445.iota);
            zeta = (uu___235_1445.zeta);
            weak = (uu___235_1445.weak);
            hnf = (uu___235_1445.hnf);
            primops = (uu___235_1445.primops);
            do_not_unfold_pure_lets = true;
            unfold_until = (uu___235_1445.unfold_until);
            unfold_only = (uu___235_1445.unfold_only);
            unfold_fully = (uu___235_1445.unfold_fully);
            unfold_attr = (uu___235_1445.unfold_attr);
            unfold_tac = (uu___235_1445.unfold_tac);
            pure_subterms_within_computations =
              (uu___235_1445.pure_subterms_within_computations);
            simplify = (uu___235_1445.simplify);
            erase_universes = (uu___235_1445.erase_universes);
            allow_unbound_universes = (uu___235_1445.allow_unbound_universes);
            reify_ = (uu___235_1445.reify_);
            compress_uvars = (uu___235_1445.compress_uvars);
            no_full_norm = (uu___235_1445.no_full_norm);
            check_no_uvars = (uu___235_1445.check_no_uvars);
            unmeta = (uu___235_1445.unmeta);
            unascribe = (uu___235_1445.unascribe);
            in_full_norm_request = (uu___235_1445.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___235_1445.weakly_reduce_scrutinee);
            nbe_step = (uu___235_1445.nbe_step)
          }
      | FStar_TypeChecker_Env.UnfoldUntil d ->
          let uu___236_1447 = fs  in
          {
            beta = (uu___236_1447.beta);
            iota = (uu___236_1447.iota);
            zeta = (uu___236_1447.zeta);
            weak = (uu___236_1447.weak);
            hnf = (uu___236_1447.hnf);
            primops = (uu___236_1447.primops);
            do_not_unfold_pure_lets = (uu___236_1447.do_not_unfold_pure_lets);
            unfold_until = (FStar_Pervasives_Native.Some d);
            unfold_only = (uu___236_1447.unfold_only);
            unfold_fully = (uu___236_1447.unfold_fully);
            unfold_attr = (uu___236_1447.unfold_attr);
            unfold_tac = (uu___236_1447.unfold_tac);
            pure_subterms_within_computations =
              (uu___236_1447.pure_subterms_within_computations);
            simplify = (uu___236_1447.simplify);
            erase_universes = (uu___236_1447.erase_universes);
            allow_unbound_universes = (uu___236_1447.allow_unbound_universes);
            reify_ = (uu___236_1447.reify_);
            compress_uvars = (uu___236_1447.compress_uvars);
            no_full_norm = (uu___236_1447.no_full_norm);
            check_no_uvars = (uu___236_1447.check_no_uvars);
            unmeta = (uu___236_1447.unmeta);
            unascribe = (uu___236_1447.unascribe);
            in_full_norm_request = (uu___236_1447.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___236_1447.weakly_reduce_scrutinee);
            nbe_step = (uu___236_1447.nbe_step)
          }
      | FStar_TypeChecker_Env.UnfoldOnly lids ->
          let uu___237_1451 = fs  in
          {
            beta = (uu___237_1451.beta);
            iota = (uu___237_1451.iota);
            zeta = (uu___237_1451.zeta);
            weak = (uu___237_1451.weak);
            hnf = (uu___237_1451.hnf);
            primops = (uu___237_1451.primops);
            do_not_unfold_pure_lets = (uu___237_1451.do_not_unfold_pure_lets);
            unfold_until = (uu___237_1451.unfold_until);
            unfold_only = (FStar_Pervasives_Native.Some lids);
            unfold_fully = (uu___237_1451.unfold_fully);
            unfold_attr = (uu___237_1451.unfold_attr);
            unfold_tac = (uu___237_1451.unfold_tac);
            pure_subterms_within_computations =
              (uu___237_1451.pure_subterms_within_computations);
            simplify = (uu___237_1451.simplify);
            erase_universes = (uu___237_1451.erase_universes);
            allow_unbound_universes = (uu___237_1451.allow_unbound_universes);
            reify_ = (uu___237_1451.reify_);
            compress_uvars = (uu___237_1451.compress_uvars);
            no_full_norm = (uu___237_1451.no_full_norm);
            check_no_uvars = (uu___237_1451.check_no_uvars);
            unmeta = (uu___237_1451.unmeta);
            unascribe = (uu___237_1451.unascribe);
            in_full_norm_request = (uu___237_1451.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___237_1451.weakly_reduce_scrutinee);
            nbe_step = (uu___237_1451.nbe_step)
          }
      | FStar_TypeChecker_Env.UnfoldFully lids ->
          let uu___238_1457 = fs  in
          {
            beta = (uu___238_1457.beta);
            iota = (uu___238_1457.iota);
            zeta = (uu___238_1457.zeta);
            weak = (uu___238_1457.weak);
            hnf = (uu___238_1457.hnf);
            primops = (uu___238_1457.primops);
            do_not_unfold_pure_lets = (uu___238_1457.do_not_unfold_pure_lets);
            unfold_until = (uu___238_1457.unfold_until);
            unfold_only = (uu___238_1457.unfold_only);
            unfold_fully = (FStar_Pervasives_Native.Some lids);
            unfold_attr = (uu___238_1457.unfold_attr);
            unfold_tac = (uu___238_1457.unfold_tac);
            pure_subterms_within_computations =
              (uu___238_1457.pure_subterms_within_computations);
            simplify = (uu___238_1457.simplify);
            erase_universes = (uu___238_1457.erase_universes);
            allow_unbound_universes = (uu___238_1457.allow_unbound_universes);
            reify_ = (uu___238_1457.reify_);
            compress_uvars = (uu___238_1457.compress_uvars);
            no_full_norm = (uu___238_1457.no_full_norm);
            check_no_uvars = (uu___238_1457.check_no_uvars);
            unmeta = (uu___238_1457.unmeta);
            unascribe = (uu___238_1457.unascribe);
            in_full_norm_request = (uu___238_1457.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___238_1457.weakly_reduce_scrutinee);
            nbe_step = (uu___238_1457.nbe_step)
          }
      | FStar_TypeChecker_Env.UnfoldAttr attr ->
          let uu___239_1461 = fs  in
          {
            beta = (uu___239_1461.beta);
            iota = (uu___239_1461.iota);
            zeta = (uu___239_1461.zeta);
            weak = (uu___239_1461.weak);
            hnf = (uu___239_1461.hnf);
            primops = (uu___239_1461.primops);
            do_not_unfold_pure_lets = (uu___239_1461.do_not_unfold_pure_lets);
            unfold_until = (uu___239_1461.unfold_until);
            unfold_only = (uu___239_1461.unfold_only);
            unfold_fully = (uu___239_1461.unfold_fully);
            unfold_attr = (add_opt attr fs.unfold_attr);
            unfold_tac = (uu___239_1461.unfold_tac);
            pure_subterms_within_computations =
              (uu___239_1461.pure_subterms_within_computations);
            simplify = (uu___239_1461.simplify);
            erase_universes = (uu___239_1461.erase_universes);
            allow_unbound_universes = (uu___239_1461.allow_unbound_universes);
            reify_ = (uu___239_1461.reify_);
            compress_uvars = (uu___239_1461.compress_uvars);
            no_full_norm = (uu___239_1461.no_full_norm);
            check_no_uvars = (uu___239_1461.check_no_uvars);
            unmeta = (uu___239_1461.unmeta);
            unascribe = (uu___239_1461.unascribe);
            in_full_norm_request = (uu___239_1461.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___239_1461.weakly_reduce_scrutinee);
            nbe_step = (uu___239_1461.nbe_step)
          }
      | FStar_TypeChecker_Env.UnfoldTac  ->
          let uu___240_1462 = fs  in
          {
            beta = (uu___240_1462.beta);
            iota = (uu___240_1462.iota);
            zeta = (uu___240_1462.zeta);
            weak = (uu___240_1462.weak);
            hnf = (uu___240_1462.hnf);
            primops = (uu___240_1462.primops);
            do_not_unfold_pure_lets = (uu___240_1462.do_not_unfold_pure_lets);
            unfold_until = (uu___240_1462.unfold_until);
            unfold_only = (uu___240_1462.unfold_only);
            unfold_fully = (uu___240_1462.unfold_fully);
            unfold_attr = (uu___240_1462.unfold_attr);
            unfold_tac = true;
            pure_subterms_within_computations =
              (uu___240_1462.pure_subterms_within_computations);
            simplify = (uu___240_1462.simplify);
            erase_universes = (uu___240_1462.erase_universes);
            allow_unbound_universes = (uu___240_1462.allow_unbound_universes);
            reify_ = (uu___240_1462.reify_);
            compress_uvars = (uu___240_1462.compress_uvars);
            no_full_norm = (uu___240_1462.no_full_norm);
            check_no_uvars = (uu___240_1462.check_no_uvars);
            unmeta = (uu___240_1462.unmeta);
            unascribe = (uu___240_1462.unascribe);
            in_full_norm_request = (uu___240_1462.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___240_1462.weakly_reduce_scrutinee);
            nbe_step = (uu___240_1462.nbe_step)
          }
      | FStar_TypeChecker_Env.PureSubtermsWithinComputations  ->
          let uu___241_1463 = fs  in
          {
            beta = (uu___241_1463.beta);
            iota = (uu___241_1463.iota);
            zeta = (uu___241_1463.zeta);
            weak = (uu___241_1463.weak);
            hnf = (uu___241_1463.hnf);
            primops = (uu___241_1463.primops);
            do_not_unfold_pure_lets = (uu___241_1463.do_not_unfold_pure_lets);
            unfold_until = (uu___241_1463.unfold_until);
            unfold_only = (uu___241_1463.unfold_only);
            unfold_fully = (uu___241_1463.unfold_fully);
            unfold_attr = (uu___241_1463.unfold_attr);
            unfold_tac = (uu___241_1463.unfold_tac);
            pure_subterms_within_computations = true;
            simplify = (uu___241_1463.simplify);
            erase_universes = (uu___241_1463.erase_universes);
            allow_unbound_universes = (uu___241_1463.allow_unbound_universes);
            reify_ = (uu___241_1463.reify_);
            compress_uvars = (uu___241_1463.compress_uvars);
            no_full_norm = (uu___241_1463.no_full_norm);
            check_no_uvars = (uu___241_1463.check_no_uvars);
            unmeta = (uu___241_1463.unmeta);
            unascribe = (uu___241_1463.unascribe);
            in_full_norm_request = (uu___241_1463.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___241_1463.weakly_reduce_scrutinee);
            nbe_step = (uu___241_1463.nbe_step)
          }
      | FStar_TypeChecker_Env.Simplify  ->
          let uu___242_1464 = fs  in
          {
            beta = (uu___242_1464.beta);
            iota = (uu___242_1464.iota);
            zeta = (uu___242_1464.zeta);
            weak = (uu___242_1464.weak);
            hnf = (uu___242_1464.hnf);
            primops = (uu___242_1464.primops);
            do_not_unfold_pure_lets = (uu___242_1464.do_not_unfold_pure_lets);
            unfold_until = (uu___242_1464.unfold_until);
            unfold_only = (uu___242_1464.unfold_only);
            unfold_fully = (uu___242_1464.unfold_fully);
            unfold_attr = (uu___242_1464.unfold_attr);
            unfold_tac = (uu___242_1464.unfold_tac);
            pure_subterms_within_computations =
              (uu___242_1464.pure_subterms_within_computations);
            simplify = true;
            erase_universes = (uu___242_1464.erase_universes);
            allow_unbound_universes = (uu___242_1464.allow_unbound_universes);
            reify_ = (uu___242_1464.reify_);
            compress_uvars = (uu___242_1464.compress_uvars);
            no_full_norm = (uu___242_1464.no_full_norm);
            check_no_uvars = (uu___242_1464.check_no_uvars);
            unmeta = (uu___242_1464.unmeta);
            unascribe = (uu___242_1464.unascribe);
            in_full_norm_request = (uu___242_1464.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___242_1464.weakly_reduce_scrutinee);
            nbe_step = (uu___242_1464.nbe_step)
          }
      | FStar_TypeChecker_Env.EraseUniverses  ->
          let uu___243_1465 = fs  in
          {
            beta = (uu___243_1465.beta);
            iota = (uu___243_1465.iota);
            zeta = (uu___243_1465.zeta);
            weak = (uu___243_1465.weak);
            hnf = (uu___243_1465.hnf);
            primops = (uu___243_1465.primops);
            do_not_unfold_pure_lets = (uu___243_1465.do_not_unfold_pure_lets);
            unfold_until = (uu___243_1465.unfold_until);
            unfold_only = (uu___243_1465.unfold_only);
            unfold_fully = (uu___243_1465.unfold_fully);
            unfold_attr = (uu___243_1465.unfold_attr);
            unfold_tac = (uu___243_1465.unfold_tac);
            pure_subterms_within_computations =
              (uu___243_1465.pure_subterms_within_computations);
            simplify = (uu___243_1465.simplify);
            erase_universes = true;
            allow_unbound_universes = (uu___243_1465.allow_unbound_universes);
            reify_ = (uu___243_1465.reify_);
            compress_uvars = (uu___243_1465.compress_uvars);
            no_full_norm = (uu___243_1465.no_full_norm);
            check_no_uvars = (uu___243_1465.check_no_uvars);
            unmeta = (uu___243_1465.unmeta);
            unascribe = (uu___243_1465.unascribe);
            in_full_norm_request = (uu___243_1465.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___243_1465.weakly_reduce_scrutinee);
            nbe_step = (uu___243_1465.nbe_step)
          }
      | FStar_TypeChecker_Env.AllowUnboundUniverses  ->
          let uu___244_1466 = fs  in
          {
            beta = (uu___244_1466.beta);
            iota = (uu___244_1466.iota);
            zeta = (uu___244_1466.zeta);
            weak = (uu___244_1466.weak);
            hnf = (uu___244_1466.hnf);
            primops = (uu___244_1466.primops);
            do_not_unfold_pure_lets = (uu___244_1466.do_not_unfold_pure_lets);
            unfold_until = (uu___244_1466.unfold_until);
            unfold_only = (uu___244_1466.unfold_only);
            unfold_fully = (uu___244_1466.unfold_fully);
            unfold_attr = (uu___244_1466.unfold_attr);
            unfold_tac = (uu___244_1466.unfold_tac);
            pure_subterms_within_computations =
              (uu___244_1466.pure_subterms_within_computations);
            simplify = (uu___244_1466.simplify);
            erase_universes = (uu___244_1466.erase_universes);
            allow_unbound_universes = true;
            reify_ = (uu___244_1466.reify_);
            compress_uvars = (uu___244_1466.compress_uvars);
            no_full_norm = (uu___244_1466.no_full_norm);
            check_no_uvars = (uu___244_1466.check_no_uvars);
            unmeta = (uu___244_1466.unmeta);
            unascribe = (uu___244_1466.unascribe);
            in_full_norm_request = (uu___244_1466.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___244_1466.weakly_reduce_scrutinee);
            nbe_step = (uu___244_1466.nbe_step)
          }
      | FStar_TypeChecker_Env.Reify  ->
          let uu___245_1467 = fs  in
          {
            beta = (uu___245_1467.beta);
            iota = (uu___245_1467.iota);
            zeta = (uu___245_1467.zeta);
            weak = (uu___245_1467.weak);
            hnf = (uu___245_1467.hnf);
            primops = (uu___245_1467.primops);
            do_not_unfold_pure_lets = (uu___245_1467.do_not_unfold_pure_lets);
            unfold_until = (uu___245_1467.unfold_until);
            unfold_only = (uu___245_1467.unfold_only);
            unfold_fully = (uu___245_1467.unfold_fully);
            unfold_attr = (uu___245_1467.unfold_attr);
            unfold_tac = (uu___245_1467.unfold_tac);
            pure_subterms_within_computations =
              (uu___245_1467.pure_subterms_within_computations);
            simplify = (uu___245_1467.simplify);
            erase_universes = (uu___245_1467.erase_universes);
            allow_unbound_universes = (uu___245_1467.allow_unbound_universes);
            reify_ = true;
            compress_uvars = (uu___245_1467.compress_uvars);
            no_full_norm = (uu___245_1467.no_full_norm);
            check_no_uvars = (uu___245_1467.check_no_uvars);
            unmeta = (uu___245_1467.unmeta);
            unascribe = (uu___245_1467.unascribe);
            in_full_norm_request = (uu___245_1467.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___245_1467.weakly_reduce_scrutinee);
            nbe_step = (uu___245_1467.nbe_step)
          }
      | FStar_TypeChecker_Env.CompressUvars  ->
          let uu___246_1468 = fs  in
          {
            beta = (uu___246_1468.beta);
            iota = (uu___246_1468.iota);
            zeta = (uu___246_1468.zeta);
            weak = (uu___246_1468.weak);
            hnf = (uu___246_1468.hnf);
            primops = (uu___246_1468.primops);
            do_not_unfold_pure_lets = (uu___246_1468.do_not_unfold_pure_lets);
            unfold_until = (uu___246_1468.unfold_until);
            unfold_only = (uu___246_1468.unfold_only);
            unfold_fully = (uu___246_1468.unfold_fully);
            unfold_attr = (uu___246_1468.unfold_attr);
            unfold_tac = (uu___246_1468.unfold_tac);
            pure_subterms_within_computations =
              (uu___246_1468.pure_subterms_within_computations);
            simplify = (uu___246_1468.simplify);
            erase_universes = (uu___246_1468.erase_universes);
            allow_unbound_universes = (uu___246_1468.allow_unbound_universes);
            reify_ = (uu___246_1468.reify_);
            compress_uvars = true;
            no_full_norm = (uu___246_1468.no_full_norm);
            check_no_uvars = (uu___246_1468.check_no_uvars);
            unmeta = (uu___246_1468.unmeta);
            unascribe = (uu___246_1468.unascribe);
            in_full_norm_request = (uu___246_1468.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___246_1468.weakly_reduce_scrutinee);
            nbe_step = (uu___246_1468.nbe_step)
          }
      | FStar_TypeChecker_Env.NoFullNorm  ->
          let uu___247_1469 = fs  in
          {
            beta = (uu___247_1469.beta);
            iota = (uu___247_1469.iota);
            zeta = (uu___247_1469.zeta);
            weak = (uu___247_1469.weak);
            hnf = (uu___247_1469.hnf);
            primops = (uu___247_1469.primops);
            do_not_unfold_pure_lets = (uu___247_1469.do_not_unfold_pure_lets);
            unfold_until = (uu___247_1469.unfold_until);
            unfold_only = (uu___247_1469.unfold_only);
            unfold_fully = (uu___247_1469.unfold_fully);
            unfold_attr = (uu___247_1469.unfold_attr);
            unfold_tac = (uu___247_1469.unfold_tac);
            pure_subterms_within_computations =
              (uu___247_1469.pure_subterms_within_computations);
            simplify = (uu___247_1469.simplify);
            erase_universes = (uu___247_1469.erase_universes);
            allow_unbound_universes = (uu___247_1469.allow_unbound_universes);
            reify_ = (uu___247_1469.reify_);
            compress_uvars = (uu___247_1469.compress_uvars);
            no_full_norm = true;
            check_no_uvars = (uu___247_1469.check_no_uvars);
            unmeta = (uu___247_1469.unmeta);
            unascribe = (uu___247_1469.unascribe);
            in_full_norm_request = (uu___247_1469.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___247_1469.weakly_reduce_scrutinee);
            nbe_step = (uu___247_1469.nbe_step)
          }
      | FStar_TypeChecker_Env.CheckNoUvars  ->
          let uu___248_1470 = fs  in
          {
            beta = (uu___248_1470.beta);
            iota = (uu___248_1470.iota);
            zeta = (uu___248_1470.zeta);
            weak = (uu___248_1470.weak);
            hnf = (uu___248_1470.hnf);
            primops = (uu___248_1470.primops);
            do_not_unfold_pure_lets = (uu___248_1470.do_not_unfold_pure_lets);
            unfold_until = (uu___248_1470.unfold_until);
            unfold_only = (uu___248_1470.unfold_only);
            unfold_fully = (uu___248_1470.unfold_fully);
            unfold_attr = (uu___248_1470.unfold_attr);
            unfold_tac = (uu___248_1470.unfold_tac);
            pure_subterms_within_computations =
              (uu___248_1470.pure_subterms_within_computations);
            simplify = (uu___248_1470.simplify);
            erase_universes = (uu___248_1470.erase_universes);
            allow_unbound_universes = (uu___248_1470.allow_unbound_universes);
            reify_ = (uu___248_1470.reify_);
            compress_uvars = (uu___248_1470.compress_uvars);
            no_full_norm = (uu___248_1470.no_full_norm);
            check_no_uvars = true;
            unmeta = (uu___248_1470.unmeta);
            unascribe = (uu___248_1470.unascribe);
            in_full_norm_request = (uu___248_1470.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___248_1470.weakly_reduce_scrutinee);
            nbe_step = (uu___248_1470.nbe_step)
          }
      | FStar_TypeChecker_Env.Unmeta  ->
          let uu___249_1471 = fs  in
          {
            beta = (uu___249_1471.beta);
            iota = (uu___249_1471.iota);
            zeta = (uu___249_1471.zeta);
            weak = (uu___249_1471.weak);
            hnf = (uu___249_1471.hnf);
            primops = (uu___249_1471.primops);
            do_not_unfold_pure_lets = (uu___249_1471.do_not_unfold_pure_lets);
            unfold_until = (uu___249_1471.unfold_until);
            unfold_only = (uu___249_1471.unfold_only);
            unfold_fully = (uu___249_1471.unfold_fully);
            unfold_attr = (uu___249_1471.unfold_attr);
            unfold_tac = (uu___249_1471.unfold_tac);
            pure_subterms_within_computations =
              (uu___249_1471.pure_subterms_within_computations);
            simplify = (uu___249_1471.simplify);
            erase_universes = (uu___249_1471.erase_universes);
            allow_unbound_universes = (uu___249_1471.allow_unbound_universes);
            reify_ = (uu___249_1471.reify_);
            compress_uvars = (uu___249_1471.compress_uvars);
            no_full_norm = (uu___249_1471.no_full_norm);
            check_no_uvars = (uu___249_1471.check_no_uvars);
            unmeta = true;
            unascribe = (uu___249_1471.unascribe);
            in_full_norm_request = (uu___249_1471.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___249_1471.weakly_reduce_scrutinee);
            nbe_step = (uu___249_1471.nbe_step)
          }
      | FStar_TypeChecker_Env.Unascribe  ->
          let uu___250_1472 = fs  in
          {
            beta = (uu___250_1472.beta);
            iota = (uu___250_1472.iota);
            zeta = (uu___250_1472.zeta);
            weak = (uu___250_1472.weak);
            hnf = (uu___250_1472.hnf);
            primops = (uu___250_1472.primops);
            do_not_unfold_pure_lets = (uu___250_1472.do_not_unfold_pure_lets);
            unfold_until = (uu___250_1472.unfold_until);
            unfold_only = (uu___250_1472.unfold_only);
            unfold_fully = (uu___250_1472.unfold_fully);
            unfold_attr = (uu___250_1472.unfold_attr);
            unfold_tac = (uu___250_1472.unfold_tac);
            pure_subterms_within_computations =
              (uu___250_1472.pure_subterms_within_computations);
            simplify = (uu___250_1472.simplify);
            erase_universes = (uu___250_1472.erase_universes);
            allow_unbound_universes = (uu___250_1472.allow_unbound_universes);
            reify_ = (uu___250_1472.reify_);
            compress_uvars = (uu___250_1472.compress_uvars);
            no_full_norm = (uu___250_1472.no_full_norm);
            check_no_uvars = (uu___250_1472.check_no_uvars);
            unmeta = (uu___250_1472.unmeta);
            unascribe = true;
            in_full_norm_request = (uu___250_1472.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___250_1472.weakly_reduce_scrutinee);
            nbe_step = (uu___250_1472.nbe_step)
          }
      | FStar_TypeChecker_Env.NBE  ->
          let uu___251_1473 = fs  in
          {
            beta = (uu___251_1473.beta);
            iota = (uu___251_1473.iota);
            zeta = (uu___251_1473.zeta);
            weak = (uu___251_1473.weak);
            hnf = (uu___251_1473.hnf);
            primops = (uu___251_1473.primops);
            do_not_unfold_pure_lets = (uu___251_1473.do_not_unfold_pure_lets);
            unfold_until = (uu___251_1473.unfold_until);
            unfold_only = (uu___251_1473.unfold_only);
            unfold_fully = (uu___251_1473.unfold_fully);
            unfold_attr = (uu___251_1473.unfold_attr);
            unfold_tac = (uu___251_1473.unfold_tac);
            pure_subterms_within_computations =
              (uu___251_1473.pure_subterms_within_computations);
            simplify = (uu___251_1473.simplify);
            erase_universes = (uu___251_1473.erase_universes);
            allow_unbound_universes = (uu___251_1473.allow_unbound_universes);
            reify_ = (uu___251_1473.reify_);
            compress_uvars = (uu___251_1473.compress_uvars);
            no_full_norm = (uu___251_1473.no_full_norm);
            check_no_uvars = (uu___251_1473.check_no_uvars);
            unmeta = (uu___251_1473.unmeta);
            unascribe = (uu___251_1473.unascribe);
            in_full_norm_request = (uu___251_1473.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___251_1473.weakly_reduce_scrutinee);
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
  { psc_range = FStar_Range.dummyRange; psc_subst = (fun uu____1526  -> []) } 
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
      FStar_Syntax_Syntax.args ->
        FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
    ;
  interpretation_nbe:
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
    let uu____2250 =
      let uu____2253 =
        let uu____2256 =
          let uu____2257 = steps_to_string cfg.steps  in
          FStar_Util.format1 "  steps = %s" uu____2257  in
        [uu____2256; "}"]  in
      "{" :: uu____2253  in
    FStar_String.concat "\n" uu____2250
  
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
             let uu____2294 = FStar_Ident.text_of_lid p.name  in
             FStar_Util.psmap_add m1 uu____2294 p) l m
  
let (prim_from_list :
  primitive_step Prims.list -> primitive_step FStar_Util.psmap) =
  fun l  ->
    let uu____2308 = FStar_Util.psmap_empty ()  in add_steps uu____2308 l
  
let (find_prim_step :
  cfg ->
    FStar_Syntax_Syntax.fv -> primitive_step FStar_Pervasives_Native.option)
  =
  fun cfg  ->
    fun fv  ->
      let uu____2323 =
        FStar_Ident.text_of_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
         in
      FStar_Util.psmap_try_find cfg.primitive_steps uu____2323
  
let (is_prim_step : cfg -> FStar_Syntax_Syntax.fv -> Prims.bool) =
  fun cfg  ->
    fun fv  ->
      let uu____2334 =
        let uu____2337 =
          FStar_Ident.text_of_lid
            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
           in
        FStar_Util.psmap_try_find cfg.primitive_steps uu____2337  in
      FStar_Util.is_some uu____2334
  
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
      let uu____2433 =
        FStar_All.pipe_left (FStar_TypeChecker_Env.debug cfg.tcenv)
          (FStar_Options.Other "NBE")
         in
      if uu____2433 then f () else ()
  
let mk :
  'Auu____2441 .
    'Auu____2441 ->
      FStar_Range.range -> 'Auu____2441 FStar_Syntax_Syntax.syntax
  =
  fun t  -> fun r  -> FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None r 
let (built_in_primitive_steps : primitive_step FStar_Util.psmap) =
  let arg_as_int1 a =
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a)
      (FStar_Syntax_Embeddings.try_unembed FStar_Syntax_Embeddings.e_int)
     in
  let arg_as_bool1 a =
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a)
      (FStar_Syntax_Embeddings.try_unembed FStar_Syntax_Embeddings.e_bool)
     in
  let arg_as_char1 a =
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a)
      (FStar_Syntax_Embeddings.try_unembed FStar_Syntax_Embeddings.e_char)
     in
  let arg_as_string1 a =
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a)
      (FStar_Syntax_Embeddings.try_unembed FStar_Syntax_Embeddings.e_string)
     in
  let arg_as_list1 e a =
    let uu____2555 =
      let uu____2564 = FStar_Syntax_Embeddings.e_list e  in
      FStar_Syntax_Embeddings.try_unembed uu____2564  in
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a) uu____2555  in
  let arg_as_bounded_int1 uu____2594 =
    match uu____2594 with
    | (a,uu____2608) ->
        let uu____2619 =
          let uu____2620 = FStar_Syntax_Subst.compress a  in
          uu____2620.FStar_Syntax_Syntax.n  in
        (match uu____2619 with
         | FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv1;
                FStar_Syntax_Syntax.pos = uu____2630;
                FStar_Syntax_Syntax.vars = uu____2631;_},({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_constant
                                                              (FStar_Const.Const_int
                                                              (i,FStar_Pervasives_Native.None
                                                               ));
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____2633;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____2634;_},uu____2635)::[])
             when
             let uu____2684 =
               FStar_Ident.text_of_lid
                 (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                in
             FStar_Util.ends_with uu____2684 "int_to_t" ->
             let uu____2685 =
               let uu____2690 = FStar_BigInt.big_int_of_string i  in
               (fv1, uu____2690)  in
             FStar_Pervasives_Native.Some uu____2685
         | uu____2695 -> FStar_Pervasives_Native.None)
     in
  let lift_unary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a)::[] ->
        let uu____2743 = f a  in FStar_Pervasives_Native.Some uu____2743
    | uu____2744 -> FStar_Pervasives_Native.None  in
  let lift_binary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a0)::(FStar_Pervasives_Native.Some
        a1)::[] ->
        let uu____2800 = f a0 a1  in FStar_Pervasives_Native.Some uu____2800
    | uu____2801 -> FStar_Pervasives_Native.None  in
  let unary_op1 as_a f res args =
    let uu____2859 = FStar_List.map as_a args  in
    lift_unary (f res.psc_range) uu____2859  in
  let binary_op1 as_a f res args =
    let uu____2932 = FStar_List.map as_a args  in
    lift_binary (f res.psc_range) uu____2932  in
  let as_primitive_step is_strong uu____2980 =
    match uu____2980 with
    | (l,arity,u_arity,f,f_nbe) ->
        {
          name = l;
          arity;
          univ_arity = u_arity;
          auto_reflect = FStar_Pervasives_Native.None;
          strong_reduction_ok = is_strong;
          requires_binder_substitution = false;
          interpretation = f;
          interpretation_nbe = f_nbe
        }
     in
  let unary_int_op1 f =
    unary_op1 arg_as_int1
      (fun r  ->
         fun x  ->
           let uu____3060 = f x  in
           FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_int r
             uu____3060)
     in
  let binary_int_op1 f =
    binary_op1 arg_as_int1
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____3096 = f x y  in
             FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_int r
               uu____3096)
     in
  let unary_bool_op1 f =
    unary_op1 arg_as_bool1
      (fun r  ->
         fun x  ->
           let uu____3125 = f x  in
           FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_bool r
             uu____3125)
     in
  let binary_bool_op1 f =
    binary_op1 arg_as_bool1
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____3161 = f x y  in
             FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_bool r
               uu____3161)
     in
  let binary_string_op1 f =
    binary_op1 arg_as_string1
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____3197 = f x y  in
             FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_string r
               uu____3197)
     in
  let mixed_binary_op1 as_a as_b embed_c f res args =
    match args with
    | a::b::[] ->
        let uu____3339 =
          let uu____3348 = as_a a  in
          let uu____3351 = as_b b  in (uu____3348, uu____3351)  in
        (match uu____3339 with
         | (FStar_Pervasives_Native.Some a1,FStar_Pervasives_Native.Some b1)
             ->
             let uu____3366 =
               let uu____3367 = f res.psc_range a1 b1  in
               embed_c res.psc_range uu____3367  in
             FStar_Pervasives_Native.Some uu____3366
         | uu____3368 -> FStar_Pervasives_Native.None)
    | uu____3377 -> FStar_Pervasives_Native.None  in
  let list_of_string'1 rng s =
    let name l =
      let uu____3397 =
        let uu____3398 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
            FStar_Pervasives_Native.None
           in
        FStar_Syntax_Syntax.Tm_fvar uu____3398  in
      mk uu____3397 rng  in
    let char_t = name FStar_Parser_Const.char_lid  in
    let charterm c =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c)) rng  in
    let uu____3412 =
      let uu____3415 = FStar_String.list_of_string s  in
      FStar_List.map charterm uu____3415  in
    FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu____3412  in
  let string_of_list'1 rng l =
    let s = FStar_String.string_of_list l  in FStar_Syntax_Util.exp_string s
     in
  let string_compare'1 rng s1 s2 =
    let r = FStar_String.compare s1 s2  in
    let uu____3457 =
      let uu____3458 = FStar_Util.string_of_int r  in
      FStar_BigInt.big_int_of_string uu____3458  in
    FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_int rng
      uu____3457
     in
  let string_concat'1 psc args =
    match args with
    | a1::a2::[] ->
        let uu____3536 = arg_as_string1 a1  in
        (match uu____3536 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____3542 =
               arg_as_list1 FStar_Syntax_Embeddings.e_string a2  in
             (match uu____3542 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2  in
                  let uu____3555 =
                    FStar_Syntax_Embeddings.embed
                      FStar_Syntax_Embeddings.e_string psc.psc_range r
                     in
                  FStar_Pervasives_Native.Some uu____3555
              | uu____3556 -> FStar_Pervasives_Native.None)
         | uu____3561 -> FStar_Pervasives_Native.None)
    | uu____3564 -> FStar_Pervasives_Native.None  in
  let string_split'1 psc args =
    match args with
    | a1::a2::[] ->
        let uu____3638 = arg_as_list1 FStar_Syntax_Embeddings.e_char a1  in
        (match uu____3638 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____3654 = arg_as_string1 a2  in
             (match uu____3654 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.split s1 s2  in
                  let uu____3663 =
                    let uu____3664 =
                      FStar_Syntax_Embeddings.e_list
                        FStar_Syntax_Embeddings.e_string
                       in
                    FStar_Syntax_Embeddings.embed uu____3664 psc.psc_range r
                     in
                  FStar_Pervasives_Native.Some uu____3663
              | uu____3671 -> FStar_Pervasives_Native.None)
         | uu____3674 -> FStar_Pervasives_Native.None)
    | uu____3680 -> FStar_Pervasives_Native.None  in
  let string_substring'1 psc args =
    match args with
    | a1::a2::a3::[] ->
        let uu____3711 =
          let uu____3724 = arg_as_string1 a1  in
          let uu____3727 = arg_as_int1 a2  in
          let uu____3730 = arg_as_int1 a3  in
          (uu____3724, uu____3727, uu____3730)  in
        (match uu____3711 with
         | (FStar_Pervasives_Native.Some s1,FStar_Pervasives_Native.Some
            n1,FStar_Pervasives_Native.Some n2) ->
             let n11 = FStar_BigInt.to_int_fs n1  in
             let n21 = FStar_BigInt.to_int_fs n2  in
             (try
                (fun uu___253_3757  ->
                   match () with
                   | () ->
                       let r = FStar_String.substring s1 n11 n21  in
                       let uu____3761 =
                         FStar_Syntax_Embeddings.embed
                           FStar_Syntax_Embeddings.e_string psc.psc_range r
                          in
                       FStar_Pervasives_Native.Some uu____3761) ()
              with | uu___252_3763 -> FStar_Pervasives_Native.None)
         | uu____3766 -> FStar_Pervasives_Native.None)
    | uu____3779 -> FStar_Pervasives_Native.None  in
  let string_of_int1 rng i =
    let uu____3793 = FStar_BigInt.string_of_big_int i  in
    FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_string rng
      uu____3793
     in
  let string_of_bool1 rng b =
    FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_string rng
      (if b then "true" else "false")
     in
  let mk_range1 psc args =
    match args with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____3830 =
          let uu____3851 = arg_as_string1 fn  in
          let uu____3854 = arg_as_int1 from_line  in
          let uu____3857 = arg_as_int1 from_col  in
          let uu____3860 = arg_as_int1 to_line  in
          let uu____3863 = arg_as_int1 to_col  in
          (uu____3851, uu____3854, uu____3857, uu____3860, uu____3863)  in
        (match uu____3830 with
         | (FStar_Pervasives_Native.Some fn1,FStar_Pervasives_Native.Some
            from_l,FStar_Pervasives_Native.Some
            from_c,FStar_Pervasives_Native.Some
            to_l,FStar_Pervasives_Native.Some to_c) ->
             let r =
               let uu____3894 =
                 let uu____3895 = FStar_BigInt.to_int_fs from_l  in
                 let uu____3896 = FStar_BigInt.to_int_fs from_c  in
                 FStar_Range.mk_pos uu____3895 uu____3896  in
               let uu____3897 =
                 let uu____3898 = FStar_BigInt.to_int_fs to_l  in
                 let uu____3899 = FStar_BigInt.to_int_fs to_c  in
                 FStar_Range.mk_pos uu____3898 uu____3899  in
               FStar_Range.mk_range fn1 uu____3894 uu____3897  in
             let uu____3900 =
               FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_range
                 psc.psc_range r
                in
             FStar_Pervasives_Native.Some uu____3900
         | uu____3901 -> FStar_Pervasives_Native.None)
    | uu____3922 -> FStar_Pervasives_Native.None  in
  let decidable_eq1 neg psc args =
    let r = psc.psc_range  in
    let tru =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool true)) r
       in
    let fal =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool false)) r
       in
    match args with
    | (_typ,uu____3955)::(a1,uu____3957)::(a2,uu____3959)::[] ->
        let uu____4016 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____4016 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some (if neg then fal else tru)
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some (if neg then tru else fal)
         | uu____4021 -> FStar_Pervasives_Native.None)
    | uu____4022 -> failwith "Unexpected number of arguments"  in
  let prims_to_fstar_range_step1 psc args =
    match args with
    | (a1,uu____4057)::[] ->
        let uu____4074 =
          FStar_Syntax_Embeddings.try_unembed FStar_Syntax_Embeddings.e_range
            a1
           in
        (match uu____4074 with
         | FStar_Pervasives_Native.Some r ->
             let uu____4080 =
               FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_range
                 psc.psc_range r
                in
             FStar_Pervasives_Native.Some uu____4080
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
    | uu____4081 -> failwith "Unexpected number of arguments"  in
  let basic_ops =
    let uu____4118 =
      let uu____4142 =
        FStar_TypeChecker_NBETerm.unary_int_op
          (fun x  -> FStar_BigInt.minus_big_int x)
         in
      (FStar_Parser_Const.op_Minus, (Prims.parse_int "1"),
        (Prims.parse_int "0"),
        (unary_int_op1 (fun x  -> FStar_BigInt.minus_big_int x)), uu____4142)
       in
    let uu____4168 =
      let uu____4194 =
        let uu____4218 =
          FStar_TypeChecker_NBETerm.binary_int_op
            (fun x  -> fun y  -> FStar_BigInt.add_big_int x y)
           in
        (FStar_Parser_Const.op_Addition, (Prims.parse_int "2"),
          (Prims.parse_int "0"),
          (binary_int_op1 (fun x  -> fun y  -> FStar_BigInt.add_big_int x y)),
          uu____4218)
         in
      let uu____4250 =
        let uu____4276 =
          let uu____4300 =
            FStar_TypeChecker_NBETerm.binary_int_op
              (fun x  -> fun y  -> FStar_BigInt.sub_big_int x y)
             in
          (FStar_Parser_Const.op_Subtraction, (Prims.parse_int "2"),
            (Prims.parse_int "0"),
            (binary_int_op1
               (fun x  -> fun y  -> FStar_BigInt.sub_big_int x y)),
            uu____4300)
           in
        let uu____4332 =
          let uu____4358 =
            let uu____4382 =
              FStar_TypeChecker_NBETerm.binary_int_op
                (fun x  -> fun y  -> FStar_BigInt.mult_big_int x y)
               in
            (FStar_Parser_Const.op_Multiply, (Prims.parse_int "2"),
              (Prims.parse_int "0"),
              (binary_int_op1
                 (fun x  -> fun y  -> FStar_BigInt.mult_big_int x y)),
              uu____4382)
             in
          let uu____4414 =
            let uu____4440 =
              let uu____4464 =
                FStar_TypeChecker_NBETerm.binary_int_op
                  (fun x  -> fun y  -> FStar_BigInt.div_big_int x y)
                 in
              (FStar_Parser_Const.op_Division, (Prims.parse_int "2"),
                (Prims.parse_int "0"),
                (binary_int_op1
                   (fun x  -> fun y  -> FStar_BigInt.div_big_int x y)),
                uu____4464)
               in
            let uu____4496 =
              let uu____4522 =
                let uu____4546 =
                  FStar_TypeChecker_NBETerm.binary_op
                    FStar_TypeChecker_NBETerm.arg_as_int
                    (fun x  ->
                       fun y  ->
                         let uu____4558 = FStar_BigInt.lt_big_int x y  in
                         FStar_TypeChecker_NBETerm.embed
                           FStar_TypeChecker_NBETerm.e_bool uu____4558)
                   in
                (FStar_Parser_Const.op_LT, (Prims.parse_int "2"),
                  (Prims.parse_int "0"),
                  (binary_op1 arg_as_int1
                     (fun r  ->
                        fun x  ->
                          fun y  ->
                            let uu____4579 = FStar_BigInt.lt_big_int x y  in
                            FStar_Syntax_Embeddings.embed
                              FStar_Syntax_Embeddings.e_bool r uu____4579)),
                  uu____4546)
                 in
              let uu____4580 =
                let uu____4606 =
                  let uu____4630 =
                    FStar_TypeChecker_NBETerm.binary_op
                      FStar_TypeChecker_NBETerm.arg_as_int
                      (fun x  ->
                         fun y  ->
                           let uu____4642 = FStar_BigInt.le_big_int x y  in
                           FStar_TypeChecker_NBETerm.embed
                             FStar_TypeChecker_NBETerm.e_bool uu____4642)
                     in
                  (FStar_Parser_Const.op_LTE, (Prims.parse_int "2"),
                    (Prims.parse_int "0"),
                    (binary_op1 arg_as_int1
                       (fun r  ->
                          fun x  ->
                            fun y  ->
                              let uu____4663 = FStar_BigInt.le_big_int x y
                                 in
                              FStar_Syntax_Embeddings.embed
                                FStar_Syntax_Embeddings.e_bool r uu____4663)),
                    uu____4630)
                   in
                let uu____4664 =
                  let uu____4690 =
                    let uu____4714 =
                      FStar_TypeChecker_NBETerm.binary_op
                        FStar_TypeChecker_NBETerm.arg_as_int
                        (fun x  ->
                           fun y  ->
                             let uu____4726 = FStar_BigInt.gt_big_int x y  in
                             FStar_TypeChecker_NBETerm.embed
                               FStar_TypeChecker_NBETerm.e_bool uu____4726)
                       in
                    (FStar_Parser_Const.op_GT, (Prims.parse_int "2"),
                      (Prims.parse_int "0"),
                      (binary_op1 arg_as_int1
                         (fun r  ->
                            fun x  ->
                              fun y  ->
                                let uu____4747 = FStar_BigInt.gt_big_int x y
                                   in
                                FStar_Syntax_Embeddings.embed
                                  FStar_Syntax_Embeddings.e_bool r uu____4747)),
                      uu____4714)
                     in
                  let uu____4748 =
                    let uu____4774 =
                      let uu____4798 =
                        FStar_TypeChecker_NBETerm.binary_op
                          FStar_TypeChecker_NBETerm.arg_as_int
                          (fun x  ->
                             fun y  ->
                               let uu____4810 = FStar_BigInt.ge_big_int x y
                                  in
                               FStar_TypeChecker_NBETerm.embed
                                 FStar_TypeChecker_NBETerm.e_bool uu____4810)
                         in
                      (FStar_Parser_Const.op_GTE, (Prims.parse_int "2"),
                        (Prims.parse_int "0"),
                        (binary_op1 arg_as_int1
                           (fun r  ->
                              fun x  ->
                                fun y  ->
                                  let uu____4831 =
                                    FStar_BigInt.ge_big_int x y  in
                                  FStar_Syntax_Embeddings.embed
                                    FStar_Syntax_Embeddings.e_bool r
                                    uu____4831)), uu____4798)
                       in
                    let uu____4832 =
                      let uu____4858 =
                        let uu____4882 =
                          FStar_TypeChecker_NBETerm.binary_int_op
                            (fun x  -> fun y  -> FStar_BigInt.mod_big_int x y)
                           in
                        (FStar_Parser_Const.op_Modulus,
                          (Prims.parse_int "2"), (Prims.parse_int "0"),
                          (binary_int_op1
                             (fun x  ->
                                fun y  -> FStar_BigInt.mod_big_int x y)),
                          uu____4882)
                         in
                      let uu____4914 =
                        let uu____4940 =
                          let uu____4964 =
                            FStar_TypeChecker_NBETerm.unary_bool_op
                              (fun x  -> Prims.op_Negation x)
                             in
                          (FStar_Parser_Const.op_Negation,
                            (Prims.parse_int "1"), (Prims.parse_int "0"),
                            (unary_bool_op1 (fun x  -> Prims.op_Negation x)),
                            uu____4964)
                           in
                        let uu____4990 =
                          let uu____5016 =
                            let uu____5040 =
                              FStar_TypeChecker_NBETerm.binary_bool_op
                                (fun x  -> fun y  -> x && y)
                               in
                            (FStar_Parser_Const.op_And,
                              (Prims.parse_int "2"), (Prims.parse_int "0"),
                              (binary_bool_op1 (fun x  -> fun y  -> x && y)),
                              uu____5040)
                             in
                          let uu____5072 =
                            let uu____5098 =
                              let uu____5122 =
                                FStar_TypeChecker_NBETerm.binary_bool_op
                                  (fun x  -> fun y  -> x || y)
                                 in
                              (FStar_Parser_Const.op_Or,
                                (Prims.parse_int "2"), (Prims.parse_int "0"),
                                (binary_bool_op1 (fun x  -> fun y  -> x || y)),
                                uu____5122)
                               in
                            let uu____5154 =
                              let uu____5180 =
                                let uu____5204 =
                                  FStar_TypeChecker_NBETerm.binary_string_op
                                    (fun x  -> fun y  -> Prims.strcat x y)
                                   in
                                (FStar_Parser_Const.strcat_lid,
                                  (Prims.parse_int "2"),
                                  (Prims.parse_int "0"),
                                  (binary_string_op1
                                     (fun x  -> fun y  -> Prims.strcat x y)),
                                  uu____5204)
                                 in
                              let uu____5236 =
                                let uu____5262 =
                                  let uu____5286 =
                                    FStar_TypeChecker_NBETerm.binary_string_op
                                      (fun x  -> fun y  -> Prims.strcat x y)
                                     in
                                  (FStar_Parser_Const.strcat_lid',
                                    (Prims.parse_int "2"),
                                    (Prims.parse_int "0"),
                                    (binary_string_op1
                                       (fun x  -> fun y  -> Prims.strcat x y)),
                                    uu____5286)
                                   in
                                let uu____5318 =
                                  let uu____5344 =
                                    let uu____5370 =
                                      let uu____5394 =
                                        FStar_TypeChecker_NBETerm.unary_op
                                          FStar_TypeChecker_NBETerm.arg_as_int
                                          FStar_TypeChecker_NBETerm.string_of_int
                                         in
                                      (FStar_Parser_Const.string_of_int_lid,
                                        (Prims.parse_int "1"),
                                        (Prims.parse_int "0"),
                                        (unary_op1 arg_as_int1 string_of_int1),
                                        uu____5394)
                                       in
                                    let uu____5414 =
                                      let uu____5440 =
                                        let uu____5464 =
                                          FStar_TypeChecker_NBETerm.unary_op
                                            FStar_TypeChecker_NBETerm.arg_as_bool
                                            FStar_TypeChecker_NBETerm.string_of_bool
                                           in
                                        (FStar_Parser_Const.string_of_bool_lid,
                                          (Prims.parse_int "1"),
                                          (Prims.parse_int "0"),
                                          (unary_op1 arg_as_bool1
                                             string_of_bool1), uu____5464)
                                         in
                                      let uu____5484 =
                                        let uu____5510 =
                                          let uu____5534 =
                                            FStar_TypeChecker_NBETerm.binary_op
                                              FStar_TypeChecker_NBETerm.arg_as_string
                                              FStar_TypeChecker_NBETerm.string_compare'
                                             in
                                          (FStar_Parser_Const.string_compare,
                                            (Prims.parse_int "2"),
                                            (Prims.parse_int "0"),
                                            (binary_op1 arg_as_string1
                                               string_compare'1), uu____5534)
                                           in
                                        let uu____5554 =
                                          let uu____5580 =
                                            let uu____5606 =
                                              let uu____5632 =
                                                let uu____5656 =
                                                  FStar_Parser_Const.p2l
                                                    ["FStar";
                                                    "String";
                                                    "list_of_string"]
                                                   in
                                                let uu____5657 =
                                                  FStar_TypeChecker_NBETerm.unary_op
                                                    FStar_TypeChecker_NBETerm.arg_as_string
                                                    FStar_TypeChecker_NBETerm.list_of_string'
                                                   in
                                                (uu____5656,
                                                  (Prims.parse_int "1"),
                                                  (Prims.parse_int "0"),
                                                  (unary_op1 arg_as_string1
                                                     list_of_string'1),
                                                  uu____5657)
                                                 in
                                              let uu____5677 =
                                                let uu____5703 =
                                                  let uu____5727 =
                                                    FStar_Parser_Const.p2l
                                                      ["FStar";
                                                      "String";
                                                      "string_of_list"]
                                                     in
                                                  let uu____5728 =
                                                    FStar_TypeChecker_NBETerm.unary_op
                                                      (FStar_TypeChecker_NBETerm.arg_as_list
                                                         FStar_TypeChecker_NBETerm.e_char)
                                                      FStar_TypeChecker_NBETerm.string_of_list'
                                                     in
                                                  (uu____5727,
                                                    (Prims.parse_int "1"),
                                                    (Prims.parse_int "0"),
                                                    (unary_op1
                                                       (arg_as_list1
                                                          FStar_Syntax_Embeddings.e_char)
                                                       string_of_list'1),
                                                    uu____5728)
                                                   in
                                                let uu____5756 =
                                                  let uu____5782 =
                                                    let uu____5806 =
                                                      FStar_Parser_Const.p2l
                                                        ["FStar";
                                                        "String";
                                                        "split"]
                                                       in
                                                    (uu____5806,
                                                      (Prims.parse_int "2"),
                                                      (Prims.parse_int "0"),
                                                      string_split'1,
                                                      FStar_TypeChecker_NBETerm.string_split')
                                                     in
                                                  let uu____5820 =
                                                    let uu____5846 =
                                                      let uu____5870 =
                                                        FStar_Parser_Const.p2l
                                                          ["FStar";
                                                          "String";
                                                          "substring"]
                                                         in
                                                      (uu____5870,
                                                        (Prims.parse_int "3"),
                                                        (Prims.parse_int "0"),
                                                        string_substring'1,
                                                        FStar_TypeChecker_NBETerm.string_substring')
                                                       in
                                                    let uu____5884 =
                                                      let uu____5910 =
                                                        let uu____5934 =
                                                          FStar_Parser_Const.p2l
                                                            ["FStar";
                                                            "String";
                                                            "concat"]
                                                           in
                                                        (uu____5934,
                                                          (Prims.parse_int "2"),
                                                          (Prims.parse_int "0"),
                                                          string_concat'1,
                                                          FStar_TypeChecker_NBETerm.string_concat')
                                                         in
                                                      let uu____5948 =
                                                        let uu____5974 =
                                                          let uu____5998 =
                                                            FStar_Parser_Const.p2l
                                                              ["Prims";
                                                              "mk_range"]
                                                             in
                                                          let uu____5999 =
                                                            let uu____6006 =
                                                              FStar_Parser_Const.p2l
                                                                ["Prims";
                                                                "mk_range"]
                                                               in
                                                            FStar_TypeChecker_NBETerm.dummy_interp
                                                              uu____6006
                                                             in
                                                          (uu____5998,
                                                            (Prims.parse_int "5"),
                                                            (Prims.parse_int "0"),
                                                            mk_range1,
                                                            uu____5999)
                                                           in
                                                        [uu____5974]  in
                                                      uu____5910 ::
                                                        uu____5948
                                                       in
                                                    uu____5846 :: uu____5884
                                                     in
                                                  uu____5782 :: uu____5820
                                                   in
                                                uu____5703 :: uu____5756  in
                                              uu____5632 :: uu____5677  in
                                            (FStar_Parser_Const.op_notEq,
                                              (Prims.parse_int "3"),
                                              (Prims.parse_int "1"),
                                              (decidable_eq1 true),
                                              (FStar_TypeChecker_NBETerm.decidable_eq
                                                 true))
                                              :: uu____5606
                                             in
                                          (FStar_Parser_Const.op_Eq,
                                            (Prims.parse_int "3"),
                                            (Prims.parse_int "1"),
                                            (decidable_eq1 false),
                                            (FStar_TypeChecker_NBETerm.decidable_eq
                                               false))
                                            :: uu____5580
                                           in
                                        uu____5510 :: uu____5554  in
                                      uu____5440 :: uu____5484  in
                                    uu____5370 :: uu____5414  in
                                  (FStar_Parser_Const.str_make_lid,
                                    (Prims.parse_int "2"),
                                    (Prims.parse_int "0"),
                                    (mixed_binary_op1 arg_as_int1
                                       arg_as_char1
                                       (FStar_Syntax_Embeddings.embed
                                          FStar_Syntax_Embeddings.e_string)
                                       (fun r  ->
                                          fun x  ->
                                            fun y  ->
                                              let uu____6367 =
                                                FStar_BigInt.to_int_fs x  in
                                              FStar_String.make uu____6367 y)),
                                    (FStar_TypeChecker_NBETerm.mixed_binary_op
                                       FStar_TypeChecker_NBETerm.arg_as_int
                                       FStar_TypeChecker_NBETerm.arg_as_char
                                       (FStar_TypeChecker_NBETerm.embed
                                          FStar_TypeChecker_NBETerm.e_string)
                                       (fun x  ->
                                          fun y  ->
                                            let uu____6375 =
                                              FStar_BigInt.to_int_fs x  in
                                            FStar_String.make uu____6375 y)))
                                    :: uu____5344
                                   in
                                uu____5262 :: uu____5318  in
                              uu____5180 :: uu____5236  in
                            uu____5098 :: uu____5154  in
                          uu____5016 :: uu____5072  in
                        uu____4940 :: uu____4990  in
                      uu____4858 :: uu____4914  in
                    uu____4774 :: uu____4832  in
                  uu____4690 :: uu____4748  in
                uu____4606 :: uu____4664  in
              uu____4522 :: uu____4580  in
            uu____4440 :: uu____4496  in
          uu____4358 :: uu____4414  in
        uu____4276 :: uu____4332  in
      uu____4194 :: uu____4250  in
    uu____4118 :: uu____4168  in
  let weak_ops =
    let uu____6747 =
      let uu____6771 =
        FStar_Parser_Const.p2l ["FStar"; "Range"; "prims_to_fstar_range"]  in
      (uu____6771, (Prims.parse_int "1"), (Prims.parse_int "0"),
        prims_to_fstar_range_step1,
        FStar_TypeChecker_NBETerm.prims_to_fstar_range_step)
       in
    [uu____6747]  in
  let bounded_arith_ops =
    let bounded_signed_int_types = ["Int8"; "Int16"; "Int32"; "Int64"]  in
    let bounded_unsigned_int_types =
      ["UInt8"; "UInt16"; "UInt32"; "UInt64"; "UInt128"]  in
    let int_as_bounded1 r int_to_t1 n1 =
      let c =
        FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_int r n1  in
      let int_to_t2 = FStar_Syntax_Syntax.fv_to_tm int_to_t1  in
      let uu____6883 =
        let uu____6888 =
          let uu____6889 = FStar_Syntax_Syntax.as_arg c  in [uu____6889]  in
        FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____6888  in
      uu____6883 FStar_Pervasives_Native.None r  in
    let add_sub_mul_v =
      FStar_All.pipe_right
        (FStar_List.append bounded_signed_int_types
           bounded_unsigned_int_types)
        (FStar_List.collect
           (fun m  ->
              let uu____6996 =
                let uu____7020 = FStar_Parser_Const.p2l ["FStar"; m; "add"]
                   in
                let uu____7021 =
                  FStar_TypeChecker_NBETerm.binary_op
                    FStar_TypeChecker_NBETerm.arg_as_bounded_int
                    (fun uu____7039  ->
                       fun uu____7040  ->
                         match (uu____7039, uu____7040) with
                         | ((int_to_t1,x),(uu____7059,y)) ->
                             let uu____7069 = FStar_BigInt.add_big_int x y
                                in
                             FStar_TypeChecker_NBETerm.int_as_bounded
                               int_to_t1 uu____7069)
                   in
                (uu____7020, (Prims.parse_int "2"), (Prims.parse_int "0"),
                  (binary_op1 arg_as_bounded_int1
                     (fun r  ->
                        fun uu____7096  ->
                          fun uu____7097  ->
                            match (uu____7096, uu____7097) with
                            | ((int_to_t1,x),(uu____7116,y)) ->
                                let uu____7126 = FStar_BigInt.add_big_int x y
                                   in
                                int_as_bounded1 r int_to_t1 uu____7126)),
                  uu____7021)
                 in
              let uu____7127 =
                let uu____7153 =
                  let uu____7177 = FStar_Parser_Const.p2l ["FStar"; m; "sub"]
                     in
                  let uu____7178 =
                    FStar_TypeChecker_NBETerm.binary_op
                      FStar_TypeChecker_NBETerm.arg_as_bounded_int
                      (fun uu____7196  ->
                         fun uu____7197  ->
                           match (uu____7196, uu____7197) with
                           | ((int_to_t1,x),(uu____7216,y)) ->
                               let uu____7226 = FStar_BigInt.sub_big_int x y
                                  in
                               FStar_TypeChecker_NBETerm.int_as_bounded
                                 int_to_t1 uu____7226)
                     in
                  (uu____7177, (Prims.parse_int "2"), (Prims.parse_int "0"),
                    (binary_op1 arg_as_bounded_int1
                       (fun r  ->
                          fun uu____7253  ->
                            fun uu____7254  ->
                              match (uu____7253, uu____7254) with
                              | ((int_to_t1,x),(uu____7273,y)) ->
                                  let uu____7283 =
                                    FStar_BigInt.sub_big_int x y  in
                                  int_as_bounded1 r int_to_t1 uu____7283)),
                    uu____7178)
                   in
                let uu____7284 =
                  let uu____7310 =
                    let uu____7334 =
                      FStar_Parser_Const.p2l ["FStar"; m; "mul"]  in
                    let uu____7335 =
                      FStar_TypeChecker_NBETerm.binary_op
                        FStar_TypeChecker_NBETerm.arg_as_bounded_int
                        (fun uu____7353  ->
                           fun uu____7354  ->
                             match (uu____7353, uu____7354) with
                             | ((int_to_t1,x),(uu____7373,y)) ->
                                 let uu____7383 =
                                   FStar_BigInt.mult_big_int x y  in
                                 FStar_TypeChecker_NBETerm.int_as_bounded
                                   int_to_t1 uu____7383)
                       in
                    (uu____7334, (Prims.parse_int "2"),
                      (Prims.parse_int "0"),
                      (binary_op1 arg_as_bounded_int1
                         (fun r  ->
                            fun uu____7410  ->
                              fun uu____7411  ->
                                match (uu____7410, uu____7411) with
                                | ((int_to_t1,x),(uu____7430,y)) ->
                                    let uu____7440 =
                                      FStar_BigInt.mult_big_int x y  in
                                    int_as_bounded1 r int_to_t1 uu____7440)),
                      uu____7335)
                     in
                  let uu____7441 =
                    let uu____7467 =
                      let uu____7491 =
                        FStar_Parser_Const.p2l ["FStar"; m; "v"]  in
                      let uu____7492 =
                        FStar_TypeChecker_NBETerm.unary_op
                          FStar_TypeChecker_NBETerm.arg_as_bounded_int
                          (fun uu____7506  ->
                             match uu____7506 with
                             | (int_to_t1,x) ->
                                 FStar_TypeChecker_NBETerm.embed
                                   FStar_TypeChecker_NBETerm.e_int x)
                         in
                      (uu____7491, (Prims.parse_int "1"),
                        (Prims.parse_int "0"),
                        (unary_op1 arg_as_bounded_int1
                           (fun r  ->
                              fun uu____7535  ->
                                match uu____7535 with
                                | (int_to_t1,x) ->
                                    FStar_Syntax_Embeddings.embed
                                      FStar_Syntax_Embeddings.e_int r x)),
                        uu____7492)
                       in
                    [uu____7467]  in
                  uu____7310 :: uu____7441  in
                uu____7153 :: uu____7284  in
              uu____6996 :: uu____7127))
       in
    let div_mod_unsigned =
      FStar_All.pipe_right bounded_unsigned_int_types
        (FStar_List.collect
           (fun m  ->
              let uu____7737 =
                let uu____7761 = FStar_Parser_Const.p2l ["FStar"; m; "div"]
                   in
                let uu____7762 =
                  FStar_TypeChecker_NBETerm.binary_op
                    FStar_TypeChecker_NBETerm.arg_as_bounded_int
                    (fun uu____7780  ->
                       fun uu____7781  ->
                         match (uu____7780, uu____7781) with
                         | ((int_to_t1,x),(uu____7800,y)) ->
                             let uu____7810 = FStar_BigInt.div_big_int x y
                                in
                             FStar_TypeChecker_NBETerm.int_as_bounded
                               int_to_t1 uu____7810)
                   in
                (uu____7761, (Prims.parse_int "2"), (Prims.parse_int "0"),
                  (binary_op1 arg_as_bounded_int1
                     (fun r  ->
                        fun uu____7837  ->
                          fun uu____7838  ->
                            match (uu____7837, uu____7838) with
                            | ((int_to_t1,x),(uu____7857,y)) ->
                                let uu____7867 = FStar_BigInt.div_big_int x y
                                   in
                                int_as_bounded1 r int_to_t1 uu____7867)),
                  uu____7762)
                 in
              let uu____7868 =
                let uu____7894 =
                  let uu____7918 = FStar_Parser_Const.p2l ["FStar"; m; "rem"]
                     in
                  let uu____7919 =
                    FStar_TypeChecker_NBETerm.binary_op
                      FStar_TypeChecker_NBETerm.arg_as_bounded_int
                      (fun uu____7937  ->
                         fun uu____7938  ->
                           match (uu____7937, uu____7938) with
                           | ((int_to_t1,x),(uu____7957,y)) ->
                               let uu____7967 = FStar_BigInt.mod_big_int x y
                                  in
                               FStar_TypeChecker_NBETerm.int_as_bounded
                                 int_to_t1 uu____7967)
                     in
                  (uu____7918, (Prims.parse_int "2"), (Prims.parse_int "0"),
                    (binary_op1 arg_as_bounded_int1
                       (fun r  ->
                          fun uu____7994  ->
                            fun uu____7995  ->
                              match (uu____7994, uu____7995) with
                              | ((int_to_t1,x),(uu____8014,y)) ->
                                  let uu____8024 =
                                    FStar_BigInt.mod_big_int x y  in
                                  int_as_bounded1 r int_to_t1 uu____8024)),
                    uu____7919)
                   in
                [uu____7894]  in
              uu____7737 :: uu____7868))
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
  let interp_prop1 psc args =
    let r = psc.psc_range  in
    match args with
    | (_typ,uu____8219)::(a1,uu____8221)::(a2,uu____8223)::[] ->
        let uu____8280 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____8280 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___254_8284 = FStar_Syntax_Util.t_true  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___254_8284.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___254_8284.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___255_8286 = FStar_Syntax_Util.t_false  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___255_8286.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___255_8286.FStar_Syntax_Syntax.vars)
                })
         | uu____8287 -> FStar_Pervasives_Native.None)
    | (_typ,uu____8289)::uu____8290::(a1,uu____8292)::(a2,uu____8294)::[] ->
        let uu____8367 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____8367 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___254_8371 = FStar_Syntax_Util.t_true  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___254_8371.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___254_8371.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___255_8373 = FStar_Syntax_Util.t_false  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___255_8373.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___255_8373.FStar_Syntax_Syntax.vars)
                })
         | uu____8374 -> FStar_Pervasives_Native.None)
    | uu____8375 -> failwith "Unexpected number of arguments"  in
  let propositional_equality =
    {
      name = FStar_Parser_Const.eq2_lid;
      arity = (Prims.parse_int "3");
      univ_arity = (Prims.parse_int "1");
      auto_reflect = FStar_Pervasives_Native.None;
      strong_reduction_ok = true;
      requires_binder_substitution = false;
      interpretation = interp_prop1;
      interpretation_nbe = FStar_TypeChecker_NBETerm.interp_prop
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
      interpretation_nbe = FStar_TypeChecker_NBETerm.interp_prop
    }  in
  prim_from_list [propositional_equality; hetero_propositional_equality] 
let (plugins :
  (primitive_step -> unit,unit -> primitive_step Prims.list)
    FStar_Pervasives_Native.tuple2)
  =
  let plugins = FStar_Util.mk_ref []  in
  let register p =
    let uu____8405 =
      let uu____8408 = FStar_ST.op_Bang plugins  in p :: uu____8408  in
    FStar_ST.op_Colon_Equals plugins uu____8405  in
  let retrieve uu____8508 = FStar_ST.op_Bang plugins  in (register, retrieve) 
let (register_plugin : primitive_step -> unit) =
  fun p  -> FStar_Pervasives_Native.fst plugins p 
let (retrieve_plugins : unit -> primitive_step Prims.list) =
  fun uu____8581  -> FStar_Pervasives_Native.snd plugins () 
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
               (fun uu___225_8622  ->
                  match uu___225_8622 with
                  | FStar_TypeChecker_Env.UnfoldUntil k ->
                      [FStar_TypeChecker_Env.Unfold k]
                  | FStar_TypeChecker_Env.Eager_unfolding  ->
                      [FStar_TypeChecker_Env.Eager_unfolding_only]
                  | FStar_TypeChecker_Env.Inlining  ->
                      [FStar_TypeChecker_Env.InliningDelta]
                  | uu____8626 -> []))
           in
        let d1 =
          match d with
          | [] -> [FStar_TypeChecker_Env.NoDelta]
          | uu____8632 -> d  in
        let uu____8635 = to_fsteps s  in
        let uu____8636 =
          let uu____8637 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Norm")  in
          let uu____8638 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "NormTop")  in
          let uu____8639 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "NormCfg")  in
          let uu____8640 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Primops")  in
          let uu____8641 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Unfolding")
             in
          let uu____8642 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "380")  in
          let uu____8643 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "WPE")  in
          let uu____8644 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "NormDelayed")
             in
          let uu____8645 =
            FStar_TypeChecker_Env.debug e
              (FStar_Options.Other "print_normalized_terms")
             in
          {
            gen = uu____8637;
            top = uu____8638;
            cfg = uu____8639;
            primop = uu____8640;
            unfolding = uu____8641;
            b380 = uu____8642;
            wpe = uu____8643;
            norm_delayed = uu____8644;
            print_normalized = uu____8645
          }  in
        let uu____8646 =
          let uu____8649 =
            let uu____8652 = retrieve_plugins ()  in
            FStar_List.append uu____8652 psteps  in
          add_steps built_in_primitive_steps uu____8649  in
        let uu____8655 =
          (FStar_Options.normalize_pure_terms_for_extraction ()) ||
            (let uu____8657 =
               FStar_All.pipe_right s
                 (FStar_List.contains
                    FStar_TypeChecker_Env.PureSubtermsWithinComputations)
                in
             Prims.op_Negation uu____8657)
           in
        {
          steps = uu____8635;
          tcenv = e;
          debug = uu____8636;
          delta_level = d1;
          primitive_steps = uu____8646;
          strong = false;
          memoize_lazy = true;
          normalize_pure_lets = uu____8655;
          reifying = false
        }
  
let (config :
  FStar_TypeChecker_Env.step Prims.list -> FStar_TypeChecker_Env.env -> cfg)
  = fun s  -> fun e  -> config' [] s e 