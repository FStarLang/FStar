open Prims
let cases :
  'Auu____11 'Auu____12 .
    ('Auu____11 -> 'Auu____12) ->
      'Auu____12 -> 'Auu____11 FStar_Pervasives_Native.option -> 'Auu____12
  =
  fun f  ->
    fun d  ->
      fun uu___239_32  ->
        match uu___239_32 with
        | FStar_Pervasives_Native.Some x -> f x
        | FStar_Pervasives_Native.None  -> d
  
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
      let add_opt x uu___240_1339 =
        match uu___240_1339 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.Some [x]
        | FStar_Pervasives_Native.Some xs ->
            FStar_Pervasives_Native.Some (x :: xs)
         in
      match s with
      | FStar_TypeChecker_Env.Beta  ->
          let uu___260_1359 = fs  in
          {
            beta = true;
            iota = (uu___260_1359.iota);
            zeta = (uu___260_1359.zeta);
            weak = (uu___260_1359.weak);
            hnf = (uu___260_1359.hnf);
            primops = (uu___260_1359.primops);
            do_not_unfold_pure_lets = (uu___260_1359.do_not_unfold_pure_lets);
            unfold_until = (uu___260_1359.unfold_until);
            unfold_only = (uu___260_1359.unfold_only);
            unfold_fully = (uu___260_1359.unfold_fully);
            unfold_attr = (uu___260_1359.unfold_attr);
            unfold_tac = (uu___260_1359.unfold_tac);
            pure_subterms_within_computations =
              (uu___260_1359.pure_subterms_within_computations);
            simplify = (uu___260_1359.simplify);
            erase_universes = (uu___260_1359.erase_universes);
            allow_unbound_universes = (uu___260_1359.allow_unbound_universes);
            reify_ = (uu___260_1359.reify_);
            compress_uvars = (uu___260_1359.compress_uvars);
            no_full_norm = (uu___260_1359.no_full_norm);
            check_no_uvars = (uu___260_1359.check_no_uvars);
            unmeta = (uu___260_1359.unmeta);
            unascribe = (uu___260_1359.unascribe);
            in_full_norm_request = (uu___260_1359.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___260_1359.weakly_reduce_scrutinee);
            nbe_step = (uu___260_1359.nbe_step)
          }
      | FStar_TypeChecker_Env.Iota  ->
          let uu___261_1360 = fs  in
          {
            beta = (uu___261_1360.beta);
            iota = true;
            zeta = (uu___261_1360.zeta);
            weak = (uu___261_1360.weak);
            hnf = (uu___261_1360.hnf);
            primops = (uu___261_1360.primops);
            do_not_unfold_pure_lets = (uu___261_1360.do_not_unfold_pure_lets);
            unfold_until = (uu___261_1360.unfold_until);
            unfold_only = (uu___261_1360.unfold_only);
            unfold_fully = (uu___261_1360.unfold_fully);
            unfold_attr = (uu___261_1360.unfold_attr);
            unfold_tac = (uu___261_1360.unfold_tac);
            pure_subterms_within_computations =
              (uu___261_1360.pure_subterms_within_computations);
            simplify = (uu___261_1360.simplify);
            erase_universes = (uu___261_1360.erase_universes);
            allow_unbound_universes = (uu___261_1360.allow_unbound_universes);
            reify_ = (uu___261_1360.reify_);
            compress_uvars = (uu___261_1360.compress_uvars);
            no_full_norm = (uu___261_1360.no_full_norm);
            check_no_uvars = (uu___261_1360.check_no_uvars);
            unmeta = (uu___261_1360.unmeta);
            unascribe = (uu___261_1360.unascribe);
            in_full_norm_request = (uu___261_1360.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___261_1360.weakly_reduce_scrutinee);
            nbe_step = (uu___261_1360.nbe_step)
          }
      | FStar_TypeChecker_Env.Zeta  ->
          let uu___262_1361 = fs  in
          {
            beta = (uu___262_1361.beta);
            iota = (uu___262_1361.iota);
            zeta = true;
            weak = (uu___262_1361.weak);
            hnf = (uu___262_1361.hnf);
            primops = (uu___262_1361.primops);
            do_not_unfold_pure_lets = (uu___262_1361.do_not_unfold_pure_lets);
            unfold_until = (uu___262_1361.unfold_until);
            unfold_only = (uu___262_1361.unfold_only);
            unfold_fully = (uu___262_1361.unfold_fully);
            unfold_attr = (uu___262_1361.unfold_attr);
            unfold_tac = (uu___262_1361.unfold_tac);
            pure_subterms_within_computations =
              (uu___262_1361.pure_subterms_within_computations);
            simplify = (uu___262_1361.simplify);
            erase_universes = (uu___262_1361.erase_universes);
            allow_unbound_universes = (uu___262_1361.allow_unbound_universes);
            reify_ = (uu___262_1361.reify_);
            compress_uvars = (uu___262_1361.compress_uvars);
            no_full_norm = (uu___262_1361.no_full_norm);
            check_no_uvars = (uu___262_1361.check_no_uvars);
            unmeta = (uu___262_1361.unmeta);
            unascribe = (uu___262_1361.unascribe);
            in_full_norm_request = (uu___262_1361.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___262_1361.weakly_reduce_scrutinee);
            nbe_step = (uu___262_1361.nbe_step)
          }
      | FStar_TypeChecker_Env.Exclude (FStar_TypeChecker_Env.Beta ) ->
          let uu___263_1362 = fs  in
          {
            beta = false;
            iota = (uu___263_1362.iota);
            zeta = (uu___263_1362.zeta);
            weak = (uu___263_1362.weak);
            hnf = (uu___263_1362.hnf);
            primops = (uu___263_1362.primops);
            do_not_unfold_pure_lets = (uu___263_1362.do_not_unfold_pure_lets);
            unfold_until = (uu___263_1362.unfold_until);
            unfold_only = (uu___263_1362.unfold_only);
            unfold_fully = (uu___263_1362.unfold_fully);
            unfold_attr = (uu___263_1362.unfold_attr);
            unfold_tac = (uu___263_1362.unfold_tac);
            pure_subterms_within_computations =
              (uu___263_1362.pure_subterms_within_computations);
            simplify = (uu___263_1362.simplify);
            erase_universes = (uu___263_1362.erase_universes);
            allow_unbound_universes = (uu___263_1362.allow_unbound_universes);
            reify_ = (uu___263_1362.reify_);
            compress_uvars = (uu___263_1362.compress_uvars);
            no_full_norm = (uu___263_1362.no_full_norm);
            check_no_uvars = (uu___263_1362.check_no_uvars);
            unmeta = (uu___263_1362.unmeta);
            unascribe = (uu___263_1362.unascribe);
            in_full_norm_request = (uu___263_1362.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___263_1362.weakly_reduce_scrutinee);
            nbe_step = (uu___263_1362.nbe_step)
          }
      | FStar_TypeChecker_Env.Exclude (FStar_TypeChecker_Env.Iota ) ->
          let uu___264_1363 = fs  in
          {
            beta = (uu___264_1363.beta);
            iota = false;
            zeta = (uu___264_1363.zeta);
            weak = (uu___264_1363.weak);
            hnf = (uu___264_1363.hnf);
            primops = (uu___264_1363.primops);
            do_not_unfold_pure_lets = (uu___264_1363.do_not_unfold_pure_lets);
            unfold_until = (uu___264_1363.unfold_until);
            unfold_only = (uu___264_1363.unfold_only);
            unfold_fully = (uu___264_1363.unfold_fully);
            unfold_attr = (uu___264_1363.unfold_attr);
            unfold_tac = (uu___264_1363.unfold_tac);
            pure_subterms_within_computations =
              (uu___264_1363.pure_subterms_within_computations);
            simplify = (uu___264_1363.simplify);
            erase_universes = (uu___264_1363.erase_universes);
            allow_unbound_universes = (uu___264_1363.allow_unbound_universes);
            reify_ = (uu___264_1363.reify_);
            compress_uvars = (uu___264_1363.compress_uvars);
            no_full_norm = (uu___264_1363.no_full_norm);
            check_no_uvars = (uu___264_1363.check_no_uvars);
            unmeta = (uu___264_1363.unmeta);
            unascribe = (uu___264_1363.unascribe);
            in_full_norm_request = (uu___264_1363.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___264_1363.weakly_reduce_scrutinee);
            nbe_step = (uu___264_1363.nbe_step)
          }
      | FStar_TypeChecker_Env.Exclude (FStar_TypeChecker_Env.Zeta ) ->
          let uu___265_1364 = fs  in
          {
            beta = (uu___265_1364.beta);
            iota = (uu___265_1364.iota);
            zeta = false;
            weak = (uu___265_1364.weak);
            hnf = (uu___265_1364.hnf);
            primops = (uu___265_1364.primops);
            do_not_unfold_pure_lets = (uu___265_1364.do_not_unfold_pure_lets);
            unfold_until = (uu___265_1364.unfold_until);
            unfold_only = (uu___265_1364.unfold_only);
            unfold_fully = (uu___265_1364.unfold_fully);
            unfold_attr = (uu___265_1364.unfold_attr);
            unfold_tac = (uu___265_1364.unfold_tac);
            pure_subterms_within_computations =
              (uu___265_1364.pure_subterms_within_computations);
            simplify = (uu___265_1364.simplify);
            erase_universes = (uu___265_1364.erase_universes);
            allow_unbound_universes = (uu___265_1364.allow_unbound_universes);
            reify_ = (uu___265_1364.reify_);
            compress_uvars = (uu___265_1364.compress_uvars);
            no_full_norm = (uu___265_1364.no_full_norm);
            check_no_uvars = (uu___265_1364.check_no_uvars);
            unmeta = (uu___265_1364.unmeta);
            unascribe = (uu___265_1364.unascribe);
            in_full_norm_request = (uu___265_1364.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___265_1364.weakly_reduce_scrutinee);
            nbe_step = (uu___265_1364.nbe_step)
          }
      | FStar_TypeChecker_Env.Exclude uu____1365 -> failwith "Bad exclude"
      | FStar_TypeChecker_Env.Weak  ->
          let uu___266_1366 = fs  in
          {
            beta = (uu___266_1366.beta);
            iota = (uu___266_1366.iota);
            zeta = (uu___266_1366.zeta);
            weak = true;
            hnf = (uu___266_1366.hnf);
            primops = (uu___266_1366.primops);
            do_not_unfold_pure_lets = (uu___266_1366.do_not_unfold_pure_lets);
            unfold_until = (uu___266_1366.unfold_until);
            unfold_only = (uu___266_1366.unfold_only);
            unfold_fully = (uu___266_1366.unfold_fully);
            unfold_attr = (uu___266_1366.unfold_attr);
            unfold_tac = (uu___266_1366.unfold_tac);
            pure_subterms_within_computations =
              (uu___266_1366.pure_subterms_within_computations);
            simplify = (uu___266_1366.simplify);
            erase_universes = (uu___266_1366.erase_universes);
            allow_unbound_universes = (uu___266_1366.allow_unbound_universes);
            reify_ = (uu___266_1366.reify_);
            compress_uvars = (uu___266_1366.compress_uvars);
            no_full_norm = (uu___266_1366.no_full_norm);
            check_no_uvars = (uu___266_1366.check_no_uvars);
            unmeta = (uu___266_1366.unmeta);
            unascribe = (uu___266_1366.unascribe);
            in_full_norm_request = (uu___266_1366.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___266_1366.weakly_reduce_scrutinee);
            nbe_step = (uu___266_1366.nbe_step)
          }
      | FStar_TypeChecker_Env.HNF  ->
          let uu___267_1367 = fs  in
          {
            beta = (uu___267_1367.beta);
            iota = (uu___267_1367.iota);
            zeta = (uu___267_1367.zeta);
            weak = (uu___267_1367.weak);
            hnf = true;
            primops = (uu___267_1367.primops);
            do_not_unfold_pure_lets = (uu___267_1367.do_not_unfold_pure_lets);
            unfold_until = (uu___267_1367.unfold_until);
            unfold_only = (uu___267_1367.unfold_only);
            unfold_fully = (uu___267_1367.unfold_fully);
            unfold_attr = (uu___267_1367.unfold_attr);
            unfold_tac = (uu___267_1367.unfold_tac);
            pure_subterms_within_computations =
              (uu___267_1367.pure_subterms_within_computations);
            simplify = (uu___267_1367.simplify);
            erase_universes = (uu___267_1367.erase_universes);
            allow_unbound_universes = (uu___267_1367.allow_unbound_universes);
            reify_ = (uu___267_1367.reify_);
            compress_uvars = (uu___267_1367.compress_uvars);
            no_full_norm = (uu___267_1367.no_full_norm);
            check_no_uvars = (uu___267_1367.check_no_uvars);
            unmeta = (uu___267_1367.unmeta);
            unascribe = (uu___267_1367.unascribe);
            in_full_norm_request = (uu___267_1367.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___267_1367.weakly_reduce_scrutinee);
            nbe_step = (uu___267_1367.nbe_step)
          }
      | FStar_TypeChecker_Env.Primops  ->
          let uu___268_1368 = fs  in
          {
            beta = (uu___268_1368.beta);
            iota = (uu___268_1368.iota);
            zeta = (uu___268_1368.zeta);
            weak = (uu___268_1368.weak);
            hnf = (uu___268_1368.hnf);
            primops = true;
            do_not_unfold_pure_lets = (uu___268_1368.do_not_unfold_pure_lets);
            unfold_until = (uu___268_1368.unfold_until);
            unfold_only = (uu___268_1368.unfold_only);
            unfold_fully = (uu___268_1368.unfold_fully);
            unfold_attr = (uu___268_1368.unfold_attr);
            unfold_tac = (uu___268_1368.unfold_tac);
            pure_subterms_within_computations =
              (uu___268_1368.pure_subterms_within_computations);
            simplify = (uu___268_1368.simplify);
            erase_universes = (uu___268_1368.erase_universes);
            allow_unbound_universes = (uu___268_1368.allow_unbound_universes);
            reify_ = (uu___268_1368.reify_);
            compress_uvars = (uu___268_1368.compress_uvars);
            no_full_norm = (uu___268_1368.no_full_norm);
            check_no_uvars = (uu___268_1368.check_no_uvars);
            unmeta = (uu___268_1368.unmeta);
            unascribe = (uu___268_1368.unascribe);
            in_full_norm_request = (uu___268_1368.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___268_1368.weakly_reduce_scrutinee);
            nbe_step = (uu___268_1368.nbe_step)
          }
      | FStar_TypeChecker_Env.Eager_unfolding  -> fs
      | FStar_TypeChecker_Env.Inlining  -> fs
      | FStar_TypeChecker_Env.DoNotUnfoldPureLets  ->
          let uu___269_1369 = fs  in
          {
            beta = (uu___269_1369.beta);
            iota = (uu___269_1369.iota);
            zeta = (uu___269_1369.zeta);
            weak = (uu___269_1369.weak);
            hnf = (uu___269_1369.hnf);
            primops = (uu___269_1369.primops);
            do_not_unfold_pure_lets = true;
            unfold_until = (uu___269_1369.unfold_until);
            unfold_only = (uu___269_1369.unfold_only);
            unfold_fully = (uu___269_1369.unfold_fully);
            unfold_attr = (uu___269_1369.unfold_attr);
            unfold_tac = (uu___269_1369.unfold_tac);
            pure_subterms_within_computations =
              (uu___269_1369.pure_subterms_within_computations);
            simplify = (uu___269_1369.simplify);
            erase_universes = (uu___269_1369.erase_universes);
            allow_unbound_universes = (uu___269_1369.allow_unbound_universes);
            reify_ = (uu___269_1369.reify_);
            compress_uvars = (uu___269_1369.compress_uvars);
            no_full_norm = (uu___269_1369.no_full_norm);
            check_no_uvars = (uu___269_1369.check_no_uvars);
            unmeta = (uu___269_1369.unmeta);
            unascribe = (uu___269_1369.unascribe);
            in_full_norm_request = (uu___269_1369.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___269_1369.weakly_reduce_scrutinee);
            nbe_step = (uu___269_1369.nbe_step)
          }
      | FStar_TypeChecker_Env.UnfoldUntil d ->
          let uu___270_1371 = fs  in
          {
            beta = (uu___270_1371.beta);
            iota = (uu___270_1371.iota);
            zeta = (uu___270_1371.zeta);
            weak = (uu___270_1371.weak);
            hnf = (uu___270_1371.hnf);
            primops = (uu___270_1371.primops);
            do_not_unfold_pure_lets = (uu___270_1371.do_not_unfold_pure_lets);
            unfold_until = (FStar_Pervasives_Native.Some d);
            unfold_only = (uu___270_1371.unfold_only);
            unfold_fully = (uu___270_1371.unfold_fully);
            unfold_attr = (uu___270_1371.unfold_attr);
            unfold_tac = (uu___270_1371.unfold_tac);
            pure_subterms_within_computations =
              (uu___270_1371.pure_subterms_within_computations);
            simplify = (uu___270_1371.simplify);
            erase_universes = (uu___270_1371.erase_universes);
            allow_unbound_universes = (uu___270_1371.allow_unbound_universes);
            reify_ = (uu___270_1371.reify_);
            compress_uvars = (uu___270_1371.compress_uvars);
            no_full_norm = (uu___270_1371.no_full_norm);
            check_no_uvars = (uu___270_1371.check_no_uvars);
            unmeta = (uu___270_1371.unmeta);
            unascribe = (uu___270_1371.unascribe);
            in_full_norm_request = (uu___270_1371.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___270_1371.weakly_reduce_scrutinee);
            nbe_step = (uu___270_1371.nbe_step)
          }
      | FStar_TypeChecker_Env.UnfoldOnly lids ->
          let uu___271_1375 = fs  in
          {
            beta = (uu___271_1375.beta);
            iota = (uu___271_1375.iota);
            zeta = (uu___271_1375.zeta);
            weak = (uu___271_1375.weak);
            hnf = (uu___271_1375.hnf);
            primops = (uu___271_1375.primops);
            do_not_unfold_pure_lets = (uu___271_1375.do_not_unfold_pure_lets);
            unfold_until = (uu___271_1375.unfold_until);
            unfold_only = (FStar_Pervasives_Native.Some lids);
            unfold_fully = (uu___271_1375.unfold_fully);
            unfold_attr = (uu___271_1375.unfold_attr);
            unfold_tac = (uu___271_1375.unfold_tac);
            pure_subterms_within_computations =
              (uu___271_1375.pure_subterms_within_computations);
            simplify = (uu___271_1375.simplify);
            erase_universes = (uu___271_1375.erase_universes);
            allow_unbound_universes = (uu___271_1375.allow_unbound_universes);
            reify_ = (uu___271_1375.reify_);
            compress_uvars = (uu___271_1375.compress_uvars);
            no_full_norm = (uu___271_1375.no_full_norm);
            check_no_uvars = (uu___271_1375.check_no_uvars);
            unmeta = (uu___271_1375.unmeta);
            unascribe = (uu___271_1375.unascribe);
            in_full_norm_request = (uu___271_1375.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___271_1375.weakly_reduce_scrutinee);
            nbe_step = (uu___271_1375.nbe_step)
          }
      | FStar_TypeChecker_Env.UnfoldFully lids ->
          let uu___272_1381 = fs  in
          {
            beta = (uu___272_1381.beta);
            iota = (uu___272_1381.iota);
            zeta = (uu___272_1381.zeta);
            weak = (uu___272_1381.weak);
            hnf = (uu___272_1381.hnf);
            primops = (uu___272_1381.primops);
            do_not_unfold_pure_lets = (uu___272_1381.do_not_unfold_pure_lets);
            unfold_until = (uu___272_1381.unfold_until);
            unfold_only = (uu___272_1381.unfold_only);
            unfold_fully = (FStar_Pervasives_Native.Some lids);
            unfold_attr = (uu___272_1381.unfold_attr);
            unfold_tac = (uu___272_1381.unfold_tac);
            pure_subterms_within_computations =
              (uu___272_1381.pure_subterms_within_computations);
            simplify = (uu___272_1381.simplify);
            erase_universes = (uu___272_1381.erase_universes);
            allow_unbound_universes = (uu___272_1381.allow_unbound_universes);
            reify_ = (uu___272_1381.reify_);
            compress_uvars = (uu___272_1381.compress_uvars);
            no_full_norm = (uu___272_1381.no_full_norm);
            check_no_uvars = (uu___272_1381.check_no_uvars);
            unmeta = (uu___272_1381.unmeta);
            unascribe = (uu___272_1381.unascribe);
            in_full_norm_request = (uu___272_1381.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___272_1381.weakly_reduce_scrutinee);
            nbe_step = (uu___272_1381.nbe_step)
          }
      | FStar_TypeChecker_Env.UnfoldAttr attr ->
          let uu___273_1385 = fs  in
          {
            beta = (uu___273_1385.beta);
            iota = (uu___273_1385.iota);
            zeta = (uu___273_1385.zeta);
            weak = (uu___273_1385.weak);
            hnf = (uu___273_1385.hnf);
            primops = (uu___273_1385.primops);
            do_not_unfold_pure_lets = (uu___273_1385.do_not_unfold_pure_lets);
            unfold_until = (uu___273_1385.unfold_until);
            unfold_only = (uu___273_1385.unfold_only);
            unfold_fully = (uu___273_1385.unfold_fully);
            unfold_attr = (add_opt attr fs.unfold_attr);
            unfold_tac = (uu___273_1385.unfold_tac);
            pure_subterms_within_computations =
              (uu___273_1385.pure_subterms_within_computations);
            simplify = (uu___273_1385.simplify);
            erase_universes = (uu___273_1385.erase_universes);
            allow_unbound_universes = (uu___273_1385.allow_unbound_universes);
            reify_ = (uu___273_1385.reify_);
            compress_uvars = (uu___273_1385.compress_uvars);
            no_full_norm = (uu___273_1385.no_full_norm);
            check_no_uvars = (uu___273_1385.check_no_uvars);
            unmeta = (uu___273_1385.unmeta);
            unascribe = (uu___273_1385.unascribe);
            in_full_norm_request = (uu___273_1385.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___273_1385.weakly_reduce_scrutinee);
            nbe_step = (uu___273_1385.nbe_step)
          }
      | FStar_TypeChecker_Env.UnfoldTac  ->
          let uu___274_1386 = fs  in
          {
            beta = (uu___274_1386.beta);
            iota = (uu___274_1386.iota);
            zeta = (uu___274_1386.zeta);
            weak = (uu___274_1386.weak);
            hnf = (uu___274_1386.hnf);
            primops = (uu___274_1386.primops);
            do_not_unfold_pure_lets = (uu___274_1386.do_not_unfold_pure_lets);
            unfold_until = (uu___274_1386.unfold_until);
            unfold_only = (uu___274_1386.unfold_only);
            unfold_fully = (uu___274_1386.unfold_fully);
            unfold_attr = (uu___274_1386.unfold_attr);
            unfold_tac = true;
            pure_subterms_within_computations =
              (uu___274_1386.pure_subterms_within_computations);
            simplify = (uu___274_1386.simplify);
            erase_universes = (uu___274_1386.erase_universes);
            allow_unbound_universes = (uu___274_1386.allow_unbound_universes);
            reify_ = (uu___274_1386.reify_);
            compress_uvars = (uu___274_1386.compress_uvars);
            no_full_norm = (uu___274_1386.no_full_norm);
            check_no_uvars = (uu___274_1386.check_no_uvars);
            unmeta = (uu___274_1386.unmeta);
            unascribe = (uu___274_1386.unascribe);
            in_full_norm_request = (uu___274_1386.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___274_1386.weakly_reduce_scrutinee);
            nbe_step = (uu___274_1386.nbe_step)
          }
      | FStar_TypeChecker_Env.PureSubtermsWithinComputations  ->
          let uu___275_1387 = fs  in
          {
            beta = (uu___275_1387.beta);
            iota = (uu___275_1387.iota);
            zeta = (uu___275_1387.zeta);
            weak = (uu___275_1387.weak);
            hnf = (uu___275_1387.hnf);
            primops = (uu___275_1387.primops);
            do_not_unfold_pure_lets = (uu___275_1387.do_not_unfold_pure_lets);
            unfold_until = (uu___275_1387.unfold_until);
            unfold_only = (uu___275_1387.unfold_only);
            unfold_fully = (uu___275_1387.unfold_fully);
            unfold_attr = (uu___275_1387.unfold_attr);
            unfold_tac = (uu___275_1387.unfold_tac);
            pure_subterms_within_computations = true;
            simplify = (uu___275_1387.simplify);
            erase_universes = (uu___275_1387.erase_universes);
            allow_unbound_universes = (uu___275_1387.allow_unbound_universes);
            reify_ = (uu___275_1387.reify_);
            compress_uvars = (uu___275_1387.compress_uvars);
            no_full_norm = (uu___275_1387.no_full_norm);
            check_no_uvars = (uu___275_1387.check_no_uvars);
            unmeta = (uu___275_1387.unmeta);
            unascribe = (uu___275_1387.unascribe);
            in_full_norm_request = (uu___275_1387.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___275_1387.weakly_reduce_scrutinee);
            nbe_step = (uu___275_1387.nbe_step)
          }
      | FStar_TypeChecker_Env.Simplify  ->
          let uu___276_1388 = fs  in
          {
            beta = (uu___276_1388.beta);
            iota = (uu___276_1388.iota);
            zeta = (uu___276_1388.zeta);
            weak = (uu___276_1388.weak);
            hnf = (uu___276_1388.hnf);
            primops = (uu___276_1388.primops);
            do_not_unfold_pure_lets = (uu___276_1388.do_not_unfold_pure_lets);
            unfold_until = (uu___276_1388.unfold_until);
            unfold_only = (uu___276_1388.unfold_only);
            unfold_fully = (uu___276_1388.unfold_fully);
            unfold_attr = (uu___276_1388.unfold_attr);
            unfold_tac = (uu___276_1388.unfold_tac);
            pure_subterms_within_computations =
              (uu___276_1388.pure_subterms_within_computations);
            simplify = true;
            erase_universes = (uu___276_1388.erase_universes);
            allow_unbound_universes = (uu___276_1388.allow_unbound_universes);
            reify_ = (uu___276_1388.reify_);
            compress_uvars = (uu___276_1388.compress_uvars);
            no_full_norm = (uu___276_1388.no_full_norm);
            check_no_uvars = (uu___276_1388.check_no_uvars);
            unmeta = (uu___276_1388.unmeta);
            unascribe = (uu___276_1388.unascribe);
            in_full_norm_request = (uu___276_1388.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___276_1388.weakly_reduce_scrutinee);
            nbe_step = (uu___276_1388.nbe_step)
          }
      | FStar_TypeChecker_Env.EraseUniverses  ->
          let uu___277_1389 = fs  in
          {
            beta = (uu___277_1389.beta);
            iota = (uu___277_1389.iota);
            zeta = (uu___277_1389.zeta);
            weak = (uu___277_1389.weak);
            hnf = (uu___277_1389.hnf);
            primops = (uu___277_1389.primops);
            do_not_unfold_pure_lets = (uu___277_1389.do_not_unfold_pure_lets);
            unfold_until = (uu___277_1389.unfold_until);
            unfold_only = (uu___277_1389.unfold_only);
            unfold_fully = (uu___277_1389.unfold_fully);
            unfold_attr = (uu___277_1389.unfold_attr);
            unfold_tac = (uu___277_1389.unfold_tac);
            pure_subterms_within_computations =
              (uu___277_1389.pure_subterms_within_computations);
            simplify = (uu___277_1389.simplify);
            erase_universes = true;
            allow_unbound_universes = (uu___277_1389.allow_unbound_universes);
            reify_ = (uu___277_1389.reify_);
            compress_uvars = (uu___277_1389.compress_uvars);
            no_full_norm = (uu___277_1389.no_full_norm);
            check_no_uvars = (uu___277_1389.check_no_uvars);
            unmeta = (uu___277_1389.unmeta);
            unascribe = (uu___277_1389.unascribe);
            in_full_norm_request = (uu___277_1389.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___277_1389.weakly_reduce_scrutinee);
            nbe_step = (uu___277_1389.nbe_step)
          }
      | FStar_TypeChecker_Env.AllowUnboundUniverses  ->
          let uu___278_1390 = fs  in
          {
            beta = (uu___278_1390.beta);
            iota = (uu___278_1390.iota);
            zeta = (uu___278_1390.zeta);
            weak = (uu___278_1390.weak);
            hnf = (uu___278_1390.hnf);
            primops = (uu___278_1390.primops);
            do_not_unfold_pure_lets = (uu___278_1390.do_not_unfold_pure_lets);
            unfold_until = (uu___278_1390.unfold_until);
            unfold_only = (uu___278_1390.unfold_only);
            unfold_fully = (uu___278_1390.unfold_fully);
            unfold_attr = (uu___278_1390.unfold_attr);
            unfold_tac = (uu___278_1390.unfold_tac);
            pure_subterms_within_computations =
              (uu___278_1390.pure_subterms_within_computations);
            simplify = (uu___278_1390.simplify);
            erase_universes = (uu___278_1390.erase_universes);
            allow_unbound_universes = true;
            reify_ = (uu___278_1390.reify_);
            compress_uvars = (uu___278_1390.compress_uvars);
            no_full_norm = (uu___278_1390.no_full_norm);
            check_no_uvars = (uu___278_1390.check_no_uvars);
            unmeta = (uu___278_1390.unmeta);
            unascribe = (uu___278_1390.unascribe);
            in_full_norm_request = (uu___278_1390.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___278_1390.weakly_reduce_scrutinee);
            nbe_step = (uu___278_1390.nbe_step)
          }
      | FStar_TypeChecker_Env.Reify  ->
          let uu___279_1391 = fs  in
          {
            beta = (uu___279_1391.beta);
            iota = (uu___279_1391.iota);
            zeta = (uu___279_1391.zeta);
            weak = (uu___279_1391.weak);
            hnf = (uu___279_1391.hnf);
            primops = (uu___279_1391.primops);
            do_not_unfold_pure_lets = (uu___279_1391.do_not_unfold_pure_lets);
            unfold_until = (uu___279_1391.unfold_until);
            unfold_only = (uu___279_1391.unfold_only);
            unfold_fully = (uu___279_1391.unfold_fully);
            unfold_attr = (uu___279_1391.unfold_attr);
            unfold_tac = (uu___279_1391.unfold_tac);
            pure_subterms_within_computations =
              (uu___279_1391.pure_subterms_within_computations);
            simplify = (uu___279_1391.simplify);
            erase_universes = (uu___279_1391.erase_universes);
            allow_unbound_universes = (uu___279_1391.allow_unbound_universes);
            reify_ = true;
            compress_uvars = (uu___279_1391.compress_uvars);
            no_full_norm = (uu___279_1391.no_full_norm);
            check_no_uvars = (uu___279_1391.check_no_uvars);
            unmeta = (uu___279_1391.unmeta);
            unascribe = (uu___279_1391.unascribe);
            in_full_norm_request = (uu___279_1391.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___279_1391.weakly_reduce_scrutinee);
            nbe_step = (uu___279_1391.nbe_step)
          }
      | FStar_TypeChecker_Env.CompressUvars  ->
          let uu___280_1392 = fs  in
          {
            beta = (uu___280_1392.beta);
            iota = (uu___280_1392.iota);
            zeta = (uu___280_1392.zeta);
            weak = (uu___280_1392.weak);
            hnf = (uu___280_1392.hnf);
            primops = (uu___280_1392.primops);
            do_not_unfold_pure_lets = (uu___280_1392.do_not_unfold_pure_lets);
            unfold_until = (uu___280_1392.unfold_until);
            unfold_only = (uu___280_1392.unfold_only);
            unfold_fully = (uu___280_1392.unfold_fully);
            unfold_attr = (uu___280_1392.unfold_attr);
            unfold_tac = (uu___280_1392.unfold_tac);
            pure_subterms_within_computations =
              (uu___280_1392.pure_subterms_within_computations);
            simplify = (uu___280_1392.simplify);
            erase_universes = (uu___280_1392.erase_universes);
            allow_unbound_universes = (uu___280_1392.allow_unbound_universes);
            reify_ = (uu___280_1392.reify_);
            compress_uvars = true;
            no_full_norm = (uu___280_1392.no_full_norm);
            check_no_uvars = (uu___280_1392.check_no_uvars);
            unmeta = (uu___280_1392.unmeta);
            unascribe = (uu___280_1392.unascribe);
            in_full_norm_request = (uu___280_1392.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___280_1392.weakly_reduce_scrutinee);
            nbe_step = (uu___280_1392.nbe_step)
          }
      | FStar_TypeChecker_Env.NoFullNorm  ->
          let uu___281_1393 = fs  in
          {
            beta = (uu___281_1393.beta);
            iota = (uu___281_1393.iota);
            zeta = (uu___281_1393.zeta);
            weak = (uu___281_1393.weak);
            hnf = (uu___281_1393.hnf);
            primops = (uu___281_1393.primops);
            do_not_unfold_pure_lets = (uu___281_1393.do_not_unfold_pure_lets);
            unfold_until = (uu___281_1393.unfold_until);
            unfold_only = (uu___281_1393.unfold_only);
            unfold_fully = (uu___281_1393.unfold_fully);
            unfold_attr = (uu___281_1393.unfold_attr);
            unfold_tac = (uu___281_1393.unfold_tac);
            pure_subterms_within_computations =
              (uu___281_1393.pure_subterms_within_computations);
            simplify = (uu___281_1393.simplify);
            erase_universes = (uu___281_1393.erase_universes);
            allow_unbound_universes = (uu___281_1393.allow_unbound_universes);
            reify_ = (uu___281_1393.reify_);
            compress_uvars = (uu___281_1393.compress_uvars);
            no_full_norm = true;
            check_no_uvars = (uu___281_1393.check_no_uvars);
            unmeta = (uu___281_1393.unmeta);
            unascribe = (uu___281_1393.unascribe);
            in_full_norm_request = (uu___281_1393.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___281_1393.weakly_reduce_scrutinee);
            nbe_step = (uu___281_1393.nbe_step)
          }
      | FStar_TypeChecker_Env.CheckNoUvars  ->
          let uu___282_1394 = fs  in
          {
            beta = (uu___282_1394.beta);
            iota = (uu___282_1394.iota);
            zeta = (uu___282_1394.zeta);
            weak = (uu___282_1394.weak);
            hnf = (uu___282_1394.hnf);
            primops = (uu___282_1394.primops);
            do_not_unfold_pure_lets = (uu___282_1394.do_not_unfold_pure_lets);
            unfold_until = (uu___282_1394.unfold_until);
            unfold_only = (uu___282_1394.unfold_only);
            unfold_fully = (uu___282_1394.unfold_fully);
            unfold_attr = (uu___282_1394.unfold_attr);
            unfold_tac = (uu___282_1394.unfold_tac);
            pure_subterms_within_computations =
              (uu___282_1394.pure_subterms_within_computations);
            simplify = (uu___282_1394.simplify);
            erase_universes = (uu___282_1394.erase_universes);
            allow_unbound_universes = (uu___282_1394.allow_unbound_universes);
            reify_ = (uu___282_1394.reify_);
            compress_uvars = (uu___282_1394.compress_uvars);
            no_full_norm = (uu___282_1394.no_full_norm);
            check_no_uvars = true;
            unmeta = (uu___282_1394.unmeta);
            unascribe = (uu___282_1394.unascribe);
            in_full_norm_request = (uu___282_1394.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___282_1394.weakly_reduce_scrutinee);
            nbe_step = (uu___282_1394.nbe_step)
          }
      | FStar_TypeChecker_Env.Unmeta  ->
          let uu___283_1395 = fs  in
          {
            beta = (uu___283_1395.beta);
            iota = (uu___283_1395.iota);
            zeta = (uu___283_1395.zeta);
            weak = (uu___283_1395.weak);
            hnf = (uu___283_1395.hnf);
            primops = (uu___283_1395.primops);
            do_not_unfold_pure_lets = (uu___283_1395.do_not_unfold_pure_lets);
            unfold_until = (uu___283_1395.unfold_until);
            unfold_only = (uu___283_1395.unfold_only);
            unfold_fully = (uu___283_1395.unfold_fully);
            unfold_attr = (uu___283_1395.unfold_attr);
            unfold_tac = (uu___283_1395.unfold_tac);
            pure_subterms_within_computations =
              (uu___283_1395.pure_subterms_within_computations);
            simplify = (uu___283_1395.simplify);
            erase_universes = (uu___283_1395.erase_universes);
            allow_unbound_universes = (uu___283_1395.allow_unbound_universes);
            reify_ = (uu___283_1395.reify_);
            compress_uvars = (uu___283_1395.compress_uvars);
            no_full_norm = (uu___283_1395.no_full_norm);
            check_no_uvars = (uu___283_1395.check_no_uvars);
            unmeta = true;
            unascribe = (uu___283_1395.unascribe);
            in_full_norm_request = (uu___283_1395.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___283_1395.weakly_reduce_scrutinee);
            nbe_step = (uu___283_1395.nbe_step)
          }
      | FStar_TypeChecker_Env.Unascribe  ->
          let uu___284_1396 = fs  in
          {
            beta = (uu___284_1396.beta);
            iota = (uu___284_1396.iota);
            zeta = (uu___284_1396.zeta);
            weak = (uu___284_1396.weak);
            hnf = (uu___284_1396.hnf);
            primops = (uu___284_1396.primops);
            do_not_unfold_pure_lets = (uu___284_1396.do_not_unfold_pure_lets);
            unfold_until = (uu___284_1396.unfold_until);
            unfold_only = (uu___284_1396.unfold_only);
            unfold_fully = (uu___284_1396.unfold_fully);
            unfold_attr = (uu___284_1396.unfold_attr);
            unfold_tac = (uu___284_1396.unfold_tac);
            pure_subterms_within_computations =
              (uu___284_1396.pure_subterms_within_computations);
            simplify = (uu___284_1396.simplify);
            erase_universes = (uu___284_1396.erase_universes);
            allow_unbound_universes = (uu___284_1396.allow_unbound_universes);
            reify_ = (uu___284_1396.reify_);
            compress_uvars = (uu___284_1396.compress_uvars);
            no_full_norm = (uu___284_1396.no_full_norm);
            check_no_uvars = (uu___284_1396.check_no_uvars);
            unmeta = (uu___284_1396.unmeta);
            unascribe = true;
            in_full_norm_request = (uu___284_1396.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___284_1396.weakly_reduce_scrutinee);
            nbe_step = (uu___284_1396.nbe_step)
          }
      | FStar_TypeChecker_Env.NBE  ->
          let uu___285_1397 = fs  in
          {
            beta = (uu___285_1397.beta);
            iota = (uu___285_1397.iota);
            zeta = (uu___285_1397.zeta);
            weak = (uu___285_1397.weak);
            hnf = (uu___285_1397.hnf);
            primops = (uu___285_1397.primops);
            do_not_unfold_pure_lets = (uu___285_1397.do_not_unfold_pure_lets);
            unfold_until = (uu___285_1397.unfold_until);
            unfold_only = (uu___285_1397.unfold_only);
            unfold_fully = (uu___285_1397.unfold_fully);
            unfold_attr = (uu___285_1397.unfold_attr);
            unfold_tac = (uu___285_1397.unfold_tac);
            pure_subterms_within_computations =
              (uu___285_1397.pure_subterms_within_computations);
            simplify = (uu___285_1397.simplify);
            erase_universes = (uu___285_1397.erase_universes);
            allow_unbound_universes = (uu___285_1397.allow_unbound_universes);
            reify_ = (uu___285_1397.reify_);
            compress_uvars = (uu___285_1397.compress_uvars);
            no_full_norm = (uu___285_1397.no_full_norm);
            check_no_uvars = (uu___285_1397.check_no_uvars);
            unmeta = (uu___285_1397.unmeta);
            unascribe = (uu___285_1397.unascribe);
            in_full_norm_request = (uu___285_1397.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___285_1397.weakly_reduce_scrutinee);
            nbe_step = true
          }
  
let rec (to_fsteps : FStar_TypeChecker_Env.step Prims.list -> fsteps) =
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
  { psc_range = FStar_Range.dummyRange; psc_subst = (fun uu____1450  -> []) } 
let (psc_range : psc -> FStar_Range.range) = fun psc  -> psc.psc_range 
let (psc_subst : psc -> FStar_Syntax_Syntax.subst_t) =
  fun psc  -> psc.psc_subst () 
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
  
type closure =
  | Clos of
  ((FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
     FStar_Pervasives_Native.tuple2 Prims.list,FStar_Syntax_Syntax.term,
  ((FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
     FStar_Pervasives_Native.tuple2 Prims.list,FStar_Syntax_Syntax.term)
    FStar_Pervasives_Native.tuple2 FStar_Syntax_Syntax.memo,Prims.bool)
  FStar_Pervasives_Native.tuple4 
  | Univ of FStar_Syntax_Syntax.universe 
  | Dummy 
let (uu___is_Clos : closure -> Prims.bool) =
  fun projectee  ->
    match projectee with | Clos _0 -> true | uu____1739 -> false
  
let (__proj__Clos__item___0 :
  closure ->
    ((FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
       FStar_Pervasives_Native.tuple2 Prims.list,FStar_Syntax_Syntax.term,
      ((FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
         FStar_Pervasives_Native.tuple2 Prims.list,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2 FStar_Syntax_Syntax.memo,Prims.bool)
      FStar_Pervasives_Native.tuple4)
  = fun projectee  -> match projectee with | Clos _0 -> _0 
let (uu___is_Univ : closure -> Prims.bool) =
  fun projectee  ->
    match projectee with | Univ _0 -> true | uu____1843 -> false
  
let (__proj__Univ__item___0 : closure -> FStar_Syntax_Syntax.universe) =
  fun projectee  -> match projectee with | Univ _0 -> _0 
let (uu___is_Dummy : closure -> Prims.bool) =
  fun projectee  ->
    match projectee with | Dummy  -> true | uu____1856 -> false
  
type env =
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
    FStar_Pervasives_Native.tuple2 Prims.list
let (dummy :
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
    FStar_Pervasives_Native.tuple2)
  = (FStar_Pervasives_Native.None, Dummy) 
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
  
type cfg =
  {
  steps: fsteps ;
  tcenv: FStar_TypeChecker_Env.env ;
  debug: debug_switches ;
  delta_level: FStar_TypeChecker_Env.delta_level Prims.list ;
  primitive_steps: primitive_step FStar_Util.psmap ;
  strong: Prims.bool ;
  memoize_lazy: Prims.bool ;
  normalize_pure_lets: Prims.bool }
let (__proj__Mkcfg__item__steps : cfg -> fsteps) =
  fun projectee  ->
    match projectee with
    | { steps = __fname__steps; tcenv = __fname__tcenv;
        debug = __fname__debug; delta_level = __fname__delta_level;
        primitive_steps = __fname__primitive_steps; strong = __fname__strong;
        memoize_lazy = __fname__memoize_lazy;
        normalize_pure_lets = __fname__normalize_pure_lets;_} ->
        __fname__steps
  
let (__proj__Mkcfg__item__tcenv : cfg -> FStar_TypeChecker_Env.env) =
  fun projectee  ->
    match projectee with
    | { steps = __fname__steps; tcenv = __fname__tcenv;
        debug = __fname__debug; delta_level = __fname__delta_level;
        primitive_steps = __fname__primitive_steps; strong = __fname__strong;
        memoize_lazy = __fname__memoize_lazy;
        normalize_pure_lets = __fname__normalize_pure_lets;_} ->
        __fname__tcenv
  
let (__proj__Mkcfg__item__debug : cfg -> debug_switches) =
  fun projectee  ->
    match projectee with
    | { steps = __fname__steps; tcenv = __fname__tcenv;
        debug = __fname__debug; delta_level = __fname__delta_level;
        primitive_steps = __fname__primitive_steps; strong = __fname__strong;
        memoize_lazy = __fname__memoize_lazy;
        normalize_pure_lets = __fname__normalize_pure_lets;_} ->
        __fname__debug
  
let (__proj__Mkcfg__item__delta_level :
  cfg -> FStar_TypeChecker_Env.delta_level Prims.list) =
  fun projectee  ->
    match projectee with
    | { steps = __fname__steps; tcenv = __fname__tcenv;
        debug = __fname__debug; delta_level = __fname__delta_level;
        primitive_steps = __fname__primitive_steps; strong = __fname__strong;
        memoize_lazy = __fname__memoize_lazy;
        normalize_pure_lets = __fname__normalize_pure_lets;_} ->
        __fname__delta_level
  
let (__proj__Mkcfg__item__primitive_steps :
  cfg -> primitive_step FStar_Util.psmap) =
  fun projectee  ->
    match projectee with
    | { steps = __fname__steps; tcenv = __fname__tcenv;
        debug = __fname__debug; delta_level = __fname__delta_level;
        primitive_steps = __fname__primitive_steps; strong = __fname__strong;
        memoize_lazy = __fname__memoize_lazy;
        normalize_pure_lets = __fname__normalize_pure_lets;_} ->
        __fname__primitive_steps
  
let (__proj__Mkcfg__item__strong : cfg -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { steps = __fname__steps; tcenv = __fname__tcenv;
        debug = __fname__debug; delta_level = __fname__delta_level;
        primitive_steps = __fname__primitive_steps; strong = __fname__strong;
        memoize_lazy = __fname__memoize_lazy;
        normalize_pure_lets = __fname__normalize_pure_lets;_} ->
        __fname__strong
  
let (__proj__Mkcfg__item__memoize_lazy : cfg -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { steps = __fname__steps; tcenv = __fname__tcenv;
        debug = __fname__debug; delta_level = __fname__delta_level;
        primitive_steps = __fname__primitive_steps; strong = __fname__strong;
        memoize_lazy = __fname__memoize_lazy;
        normalize_pure_lets = __fname__normalize_pure_lets;_} ->
        __fname__memoize_lazy
  
let (__proj__Mkcfg__item__normalize_pure_lets : cfg -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { steps = __fname__steps; tcenv = __fname__tcenv;
        debug = __fname__debug; delta_level = __fname__delta_level;
        primitive_steps = __fname__primitive_steps; strong = __fname__strong;
        memoize_lazy = __fname__memoize_lazy;
        normalize_pure_lets = __fname__normalize_pure_lets;_} ->
        __fname__normalize_pure_lets
  
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
             let uu____2216 = FStar_Ident.text_of_lid p.name  in
             FStar_Util.psmap_add m1 uu____2216 p) l m
  
let (prim_from_list :
  primitive_step Prims.list -> primitive_step FStar_Util.psmap) =
  fun l  ->
    let uu____2230 = FStar_Util.psmap_empty ()  in add_steps uu____2230 l
  
let (find_prim_step :
  cfg ->
    FStar_Syntax_Syntax.fv -> primitive_step FStar_Pervasives_Native.option)
  =
  fun cfg  ->
    fun fv  ->
      let uu____2245 =
        FStar_Ident.text_of_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
         in
      FStar_Util.psmap_try_find cfg.primitive_steps uu____2245
  
let (is_prim_step : cfg -> FStar_Syntax_Syntax.fv -> Prims.bool) =
  fun cfg  ->
    fun fv  ->
      let uu____2256 =
        let uu____2259 =
          FStar_Ident.text_of_lid
            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
           in
        FStar_Util.psmap_try_find cfg.primitive_steps uu____2259  in
      FStar_Util.is_some uu____2256
  
type branches =
  (FStar_Syntax_Syntax.pat,FStar_Syntax_Syntax.term
                             FStar_Pervasives_Native.option,FStar_Syntax_Syntax.term)
    FStar_Pervasives_Native.tuple3 Prims.list
type stack_elt =
  | Arg of (closure,FStar_Syntax_Syntax.aqual,FStar_Range.range)
  FStar_Pervasives_Native.tuple3 
  | UnivArgs of (FStar_Syntax_Syntax.universe Prims.list,FStar_Range.range)
  FStar_Pervasives_Native.tuple2 
  | MemoLazy of (env,FStar_Syntax_Syntax.term) FStar_Pervasives_Native.tuple2
  FStar_Syntax_Syntax.memo 
  | Match of (env,branches,cfg,FStar_Range.range)
  FStar_Pervasives_Native.tuple4 
  | Abs of
  (env,FStar_Syntax_Syntax.binders,env,FStar_Syntax_Syntax.residual_comp
                                         FStar_Pervasives_Native.option,
  FStar_Range.range) FStar_Pervasives_Native.tuple5 
  | App of
  (env,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual,FStar_Range.range)
  FStar_Pervasives_Native.tuple4 
  | Meta of (env,FStar_Syntax_Syntax.metadata,FStar_Range.range)
  FStar_Pervasives_Native.tuple3 
  | Let of
  (env,FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.letbinding,FStar_Range.range)
  FStar_Pervasives_Native.tuple4 
  | Cfg of cfg 
  | Debug of (FStar_Syntax_Syntax.term,FStar_Util.time)
  FStar_Pervasives_Native.tuple2 
let (uu___is_Arg : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Arg _0 -> true | uu____2417 -> false
  
let (__proj__Arg__item___0 :
  stack_elt ->
    (closure,FStar_Syntax_Syntax.aqual,FStar_Range.range)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | Arg _0 -> _0 
let (uu___is_UnivArgs : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnivArgs _0 -> true | uu____2455 -> false
  
let (__proj__UnivArgs__item___0 :
  stack_elt ->
    (FStar_Syntax_Syntax.universe Prims.list,FStar_Range.range)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | UnivArgs _0 -> _0 
let (uu___is_MemoLazy : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | MemoLazy _0 -> true | uu____2493 -> false
  
let (__proj__MemoLazy__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.term) FStar_Pervasives_Native.tuple2
      FStar_Syntax_Syntax.memo)
  = fun projectee  -> match projectee with | MemoLazy _0 -> _0 
let (uu___is_Match : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____2566 -> false
  
let (__proj__Match__item___0 :
  stack_elt ->
    (env,branches,cfg,FStar_Range.range) FStar_Pervasives_Native.tuple4)
  = fun projectee  -> match projectee with | Match _0 -> _0 
let (uu___is_Abs : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Abs _0 -> true | uu____2616 -> false
  
let (__proj__Abs__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.binders,env,FStar_Syntax_Syntax.residual_comp
                                           FStar_Pervasives_Native.option,
      FStar_Range.range) FStar_Pervasives_Native.tuple5)
  = fun projectee  -> match projectee with | Abs _0 -> _0 
let (uu___is_App : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____2674 -> false
  
let (__proj__App__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual,FStar_Range.range)
      FStar_Pervasives_Native.tuple4)
  = fun projectee  -> match projectee with | App _0 -> _0 
let (uu___is_Meta : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Meta _0 -> true | uu____2718 -> false
  
let (__proj__Meta__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.metadata,FStar_Range.range)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | Meta _0 -> _0 
let (uu___is_Let : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Let _0 -> true | uu____2758 -> false
  
let (__proj__Let__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.letbinding,FStar_Range.range)
      FStar_Pervasives_Native.tuple4)
  = fun projectee  -> match projectee with | Let _0 -> _0 
let (uu___is_Cfg : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Cfg _0 -> true | uu____2796 -> false
  
let (__proj__Cfg__item___0 : stack_elt -> cfg) =
  fun projectee  -> match projectee with | Cfg _0 -> _0 
let (uu___is_Debug : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Debug _0 -> true | uu____2814 -> false
  
let (__proj__Debug__item___0 :
  stack_elt ->
    (FStar_Syntax_Syntax.term,FStar_Util.time) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Debug _0 -> _0 
type stack = stack_elt Prims.list
let (head_of : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____2841 = FStar_Syntax_Util.head_and_args' t  in
    match uu____2841 with | (hd1,uu____2855) -> hd1
  
let mk :
  'Auu____2878 .
    'Auu____2878 ->
      FStar_Range.range -> 'Auu____2878 FStar_Syntax_Syntax.syntax
  =
  fun t  -> fun r  -> FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None r 
let set_memo : 'a . cfg -> 'a FStar_Syntax_Syntax.memo -> 'a -> unit =
  fun cfg  ->
    fun r  ->
      fun t  ->
        if cfg.memoize_lazy
        then
          let uu____2941 = FStar_ST.op_Bang r  in
          match uu____2941 with
          | FStar_Pervasives_Native.Some uu____2993 ->
              failwith "Unexpected set_memo: thunk already evaluated"
          | FStar_Pervasives_Native.None  ->
              FStar_ST.op_Colon_Equals r (FStar_Pervasives_Native.Some t)
        else ()
  
let rec (env_to_string :
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
    FStar_Pervasives_Native.tuple2 Prims.list -> Prims.string)
  =
  fun env  ->
    let uu____3069 =
      FStar_List.map
        (fun uu____3083  ->
           match uu____3083 with
           | (bopt,c) ->
               let uu____3096 =
                 match bopt with
                 | FStar_Pervasives_Native.None  -> "."
                 | FStar_Pervasives_Native.Some x ->
                     FStar_Syntax_Print.binder_to_string x
                  in
               let uu____3098 = closure_to_string c  in
               FStar_Util.format2 "(%s, %s)" uu____3096 uu____3098) env
       in
    FStar_All.pipe_right uu____3069 (FStar_String.concat "; ")

and (closure_to_string : closure -> Prims.string) =
  fun uu___241_3101  ->
    match uu___241_3101 with
    | Clos (env,t,uu____3104,uu____3105) ->
        let uu____3150 =
          FStar_All.pipe_right (FStar_List.length env)
            FStar_Util.string_of_int
           in
        let uu____3157 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format2 "(env=%s elts; %s)" uu____3150 uu____3157
    | Univ uu____3158 -> "Univ"
    | Dummy  -> "dummy"

let (stack_elt_to_string : stack_elt -> Prims.string) =
  fun uu___242_3163  ->
    match uu___242_3163 with
    | Arg (c,uu____3165,uu____3166) ->
        let uu____3167 = closure_to_string c  in
        FStar_Util.format1 "Closure %s" uu____3167
    | MemoLazy uu____3168 -> "MemoLazy"
    | Abs (uu____3175,bs,uu____3177,uu____3178,uu____3179) ->
        let uu____3184 =
          FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs)
           in
        FStar_Util.format1 "Abs %s" uu____3184
    | UnivArgs uu____3189 -> "UnivArgs"
    | Match uu____3196 -> "Match"
    | App (uu____3205,t,uu____3207,uu____3208) ->
        let uu____3209 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "App %s" uu____3209
    | Meta (uu____3210,m,uu____3212) -> "Meta"
    | Let uu____3213 -> "Let"
    | Cfg uu____3222 -> "Cfg"
    | Debug (t,uu____3224) ->
        let uu____3225 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "Debug %s" uu____3225
  
let (stack_to_string : stack_elt Prims.list -> Prims.string) =
  fun s  ->
    let uu____3235 = FStar_List.map stack_elt_to_string s  in
    FStar_All.pipe_right uu____3235 (FStar_String.concat "; ")
  
let (log : cfg -> (unit -> unit) -> unit) =
  fun cfg  -> fun f  -> if (cfg.debug).gen then f () else () 
let (log_primops : cfg -> (unit -> unit) -> unit) =
  fun cfg  -> fun f  -> if (cfg.debug).primop then f () else () 
let (log_unfolding : cfg -> (unit -> unit) -> unit) =
  fun cfg  -> fun f  -> if (cfg.debug).unfolding then f () else () 
let (log_nbe : cfg -> (unit -> unit) -> unit) =
  fun cfg  ->
    fun f  ->
      let uu____3303 =
        FStar_All.pipe_left (FStar_TypeChecker_Env.debug cfg.tcenv)
          (FStar_Options.Other "NBE")
         in
      if uu____3303 then f () else ()
  
let is_empty : 'Auu____3309 . 'Auu____3309 Prims.list -> Prims.bool =
  fun uu___243_3316  ->
    match uu___243_3316 with | [] -> true | uu____3319 -> false
  
let (lookup_bvar :
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    FStar_Syntax_Syntax.bv -> closure)
  =
  fun env  ->
    fun x  ->
      try
        let uu____3351 = FStar_List.nth env x.FStar_Syntax_Syntax.index  in
        FStar_Pervasives_Native.snd uu____3351
      with
      | uu____3370 ->
          let uu____3371 =
            let uu____3372 = FStar_Syntax_Print.db_to_string x  in
            let uu____3373 = env_to_string env  in
            FStar_Util.format2 "Failed to find %s\nEnv is %s\n" uu____3372
              uu____3373
             in
          failwith uu____3371
  
let (downgrade_ghost_effect_name :
  FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option) =
  fun l  ->
    let uu____3381 =
      FStar_Ident.lid_equals l FStar_Parser_Const.effect_Ghost_lid  in
    if uu____3381
    then FStar_Pervasives_Native.Some FStar_Parser_Const.effect_Pure_lid
    else
      (let uu____3385 =
         FStar_Ident.lid_equals l FStar_Parser_Const.effect_GTot_lid  in
       if uu____3385
       then FStar_Pervasives_Native.Some FStar_Parser_Const.effect_Tot_lid
       else
         (let uu____3389 =
            FStar_Ident.lid_equals l FStar_Parser_Const.effect_GHOST_lid  in
          if uu____3389
          then
            FStar_Pervasives_Native.Some FStar_Parser_Const.effect_PURE_lid
          else FStar_Pervasives_Native.None))
  
let (norm_universe :
  cfg -> env -> FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe)
  =
  fun cfg  ->
    fun env  ->
      fun u  ->
        let norm_univs us =
          let us1 = FStar_Util.sort_with FStar_Syntax_Util.compare_univs us
             in
          let uu____3423 =
            FStar_List.fold_left
              (fun uu____3449  ->
                 fun u1  ->
                   match uu____3449 with
                   | (cur_kernel,cur_max,out) ->
                       let uu____3474 = FStar_Syntax_Util.univ_kernel u1  in
                       (match uu____3474 with
                        | (k_u,n1) ->
                            let uu____3489 =
                              FStar_Syntax_Util.eq_univs cur_kernel k_u  in
                            if uu____3489
                            then (cur_kernel, u1, out)
                            else (k_u, u1, (cur_max :: out))))
              (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero, [])
              us1
             in
          match uu____3423 with
          | (uu____3507,u1,out) -> FStar_List.rev (u1 :: out)  in
        let rec aux u1 =
          let u2 = FStar_Syntax_Subst.compress_univ u1  in
          match u2 with
          | FStar_Syntax_Syntax.U_bvar x ->
              (try
                 let uu____3535 =
                   let uu____3536 = FStar_List.nth env x  in
                   FStar_Pervasives_Native.snd uu____3536  in
                 match uu____3535 with
                 | Univ u3 ->
                     ((let uu____3555 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug cfg.tcenv)
                           (FStar_Options.Other "univ_norm")
                          in
                       if uu____3555
                       then
                         let uu____3556 =
                           FStar_Syntax_Print.univ_to_string u3  in
                         FStar_Util.print1 "Univ (in norm_universe): %s\n"
                           uu____3556
                       else ());
                      aux u3)
                 | Dummy  -> [u2]
                 | uu____3558 ->
                     failwith "Impossible: universe variable bound to a term"
               with
               | uu____3566 ->
                   if (cfg.steps).allow_unbound_universes
                   then [FStar_Syntax_Syntax.U_unknown]
                   else failwith "Universe variable not found")
          | FStar_Syntax_Syntax.U_unif uu____3572 when
              (cfg.steps).check_no_uvars -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_zero  -> [u2]
          | FStar_Syntax_Syntax.U_unif uu____3581 -> [u2]
          | FStar_Syntax_Syntax.U_name uu____3590 -> [u2]
          | FStar_Syntax_Syntax.U_unknown  -> [u2]
          | FStar_Syntax_Syntax.U_max [] -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_max us ->
              let us1 =
                let uu____3597 = FStar_List.collect aux us  in
                FStar_All.pipe_right uu____3597 norm_univs  in
              (match us1 with
               | u_k::hd1::rest ->
                   let rest1 = hd1 :: rest  in
                   let uu____3614 = FStar_Syntax_Util.univ_kernel u_k  in
                   (match uu____3614 with
                    | (FStar_Syntax_Syntax.U_zero ,n1) ->
                        let uu____3622 =
                          FStar_All.pipe_right rest1
                            (FStar_List.for_all
                               (fun u3  ->
                                  let uu____3630 =
                                    FStar_Syntax_Util.univ_kernel u3  in
                                  match uu____3630 with
                                  | (uu____3635,m) -> n1 <= m))
                           in
                        if uu____3622 then rest1 else us1
                    | uu____3640 -> us1)
               | uu____3645 -> us1)
          | FStar_Syntax_Syntax.U_succ u3 ->
              let uu____3649 = aux u3  in
              FStar_List.map (fun _0_16  -> FStar_Syntax_Syntax.U_succ _0_16)
                uu____3649
           in
        if (cfg.steps).erase_universes
        then FStar_Syntax_Syntax.U_unknown
        else
          (let uu____3653 = aux u  in
           match uu____3653 with
           | [] -> FStar_Syntax_Syntax.U_zero
           | (FStar_Syntax_Syntax.U_zero )::[] -> FStar_Syntax_Syntax.U_zero
           | (FStar_Syntax_Syntax.U_zero )::u1::[] -> u1
           | (FStar_Syntax_Syntax.U_zero )::us ->
               FStar_Syntax_Syntax.U_max us
           | u1::[] -> u1
           | us -> FStar_Syntax_Syntax.U_max us)
  
let rec (inline_closure_env :
  cfg ->
    env ->
      stack_elt Prims.list ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          log cfg
            (fun uu____3801  ->
               let uu____3802 = FStar_Syntax_Print.tag_of_term t  in
               let uu____3803 = env_to_string env  in
               let uu____3804 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print3 "\n>>> %s (env=%s) Closure_as_term %s\n"
                 uu____3802 uu____3803 uu____3804);
          (match env with
           | [] when
               FStar_All.pipe_left Prims.op_Negation
                 (cfg.steps).compress_uvars
               -> rebuild_closure cfg env stack t
           | uu____3813 ->
               (match t.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_delayed uu____3816 ->
                    let uu____3839 = FStar_Syntax_Subst.compress t  in
                    inline_closure_env cfg env stack uu____3839
                | FStar_Syntax_Syntax.Tm_unknown  ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_constant uu____3840 ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_name uu____3841 ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_lazy uu____3842 ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_fvar uu____3843 ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_uvar (uv,s) ->
                    if (cfg.steps).check_no_uvars
                    then
                      let t1 = FStar_Syntax_Subst.compress t  in
                      (match t1.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_uvar uu____3867 ->
                           let uu____3880 =
                             let uu____3881 =
                               FStar_Range.string_of_range
                                 t1.FStar_Syntax_Syntax.pos
                                in
                             let uu____3882 =
                               FStar_Syntax_Print.term_to_string t1  in
                             FStar_Util.format2
                               "(%s): CheckNoUvars: Unexpected unification variable remains: %s"
                               uu____3881 uu____3882
                              in
                           failwith uu____3880
                       | uu____3885 -> inline_closure_env cfg env stack t1)
                    else
                      (let s' =
                         FStar_All.pipe_right (FStar_Pervasives_Native.fst s)
                           (FStar_List.map
                              (fun s1  ->
                                 FStar_All.pipe_right s1
                                   (FStar_List.map
                                      (fun uu___244_3920  ->
                                         match uu___244_3920 with
                                         | FStar_Syntax_Syntax.NT (x,t1) ->
                                             let uu____3927 =
                                               let uu____3934 =
                                                 inline_closure_env cfg env
                                                   [] t1
                                                  in
                                               (x, uu____3934)  in
                                             FStar_Syntax_Syntax.NT
                                               uu____3927
                                         | FStar_Syntax_Syntax.NM (x,i) ->
                                             let x_i =
                                               FStar_Syntax_Syntax.bv_to_tm
                                                 (let uu___290_3944 = x  in
                                                  {
                                                    FStar_Syntax_Syntax.ppname
                                                      =
                                                      (uu___290_3944.FStar_Syntax_Syntax.ppname);
                                                    FStar_Syntax_Syntax.index
                                                      = i;
                                                    FStar_Syntax_Syntax.sort
                                                      =
                                                      (uu___290_3944.FStar_Syntax_Syntax.sort)
                                                  })
                                                in
                                             let t1 =
                                               inline_closure_env cfg env []
                                                 x_i
                                                in
                                             (match t1.FStar_Syntax_Syntax.n
                                              with
                                              | FStar_Syntax_Syntax.Tm_bvar
                                                  x_j ->
                                                  FStar_Syntax_Syntax.NM
                                                    (x,
                                                      (x_j.FStar_Syntax_Syntax.index))
                                              | uu____3949 ->
                                                  FStar_Syntax_Syntax.NT
                                                    (x, t1))
                                         | uu____3952 ->
                                             failwith
                                               "Impossible: subst invariant of uvar nodes"))))
                          in
                       let t1 =
                         let uu___291_3956 = t  in
                         {
                           FStar_Syntax_Syntax.n =
                             (FStar_Syntax_Syntax.Tm_uvar
                                (uv, (s', (FStar_Pervasives_Native.snd s))));
                           FStar_Syntax_Syntax.pos =
                             (uu___291_3956.FStar_Syntax_Syntax.pos);
                           FStar_Syntax_Syntax.vars =
                             (uu___291_3956.FStar_Syntax_Syntax.vars)
                         }  in
                       rebuild_closure cfg env stack t1)
                | FStar_Syntax_Syntax.Tm_type u ->
                    let t1 =
                      let uu____3977 =
                        let uu____3978 = norm_universe cfg env u  in
                        FStar_Syntax_Syntax.Tm_type uu____3978  in
                      mk uu____3977 t.FStar_Syntax_Syntax.pos  in
                    rebuild_closure cfg env stack t1
                | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
                    let t1 =
                      let uu____3986 =
                        FStar_List.map (norm_universe cfg env) us  in
                      FStar_Syntax_Syntax.mk_Tm_uinst t' uu____3986  in
                    rebuild_closure cfg env stack t1
                | FStar_Syntax_Syntax.Tm_bvar x ->
                    let uu____3988 = lookup_bvar env x  in
                    (match uu____3988 with
                     | Univ uu____3991 ->
                         failwith
                           "Impossible: term variable is bound to a universe"
                     | Dummy  ->
                         let x1 =
                           let uu___292_3995 = x  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___292_3995.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___292_3995.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort =
                               FStar_Syntax_Syntax.tun
                           }  in
                         let t1 =
                           mk (FStar_Syntax_Syntax.Tm_bvar x1)
                             t.FStar_Syntax_Syntax.pos
                            in
                         rebuild_closure cfg env stack t1
                     | Clos (env1,t0,uu____4001,uu____4002) ->
                         inline_closure_env cfg env1 stack t0)
                | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                    let stack1 =
                      FStar_All.pipe_right stack
                        (FStar_List.fold_right
                           (fun uu____4087  ->
                              fun stack1  ->
                                match uu____4087 with
                                | (a,aq) ->
                                    let uu____4099 =
                                      let uu____4100 =
                                        let uu____4107 =
                                          let uu____4108 =
                                            let uu____4139 =
                                              FStar_Util.mk_ref
                                                FStar_Pervasives_Native.None
                                               in
                                            (env, a, uu____4139, false)  in
                                          Clos uu____4108  in
                                        (uu____4107, aq,
                                          (t.FStar_Syntax_Syntax.pos))
                                         in
                                      Arg uu____4100  in
                                    uu____4099 :: stack1) args)
                       in
                    inline_closure_env cfg env stack1 head1
                | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
                    let env' =
                      FStar_All.pipe_right env
                        (FStar_List.fold_right
                           (fun _b  ->
                              fun env1  ->
                                (FStar_Pervasives_Native.None, Dummy) :: env1)
                           bs)
                       in
                    let stack1 =
                      (Abs (env, bs, env', lopt, (t.FStar_Syntax_Syntax.pos)))
                      :: stack  in
                    inline_closure_env cfg env' stack1 body
                | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                    let uu____4315 = close_binders cfg env bs  in
                    (match uu____4315 with
                     | (bs1,env') ->
                         let c1 = close_comp cfg env' c  in
                         let t1 =
                           mk (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
                             t.FStar_Syntax_Syntax.pos
                            in
                         rebuild_closure cfg env stack t1)
                | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
                    let uu____4362 =
                      let uu____4373 =
                        let uu____4380 = FStar_Syntax_Syntax.mk_binder x  in
                        [uu____4380]  in
                      close_binders cfg env uu____4373  in
                    (match uu____4362 with
                     | (x1,env1) ->
                         let phi1 = non_tail_inline_closure_env cfg env1 phi
                            in
                         let t1 =
                           let uu____4415 =
                             let uu____4416 =
                               let uu____4423 =
                                 let uu____4424 = FStar_List.hd x1  in
                                 FStar_All.pipe_right uu____4424
                                   FStar_Pervasives_Native.fst
                                  in
                               (uu____4423, phi1)  in
                             FStar_Syntax_Syntax.Tm_refine uu____4416  in
                           mk uu____4415 t.FStar_Syntax_Syntax.pos  in
                         rebuild_closure cfg env1 stack t1)
                | FStar_Syntax_Syntax.Tm_ascribed (t1,(annot,tacopt),lopt) ->
                    let annot1 =
                      match annot with
                      | FStar_Util.Inl t2 ->
                          let uu____4515 =
                            non_tail_inline_closure_env cfg env t2  in
                          FStar_Util.Inl uu____4515
                      | FStar_Util.Inr c ->
                          let uu____4529 = close_comp cfg env c  in
                          FStar_Util.Inr uu____4529
                       in
                    let tacopt1 =
                      FStar_Util.map_opt tacopt
                        (non_tail_inline_closure_env cfg env)
                       in
                    let t2 =
                      let uu____4548 =
                        let uu____4549 =
                          let uu____4576 =
                            non_tail_inline_closure_env cfg env t1  in
                          (uu____4576, (annot1, tacopt1), lopt)  in
                        FStar_Syntax_Syntax.Tm_ascribed uu____4549  in
                      mk uu____4548 t.FStar_Syntax_Syntax.pos  in
                    rebuild_closure cfg env stack t2
                | FStar_Syntax_Syntax.Tm_quoted (t',qi) ->
                    let t1 =
                      match qi.FStar_Syntax_Syntax.qkind with
                      | FStar_Syntax_Syntax.Quote_dynamic  ->
                          let uu____4622 =
                            let uu____4623 =
                              let uu____4630 =
                                non_tail_inline_closure_env cfg env t'  in
                              (uu____4630, qi)  in
                            FStar_Syntax_Syntax.Tm_quoted uu____4623  in
                          mk uu____4622 t.FStar_Syntax_Syntax.pos
                      | FStar_Syntax_Syntax.Quote_static  ->
                          let qi1 =
                            FStar_Syntax_Syntax.on_antiquoted
                              (non_tail_inline_closure_env cfg env) qi
                             in
                          mk (FStar_Syntax_Syntax.Tm_quoted (t', qi1))
                            t.FStar_Syntax_Syntax.pos
                       in
                    rebuild_closure cfg env stack t1
                | FStar_Syntax_Syntax.Tm_meta (t',m) ->
                    let stack1 = (Meta (env, m, (t.FStar_Syntax_Syntax.pos)))
                      :: stack  in
                    inline_closure_env cfg env stack1 t'
                | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                    let env0 = env  in
                    let env1 =
                      FStar_List.fold_left
                        (fun env1  -> fun uu____4682  -> dummy :: env1) env
                        lb.FStar_Syntax_Syntax.lbunivs
                       in
                    let typ =
                      non_tail_inline_closure_env cfg env1
                        lb.FStar_Syntax_Syntax.lbtyp
                       in
                    let def =
                      non_tail_inline_closure_env cfg env1
                        lb.FStar_Syntax_Syntax.lbdef
                       in
                    let uu____4703 =
                      let uu____4714 = FStar_Syntax_Syntax.is_top_level [lb]
                         in
                      if uu____4714
                      then ((lb.FStar_Syntax_Syntax.lbname), body)
                      else
                        (let x =
                           FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                         let uu____4733 =
                           non_tail_inline_closure_env cfg (dummy :: env0)
                             body
                            in
                         ((FStar_Util.Inl
                             (let uu___293_4749 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___293_4749.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___293_4749.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = typ
                              })), uu____4733))
                       in
                    (match uu____4703 with
                     | (nm,body1) ->
                         let lb1 =
                           let uu___294_4767 = lb  in
                           {
                             FStar_Syntax_Syntax.lbname = nm;
                             FStar_Syntax_Syntax.lbunivs =
                               (uu___294_4767.FStar_Syntax_Syntax.lbunivs);
                             FStar_Syntax_Syntax.lbtyp = typ;
                             FStar_Syntax_Syntax.lbeff =
                               (uu___294_4767.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = def;
                             FStar_Syntax_Syntax.lbattrs =
                               (uu___294_4767.FStar_Syntax_Syntax.lbattrs);
                             FStar_Syntax_Syntax.lbpos =
                               (uu___294_4767.FStar_Syntax_Syntax.lbpos)
                           }  in
                         let t1 =
                           mk
                             (FStar_Syntax_Syntax.Tm_let
                                ((false, [lb1]), body1))
                             t.FStar_Syntax_Syntax.pos
                            in
                         rebuild_closure cfg env0 stack t1)
                | FStar_Syntax_Syntax.Tm_let ((uu____4781,lbs),body) ->
                    let norm_one_lb env1 lb =
                      let env_univs =
                        FStar_List.fold_right
                          (fun uu____4844  -> fun env2  -> dummy :: env2)
                          lb.FStar_Syntax_Syntax.lbunivs env1
                         in
                      let env2 =
                        let uu____4861 = FStar_Syntax_Syntax.is_top_level lbs
                           in
                        if uu____4861
                        then env_univs
                        else
                          FStar_List.fold_right
                            (fun uu____4873  -> fun env2  -> dummy :: env2)
                            lbs env_univs
                         in
                      let ty =
                        non_tail_inline_closure_env cfg env_univs
                          lb.FStar_Syntax_Syntax.lbtyp
                         in
                      let nm =
                        let uu____4897 = FStar_Syntax_Syntax.is_top_level lbs
                           in
                        if uu____4897
                        then lb.FStar_Syntax_Syntax.lbname
                        else
                          (let x =
                             FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                              in
                           FStar_Util.Inl
                             (let uu___295_4905 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___295_4905.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___295_4905.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = ty
                              }))
                         in
                      let uu___296_4906 = lb  in
                      let uu____4907 =
                        non_tail_inline_closure_env cfg env2
                          lb.FStar_Syntax_Syntax.lbdef
                         in
                      {
                        FStar_Syntax_Syntax.lbname = nm;
                        FStar_Syntax_Syntax.lbunivs =
                          (uu___296_4906.FStar_Syntax_Syntax.lbunivs);
                        FStar_Syntax_Syntax.lbtyp = ty;
                        FStar_Syntax_Syntax.lbeff =
                          (uu___296_4906.FStar_Syntax_Syntax.lbeff);
                        FStar_Syntax_Syntax.lbdef = uu____4907;
                        FStar_Syntax_Syntax.lbattrs =
                          (uu___296_4906.FStar_Syntax_Syntax.lbattrs);
                        FStar_Syntax_Syntax.lbpos =
                          (uu___296_4906.FStar_Syntax_Syntax.lbpos)
                      }  in
                    let lbs1 =
                      FStar_All.pipe_right lbs
                        (FStar_List.map (norm_one_lb env))
                       in
                    let body1 =
                      let body_env =
                        FStar_List.fold_right
                          (fun uu____4939  -> fun env1  -> dummy :: env1)
                          lbs1 env
                         in
                      non_tail_inline_closure_env cfg body_env body  in
                    let t1 =
                      mk (FStar_Syntax_Syntax.Tm_let ((true, lbs1), body1))
                        t.FStar_Syntax_Syntax.pos
                       in
                    rebuild_closure cfg env stack t1
                | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
                    let stack1 =
                      (Match
                         (env, branches, cfg, (t.FStar_Syntax_Syntax.pos)))
                      :: stack  in
                    inline_closure_env cfg env stack1 head1))

and (non_tail_inline_closure_env :
  cfg ->
    env ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  = fun cfg  -> fun env  -> fun t  -> inline_closure_env cfg env [] t

and (rebuild_closure :
  cfg ->
    env ->
      stack_elt Prims.list ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          log cfg
            (fun uu____5028  ->
               let uu____5029 = FStar_Syntax_Print.tag_of_term t  in
               let uu____5030 = env_to_string env  in
               let uu____5031 = stack_to_string stack  in
               let uu____5032 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print4
                 "\n>>> %s (env=%s, stack=%s) Rebuild closure_as_term %s\n"
                 uu____5029 uu____5030 uu____5031 uu____5032);
          (match stack with
           | [] -> t
           | (Arg (Clos (env_arg,tm,uu____5037,uu____5038),aq,r))::stack1 ->
               let stack2 = (App (env, t, aq, r)) :: stack1  in
               inline_closure_env cfg env_arg stack2 tm
           | (App (env1,head1,aq,r))::stack1 ->
               let t1 =
                 FStar_Syntax_Syntax.extend_app head1 (t, aq)
                   FStar_Pervasives_Native.None r
                  in
               rebuild_closure cfg env1 stack1 t1
           | (Abs (env',bs,env'',lopt,r))::stack1 ->
               let uu____5115 = close_binders cfg env' bs  in
               (match uu____5115 with
                | (bs1,uu____5129) ->
                    let lopt1 = close_lcomp_opt cfg env'' lopt  in
                    let uu____5145 =
                      let uu___297_5148 = FStar_Syntax_Util.abs bs1 t lopt1
                         in
                      {
                        FStar_Syntax_Syntax.n =
                          (uu___297_5148.FStar_Syntax_Syntax.n);
                        FStar_Syntax_Syntax.pos = r;
                        FStar_Syntax_Syntax.vars =
                          (uu___297_5148.FStar_Syntax_Syntax.vars)
                      }  in
                    rebuild_closure cfg env stack1 uu____5145)
           | (Match (env1,branches,cfg1,r))::stack1 ->
               let close_one_branch env2 uu____5204 =
                 match uu____5204 with
                 | (pat,w_opt,tm) ->
                     let rec norm_pat env3 p =
                       match p.FStar_Syntax_Syntax.v with
                       | FStar_Syntax_Syntax.Pat_constant uu____5319 ->
                           (p, env3)
                       | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                           let uu____5348 =
                             FStar_All.pipe_right pats
                               (FStar_List.fold_left
                                  (fun uu____5432  ->
                                     fun uu____5433  ->
                                       match (uu____5432, uu____5433) with
                                       | ((pats1,env4),(p1,b)) ->
                                           let uu____5572 = norm_pat env4 p1
                                              in
                                           (match uu____5572 with
                                            | (p2,env5) ->
                                                (((p2, b) :: pats1), env5)))
                                  ([], env3))
                              in
                           (match uu____5348 with
                            | (pats1,env4) ->
                                ((let uu___298_5734 = p  in
                                  {
                                    FStar_Syntax_Syntax.v =
                                      (FStar_Syntax_Syntax.Pat_cons
                                         (fv, (FStar_List.rev pats1)));
                                    FStar_Syntax_Syntax.p =
                                      (uu___298_5734.FStar_Syntax_Syntax.p)
                                  }), env4))
                       | FStar_Syntax_Syntax.Pat_var x ->
                           let x1 =
                             let uu___299_5753 = x  in
                             let uu____5754 =
                               non_tail_inline_closure_env cfg1 env3
                                 x.FStar_Syntax_Syntax.sort
                                in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___299_5753.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___299_5753.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____5754
                             }  in
                           ((let uu___300_5768 = p  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_var x1);
                               FStar_Syntax_Syntax.p =
                                 (uu___300_5768.FStar_Syntax_Syntax.p)
                             }), (dummy :: env3))
                       | FStar_Syntax_Syntax.Pat_wild x ->
                           let x1 =
                             let uu___301_5779 = x  in
                             let uu____5780 =
                               non_tail_inline_closure_env cfg1 env3
                                 x.FStar_Syntax_Syntax.sort
                                in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___301_5779.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___301_5779.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____5780
                             }  in
                           ((let uu___302_5794 = p  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_wild x1);
                               FStar_Syntax_Syntax.p =
                                 (uu___302_5794.FStar_Syntax_Syntax.p)
                             }), (dummy :: env3))
                       | FStar_Syntax_Syntax.Pat_dot_term (x,t1) ->
                           let x1 =
                             let uu___303_5810 = x  in
                             let uu____5811 =
                               non_tail_inline_closure_env cfg1 env3
                                 x.FStar_Syntax_Syntax.sort
                                in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___303_5810.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___303_5810.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____5811
                             }  in
                           let t2 = non_tail_inline_closure_env cfg1 env3 t1
                              in
                           ((let uu___304_5828 = p  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_dot_term (x1, t2));
                               FStar_Syntax_Syntax.p =
                                 (uu___304_5828.FStar_Syntax_Syntax.p)
                             }), env3)
                        in
                     let uu____5833 = norm_pat env2 pat  in
                     (match uu____5833 with
                      | (pat1,env3) ->
                          let w_opt1 =
                            match w_opt with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Pervasives_Native.None
                            | FStar_Pervasives_Native.Some w ->
                                let uu____5902 =
                                  non_tail_inline_closure_env cfg1 env3 w  in
                                FStar_Pervasives_Native.Some uu____5902
                             in
                          let tm1 = non_tail_inline_closure_env cfg1 env3 tm
                             in
                          (pat1, w_opt1, tm1))
                  in
               let t1 =
                 let uu____5921 =
                   let uu____5922 =
                     let uu____5945 =
                       FStar_All.pipe_right branches
                         (FStar_List.map (close_one_branch env1))
                        in
                     (t, uu____5945)  in
                   FStar_Syntax_Syntax.Tm_match uu____5922  in
                 mk uu____5921 t.FStar_Syntax_Syntax.pos  in
               rebuild_closure cfg1 env1 stack1 t1
           | (Meta (env_m,m,r))::stack1 ->
               let m1 =
                 match m with
                 | FStar_Syntax_Syntax.Meta_pattern args ->
                     let uu____6058 =
                       FStar_All.pipe_right args
                         (FStar_List.map
                            (fun args1  ->
                               FStar_All.pipe_right args1
                                 (FStar_List.map
                                    (fun uu____6147  ->
                                       match uu____6147 with
                                       | (a,q) ->
                                           let uu____6166 =
                                             non_tail_inline_closure_env cfg
                                               env_m a
                                              in
                                           (uu____6166, q)))))
                        in
                     FStar_Syntax_Syntax.Meta_pattern uu____6058
                 | FStar_Syntax_Syntax.Meta_monadic (m1,tbody) ->
                     let uu____6177 =
                       let uu____6184 =
                         non_tail_inline_closure_env cfg env_m tbody  in
                       (m1, uu____6184)  in
                     FStar_Syntax_Syntax.Meta_monadic uu____6177
                 | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,tbody) ->
                     let uu____6196 =
                       let uu____6205 =
                         non_tail_inline_closure_env cfg env_m tbody  in
                       (m1, m2, uu____6205)  in
                     FStar_Syntax_Syntax.Meta_monadic_lift uu____6196
                 | uu____6210 -> m  in
               let t1 = mk (FStar_Syntax_Syntax.Tm_meta (t, m1)) r  in
               rebuild_closure cfg env stack1 t1
           | uu____6216 -> failwith "Impossible: unexpected stack element")

and (close_binders :
  cfg ->
    env ->
      (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        ((FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
           FStar_Pervasives_Native.tuple2 Prims.list,env)
          FStar_Pervasives_Native.tuple2)
  =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____6230 =
          FStar_All.pipe_right bs
            (FStar_List.fold_left
               (fun uu____6303  ->
                  fun uu____6304  ->
                    match (uu____6303, uu____6304) with
                    | ((env1,out),(b,imp)) ->
                        let b1 =
                          let uu___305_6422 = b  in
                          let uu____6423 =
                            inline_closure_env cfg env1 []
                              b.FStar_Syntax_Syntax.sort
                             in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___305_6422.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___305_6422.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = uu____6423
                          }  in
                        let env2 = dummy :: env1  in
                        (env2, ((b1, imp) :: out))) (env, []))
           in
        match uu____6230 with | (env1,bs1) -> ((FStar_List.rev bs1), env1)

and (close_comp :
  cfg ->
    env ->
      FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax)
  =
  fun cfg  ->
    fun env  ->
      fun c  ->
        match env with
        | [] when
            FStar_All.pipe_left Prims.op_Negation (cfg.steps).compress_uvars
            -> c
        | uu____6540 ->
            (match c.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Total (t,uopt) ->
                 let uu____6553 = inline_closure_env cfg env [] t  in
                 let uu____6554 =
                   FStar_Option.map (norm_universe cfg env) uopt  in
                 FStar_Syntax_Syntax.mk_Total' uu____6553 uu____6554
             | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                 let uu____6567 = inline_closure_env cfg env [] t  in
                 let uu____6568 =
                   FStar_Option.map (norm_universe cfg env) uopt  in
                 FStar_Syntax_Syntax.mk_GTotal' uu____6567 uu____6568
             | FStar_Syntax_Syntax.Comp c1 ->
                 let rt =
                   inline_closure_env cfg env []
                     c1.FStar_Syntax_Syntax.result_typ
                    in
                 let args =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args
                     (FStar_List.map
                        (fun uu____6612  ->
                           match uu____6612 with
                           | (a,q) ->
                               let uu____6625 =
                                 inline_closure_env cfg env [] a  in
                               (uu____6625, q)))
                    in
                 let flags1 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_List.map
                        (fun uu___245_6640  ->
                           match uu___245_6640 with
                           | FStar_Syntax_Syntax.DECREASES t ->
                               let uu____6644 =
                                 inline_closure_env cfg env [] t  in
                               FStar_Syntax_Syntax.DECREASES uu____6644
                           | f -> f))
                    in
                 let uu____6648 =
                   let uu___306_6649 = c1  in
                   let uu____6650 =
                     FStar_List.map (norm_universe cfg env)
                       c1.FStar_Syntax_Syntax.comp_univs
                      in
                   {
                     FStar_Syntax_Syntax.comp_univs = uu____6650;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___306_6649.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ = rt;
                     FStar_Syntax_Syntax.effect_args = args;
                     FStar_Syntax_Syntax.flags = flags1
                   }  in
                 FStar_Syntax_Syntax.mk_Comp uu____6648)

and (filter_out_lcomp_cflags :
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun flags1  ->
    FStar_All.pipe_right flags1
      (FStar_List.filter
         (fun uu___246_6660  ->
            match uu___246_6660 with
            | FStar_Syntax_Syntax.DECREASES uu____6661 -> false
            | uu____6664 -> true))

and (close_lcomp_opt :
  cfg ->
    env ->
      FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option ->
        FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option)
  =
  fun cfg  ->
    fun env  ->
      fun lopt  ->
        match lopt with
        | FStar_Pervasives_Native.Some rc ->
            let flags1 =
              FStar_All.pipe_right rc.FStar_Syntax_Syntax.residual_flags
                (FStar_List.filter
                   (fun uu___247_6682  ->
                      match uu___247_6682 with
                      | FStar_Syntax_Syntax.DECREASES uu____6683 -> false
                      | uu____6686 -> true))
               in
            let rc1 =
              let uu___307_6688 = rc  in
              let uu____6689 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (inline_closure_env cfg env [])
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___307_6688.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____6689;
                FStar_Syntax_Syntax.residual_flags = flags1
              }  in
            FStar_Pervasives_Native.Some rc1
        | uu____6698 -> lopt

let (closure_as_term :
  cfg -> env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun cfg  -> fun env  -> fun t  -> non_tail_inline_closure_env cfg env t 
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
    let uu____6803 =
      let uu____6812 = FStar_Syntax_Embeddings.e_list e  in
      FStar_Syntax_Embeddings.try_unembed uu____6812  in
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a) uu____6803  in
  let arg_as_bounded_int uu____6838 =
    match uu____6838 with
    | (a,uu____6850) ->
        let uu____6857 =
          let uu____6858 = FStar_Syntax_Subst.compress a  in
          uu____6858.FStar_Syntax_Syntax.n  in
        (match uu____6857 with
         | FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv1;
                FStar_Syntax_Syntax.pos = uu____6868;
                FStar_Syntax_Syntax.vars = uu____6869;_},({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_constant
                                                              (FStar_Const.Const_int
                                                              (i,FStar_Pervasives_Native.None
                                                               ));
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____6871;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____6872;_},uu____6873)::[])
             when
             let uu____6912 =
               FStar_Ident.text_of_lid
                 (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                in
             FStar_Util.ends_with uu____6912 "int_to_t" ->
             let uu____6913 =
               let uu____6918 = FStar_BigInt.big_int_of_string i  in
               (fv1, uu____6918)  in
             FStar_Pervasives_Native.Some uu____6913
         | uu____6923 -> FStar_Pervasives_Native.None)
     in
  let lift_unary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a)::[] ->
        let uu____6971 = f a  in FStar_Pervasives_Native.Some uu____6971
    | uu____6972 -> FStar_Pervasives_Native.None  in
  let lift_binary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a0)::(FStar_Pervasives_Native.Some
        a1)::[] ->
        let uu____7028 = f a0 a1  in FStar_Pervasives_Native.Some uu____7028
    | uu____7029 -> FStar_Pervasives_Native.None  in
  let unary_op as_a f res args =
    let uu____7087 = FStar_List.map as_a args  in
    lift_unary (f res.psc_range) uu____7087  in
  let binary_op as_a f res args =
    let uu____7158 = FStar_List.map as_a args  in
    lift_binary (f res.psc_range) uu____7158  in
  let as_primitive_step is_strong uu____7195 =
    match uu____7195 with
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
           let uu____7255 = f x  in
           FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_int r
             uu____7255)
     in
  let binary_int_op f =
    binary_op arg_as_int
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____7291 = f x y  in
             FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_int r
               uu____7291)
     in
  let unary_bool_op f =
    unary_op arg_as_bool
      (fun r  ->
         fun x  ->
           let uu____7320 = f x  in
           FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_bool r
             uu____7320)
     in
  let binary_bool_op f =
    binary_op arg_as_bool
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____7356 = f x y  in
             FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_bool r
               uu____7356)
     in
  let binary_string_op f =
    binary_op arg_as_string
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____7392 = f x y  in
             FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_string r
               uu____7392)
     in
  let mixed_binary_op as_a as_b embed_c f res args =
    match args with
    | a::b::[] ->
        let uu____7524 =
          let uu____7533 = as_a a  in
          let uu____7536 = as_b b  in (uu____7533, uu____7536)  in
        (match uu____7524 with
         | (FStar_Pervasives_Native.Some a1,FStar_Pervasives_Native.Some b1)
             ->
             let uu____7551 =
               let uu____7552 = f res.psc_range a1 b1  in
               embed_c res.psc_range uu____7552  in
             FStar_Pervasives_Native.Some uu____7551
         | uu____7553 -> FStar_Pervasives_Native.None)
    | uu____7562 -> FStar_Pervasives_Native.None  in
  let list_of_string' rng s =
    let name l =
      let uu____7582 =
        let uu____7583 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
            FStar_Pervasives_Native.None
           in
        FStar_Syntax_Syntax.Tm_fvar uu____7583  in
      mk uu____7582 rng  in
    let char_t = name FStar_Parser_Const.char_lid  in
    let charterm c =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c)) rng  in
    let uu____7597 =
      let uu____7600 = FStar_String.list_of_string s  in
      FStar_List.map charterm uu____7600  in
    FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu____7597  in
  let string_of_list' rng l =
    let s = FStar_String.string_of_list l  in FStar_Syntax_Util.exp_string s
     in
  let string_compare' rng s1 s2 =
    let r = FStar_String.compare s1 s2  in
    let uu____7642 =
      let uu____7643 = FStar_Util.string_of_int r  in
      FStar_BigInt.big_int_of_string uu____7643  in
    FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_int rng
      uu____7642
     in
  let string_concat' psc args =
    match args with
    | a1::a2::[] ->
        let uu____7707 = arg_as_string a1  in
        (match uu____7707 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____7713 = arg_as_list FStar_Syntax_Embeddings.e_string a2
                in
             (match uu____7713 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2  in
                  let uu____7726 =
                    FStar_Syntax_Embeddings.embed
                      FStar_Syntax_Embeddings.e_string psc.psc_range r
                     in
                  FStar_Pervasives_Native.Some uu____7726
              | uu____7727 -> FStar_Pervasives_Native.None)
         | uu____7732 -> FStar_Pervasives_Native.None)
    | uu____7735 -> FStar_Pervasives_Native.None  in
  let string_of_int1 rng i =
    let uu____7755 = FStar_BigInt.string_of_big_int i  in
    FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_string rng
      uu____7755
     in
  let string_of_bool1 rng b =
    FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_string rng
      (if b then "true" else "false")
     in
  let mk_range1 psc args =
    match args with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____7792 =
          let uu____7813 = arg_as_string fn  in
          let uu____7816 = arg_as_int from_line  in
          let uu____7819 = arg_as_int from_col  in
          let uu____7822 = arg_as_int to_line  in
          let uu____7825 = arg_as_int to_col  in
          (uu____7813, uu____7816, uu____7819, uu____7822, uu____7825)  in
        (match uu____7792 with
         | (FStar_Pervasives_Native.Some fn1,FStar_Pervasives_Native.Some
            from_l,FStar_Pervasives_Native.Some
            from_c,FStar_Pervasives_Native.Some
            to_l,FStar_Pervasives_Native.Some to_c) ->
             let r =
               let uu____7856 =
                 let uu____7857 = FStar_BigInt.to_int_fs from_l  in
                 let uu____7858 = FStar_BigInt.to_int_fs from_c  in
                 FStar_Range.mk_pos uu____7857 uu____7858  in
               let uu____7859 =
                 let uu____7860 = FStar_BigInt.to_int_fs to_l  in
                 let uu____7861 = FStar_BigInt.to_int_fs to_c  in
                 FStar_Range.mk_pos uu____7860 uu____7861  in
               FStar_Range.mk_range fn1 uu____7856 uu____7859  in
             let uu____7862 =
               FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_range
                 psc.psc_range r
                in
             FStar_Pervasives_Native.Some uu____7862
         | uu____7863 -> FStar_Pervasives_Native.None)
    | uu____7884 -> FStar_Pervasives_Native.None  in
  let decidable_eq neg psc args =
    let r = psc.psc_range  in
    let tru =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool true)) r
       in
    let fal =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool false)) r
       in
    match args with
    | (_typ,uu____7917)::(a1,uu____7919)::(a2,uu____7921)::[] ->
        let uu____7958 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____7958 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some (if neg then fal else tru)
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some (if neg then tru else fal)
         | uu____7963 -> FStar_Pervasives_Native.None)
    | uu____7964 -> failwith "Unexpected number of arguments"  in
  let prims_to_fstar_range_step psc args =
    match args with
    | (a1,uu____7995)::[] ->
        let uu____8004 =
          FStar_Syntax_Embeddings.try_unembed FStar_Syntax_Embeddings.e_range
            a1
           in
        (match uu____8004 with
         | FStar_Pervasives_Native.Some r ->
             let uu____8010 =
               FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_range
                 psc.psc_range r
                in
             FStar_Pervasives_Native.Some uu____8010
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
    | uu____8011 -> failwith "Unexpected number of arguments"  in
  let basic_ops =
    let uu____8037 =
      let uu____8054 =
        let uu____8071 =
          let uu____8088 =
            let uu____8105 =
              let uu____8122 =
                let uu____8139 =
                  let uu____8156 =
                    let uu____8173 =
                      let uu____8190 =
                        let uu____8207 =
                          let uu____8224 =
                            let uu____8241 =
                              let uu____8258 =
                                let uu____8275 =
                                  let uu____8292 =
                                    let uu____8309 =
                                      let uu____8326 =
                                        let uu____8343 =
                                          let uu____8360 =
                                            let uu____8377 =
                                              let uu____8394 =
                                                let uu____8409 =
                                                  FStar_Parser_Const.p2l
                                                    ["FStar";
                                                    "String";
                                                    "list_of_string"]
                                                   in
                                                (uu____8409,
                                                  (Prims.parse_int "1"),
                                                  (unary_op arg_as_string
                                                     list_of_string'))
                                                 in
                                              let uu____8418 =
                                                let uu____8435 =
                                                  let uu____8450 =
                                                    FStar_Parser_Const.p2l
                                                      ["FStar";
                                                      "String";
                                                      "string_of_list"]
                                                     in
                                                  (uu____8450,
                                                    (Prims.parse_int "1"),
                                                    (unary_op
                                                       (arg_as_list
                                                          FStar_Syntax_Embeddings.e_char)
                                                       string_of_list'))
                                                   in
                                                let uu____8463 =
                                                  let uu____8480 =
                                                    let uu____8495 =
                                                      FStar_Parser_Const.p2l
                                                        ["FStar";
                                                        "String";
                                                        "concat"]
                                                       in
                                                    (uu____8495,
                                                      (Prims.parse_int "2"),
                                                      string_concat')
                                                     in
                                                  let uu____8504 =
                                                    let uu____8521 =
                                                      let uu____8536 =
                                                        FStar_Parser_Const.p2l
                                                          ["Prims";
                                                          "mk_range"]
                                                         in
                                                      (uu____8536,
                                                        (Prims.parse_int "5"),
                                                        mk_range1)
                                                       in
                                                    [uu____8521]  in
                                                  uu____8480 :: uu____8504
                                                   in
                                                uu____8435 :: uu____8463  in
                                              uu____8394 :: uu____8418  in
                                            (FStar_Parser_Const.op_notEq,
                                              (Prims.parse_int "3"),
                                              (decidable_eq true)) ::
                                              uu____8377
                                             in
                                          (FStar_Parser_Const.op_Eq,
                                            (Prims.parse_int "3"),
                                            (decidable_eq false)) ::
                                            uu____8360
                                           in
                                        (FStar_Parser_Const.string_compare,
                                          (Prims.parse_int "2"),
                                          (binary_op arg_as_string
                                             string_compare'))
                                          :: uu____8343
                                         in
                                      (FStar_Parser_Const.string_of_bool_lid,
                                        (Prims.parse_int "1"),
                                        (unary_op arg_as_bool string_of_bool1))
                                        :: uu____8326
                                       in
                                    (FStar_Parser_Const.string_of_int_lid,
                                      (Prims.parse_int "1"),
                                      (unary_op arg_as_int string_of_int1))
                                      :: uu____8309
                                     in
                                  (FStar_Parser_Const.str_make_lid,
                                    (Prims.parse_int "2"),
                                    (mixed_binary_op arg_as_int arg_as_char
                                       (FStar_Syntax_Embeddings.embed
                                          FStar_Syntax_Embeddings.e_string)
                                       (fun r  ->
                                          fun x  ->
                                            fun y  ->
                                              let uu____8756 =
                                                FStar_BigInt.to_int_fs x  in
                                              FStar_String.make uu____8756 y)))
                                    :: uu____8292
                                   in
                                (FStar_Parser_Const.strcat_lid',
                                  (Prims.parse_int "2"),
                                  (binary_string_op
                                     (fun x  -> fun y  -> Prims.strcat x y)))
                                  :: uu____8275
                                 in
                              (FStar_Parser_Const.strcat_lid,
                                (Prims.parse_int "2"),
                                (binary_string_op
                                   (fun x  -> fun y  -> Prims.strcat x y)))
                                :: uu____8258
                               in
                            (FStar_Parser_Const.op_Or, (Prims.parse_int "2"),
                              (binary_bool_op (fun x  -> fun y  -> x || y)))
                              :: uu____8241
                             in
                          (FStar_Parser_Const.op_And, (Prims.parse_int "2"),
                            (binary_bool_op (fun x  -> fun y  -> x && y))) ::
                            uu____8224
                           in
                        (FStar_Parser_Const.op_Negation,
                          (Prims.parse_int "1"),
                          (unary_bool_op (fun x  -> Prims.op_Negation x))) ::
                          uu____8207
                         in
                      (FStar_Parser_Const.op_Modulus, (Prims.parse_int "2"),
                        (binary_int_op
                           (fun x  -> fun y  -> FStar_BigInt.mod_big_int x y)))
                        :: uu____8190
                       in
                    (FStar_Parser_Const.op_GTE, (Prims.parse_int "2"),
                      (binary_op arg_as_int
                         (fun r  ->
                            fun x  ->
                              fun y  ->
                                let uu____8951 = FStar_BigInt.ge_big_int x y
                                   in
                                FStar_Syntax_Embeddings.embed
                                  FStar_Syntax_Embeddings.e_bool r uu____8951)))
                      :: uu____8173
                     in
                  (FStar_Parser_Const.op_GT, (Prims.parse_int "2"),
                    (binary_op arg_as_int
                       (fun r  ->
                          fun x  ->
                            fun y  ->
                              let uu____8981 = FStar_BigInt.gt_big_int x y
                                 in
                              FStar_Syntax_Embeddings.embed
                                FStar_Syntax_Embeddings.e_bool r uu____8981)))
                    :: uu____8156
                   in
                (FStar_Parser_Const.op_LTE, (Prims.parse_int "2"),
                  (binary_op arg_as_int
                     (fun r  ->
                        fun x  ->
                          fun y  ->
                            let uu____9011 = FStar_BigInt.le_big_int x y  in
                            FStar_Syntax_Embeddings.embed
                              FStar_Syntax_Embeddings.e_bool r uu____9011)))
                  :: uu____8139
                 in
              (FStar_Parser_Const.op_LT, (Prims.parse_int "2"),
                (binary_op arg_as_int
                   (fun r  ->
                      fun x  ->
                        fun y  ->
                          let uu____9041 = FStar_BigInt.lt_big_int x y  in
                          FStar_Syntax_Embeddings.embed
                            FStar_Syntax_Embeddings.e_bool r uu____9041)))
                :: uu____8122
               in
            (FStar_Parser_Const.op_Division, (Prims.parse_int "2"),
              (binary_int_op
                 (fun x  -> fun y  -> FStar_BigInt.div_big_int x y)))
              :: uu____8105
             in
          (FStar_Parser_Const.op_Multiply, (Prims.parse_int "2"),
            (binary_int_op
               (fun x  -> fun y  -> FStar_BigInt.mult_big_int x y)))
            :: uu____8088
           in
        (FStar_Parser_Const.op_Subtraction, (Prims.parse_int "2"),
          (binary_int_op (fun x  -> fun y  -> FStar_BigInt.sub_big_int x y)))
          :: uu____8071
         in
      (FStar_Parser_Const.op_Addition, (Prims.parse_int "2"),
        (binary_int_op (fun x  -> fun y  -> FStar_BigInt.add_big_int x y)))
        :: uu____8054
       in
    (FStar_Parser_Const.op_Minus, (Prims.parse_int "1"),
      (unary_int_op (fun x  -> FStar_BigInt.minus_big_int x))) :: uu____8037
     in
  let weak_ops =
    let uu____9196 =
      let uu____9211 =
        FStar_Parser_Const.p2l ["FStar"; "Range"; "prims_to_fstar_range"]  in
      (uu____9211, (Prims.parse_int "1"), prims_to_fstar_range_step)  in
    [uu____9196]  in
  let bounded_arith_ops =
    let bounded_signed_int_types = ["Int8"; "Int16"; "Int32"; "Int64"]  in
    let bounded_unsigned_int_types =
      ["UInt8"; "UInt16"; "UInt32"; "UInt64"; "UInt128"]  in
    let int_as_bounded r int_to_t1 n1 =
      let c =
        FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_int r n1  in
      let int_to_t2 = FStar_Syntax_Syntax.fv_to_tm int_to_t1  in
      let uu____9291 =
        let uu____9296 =
          let uu____9297 = FStar_Syntax_Syntax.as_arg c  in [uu____9297]  in
        FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____9296  in
      uu____9291 FStar_Pervasives_Native.None r  in
    let add_sub_mul_v =
      FStar_All.pipe_right
        (FStar_List.append bounded_signed_int_types
           bounded_unsigned_int_types)
        (FStar_List.collect
           (fun m  ->
              let uu____9371 =
                let uu____9386 = FStar_Parser_Const.p2l ["FStar"; m; "add"]
                   in
                (uu____9386, (Prims.parse_int "2"),
                  (binary_op arg_as_bounded_int
                     (fun r  ->
                        fun uu____9408  ->
                          fun uu____9409  ->
                            match (uu____9408, uu____9409) with
                            | ((int_to_t1,x),(uu____9428,y)) ->
                                let uu____9438 = FStar_BigInt.add_big_int x y
                                   in
                                int_as_bounded r int_to_t1 uu____9438)))
                 in
              let uu____9439 =
                let uu____9456 =
                  let uu____9471 = FStar_Parser_Const.p2l ["FStar"; m; "sub"]
                     in
                  (uu____9471, (Prims.parse_int "2"),
                    (binary_op arg_as_bounded_int
                       (fun r  ->
                          fun uu____9493  ->
                            fun uu____9494  ->
                              match (uu____9493, uu____9494) with
                              | ((int_to_t1,x),(uu____9513,y)) ->
                                  let uu____9523 =
                                    FStar_BigInt.sub_big_int x y  in
                                  int_as_bounded r int_to_t1 uu____9523)))
                   in
                let uu____9524 =
                  let uu____9541 =
                    let uu____9556 =
                      FStar_Parser_Const.p2l ["FStar"; m; "mul"]  in
                    (uu____9556, (Prims.parse_int "2"),
                      (binary_op arg_as_bounded_int
                         (fun r  ->
                            fun uu____9578  ->
                              fun uu____9579  ->
                                match (uu____9578, uu____9579) with
                                | ((int_to_t1,x),(uu____9598,y)) ->
                                    let uu____9608 =
                                      FStar_BigInt.mult_big_int x y  in
                                    int_as_bounded r int_to_t1 uu____9608)))
                     in
                  let uu____9609 =
                    let uu____9626 =
                      let uu____9641 =
                        FStar_Parser_Const.p2l ["FStar"; m; "v"]  in
                      (uu____9641, (Prims.parse_int "1"),
                        (unary_op arg_as_bounded_int
                           (fun r  ->
                              fun uu____9659  ->
                                match uu____9659 with
                                | (int_to_t1,x) ->
                                    FStar_Syntax_Embeddings.embed
                                      FStar_Syntax_Embeddings.e_int r x)))
                       in
                    [uu____9626]  in
                  uu____9541 :: uu____9609  in
                uu____9456 :: uu____9524  in
              uu____9371 :: uu____9439))
       in
    let div_mod_unsigned =
      FStar_All.pipe_right bounded_unsigned_int_types
        (FStar_List.collect
           (fun m  ->
              let uu____9789 =
                let uu____9804 = FStar_Parser_Const.p2l ["FStar"; m; "div"]
                   in
                (uu____9804, (Prims.parse_int "2"),
                  (binary_op arg_as_bounded_int
                     (fun r  ->
                        fun uu____9826  ->
                          fun uu____9827  ->
                            match (uu____9826, uu____9827) with
                            | ((int_to_t1,x),(uu____9846,y)) ->
                                let uu____9856 = FStar_BigInt.div_big_int x y
                                   in
                                int_as_bounded r int_to_t1 uu____9856)))
                 in
              let uu____9857 =
                let uu____9874 =
                  let uu____9889 = FStar_Parser_Const.p2l ["FStar"; m; "rem"]
                     in
                  (uu____9889, (Prims.parse_int "2"),
                    (binary_op arg_as_bounded_int
                       (fun r  ->
                          fun uu____9911  ->
                            fun uu____9912  ->
                              match (uu____9911, uu____9912) with
                              | ((int_to_t1,x),(uu____9931,y)) ->
                                  let uu____9941 =
                                    FStar_BigInt.mod_big_int x y  in
                                  int_as_bounded r int_to_t1 uu____9941)))
                   in
                [uu____9874]  in
              uu____9789 :: uu____9857))
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
    | (_typ,uu____10071)::(a1,uu____10073)::(a2,uu____10075)::[] ->
        let uu____10112 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____10112 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___308_10116 = FStar_Syntax_Util.t_true  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___308_10116.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___308_10116.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___309_10118 = FStar_Syntax_Util.t_false  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___309_10118.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___309_10118.FStar_Syntax_Syntax.vars)
                })
         | uu____10119 -> FStar_Pervasives_Native.None)
    | (_typ,uu____10121)::uu____10122::(a1,uu____10124)::(a2,uu____10126)::[]
        ->
        let uu____10175 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____10175 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___308_10179 = FStar_Syntax_Util.t_true  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___308_10179.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___308_10179.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___309_10181 = FStar_Syntax_Util.t_false  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___309_10181.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___309_10181.FStar_Syntax_Syntax.vars)
                })
         | uu____10182 -> FStar_Pervasives_Native.None)
    | uu____10183 -> failwith "Unexpected number of arguments"  in
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
let (unembed_binder_knot :
  FStar_Syntax_Syntax.binder FStar_Syntax_Embeddings.embedding
    FStar_Pervasives_Native.option FStar_ST.ref)
  = FStar_Util.mk_ref FStar_Pervasives_Native.None 
let (unembed_binder :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____10237 = FStar_ST.op_Bang unembed_binder_knot  in
    match uu____10237 with
    | FStar_Pervasives_Native.Some e -> FStar_Syntax_Embeddings.unembed e t
    | FStar_Pervasives_Native.None  ->
        (FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos
           (FStar_Errors.Warning_UnembedBinderKnot,
             "unembed_binder_knot is unset!");
         FStar_Pervasives_Native.None)
  
let mk_psc_subst :
  'Auu____10289 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____10289) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_Syntax_Syntax.subst_elt Prims.list
  =
  fun cfg  ->
    fun env  ->
      FStar_List.fold_right
        (fun uu____10351  ->
           fun subst1  ->
             match uu____10351 with
             | (binder_opt,closure) ->
                 (match (binder_opt, closure) with
                  | (FStar_Pervasives_Native.Some b,Clos
                     (env1,term,uu____10392,uu____10393)) ->
                      let uu____10452 = b  in
                      (match uu____10452 with
                       | (bv,uu____10460) ->
                           let uu____10461 =
                             let uu____10462 =
                               FStar_Syntax_Util.is_constructed_typ
                                 bv.FStar_Syntax_Syntax.sort
                                 FStar_Parser_Const.binder_lid
                                in
                             Prims.op_Negation uu____10462  in
                           if uu____10461
                           then subst1
                           else
                             (let term1 = closure_as_term cfg env1 term  in
                              let uu____10467 = unembed_binder term1  in
                              match uu____10467 with
                              | FStar_Pervasives_Native.None  -> subst1
                              | FStar_Pervasives_Native.Some x ->
                                  let b1 =
                                    let uu____10474 =
                                      let uu___310_10475 = bv  in
                                      let uu____10476 =
                                        FStar_Syntax_Subst.subst subst1
                                          (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort
                                         in
                                      {
                                        FStar_Syntax_Syntax.ppname =
                                          (uu___310_10475.FStar_Syntax_Syntax.ppname);
                                        FStar_Syntax_Syntax.index =
                                          (uu___310_10475.FStar_Syntax_Syntax.index);
                                        FStar_Syntax_Syntax.sort =
                                          uu____10476
                                      }  in
                                    FStar_Syntax_Syntax.freshen_bv
                                      uu____10474
                                     in
                                  let b_for_x =
                                    let uu____10480 =
                                      let uu____10487 =
                                        FStar_Syntax_Syntax.bv_to_name b1  in
                                      ((FStar_Pervasives_Native.fst x),
                                        uu____10487)
                                       in
                                    FStar_Syntax_Syntax.NT uu____10480  in
                                  let subst2 =
                                    FStar_List.filter
                                      (fun uu___248_10501  ->
                                         match uu___248_10501 with
                                         | FStar_Syntax_Syntax.NT
                                             (uu____10502,{
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_name
                                                              b';
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____10504;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____10505;_})
                                             ->
                                             let uu____10510 =
                                               FStar_Ident.ident_equals
                                                 b1.FStar_Syntax_Syntax.ppname
                                                 b'.FStar_Syntax_Syntax.ppname
                                                in
                                             Prims.op_Negation uu____10510
                                         | uu____10511 -> true) subst1
                                     in
                                  b_for_x :: subst2))
                  | uu____10512 -> subst1)) env []
  
let reduce_primops :
  'Auu____10535 'Auu____10536 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____10535) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____10536 ->
          FStar_Syntax_Syntax.term ->
            FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          if Prims.op_Negation (cfg.steps).primops
          then tm
          else
            (let uu____10584 = FStar_Syntax_Util.head_and_args tm  in
             match uu____10584 with
             | (head1,args) ->
                 let uu____10623 =
                   let uu____10624 = FStar_Syntax_Util.un_uinst head1  in
                   uu____10624.FStar_Syntax_Syntax.n  in
                 (match uu____10623 with
                  | FStar_Syntax_Syntax.Tm_fvar fv ->
                      let uu____10630 = find_prim_step cfg fv  in
                      (match uu____10630 with
                       | FStar_Pervasives_Native.Some prim_step when
                           prim_step.strong_reduction_ok ||
                             (Prims.op_Negation cfg.strong)
                           ->
                           let l = FStar_List.length args  in
                           if l < prim_step.arity
                           then
                             (log_primops cfg
                                (fun uu____10656  ->
                                   let uu____10657 =
                                     FStar_Syntax_Print.lid_to_string
                                       prim_step.name
                                      in
                                   let uu____10658 =
                                     FStar_Util.string_of_int l  in
                                   let uu____10665 =
                                     FStar_Util.string_of_int prim_step.arity
                                      in
                                   FStar_Util.print3
                                     "primop: found partially applied %s (%s/%s args)\n"
                                     uu____10657 uu____10658 uu____10665);
                              tm)
                           else
                             (let uu____10667 =
                                if l = prim_step.arity
                                then (args, [])
                                else FStar_List.splitAt prim_step.arity args
                                 in
                              match uu____10667 with
                              | (args_1,args_2) ->
                                  (log_primops cfg
                                     (fun uu____10780  ->
                                        let uu____10781 =
                                          FStar_Syntax_Print.term_to_string
                                            tm
                                           in
                                        FStar_Util.print1
                                          "primop: trying to reduce <%s>\n"
                                          uu____10781);
                                   (let psc =
                                      {
                                        psc_range =
                                          (head1.FStar_Syntax_Syntax.pos);
                                        psc_subst =
                                          (fun uu____10784  ->
                                             if
                                               prim_step.requires_binder_substitution
                                             then mk_psc_subst cfg env
                                             else [])
                                      }  in
                                    let uu____10786 =
                                      prim_step.interpretation psc args_1  in
                                    match uu____10786 with
                                    | FStar_Pervasives_Native.None  ->
                                        (log_primops cfg
                                           (fun uu____10794  ->
                                              let uu____10795 =
                                                FStar_Syntax_Print.term_to_string
                                                  tm
                                                 in
                                              FStar_Util.print1
                                                "primop: <%s> did not reduce\n"
                                                uu____10795);
                                         tm)
                                    | FStar_Pervasives_Native.Some reduced ->
                                        (log_primops cfg
                                           (fun uu____10801  ->
                                              let uu____10802 =
                                                FStar_Syntax_Print.term_to_string
                                                  tm
                                                 in
                                              let uu____10803 =
                                                FStar_Syntax_Print.term_to_string
                                                  reduced
                                                 in
                                              FStar_Util.print2
                                                "primop: <%s> reduced to <%s>\n"
                                                uu____10802 uu____10803);
                                         FStar_Syntax_Util.mk_app reduced
                                           args_2))))
                       | FStar_Pervasives_Native.Some uu____10804 ->
                           (log_primops cfg
                              (fun uu____10808  ->
                                 let uu____10809 =
                                   FStar_Syntax_Print.term_to_string tm  in
                                 FStar_Util.print1
                                   "primop: not reducing <%s> since we're doing strong reduction\n"
                                   uu____10809);
                            tm)
                       | FStar_Pervasives_Native.None  -> tm)
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_range_of ) when
                      Prims.op_Negation cfg.strong ->
                      (log_primops cfg
                         (fun uu____10813  ->
                            let uu____10814 =
                              FStar_Syntax_Print.term_to_string tm  in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____10814);
                       (match args with
                        | (a1,uu____10818)::[] ->
                            FStar_Syntax_Embeddings.embed
                              FStar_Syntax_Embeddings.e_range
                              tm.FStar_Syntax_Syntax.pos
                              a1.FStar_Syntax_Syntax.pos
                        | uu____10835 -> tm))
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_set_range_of ) when
                      Prims.op_Negation cfg.strong ->
                      (log_primops cfg
                         (fun uu____10847  ->
                            let uu____10848 =
                              FStar_Syntax_Print.term_to_string tm  in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____10848);
                       (match args with
                        | (t,uu____10852)::(r,uu____10854)::[] ->
                            let uu____10881 =
                              FStar_Syntax_Embeddings.try_unembed
                                FStar_Syntax_Embeddings.e_range r
                               in
                            (match uu____10881 with
                             | FStar_Pervasives_Native.Some rng ->
                                 FStar_Syntax_Subst.set_use_range rng t
                             | FStar_Pervasives_Native.None  -> tm)
                        | uu____10887 -> tm))
                  | uu____10896 -> tm))
  
let reduce_equality :
  'Auu____10907 'Auu____10908 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____10907) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____10908 ->
          FStar_Syntax_Syntax.term ->
            FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun cfg  ->
    fun tm  ->
      reduce_primops
        (let uu___311_10954 = cfg  in
         {
           steps =
             (let uu___312_10957 = default_steps  in
              {
                beta = (uu___312_10957.beta);
                iota = (uu___312_10957.iota);
                zeta = (uu___312_10957.zeta);
                weak = (uu___312_10957.weak);
                hnf = (uu___312_10957.hnf);
                primops = true;
                do_not_unfold_pure_lets =
                  (uu___312_10957.do_not_unfold_pure_lets);
                unfold_until = (uu___312_10957.unfold_until);
                unfold_only = (uu___312_10957.unfold_only);
                unfold_fully = (uu___312_10957.unfold_fully);
                unfold_attr = (uu___312_10957.unfold_attr);
                unfold_tac = (uu___312_10957.unfold_tac);
                pure_subterms_within_computations =
                  (uu___312_10957.pure_subterms_within_computations);
                simplify = (uu___312_10957.simplify);
                erase_universes = (uu___312_10957.erase_universes);
                allow_unbound_universes =
                  (uu___312_10957.allow_unbound_universes);
                reify_ = (uu___312_10957.reify_);
                compress_uvars = (uu___312_10957.compress_uvars);
                no_full_norm = (uu___312_10957.no_full_norm);
                check_no_uvars = (uu___312_10957.check_no_uvars);
                unmeta = (uu___312_10957.unmeta);
                unascribe = (uu___312_10957.unascribe);
                in_full_norm_request = (uu___312_10957.in_full_norm_request);
                weakly_reduce_scrutinee =
                  (uu___312_10957.weakly_reduce_scrutinee);
                nbe_step = (uu___312_10957.nbe_step)
              });
           tcenv = (uu___311_10954.tcenv);
           debug = (uu___311_10954.debug);
           delta_level = (uu___311_10954.delta_level);
           primitive_steps = equality_ops;
           strong = (uu___311_10954.strong);
           memoize_lazy = (uu___311_10954.memoize_lazy);
           normalize_pure_lets = (uu___311_10954.normalize_pure_lets)
         }) tm
  
let is_norm_request :
  'Auu____10964 .
    FStar_Syntax_Syntax.term -> 'Auu____10964 Prims.list -> Prims.bool
  =
  fun hd1  ->
    fun args  ->
      let uu____10979 =
        let uu____10986 =
          let uu____10987 = FStar_Syntax_Util.un_uinst hd1  in
          uu____10987.FStar_Syntax_Syntax.n  in
        (uu____10986, args)  in
      match uu____10979 with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____10993::uu____10994::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____10998::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize
      | (FStar_Syntax_Syntax.Tm_fvar fv,steps::uu____11003::uu____11004::[])
          -> FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm
      | uu____11007 -> false
  
let (is_nbe_request : FStar_TypeChecker_Env.step Prims.list -> Prims.bool) =
  fun s  -> FStar_List.mem FStar_TypeChecker_Env.NBE s 
let (tr_norm_step :
  FStar_Syntax_Embeddings.norm_step -> FStar_TypeChecker_Env.step Prims.list)
  =
  fun uu___249_11029  ->
    match uu___249_11029 with
    | FStar_Syntax_Embeddings.Zeta  -> [FStar_TypeChecker_Env.Zeta]
    | FStar_Syntax_Embeddings.Iota  -> [FStar_TypeChecker_Env.Iota]
    | FStar_Syntax_Embeddings.Delta  ->
        [FStar_TypeChecker_Env.UnfoldUntil FStar_Syntax_Syntax.delta_constant]
    | FStar_Syntax_Embeddings.Simpl  -> [FStar_TypeChecker_Env.Simplify]
    | FStar_Syntax_Embeddings.Weak  -> [FStar_TypeChecker_Env.Weak]
    | FStar_Syntax_Embeddings.HNF  -> [FStar_TypeChecker_Env.HNF]
    | FStar_Syntax_Embeddings.Primops  -> [FStar_TypeChecker_Env.Primops]
    | FStar_Syntax_Embeddings.UnfoldOnly names1 ->
        let uu____11035 =
          let uu____11038 =
            let uu____11039 = FStar_List.map FStar_Ident.lid_of_str names1
               in
            FStar_TypeChecker_Env.UnfoldOnly uu____11039  in
          [uu____11038]  in
        (FStar_TypeChecker_Env.UnfoldUntil FStar_Syntax_Syntax.delta_constant)
          :: uu____11035
    | FStar_Syntax_Embeddings.UnfoldFully names1 ->
        let uu____11045 =
          let uu____11048 =
            let uu____11049 = FStar_List.map FStar_Ident.lid_of_str names1
               in
            FStar_TypeChecker_Env.UnfoldFully uu____11049  in
          [uu____11048]  in
        (FStar_TypeChecker_Env.UnfoldUntil FStar_Syntax_Syntax.delta_constant)
          :: uu____11045
    | FStar_Syntax_Embeddings.UnfoldAttr t ->
        [FStar_TypeChecker_Env.UnfoldUntil FStar_Syntax_Syntax.delta_constant;
        FStar_TypeChecker_Env.UnfoldAttr t]
    | FStar_Syntax_Embeddings.NBE  -> [FStar_TypeChecker_Env.NBE]
  
let (tr_norm_steps :
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_TypeChecker_Env.step Prims.list)
  = fun s  -> FStar_List.concatMap tr_norm_step s 
let get_norm_request :
  'Auu____11072 .
    cfg ->
      (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
        (FStar_Syntax_Syntax.term,'Auu____11072)
          FStar_Pervasives_Native.tuple2 Prims.list ->
          (FStar_TypeChecker_Env.step Prims.list,FStar_Syntax_Syntax.term)
            FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun cfg  ->
    fun full_norm  ->
      fun args  ->
        let parse_steps s =
          let uu____11123 =
            let uu____11128 =
              FStar_Syntax_Embeddings.e_list
                FStar_Syntax_Embeddings.e_norm_step
               in
            FStar_Syntax_Embeddings.try_unembed uu____11128 s  in
          match uu____11123 with
          | FStar_Pervasives_Native.Some steps ->
              let uu____11144 = tr_norm_steps steps  in
              FStar_Pervasives_Native.Some uu____11144
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None  in
        let inherited_steps =
          FStar_List.append
            (if (cfg.steps).erase_universes
             then [FStar_TypeChecker_Env.EraseUniverses]
             else [])
            (if (cfg.steps).allow_unbound_universes
             then [FStar_TypeChecker_Env.AllowUnboundUniverses]
             else [])
           in
        match args with
        | uu____11170::(tm,uu____11172)::[] ->
            let s =
              [FStar_TypeChecker_Env.Beta;
              FStar_TypeChecker_Env.Zeta;
              FStar_TypeChecker_Env.Iota;
              FStar_TypeChecker_Env.Primops;
              FStar_TypeChecker_Env.UnfoldUntil
                FStar_Syntax_Syntax.delta_constant;
              FStar_TypeChecker_Env.Reify]  in
            FStar_Pervasives_Native.Some
              ((FStar_List.append inherited_steps s), tm)
        | (tm,uu____11201)::[] ->
            let s =
              [FStar_TypeChecker_Env.Beta;
              FStar_TypeChecker_Env.Zeta;
              FStar_TypeChecker_Env.Iota;
              FStar_TypeChecker_Env.Primops;
              FStar_TypeChecker_Env.UnfoldUntil
                FStar_Syntax_Syntax.delta_constant;
              FStar_TypeChecker_Env.Reify]  in
            FStar_Pervasives_Native.Some
              ((FStar_List.append inherited_steps s), tm)
        | (steps,uu____11222)::uu____11223::(tm,uu____11225)::[] ->
            let add_exclude s z =
              if FStar_List.contains z s
              then s
              else (FStar_TypeChecker_Env.Exclude z) :: s  in
            let uu____11266 =
              let uu____11271 = full_norm steps  in parse_steps uu____11271
               in
            (match uu____11266 with
             | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
             | FStar_Pervasives_Native.Some s ->
                 let s1 = FStar_TypeChecker_Env.Beta :: s  in
                 let s2 = add_exclude s1 FStar_TypeChecker_Env.Zeta  in
                 let s3 = add_exclude s2 FStar_TypeChecker_Env.Iota  in
                 FStar_Pervasives_Native.Some
                   ((FStar_List.append inherited_steps s3), tm))
        | uu____11310 -> FStar_Pervasives_Native.None
  
let (is_reify_head : stack_elt Prims.list -> Prims.bool) =
  fun uu___250_11329  ->
    match uu___250_11329 with
    | (App
        (uu____11332,{
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reify );
                       FStar_Syntax_Syntax.pos = uu____11333;
                       FStar_Syntax_Syntax.vars = uu____11334;_},uu____11335,uu____11336))::uu____11337
        -> true
    | uu____11342 -> false
  
let firstn :
  'Auu____11351 .
    Prims.int ->
      'Auu____11351 Prims.list ->
        ('Auu____11351 Prims.list,'Auu____11351 Prims.list)
          FStar_Pervasives_Native.tuple2
  =
  fun k  ->
    fun l  ->
      if (FStar_List.length l) < k then (l, []) else FStar_Util.first_N k l
  
let (should_reify : cfg -> stack_elt Prims.list -> Prims.bool) =
  fun cfg  ->
    fun stack  ->
      match stack with
      | (App
          (uu____11393,{
                         FStar_Syntax_Syntax.n =
                           FStar_Syntax_Syntax.Tm_constant
                           (FStar_Const.Const_reify );
                         FStar_Syntax_Syntax.pos = uu____11394;
                         FStar_Syntax_Syntax.vars = uu____11395;_},uu____11396,uu____11397))::uu____11398
          -> (cfg.steps).reify_
      | uu____11403 -> false
  
let rec (maybe_weakly_reduced :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun tm  ->
    let aux_comp c =
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.GTotal (t,uu____11426) -> maybe_weakly_reduced t
      | FStar_Syntax_Syntax.Total (t,uu____11436) -> maybe_weakly_reduced t
      | FStar_Syntax_Syntax.Comp ct ->
          (maybe_weakly_reduced ct.FStar_Syntax_Syntax.result_typ) ||
            (FStar_Util.for_some
               (fun uu____11455  ->
                  match uu____11455 with
                  | (a,uu____11463) -> maybe_weakly_reduced a)
               ct.FStar_Syntax_Syntax.effect_args)
       in
    let t = FStar_Syntax_Subst.compress tm  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____11469 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_name uu____11492 -> false
    | FStar_Syntax_Syntax.Tm_uvar uu____11493 -> false
    | FStar_Syntax_Syntax.Tm_type uu____11506 -> false
    | FStar_Syntax_Syntax.Tm_bvar uu____11507 -> false
    | FStar_Syntax_Syntax.Tm_fvar uu____11508 -> false
    | FStar_Syntax_Syntax.Tm_constant uu____11509 -> false
    | FStar_Syntax_Syntax.Tm_lazy uu____11510 -> false
    | FStar_Syntax_Syntax.Tm_unknown  -> false
    | FStar_Syntax_Syntax.Tm_uinst uu____11511 -> false
    | FStar_Syntax_Syntax.Tm_quoted uu____11518 -> false
    | FStar_Syntax_Syntax.Tm_let uu____11525 -> true
    | FStar_Syntax_Syntax.Tm_abs uu____11538 -> true
    | FStar_Syntax_Syntax.Tm_arrow uu____11555 -> true
    | FStar_Syntax_Syntax.Tm_refine uu____11568 -> true
    | FStar_Syntax_Syntax.Tm_match uu____11575 -> true
    | FStar_Syntax_Syntax.Tm_app (t1,args) ->
        (maybe_weakly_reduced t1) ||
          (FStar_All.pipe_right args
             (FStar_Util.for_some
                (fun uu____11637  ->
                   match uu____11637 with
                   | (a,uu____11645) -> maybe_weakly_reduced a)))
    | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,uu____11652) ->
        ((maybe_weakly_reduced t1) ||
           (match FStar_Pervasives_Native.fst asc with
            | FStar_Util.Inl t2 -> maybe_weakly_reduced t2
            | FStar_Util.Inr c2 -> aux_comp c2))
          ||
          ((match FStar_Pervasives_Native.snd asc with
            | FStar_Pervasives_Native.None  -> false
            | FStar_Pervasives_Native.Some tac -> maybe_weakly_reduced tac))
    | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
        (maybe_weakly_reduced t1) ||
          ((match m with
            | FStar_Syntax_Syntax.Meta_pattern args ->
                FStar_Util.for_some
                  (FStar_Util.for_some
                     (fun uu____11774  ->
                        match uu____11774 with
                        | (a,uu____11782) -> maybe_weakly_reduced a)) args
            | FStar_Syntax_Syntax.Meta_monadic_lift
                (uu____11787,uu____11788,t') -> maybe_weakly_reduced t'
            | FStar_Syntax_Syntax.Meta_monadic (uu____11794,t') ->
                maybe_weakly_reduced t'
            | FStar_Syntax_Syntax.Meta_labeled uu____11800 -> false
            | FStar_Syntax_Syntax.Meta_desugared uu____11807 -> false
            | FStar_Syntax_Syntax.Meta_named uu____11808 -> false))
  
type should_unfold_res =
  | Should_unfold_no 
  | Should_unfold_yes 
  | Should_unfold_fully 
  | Should_unfold_reify 
let (uu___is_Should_unfold_no : should_unfold_res -> Prims.bool) =
  fun projectee  ->
    match projectee with | Should_unfold_no  -> true | uu____11814 -> false
  
let (uu___is_Should_unfold_yes : should_unfold_res -> Prims.bool) =
  fun projectee  ->
    match projectee with | Should_unfold_yes  -> true | uu____11820 -> false
  
let (uu___is_Should_unfold_fully : should_unfold_res -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Should_unfold_fully  -> true
    | uu____11826 -> false
  
let (uu___is_Should_unfold_reify : should_unfold_res -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Should_unfold_reify  -> true
    | uu____11832 -> false
  
let (should_unfold :
  cfg ->
    (cfg -> Prims.bool) ->
      FStar_Syntax_Syntax.fv ->
        FStar_TypeChecker_Env.qninfo -> should_unfold_res)
  =
  fun cfg  ->
    fun should_reify1  ->
      fun fv  ->
        fun qninfo  ->
          let attrs =
            let uu____11861 = FStar_TypeChecker_Env.attrs_of_qninfo qninfo
               in
            match uu____11861 with
            | FStar_Pervasives_Native.None  -> []
            | FStar_Pervasives_Native.Some ats -> ats  in
          let yes = (true, false, false)  in
          let no = (false, false, false)  in
          let fully = (true, true, false)  in
          let reif = (true, false, true)  in
          let yesno b = if b then yes else no  in
          let fullyno b = if b then fully else no  in
          let comb_or l =
            FStar_List.fold_right
              (fun uu____11989  ->
                 fun uu____11990  ->
                   match (uu____11989, uu____11990) with
                   | ((a,b,c),(x,y,z)) -> ((a || x), (b || y), (c || z))) l
              (false, false, false)
             in
          let string_of_res uu____12050 =
            match uu____12050 with
            | (x,y,z) ->
                let uu____12060 = FStar_Util.string_of_bool x  in
                let uu____12061 = FStar_Util.string_of_bool y  in
                let uu____12062 = FStar_Util.string_of_bool z  in
                FStar_Util.format3 "(%s,%s,%s)" uu____12060 uu____12061
                  uu____12062
             in
          let res =
            match (qninfo, ((cfg.steps).unfold_only),
                    ((cfg.steps).unfold_fully), ((cfg.steps).unfold_attr))
            with
            | uu____12108 when FStar_TypeChecker_Env.qninfo_is_action qninfo
                ->
                let b = should_reify1 cfg  in
                (log_unfolding cfg
                   (fun uu____12154  ->
                      let uu____12155 = FStar_Syntax_Print.fv_to_string fv
                         in
                      let uu____12156 = FStar_Util.string_of_bool b  in
                      FStar_Util.print2
                        "should_unfold: For DM4F action %s, should_reify = %s\n"
                        uu____12155 uu____12156);
                 if b then reif else no)
            | uu____12164 when
                let uu____12205 = find_prim_step cfg fv  in
                FStar_Option.isSome uu____12205 ->
                (log_unfolding cfg
                   (fun uu____12210  ->
                      FStar_Util.print_string
                        "should_unfold: primitive step, no\n");
                 no)
            | (FStar_Pervasives_Native.Some
               (FStar_Util.Inr
                ({
                   FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
                     ((is_rec,uu____12212),uu____12213);
                   FStar_Syntax_Syntax.sigrng = uu____12214;
                   FStar_Syntax_Syntax.sigquals = qs;
                   FStar_Syntax_Syntax.sigmeta = uu____12216;
                   FStar_Syntax_Syntax.sigattrs = uu____12217;_},uu____12218),uu____12219),uu____12220,uu____12221,uu____12222)
                when
                FStar_List.contains FStar_Syntax_Syntax.HasMaskedEffect qs ->
                (log_unfolding cfg
                   (fun uu____12327  ->
                      FStar_Util.print_string
                        "should_unfold: masked effect, no\n");
                 no)
            | (uu____12328,uu____12329,uu____12330,uu____12331) when
                (cfg.steps).unfold_tac &&
                  (FStar_Util.for_some
                     (FStar_Syntax_Util.attr_eq
                        FStar_Syntax_Util.tac_opaque_attr) attrs)
                ->
                (log_unfolding cfg
                   (fun uu____12398  ->
                      FStar_Util.print_string
                        "should_unfold: masked effect, no\n");
                 no)
            | (FStar_Pervasives_Native.Some
               (FStar_Util.Inr
                ({
                   FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
                     ((is_rec,uu____12400),uu____12401);
                   FStar_Syntax_Syntax.sigrng = uu____12402;
                   FStar_Syntax_Syntax.sigquals = qs;
                   FStar_Syntax_Syntax.sigmeta = uu____12404;
                   FStar_Syntax_Syntax.sigattrs = uu____12405;_},uu____12406),uu____12407),uu____12408,uu____12409,uu____12410)
                when is_rec && (Prims.op_Negation (cfg.steps).zeta) ->
                (log_unfolding cfg
                   (fun uu____12515  ->
                      FStar_Util.print_string
                        "should_unfold: recursive function without zeta, no\n");
                 no)
            | (uu____12516,FStar_Pervasives_Native.Some
               uu____12517,uu____12518,uu____12519) ->
                (log_unfolding cfg
                   (fun uu____12587  ->
                      let uu____12588 = FStar_Syntax_Print.fv_to_string fv
                         in
                      FStar_Util.print1
                        "should_unfold: Reached a %s with selective unfolding\n"
                        uu____12588);
                 (let uu____12589 =
                    let uu____12598 =
                      match (cfg.steps).unfold_only with
                      | FStar_Pervasives_Native.None  -> no
                      | FStar_Pervasives_Native.Some lids ->
                          let uu____12618 =
                            FStar_Util.for_some
                              (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                             in
                          FStar_All.pipe_left yesno uu____12618
                       in
                    let uu____12625 =
                      let uu____12634 =
                        match (cfg.steps).unfold_attr with
                        | FStar_Pervasives_Native.None  -> no
                        | FStar_Pervasives_Native.Some ats ->
                            let uu____12654 =
                              FStar_Util.for_some
                                (fun at  ->
                                   FStar_Util.for_some
                                     (FStar_Syntax_Util.attr_eq at) ats)
                                attrs
                               in
                            FStar_All.pipe_left yesno uu____12654
                         in
                      let uu____12663 =
                        let uu____12672 =
                          match (cfg.steps).unfold_fully with
                          | FStar_Pervasives_Native.None  -> no
                          | FStar_Pervasives_Native.Some lids ->
                              let uu____12692 =
                                FStar_Util.for_some
                                  (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                                 in
                              FStar_All.pipe_left fullyno uu____12692
                           in
                        [uu____12672]  in
                      uu____12634 :: uu____12663  in
                    uu____12598 :: uu____12625  in
                  comb_or uu____12589))
            | (uu____12723,uu____12724,FStar_Pervasives_Native.Some
               uu____12725,uu____12726) ->
                (log_unfolding cfg
                   (fun uu____12794  ->
                      let uu____12795 = FStar_Syntax_Print.fv_to_string fv
                         in
                      FStar_Util.print1
                        "should_unfold: Reached a %s with selective unfolding\n"
                        uu____12795);
                 (let uu____12796 =
                    let uu____12805 =
                      match (cfg.steps).unfold_only with
                      | FStar_Pervasives_Native.None  -> no
                      | FStar_Pervasives_Native.Some lids ->
                          let uu____12825 =
                            FStar_Util.for_some
                              (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                             in
                          FStar_All.pipe_left yesno uu____12825
                       in
                    let uu____12832 =
                      let uu____12841 =
                        match (cfg.steps).unfold_attr with
                        | FStar_Pervasives_Native.None  -> no
                        | FStar_Pervasives_Native.Some ats ->
                            let uu____12861 =
                              FStar_Util.for_some
                                (fun at  ->
                                   FStar_Util.for_some
                                     (FStar_Syntax_Util.attr_eq at) ats)
                                attrs
                               in
                            FStar_All.pipe_left yesno uu____12861
                         in
                      let uu____12870 =
                        let uu____12879 =
                          match (cfg.steps).unfold_fully with
                          | FStar_Pervasives_Native.None  -> no
                          | FStar_Pervasives_Native.Some lids ->
                              let uu____12899 =
                                FStar_Util.for_some
                                  (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                                 in
                              FStar_All.pipe_left fullyno uu____12899
                           in
                        [uu____12879]  in
                      uu____12841 :: uu____12870  in
                    uu____12805 :: uu____12832  in
                  comb_or uu____12796))
            | (uu____12930,uu____12931,uu____12932,FStar_Pervasives_Native.Some
               uu____12933) ->
                (log_unfolding cfg
                   (fun uu____13001  ->
                      let uu____13002 = FStar_Syntax_Print.fv_to_string fv
                         in
                      FStar_Util.print1
                        "should_unfold: Reached a %s with selective unfolding\n"
                        uu____13002);
                 (let uu____13003 =
                    let uu____13012 =
                      match (cfg.steps).unfold_only with
                      | FStar_Pervasives_Native.None  -> no
                      | FStar_Pervasives_Native.Some lids ->
                          let uu____13032 =
                            FStar_Util.for_some
                              (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                             in
                          FStar_All.pipe_left yesno uu____13032
                       in
                    let uu____13039 =
                      let uu____13048 =
                        match (cfg.steps).unfold_attr with
                        | FStar_Pervasives_Native.None  -> no
                        | FStar_Pervasives_Native.Some ats ->
                            let uu____13068 =
                              FStar_Util.for_some
                                (fun at  ->
                                   FStar_Util.for_some
                                     (FStar_Syntax_Util.attr_eq at) ats)
                                attrs
                               in
                            FStar_All.pipe_left yesno uu____13068
                         in
                      let uu____13077 =
                        let uu____13086 =
                          match (cfg.steps).unfold_fully with
                          | FStar_Pervasives_Native.None  -> no
                          | FStar_Pervasives_Native.Some lids ->
                              let uu____13106 =
                                FStar_Util.for_some
                                  (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                                 in
                              FStar_All.pipe_left fullyno uu____13106
                           in
                        [uu____13086]  in
                      uu____13048 :: uu____13077  in
                    uu____13012 :: uu____13039  in
                  comb_or uu____13003))
            | uu____13137 ->
                (log_unfolding cfg
                   (fun uu____13183  ->
                      let uu____13184 = FStar_Syntax_Print.fv_to_string fv
                         in
                      let uu____13185 =
                        FStar_Syntax_Print.delta_depth_to_string
                          fv.FStar_Syntax_Syntax.fv_delta
                         in
                      let uu____13186 =
                        FStar_Common.string_of_list
                          FStar_TypeChecker_Env.string_of_delta_level
                          cfg.delta_level
                         in
                      FStar_Util.print3
                        "should_unfold: Reached a %s with delta_depth = %s\n >> Our delta_level is %s\n"
                        uu____13184 uu____13185 uu____13186);
                 (let uu____13187 =
                    FStar_All.pipe_right cfg.delta_level
                      (FStar_Util.for_some
                         (fun uu___251_13191  ->
                            match uu___251_13191 with
                            | FStar_TypeChecker_Env.UnfoldTacDelta  -> false
                            | FStar_TypeChecker_Env.NoDelta  -> false
                            | FStar_TypeChecker_Env.InliningDelta  -> true
                            | FStar_TypeChecker_Env.Eager_unfolding_only  ->
                                true
                            | FStar_TypeChecker_Env.Unfold l ->
                                FStar_TypeChecker_Common.delta_depth_greater_than
                                  fv.FStar_Syntax_Syntax.fv_delta l))
                     in
                  FStar_All.pipe_left yesno uu____13187))
             in
          log_unfolding cfg
            (fun uu____13204  ->
               let uu____13205 = FStar_Syntax_Print.fv_to_string fv  in
               let uu____13206 =
                 let uu____13207 = FStar_Syntax_Syntax.range_of_fv fv  in
                 FStar_Range.string_of_range uu____13207  in
               let uu____13208 = string_of_res res  in
               FStar_Util.print3
                 "should_unfold: For %s (%s), unfolding res = %s\n"
                 uu____13205 uu____13206 uu____13208);
          (match res with
           | (false ,uu____13209,uu____13210) -> Should_unfold_no
           | (true ,false ,false ) -> Should_unfold_yes
           | (true ,true ,false ) -> Should_unfold_fully
           | (true ,false ,true ) -> Should_unfold_reify
           | uu____13211 ->
               let uu____13218 =
                 let uu____13219 = string_of_res res  in
                 FStar_Util.format1 "Unexpected unfolding result: %s"
                   uu____13219
                  in
               FStar_All.pipe_left failwith uu____13218)
  
let decide_unfolding :
  'Auu____13236 'Auu____13237 .
    cfg ->
      'Auu____13236 ->
        stack_elt Prims.list ->
          'Auu____13237 ->
            FStar_Syntax_Syntax.fv ->
              FStar_TypeChecker_Env.qninfo ->
                (cfg,stack_elt Prims.list) FStar_Pervasives_Native.tuple2
                  FStar_Pervasives_Native.option
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun rng  ->
          fun fv  ->
            fun qninfo  ->
              let res =
                should_unfold cfg (fun cfg1  -> should_reify cfg1 stack) fv
                  qninfo
                 in
              match res with
              | Should_unfold_no  -> FStar_Pervasives_Native.None
              | Should_unfold_yes  ->
                  FStar_Pervasives_Native.Some (cfg, stack)
              | Should_unfold_fully  ->
                  let cfg' =
                    let uu___313_13306 = cfg  in
                    {
                      steps =
                        (let uu___314_13309 = cfg.steps  in
                         {
                           beta = (uu___314_13309.beta);
                           iota = (uu___314_13309.iota);
                           zeta = (uu___314_13309.zeta);
                           weak = (uu___314_13309.weak);
                           hnf = (uu___314_13309.hnf);
                           primops = (uu___314_13309.primops);
                           do_not_unfold_pure_lets =
                             (uu___314_13309.do_not_unfold_pure_lets);
                           unfold_until =
                             (FStar_Pervasives_Native.Some
                                FStar_Syntax_Syntax.delta_constant);
                           unfold_only = FStar_Pervasives_Native.None;
                           unfold_fully = FStar_Pervasives_Native.None;
                           unfold_attr = FStar_Pervasives_Native.None;
                           unfold_tac = (uu___314_13309.unfold_tac);
                           pure_subterms_within_computations =
                             (uu___314_13309.pure_subterms_within_computations);
                           simplify = (uu___314_13309.simplify);
                           erase_universes = (uu___314_13309.erase_universes);
                           allow_unbound_universes =
                             (uu___314_13309.allow_unbound_universes);
                           reify_ = (uu___314_13309.reify_);
                           compress_uvars = (uu___314_13309.compress_uvars);
                           no_full_norm = (uu___314_13309.no_full_norm);
                           check_no_uvars = (uu___314_13309.check_no_uvars);
                           unmeta = (uu___314_13309.unmeta);
                           unascribe = (uu___314_13309.unascribe);
                           in_full_norm_request =
                             (uu___314_13309.in_full_norm_request);
                           weakly_reduce_scrutinee =
                             (uu___314_13309.weakly_reduce_scrutinee);
                           nbe_step = (uu___314_13309.nbe_step)
                         });
                      tcenv = (uu___313_13306.tcenv);
                      debug = (uu___313_13306.debug);
                      delta_level = (uu___313_13306.delta_level);
                      primitive_steps = (uu___313_13306.primitive_steps);
                      strong = (uu___313_13306.strong);
                      memoize_lazy = (uu___313_13306.memoize_lazy);
                      normalize_pure_lets =
                        (uu___313_13306.normalize_pure_lets)
                    }  in
                  let stack' = (Cfg cfg) :: stack  in
                  FStar_Pervasives_Native.Some (cfg', stack')
              | Should_unfold_reify  ->
                  let uu____13327 =
                    let uu____13334 = FStar_List.tl stack  in
                    (cfg, uu____13334)  in
                  FStar_Pervasives_Native.Some uu____13327
  
let rec (norm :
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          let t1 =
            if (cfg.debug).norm_delayed
            then
              (match t.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_delayed uu____13636 ->
                   let uu____13659 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print1 "NORM delayed: %s\n" uu____13659
               | uu____13660 -> ())
            else ();
            FStar_Syntax_Subst.compress t  in
          log cfg
            (fun uu____13668  ->
               let uu____13669 = FStar_Syntax_Print.tag_of_term t1  in
               let uu____13670 = FStar_Syntax_Print.term_to_string t1  in
               let uu____13671 =
                 FStar_Util.string_of_int (FStar_List.length env)  in
               let uu____13678 =
                 let uu____13679 =
                   let uu____13682 = firstn (Prims.parse_int "4") stack  in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____13682
                    in
                 stack_to_string uu____13679  in
               FStar_Util.print4
                 ">>> %s\nNorm %s with with %s env elements top of the stack %s \n"
                 uu____13669 uu____13670 uu____13671 uu____13678);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  ->
               (log_unfolding cfg
                  (fun uu____13708  ->
                     let uu____13709 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____13709);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_constant uu____13710 ->
               (log_unfolding cfg
                  (fun uu____13714  ->
                     let uu____13715 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____13715);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_name uu____13716 ->
               (log_unfolding cfg
                  (fun uu____13720  ->
                     let uu____13721 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____13721);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_lazy uu____13722 ->
               (log_unfolding cfg
                  (fun uu____13726  ->
                     let uu____13727 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____13727);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____13728;
                 FStar_Syntax_Syntax.fv_delta =
                   FStar_Syntax_Syntax.Delta_constant_at_level _0_17;
                 FStar_Syntax_Syntax.fv_qual = uu____13729;_}
               when _0_17 = (Prims.parse_int "0") ->
               (log_unfolding cfg
                  (fun uu____13735  ->
                     let uu____13736 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____13736);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____13737;
                 FStar_Syntax_Syntax.fv_delta = uu____13738;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Data_ctor );_}
               ->
               (log_unfolding cfg
                  (fun uu____13742  ->
                     let uu____13743 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____13743);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____13744;
                 FStar_Syntax_Syntax.fv_delta = uu____13745;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor uu____13746);_}
               ->
               (log_unfolding cfg
                  (fun uu____13756  ->
                     let uu____13757 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____13757);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let qninfo =
                 let uu____13760 = FStar_Syntax_Syntax.lid_of_fv fv  in
                 FStar_TypeChecker_Env.lookup_qname cfg.tcenv uu____13760  in
               let uu____13761 =
                 decide_unfolding cfg env stack t1.FStar_Syntax_Syntax.pos fv
                   qninfo
                  in
               (match uu____13761 with
                | FStar_Pervasives_Native.Some (cfg1,stack1) ->
                    do_unfold_fv cfg1 env stack1 t1 qninfo fv
                | FStar_Pervasives_Native.None  -> rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_quoted uu____13788 ->
               let uu____13795 = closure_as_term cfg env t1  in
               rebuild cfg env stack uu____13795
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               ((Prims.op_Negation (cfg.steps).no_full_norm) &&
                  (is_norm_request hd1 args))
                 &&
                 (let uu____13825 =
                    FStar_Ident.lid_equals
                      (cfg.tcenv).FStar_TypeChecker_Env.curmodule
                      FStar_Parser_Const.prims_lid
                     in
                  Prims.op_Negation uu____13825)
               ->
               (log_nbe cfg
                  (fun uu____13829  ->
                     let uu____13830 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 "Reached norm_request for %s\n"
                       uu____13830);
                (let cfg' =
                   let uu___315_13832 = cfg  in
                   {
                     steps =
                       (let uu___316_13835 = cfg.steps  in
                        {
                          beta = (uu___316_13835.beta);
                          iota = (uu___316_13835.iota);
                          zeta = (uu___316_13835.zeta);
                          weak = (uu___316_13835.weak);
                          hnf = (uu___316_13835.hnf);
                          primops = (uu___316_13835.primops);
                          do_not_unfold_pure_lets = false;
                          unfold_until = (uu___316_13835.unfold_until);
                          unfold_only = FStar_Pervasives_Native.None;
                          unfold_fully = FStar_Pervasives_Native.None;
                          unfold_attr = (uu___316_13835.unfold_attr);
                          unfold_tac = (uu___316_13835.unfold_tac);
                          pure_subterms_within_computations =
                            (uu___316_13835.pure_subterms_within_computations);
                          simplify = (uu___316_13835.simplify);
                          erase_universes = (uu___316_13835.erase_universes);
                          allow_unbound_universes =
                            (uu___316_13835.allow_unbound_universes);
                          reify_ = (uu___316_13835.reify_);
                          compress_uvars = (uu___316_13835.compress_uvars);
                          no_full_norm = (uu___316_13835.no_full_norm);
                          check_no_uvars = (uu___316_13835.check_no_uvars);
                          unmeta = (uu___316_13835.unmeta);
                          unascribe = (uu___316_13835.unascribe);
                          in_full_norm_request =
                            (uu___316_13835.in_full_norm_request);
                          weakly_reduce_scrutinee =
                            (uu___316_13835.weakly_reduce_scrutinee);
                          nbe_step = (uu___316_13835.nbe_step)
                        });
                     tcenv = (uu___315_13832.tcenv);
                     debug = (uu___315_13832.debug);
                     delta_level =
                       [FStar_TypeChecker_Env.Unfold
                          FStar_Syntax_Syntax.delta_constant];
                     primitive_steps = (uu___315_13832.primitive_steps);
                     strong = (uu___315_13832.strong);
                     memoize_lazy = (uu___315_13832.memoize_lazy);
                     normalize_pure_lets = true
                   }  in
                 let uu____13840 =
                   get_norm_request cfg (norm cfg' env []) args  in
                 match uu____13840 with
                 | FStar_Pervasives_Native.None  ->
                     let stack1 =
                       FStar_All.pipe_right stack
                         (FStar_List.fold_right
                            (fun uu____13869  ->
                               fun stack1  ->
                                 match uu____13869 with
                                 | (a,aq) ->
                                     let uu____13881 =
                                       let uu____13882 =
                                         let uu____13889 =
                                           let uu____13890 =
                                             let uu____13921 =
                                               FStar_Util.mk_ref
                                                 FStar_Pervasives_Native.None
                                                in
                                             (env, a, uu____13921, false)  in
                                           Clos uu____13890  in
                                         (uu____13889, aq,
                                           (t1.FStar_Syntax_Syntax.pos))
                                          in
                                       Arg uu____13882  in
                                     uu____13881 :: stack1) args)
                        in
                     (log cfg
                        (fun uu____14009  ->
                           let uu____14010 =
                             FStar_All.pipe_left FStar_Util.string_of_int
                               (FStar_List.length args)
                              in
                           FStar_Util.print1 "\tPushed %s arguments\n"
                             uu____14010);
                      norm cfg env stack1 hd1)
                 | FStar_Pervasives_Native.Some (s,tm) when is_nbe_request s
                     ->
                     let delta_level =
                       let uu____14032 =
                         FStar_All.pipe_right s
                           (FStar_Util.for_some
                              (fun uu___252_14037  ->
                                 match uu___252_14037 with
                                 | FStar_TypeChecker_Env.UnfoldUntil
                                     uu____14038 -> true
                                 | FStar_TypeChecker_Env.UnfoldOnly
                                     uu____14039 -> true
                                 | FStar_TypeChecker_Env.UnfoldFully
                                     uu____14042 -> true
                                 | uu____14045 -> false))
                          in
                       if uu____14032
                       then
                         [FStar_TypeChecker_Env.Unfold
                            FStar_Syntax_Syntax.delta_constant]
                       else [FStar_TypeChecker_Env.NoDelta]  in
                     let tm' = closure_as_term cfg env tm  in
                     (log_nbe cfg
                        (fun uu____14053  ->
                           let uu____14054 =
                             FStar_Syntax_Print.term_to_string tm'  in
                           FStar_Util.print1 "Invoking NBE with  %s\n"
                             uu____14054);
                      (let tm_norm =
                         let uu____14056 =
                           let uu____14071 = cfg_env cfg  in
                           uu____14071.FStar_TypeChecker_Env.nbe  in
                         uu____14056 s cfg.tcenv tm'  in
                       log_nbe cfg
                         (fun uu____14075  ->
                            let uu____14076 =
                              FStar_Syntax_Print.term_to_string tm_norm  in
                            FStar_Util.print1 "Result of NBE is  %s\n"
                              uu____14076);
                       norm cfg env stack tm_norm))
                 | FStar_Pervasives_Native.Some (s,tm) ->
                     let delta_level =
                       let uu____14092 =
                         FStar_All.pipe_right s
                           (FStar_Util.for_some
                              (fun uu___253_14097  ->
                                 match uu___253_14097 with
                                 | FStar_TypeChecker_Env.UnfoldUntil
                                     uu____14098 -> true
                                 | FStar_TypeChecker_Env.UnfoldOnly
                                     uu____14099 -> true
                                 | FStar_TypeChecker_Env.UnfoldFully
                                     uu____14102 -> true
                                 | uu____14105 -> false))
                          in
                       if uu____14092
                       then
                         [FStar_TypeChecker_Env.Unfold
                            FStar_Syntax_Syntax.delta_constant]
                       else [FStar_TypeChecker_Env.NoDelta]  in
                     let cfg'1 =
                       let uu___317_14110 = cfg  in
                       let uu____14111 =
                         let uu___318_14112 = to_fsteps s  in
                         {
                           beta = (uu___318_14112.beta);
                           iota = (uu___318_14112.iota);
                           zeta = (uu___318_14112.zeta);
                           weak = (uu___318_14112.weak);
                           hnf = (uu___318_14112.hnf);
                           primops = (uu___318_14112.primops);
                           do_not_unfold_pure_lets =
                             (uu___318_14112.do_not_unfold_pure_lets);
                           unfold_until = (uu___318_14112.unfold_until);
                           unfold_only = (uu___318_14112.unfold_only);
                           unfold_fully = (uu___318_14112.unfold_fully);
                           unfold_attr = (uu___318_14112.unfold_attr);
                           unfold_tac = (uu___318_14112.unfold_tac);
                           pure_subterms_within_computations =
                             (uu___318_14112.pure_subterms_within_computations);
                           simplify = (uu___318_14112.simplify);
                           erase_universes = (uu___318_14112.erase_universes);
                           allow_unbound_universes =
                             (uu___318_14112.allow_unbound_universes);
                           reify_ = (uu___318_14112.reify_);
                           compress_uvars = (uu___318_14112.compress_uvars);
                           no_full_norm = (uu___318_14112.no_full_norm);
                           check_no_uvars = (uu___318_14112.check_no_uvars);
                           unmeta = (uu___318_14112.unmeta);
                           unascribe = (uu___318_14112.unascribe);
                           in_full_norm_request = true;
                           weakly_reduce_scrutinee =
                             (uu___318_14112.weakly_reduce_scrutinee);
                           nbe_step = (uu___318_14112.nbe_step)
                         }  in
                       {
                         steps = uu____14111;
                         tcenv = (uu___317_14110.tcenv);
                         debug = (uu___317_14110.debug);
                         delta_level;
                         primitive_steps = (uu___317_14110.primitive_steps);
                         strong = (uu___317_14110.strong);
                         memoize_lazy = (uu___317_14110.memoize_lazy);
                         normalize_pure_lets = true
                       }  in
                     let stack' =
                       let tail1 = (Cfg cfg) :: stack  in
                       if (cfg.debug).print_normalized
                       then
                         let uu____14117 =
                           let uu____14118 =
                             let uu____14123 = FStar_Util.now ()  in
                             (t1, uu____14123)  in
                           Debug uu____14118  in
                         uu____14117 :: tail1
                       else tail1  in
                     norm cfg'1 env stack' tm))
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u  in
               let uu____14127 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack uu____14127
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               if (cfg.steps).erase_universes
               then norm cfg env stack t'
               else
                 (let us1 =
                    let uu____14136 =
                      let uu____14143 =
                        FStar_List.map (norm_universe cfg env) us  in
                      (uu____14143, (t1.FStar_Syntax_Syntax.pos))  in
                    UnivArgs uu____14136  in
                  let stack1 = us1 :: stack  in norm cfg env stack1 t')
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____14152 = lookup_bvar env x  in
               (match uu____14152 with
                | Univ uu____14153 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if (Prims.op_Negation fix) || (cfg.steps).zeta
                    then
                      let uu____14202 = FStar_ST.op_Bang r  in
                      (match uu____14202 with
                       | FStar_Pervasives_Native.Some (env2,t') ->
                           (log cfg
                              (fun uu____14324  ->
                                 let uu____14325 =
                                   FStar_Syntax_Print.term_to_string t1  in
                                 let uu____14326 =
                                   FStar_Syntax_Print.term_to_string t'  in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____14325
                                   uu____14326);
                            (let uu____14327 = maybe_weakly_reduced t'  in
                             if uu____14327
                             then
                               match stack with
                               | [] when
                                   (cfg.steps).weak ||
                                     (cfg.steps).compress_uvars
                                   -> rebuild cfg env2 stack t'
                               | uu____14328 -> norm cfg env2 stack t'
                             else rebuild cfg env2 stack t'))
                       | FStar_Pervasives_Native.None  ->
                           norm cfg env1 ((MemoLazy r) :: stack) t0)
                    else norm cfg env1 stack t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack with
                | (UnivArgs uu____14399)::uu____14400 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Arg (c,uu____14410,uu____14411))::stack_rest ->
                    (match c with
                     | Univ uu____14415 ->
                         norm cfg ((FStar_Pervasives_Native.None, c) :: env)
                           stack_rest t1
                     | uu____14424 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | b::[] ->
                              (log cfg
                                 (fun uu____14445  ->
                                    let uu____14446 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____14446);
                               norm cfg
                                 (((FStar_Pervasives_Native.Some b), c) ::
                                 env) stack_rest body)
                          | b::tl1 ->
                              (log cfg
                                 (fun uu____14474  ->
                                    let uu____14475 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____14475);
                               (let body1 =
                                  mk
                                    (FStar_Syntax_Syntax.Tm_abs
                                       (tl1, body, lopt))
                                    t1.FStar_Syntax_Syntax.pos
                                   in
                                norm cfg
                                  (((FStar_Pervasives_Native.Some b), c) ::
                                  env) stack_rest body1))))
                | (Cfg cfg1)::stack1 -> norm cfg1 env stack1 t1
                | (MemoLazy r)::stack1 ->
                    (set_memo cfg r (env, t1);
                     log cfg
                       (fun uu____14541  ->
                          let uu____14542 =
                            FStar_Syntax_Print.term_to_string t1  in
                          FStar_Util.print1 "\tSet memo %s\n" uu____14542);
                     norm cfg env stack1 t1)
                | (Match uu____14543)::uu____14544 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___319_14558 = cfg.steps  in
                             {
                               beta = (uu___319_14558.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___319_14558.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___319_14558.unfold_until);
                               unfold_only = (uu___319_14558.unfold_only);
                               unfold_fully = (uu___319_14558.unfold_fully);
                               unfold_attr = (uu___319_14558.unfold_attr);
                               unfold_tac = (uu___319_14558.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___319_14558.erase_universes);
                               allow_unbound_universes =
                                 (uu___319_14558.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___319_14558.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___319_14558.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___319_14558.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___319_14558.weakly_reduce_scrutinee);
                               nbe_step = (uu___319_14558.nbe_step)
                             }  in
                           let cfg' =
                             let uu___320_14560 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___320_14560.tcenv);
                               debug = (uu___320_14560.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___320_14560.primitive_steps);
                               strong = (uu___320_14560.strong);
                               memoize_lazy = (uu___320_14560.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___320_14560.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____14562 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____14562 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____14594  -> dummy :: env1) env)
                              in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   if (cfg.steps).check_no_uvars
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____14635 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____14635)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___321_14642 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___321_14642.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___321_14642.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____14643 -> lopt  in
                           (log cfg
                              (fun uu____14649  ->
                                 let uu____14650 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____14650);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___322_14659 = cfg  in
                               {
                                 steps = (uu___322_14659.steps);
                                 tcenv = (uu___322_14659.tcenv);
                                 debug = (uu___322_14659.debug);
                                 delta_level = (uu___322_14659.delta_level);
                                 primitive_steps =
                                   (uu___322_14659.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___322_14659.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___322_14659.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Debug uu____14662)::uu____14663 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___319_14673 = cfg.steps  in
                             {
                               beta = (uu___319_14673.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___319_14673.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___319_14673.unfold_until);
                               unfold_only = (uu___319_14673.unfold_only);
                               unfold_fully = (uu___319_14673.unfold_fully);
                               unfold_attr = (uu___319_14673.unfold_attr);
                               unfold_tac = (uu___319_14673.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___319_14673.erase_universes);
                               allow_unbound_universes =
                                 (uu___319_14673.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___319_14673.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___319_14673.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___319_14673.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___319_14673.weakly_reduce_scrutinee);
                               nbe_step = (uu___319_14673.nbe_step)
                             }  in
                           let cfg' =
                             let uu___320_14675 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___320_14675.tcenv);
                               debug = (uu___320_14675.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___320_14675.primitive_steps);
                               strong = (uu___320_14675.strong);
                               memoize_lazy = (uu___320_14675.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___320_14675.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____14677 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____14677 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____14709  -> dummy :: env1) env)
                              in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   if (cfg.steps).check_no_uvars
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____14750 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____14750)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___321_14757 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___321_14757.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___321_14757.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____14758 -> lopt  in
                           (log cfg
                              (fun uu____14764  ->
                                 let uu____14765 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____14765);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___322_14774 = cfg  in
                               {
                                 steps = (uu___322_14774.steps);
                                 tcenv = (uu___322_14774.tcenv);
                                 debug = (uu___322_14774.debug);
                                 delta_level = (uu___322_14774.delta_level);
                                 primitive_steps =
                                   (uu___322_14774.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___322_14774.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___322_14774.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Meta uu____14777)::uu____14778 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___319_14790 = cfg.steps  in
                             {
                               beta = (uu___319_14790.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___319_14790.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___319_14790.unfold_until);
                               unfold_only = (uu___319_14790.unfold_only);
                               unfold_fully = (uu___319_14790.unfold_fully);
                               unfold_attr = (uu___319_14790.unfold_attr);
                               unfold_tac = (uu___319_14790.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___319_14790.erase_universes);
                               allow_unbound_universes =
                                 (uu___319_14790.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___319_14790.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___319_14790.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___319_14790.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___319_14790.weakly_reduce_scrutinee);
                               nbe_step = (uu___319_14790.nbe_step)
                             }  in
                           let cfg' =
                             let uu___320_14792 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___320_14792.tcenv);
                               debug = (uu___320_14792.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___320_14792.primitive_steps);
                               strong = (uu___320_14792.strong);
                               memoize_lazy = (uu___320_14792.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___320_14792.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____14794 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____14794 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____14826  -> dummy :: env1) env)
                              in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   if (cfg.steps).check_no_uvars
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____14867 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____14867)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___321_14874 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___321_14874.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___321_14874.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____14875 -> lopt  in
                           (log cfg
                              (fun uu____14881  ->
                                 let uu____14882 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____14882);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___322_14891 = cfg  in
                               {
                                 steps = (uu___322_14891.steps);
                                 tcenv = (uu___322_14891.tcenv);
                                 debug = (uu___322_14891.debug);
                                 delta_level = (uu___322_14891.delta_level);
                                 primitive_steps =
                                   (uu___322_14891.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___322_14891.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___322_14891.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Let uu____14894)::uu____14895 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___319_14909 = cfg.steps  in
                             {
                               beta = (uu___319_14909.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___319_14909.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___319_14909.unfold_until);
                               unfold_only = (uu___319_14909.unfold_only);
                               unfold_fully = (uu___319_14909.unfold_fully);
                               unfold_attr = (uu___319_14909.unfold_attr);
                               unfold_tac = (uu___319_14909.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___319_14909.erase_universes);
                               allow_unbound_universes =
                                 (uu___319_14909.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___319_14909.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___319_14909.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___319_14909.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___319_14909.weakly_reduce_scrutinee);
                               nbe_step = (uu___319_14909.nbe_step)
                             }  in
                           let cfg' =
                             let uu___320_14911 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___320_14911.tcenv);
                               debug = (uu___320_14911.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___320_14911.primitive_steps);
                               strong = (uu___320_14911.strong);
                               memoize_lazy = (uu___320_14911.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___320_14911.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____14913 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____14913 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____14945  -> dummy :: env1) env)
                              in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   if (cfg.steps).check_no_uvars
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____14986 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____14986)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___321_14993 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___321_14993.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___321_14993.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____14994 -> lopt  in
                           (log cfg
                              (fun uu____15000  ->
                                 let uu____15001 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____15001);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___322_15010 = cfg  in
                               {
                                 steps = (uu___322_15010.steps);
                                 tcenv = (uu___322_15010.tcenv);
                                 debug = (uu___322_15010.debug);
                                 delta_level = (uu___322_15010.delta_level);
                                 primitive_steps =
                                   (uu___322_15010.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___322_15010.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___322_15010.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (App uu____15013)::uu____15014 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___319_15028 = cfg.steps  in
                             {
                               beta = (uu___319_15028.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___319_15028.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___319_15028.unfold_until);
                               unfold_only = (uu___319_15028.unfold_only);
                               unfold_fully = (uu___319_15028.unfold_fully);
                               unfold_attr = (uu___319_15028.unfold_attr);
                               unfold_tac = (uu___319_15028.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___319_15028.erase_universes);
                               allow_unbound_universes =
                                 (uu___319_15028.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___319_15028.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___319_15028.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___319_15028.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___319_15028.weakly_reduce_scrutinee);
                               nbe_step = (uu___319_15028.nbe_step)
                             }  in
                           let cfg' =
                             let uu___320_15030 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___320_15030.tcenv);
                               debug = (uu___320_15030.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___320_15030.primitive_steps);
                               strong = (uu___320_15030.strong);
                               memoize_lazy = (uu___320_15030.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___320_15030.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____15032 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____15032 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____15064  -> dummy :: env1) env)
                              in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   if (cfg.steps).check_no_uvars
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____15105 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____15105)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___321_15112 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___321_15112.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___321_15112.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____15113 -> lopt  in
                           (log cfg
                              (fun uu____15119  ->
                                 let uu____15120 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____15120);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___322_15129 = cfg  in
                               {
                                 steps = (uu___322_15129.steps);
                                 tcenv = (uu___322_15129.tcenv);
                                 debug = (uu___322_15129.debug);
                                 delta_level = (uu___322_15129.delta_level);
                                 primitive_steps =
                                   (uu___322_15129.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___322_15129.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___322_15129.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Abs uu____15132)::uu____15133 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___319_15151 = cfg.steps  in
                             {
                               beta = (uu___319_15151.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___319_15151.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___319_15151.unfold_until);
                               unfold_only = (uu___319_15151.unfold_only);
                               unfold_fully = (uu___319_15151.unfold_fully);
                               unfold_attr = (uu___319_15151.unfold_attr);
                               unfold_tac = (uu___319_15151.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___319_15151.erase_universes);
                               allow_unbound_universes =
                                 (uu___319_15151.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___319_15151.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___319_15151.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___319_15151.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___319_15151.weakly_reduce_scrutinee);
                               nbe_step = (uu___319_15151.nbe_step)
                             }  in
                           let cfg' =
                             let uu___320_15153 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___320_15153.tcenv);
                               debug = (uu___320_15153.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___320_15153.primitive_steps);
                               strong = (uu___320_15153.strong);
                               memoize_lazy = (uu___320_15153.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___320_15153.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____15155 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____15155 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____15187  -> dummy :: env1) env)
                              in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   if (cfg.steps).check_no_uvars
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____15228 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____15228)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___321_15235 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___321_15235.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___321_15235.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____15236 -> lopt  in
                           (log cfg
                              (fun uu____15242  ->
                                 let uu____15243 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____15243);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___322_15252 = cfg  in
                               {
                                 steps = (uu___322_15252.steps);
                                 tcenv = (uu___322_15252.tcenv);
                                 debug = (uu___322_15252.debug);
                                 delta_level = (uu___322_15252.delta_level);
                                 primitive_steps =
                                   (uu___322_15252.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___322_15252.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___322_15252.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | [] ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___319_15258 = cfg.steps  in
                             {
                               beta = (uu___319_15258.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___319_15258.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___319_15258.unfold_until);
                               unfold_only = (uu___319_15258.unfold_only);
                               unfold_fully = (uu___319_15258.unfold_fully);
                               unfold_attr = (uu___319_15258.unfold_attr);
                               unfold_tac = (uu___319_15258.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___319_15258.erase_universes);
                               allow_unbound_universes =
                                 (uu___319_15258.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___319_15258.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___319_15258.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___319_15258.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___319_15258.weakly_reduce_scrutinee);
                               nbe_step = (uu___319_15258.nbe_step)
                             }  in
                           let cfg' =
                             let uu___320_15260 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___320_15260.tcenv);
                               debug = (uu___320_15260.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___320_15260.primitive_steps);
                               strong = (uu___320_15260.strong);
                               memoize_lazy = (uu___320_15260.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___320_15260.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____15262 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____15262 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____15294  -> dummy :: env1) env)
                              in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   if (cfg.steps).check_no_uvars
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____15335 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____15335)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___321_15342 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___321_15342.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___321_15342.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____15343 -> lopt  in
                           (log cfg
                              (fun uu____15349  ->
                                 let uu____15350 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____15350);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___322_15359 = cfg  in
                               {
                                 steps = (uu___322_15359.steps);
                                 tcenv = (uu___322_15359.tcenv);
                                 debug = (uu___322_15359.debug);
                                 delta_level = (uu___322_15359.delta_level);
                                 primitive_steps =
                                   (uu___322_15359.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___322_15359.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___322_15359.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1))))
           | FStar_Syntax_Syntax.Tm_app (head1,args) ->
               let stack1 =
                 FStar_All.pipe_right stack
                   (FStar_List.fold_right
                      (fun uu____15398  ->
                         fun stack1  ->
                           match uu____15398 with
                           | (a,aq) ->
                               let uu____15410 =
                                 let uu____15411 =
                                   let uu____15418 =
                                     let uu____15419 =
                                       let uu____15450 =
                                         FStar_Util.mk_ref
                                           FStar_Pervasives_Native.None
                                          in
                                       (env, a, uu____15450, false)  in
                                     Clos uu____15419  in
                                   (uu____15418, aq,
                                     (t1.FStar_Syntax_Syntax.pos))
                                    in
                                 Arg uu____15411  in
                               uu____15410 :: stack1) args)
                  in
               (log cfg
                  (fun uu____15538  ->
                     let uu____15539 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args)
                        in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____15539);
                norm cfg env stack1 head1)
           | FStar_Syntax_Syntax.Tm_refine (x,f) ->
               if (cfg.steps).weak
               then
                 (match (env, stack) with
                  | ([],[]) ->
                      let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort
                         in
                      let t2 =
                        mk
                          (FStar_Syntax_Syntax.Tm_refine
                             ((let uu___323_15585 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___323_15585.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___323_15585.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos
                         in
                      rebuild cfg env stack t2
                  | uu____15586 ->
                      let uu____15601 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____15601)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort  in
                  let uu____15604 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] f
                     in
                  match uu____15604 with
                  | (closing,f1) ->
                      let f2 = norm cfg (dummy :: env) [] f1  in
                      let t2 =
                        let uu____15629 =
                          let uu____15630 =
                            let uu____15637 =
                              FStar_Syntax_Subst.close closing f2  in
                            ((let uu___324_15643 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___324_15643.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___324_15643.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____15637)
                             in
                          FStar_Syntax_Syntax.Tm_refine uu____15630  in
                        mk uu____15629 t1.FStar_Syntax_Syntax.pos  in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if (cfg.steps).weak
               then
                 let uu____15662 = closure_as_term cfg env t1  in
                 rebuild cfg env stack uu____15662
               else
                 (let uu____15664 = FStar_Syntax_Subst.open_comp bs c  in
                  match uu____15664 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____15672 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun uu____15694  -> dummy :: env1) env)
                           in
                        norm_comp cfg uu____15672 c1  in
                      let t2 =
                        let uu____15716 = norm_binders cfg env bs1  in
                        FStar_Syntax_Util.arrow uu____15716 c2  in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) when
               (cfg.steps).unascribe -> norm cfg env stack t11
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack with
                | (Match uu____15827)::uu____15828 ->
                    (log cfg
                       (fun uu____15841  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (Arg uu____15842)::uu____15843 ->
                    (log cfg
                       (fun uu____15854  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (App
                    (uu____15855,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_constant
                                     (FStar_Const.Const_reify );
                                   FStar_Syntax_Syntax.pos = uu____15856;
                                   FStar_Syntax_Syntax.vars = uu____15857;_},uu____15858,uu____15859))::uu____15860
                    ->
                    (log cfg
                       (fun uu____15867  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (MemoLazy uu____15868)::uu____15869 ->
                    (log cfg
                       (fun uu____15880  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | uu____15881 ->
                    (log cfg
                       (fun uu____15884  ->
                          FStar_Util.print_string "+++ Keeping ascription \n");
                     (let t12 = norm cfg env [] t11  in
                      log cfg
                        (fun uu____15888  ->
                           FStar_Util.print_string
                             "+++ Normalizing ascription \n");
                      (let tc1 =
                         match tc with
                         | FStar_Util.Inl t2 ->
                             let uu____15913 = norm cfg env [] t2  in
                             FStar_Util.Inl uu____15913
                         | FStar_Util.Inr c ->
                             let uu____15927 = norm_comp cfg env c  in
                             FStar_Util.Inr uu____15927
                          in
                       let tacopt1 =
                         FStar_Util.map_opt tacopt (norm cfg env [])  in
                       match stack with
                       | (Cfg cfg1)::stack1 ->
                           let t2 =
                             let uu____15950 =
                               let uu____15951 =
                                 let uu____15978 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____15978, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____15951
                                in
                             mk uu____15950 t1.FStar_Syntax_Syntax.pos  in
                           norm cfg1 env stack1 t2
                       | uu____16013 ->
                           let uu____16014 =
                             let uu____16015 =
                               let uu____16016 =
                                 let uu____16043 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____16043, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____16016
                                in
                             mk uu____16015 t1.FStar_Syntax_Syntax.pos  in
                           rebuild cfg env stack uu____16014))))
           | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
               let stack1 =
                 (Match (env, branches, cfg, (t1.FStar_Syntax_Syntax.pos)))
                 :: stack  in
               if
                 ((cfg.steps).iota && (cfg.steps).weakly_reduce_scrutinee) &&
                   (Prims.op_Negation (cfg.steps).weak)
               then
                 let cfg' =
                   let uu___325_16120 = cfg  in
                   {
                     steps =
                       (let uu___326_16123 = cfg.steps  in
                        {
                          beta = (uu___326_16123.beta);
                          iota = (uu___326_16123.iota);
                          zeta = (uu___326_16123.zeta);
                          weak = true;
                          hnf = (uu___326_16123.hnf);
                          primops = (uu___326_16123.primops);
                          do_not_unfold_pure_lets =
                            (uu___326_16123.do_not_unfold_pure_lets);
                          unfold_until = (uu___326_16123.unfold_until);
                          unfold_only = (uu___326_16123.unfold_only);
                          unfold_fully = (uu___326_16123.unfold_fully);
                          unfold_attr = (uu___326_16123.unfold_attr);
                          unfold_tac = (uu___326_16123.unfold_tac);
                          pure_subterms_within_computations =
                            (uu___326_16123.pure_subterms_within_computations);
                          simplify = (uu___326_16123.simplify);
                          erase_universes = (uu___326_16123.erase_universes);
                          allow_unbound_universes =
                            (uu___326_16123.allow_unbound_universes);
                          reify_ = (uu___326_16123.reify_);
                          compress_uvars = (uu___326_16123.compress_uvars);
                          no_full_norm = (uu___326_16123.no_full_norm);
                          check_no_uvars = (uu___326_16123.check_no_uvars);
                          unmeta = (uu___326_16123.unmeta);
                          unascribe = (uu___326_16123.unascribe);
                          in_full_norm_request =
                            (uu___326_16123.in_full_norm_request);
                          weakly_reduce_scrutinee =
                            (uu___326_16123.weakly_reduce_scrutinee);
                          nbe_step = (uu___326_16123.nbe_step)
                        });
                     tcenv = (uu___325_16120.tcenv);
                     debug = (uu___325_16120.debug);
                     delta_level = (uu___325_16120.delta_level);
                     primitive_steps = (uu___325_16120.primitive_steps);
                     strong = (uu___325_16120.strong);
                     memoize_lazy = (uu___325_16120.memoize_lazy);
                     normalize_pure_lets =
                       (uu___325_16120.normalize_pure_lets)
                   }  in
                 norm cfg' env ((Cfg cfg) :: stack1) head1
               else norm cfg env stack1 head1
           | FStar_Syntax_Syntax.Tm_let ((b,lbs),lbody) when
               (FStar_Syntax_Syntax.is_top_level lbs) &&
                 (cfg.steps).compress_uvars
               ->
               let lbs1 =
                 FStar_All.pipe_right lbs
                   (FStar_List.map
                      (fun lb  ->
                         let uu____16159 =
                           FStar_Syntax_Subst.univ_var_opening
                             lb.FStar_Syntax_Syntax.lbunivs
                            in
                         match uu____16159 with
                         | (openings,lbunivs) ->
                             let cfg1 =
                               let uu___327_16179 = cfg  in
                               let uu____16180 =
                                 FStar_TypeChecker_Env.push_univ_vars
                                   cfg.tcenv lbunivs
                                  in
                               {
                                 steps = (uu___327_16179.steps);
                                 tcenv = uu____16180;
                                 debug = (uu___327_16179.debug);
                                 delta_level = (uu___327_16179.delta_level);
                                 primitive_steps =
                                   (uu___327_16179.primitive_steps);
                                 strong = (uu___327_16179.strong);
                                 memoize_lazy = (uu___327_16179.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___327_16179.normalize_pure_lets)
                               }  in
                             let norm1 t2 =
                               let uu____16187 =
                                 let uu____16188 =
                                   FStar_Syntax_Subst.subst openings t2  in
                                 norm cfg1 env [] uu____16188  in
                               FStar_Syntax_Subst.close_univ_vars lbunivs
                                 uu____16187
                                in
                             let lbtyp = norm1 lb.FStar_Syntax_Syntax.lbtyp
                                in
                             let lbdef = norm1 lb.FStar_Syntax_Syntax.lbdef
                                in
                             let uu___328_16191 = lb  in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___328_16191.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs = lbunivs;
                               FStar_Syntax_Syntax.lbtyp = lbtyp;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___328_16191.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = lbdef;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___328_16191.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___328_16191.FStar_Syntax_Syntax.lbpos)
                             }))
                  in
               let uu____16192 =
                 mk (FStar_Syntax_Syntax.Tm_let ((b, lbs1), lbody))
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack uu____16192
           | FStar_Syntax_Syntax.Tm_let
               ((uu____16203,{
                               FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                 uu____16204;
                               FStar_Syntax_Syntax.lbunivs = uu____16205;
                               FStar_Syntax_Syntax.lbtyp = uu____16206;
                               FStar_Syntax_Syntax.lbeff = uu____16207;
                               FStar_Syntax_Syntax.lbdef = uu____16208;
                               FStar_Syntax_Syntax.lbattrs = uu____16209;
                               FStar_Syntax_Syntax.lbpos = uu____16210;_}::uu____16211),uu____16212)
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff
                  in
               let uu____16252 =
                 (Prims.op_Negation (cfg.steps).do_not_unfold_pure_lets) &&
                   ((((cfg.steps).pure_subterms_within_computations &&
                        (FStar_Syntax_Util.has_attribute
                           lb.FStar_Syntax_Syntax.lbattrs
                           FStar_Parser_Const.inline_let_attr))
                       ||
                       ((FStar_Syntax_Util.is_pure_effect n1) &&
                          (cfg.normalize_pure_lets ||
                             (FStar_Syntax_Util.has_attribute
                                lb.FStar_Syntax_Syntax.lbattrs
                                FStar_Parser_Const.inline_let_attr))))
                      ||
                      ((FStar_Syntax_Util.is_ghost_effect n1) &&
                         (Prims.op_Negation
                            (cfg.steps).pure_subterms_within_computations)))
                  in
               if uu____16252
               then
                 let binder =
                   let uu____16254 =
                     FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                   FStar_Syntax_Syntax.mk_binder uu____16254  in
                 let env1 =
                   let uu____16264 =
                     let uu____16271 =
                       let uu____16272 =
                         let uu____16303 =
                           FStar_Util.mk_ref FStar_Pervasives_Native.None  in
                         (env, (lb.FStar_Syntax_Syntax.lbdef), uu____16303,
                           false)
                          in
                       Clos uu____16272  in
                     ((FStar_Pervasives_Native.Some binder), uu____16271)  in
                   uu____16264 :: env  in
                 (log cfg
                    (fun uu____16398  ->
                       FStar_Util.print_string "+++ Reducing Tm_let\n");
                  norm cfg env1 stack body)
               else
                 if (cfg.steps).weak
                 then
                   (log cfg
                      (fun uu____16402  ->
                         FStar_Util.print_string "+++ Not touching Tm_let\n");
                    (let uu____16403 = closure_as_term cfg env t1  in
                     rebuild cfg env stack uu____16403))
                 else
                   (let uu____16405 =
                      let uu____16410 =
                        let uu____16411 =
                          let uu____16416 =
                            FStar_All.pipe_right
                              lb.FStar_Syntax_Syntax.lbname FStar_Util.left
                             in
                          FStar_All.pipe_right uu____16416
                            FStar_Syntax_Syntax.mk_binder
                           in
                        [uu____16411]  in
                      FStar_Syntax_Subst.open_term uu____16410 body  in
                    match uu____16405 with
                    | (bs,body1) ->
                        (log cfg
                           (fun uu____16437  ->
                              FStar_Util.print_string
                                "+++ Normalizing Tm_let -- type");
                         (let ty =
                            norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                          let lbname =
                            let x =
                              let uu____16445 = FStar_List.hd bs  in
                              FStar_Pervasives_Native.fst uu____16445  in
                            FStar_Util.Inl
                              (let uu___329_16455 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___329_16455.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___329_16455.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               })
                             in
                          log cfg
                            (fun uu____16458  ->
                               FStar_Util.print_string
                                 "+++ Normalizing Tm_let -- definiens\n");
                          (let lb1 =
                             let uu___330_16460 = lb  in
                             let uu____16461 =
                               norm cfg env [] lb.FStar_Syntax_Syntax.lbdef
                                in
                             {
                               FStar_Syntax_Syntax.lbname = lbname;
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___330_16460.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp = ty;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___330_16460.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = uu____16461;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___330_16460.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___330_16460.FStar_Syntax_Syntax.lbpos)
                             }  in
                           let env' =
                             FStar_All.pipe_right bs
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____16486  -> dummy :: env1) env)
                              in
                           let stack1 = (Cfg cfg) :: stack  in
                           let cfg1 =
                             let uu___331_16509 = cfg  in
                             {
                               steps = (uu___331_16509.steps);
                               tcenv = (uu___331_16509.tcenv);
                               debug = (uu___331_16509.debug);
                               delta_level = (uu___331_16509.delta_level);
                               primitive_steps =
                                 (uu___331_16509.primitive_steps);
                               strong = true;
                               memoize_lazy = (uu___331_16509.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___331_16509.normalize_pure_lets)
                             }  in
                           log cfg1
                             (fun uu____16512  ->
                                FStar_Util.print_string
                                  "+++ Normalizing Tm_let -- body\n");
                           norm cfg1 env'
                             ((Let
                                 (env, bs, lb1, (t1.FStar_Syntax_Syntax.pos)))
                             :: stack1) body1))))
           | FStar_Syntax_Syntax.Tm_let ((true ,lbs),body) when
               (cfg.steps).compress_uvars ||
                 ((Prims.op_Negation (cfg.steps).zeta) &&
                    (cfg.steps).pure_subterms_within_computations)
               ->
               let uu____16529 = FStar_Syntax_Subst.open_let_rec lbs body  in
               (match uu____16529 with
                | (lbs1,body1) ->
                    let lbs2 =
                      FStar_List.map
                        (fun lb  ->
                           let ty =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                           let lbname =
                             let uu____16565 =
                               let uu___332_16566 =
                                 FStar_Util.left
                                   lb.FStar_Syntax_Syntax.lbname
                                  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___332_16566.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___332_16566.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               }  in
                             FStar_Util.Inl uu____16565  in
                           let uu____16567 =
                             FStar_Syntax_Util.abs_formals
                               lb.FStar_Syntax_Syntax.lbdef
                              in
                           match uu____16567 with
                           | (xs,def_body,lopt) ->
                               let xs1 = norm_binders cfg env xs  in
                               let env1 =
                                 let uu____16593 =
                                   FStar_List.map (fun uu____16609  -> dummy)
                                     lbs1
                                    in
                                 let uu____16610 =
                                   let uu____16619 =
                                     FStar_List.map
                                       (fun uu____16639  -> dummy) xs1
                                      in
                                   FStar_List.append uu____16619 env  in
                                 FStar_List.append uu____16593 uu____16610
                                  in
                               let def_body1 = norm cfg env1 [] def_body  in
                               let lopt1 =
                                 match lopt with
                                 | FStar_Pervasives_Native.Some rc ->
                                     let uu____16663 =
                                       let uu___333_16664 = rc  in
                                       let uu____16665 =
                                         FStar_Util.map_opt
                                           rc.FStar_Syntax_Syntax.residual_typ
                                           (norm cfg env1 [])
                                          in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___333_16664.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           uu____16665;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___333_16664.FStar_Syntax_Syntax.residual_flags)
                                       }  in
                                     FStar_Pervasives_Native.Some uu____16663
                                 | uu____16674 -> lopt  in
                               let def =
                                 FStar_Syntax_Util.abs xs1 def_body1 lopt1
                                  in
                               let uu___334_16680 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname = lbname;
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___334_16680.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp = ty;
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___334_16680.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___334_16680.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___334_16680.FStar_Syntax_Syntax.lbpos)
                               }) lbs1
                       in
                    let env' =
                      let uu____16690 =
                        FStar_List.map (fun uu____16706  -> dummy) lbs2  in
                      FStar_List.append uu____16690 env  in
                    let body2 = norm cfg env' [] body1  in
                    let uu____16714 =
                      FStar_Syntax_Subst.close_let_rec lbs2 body2  in
                    (match uu____16714 with
                     | (lbs3,body3) ->
                         let t2 =
                           let uu___335_16730 = t1  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_let
                                  ((true, lbs3), body3));
                             FStar_Syntax_Syntax.pos =
                               (uu___335_16730.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___335_16730.FStar_Syntax_Syntax.vars)
                           }  in
                         rebuild cfg env stack t2))
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               Prims.op_Negation (cfg.steps).zeta ->
               let uu____16759 = closure_as_term cfg env t1  in
               rebuild cfg env stack uu____16759
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____16778 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____16854  ->
                        match uu____16854 with
                        | (rec_env,memos,i) ->
                            let bv =
                              let uu___336_16975 =
                                FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                                 in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___336_16975.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index = i;
                                FStar_Syntax_Syntax.sort =
                                  (uu___336_16975.FStar_Syntax_Syntax.sort)
                              }  in
                            let f_i = FStar_Syntax_Syntax.bv_to_tm bv  in
                            let fix_f_i =
                              mk (FStar_Syntax_Syntax.Tm_let (lbs, f_i))
                                t1.FStar_Syntax_Syntax.pos
                               in
                            let memo =
                              FStar_Util.mk_ref FStar_Pervasives_Native.None
                               in
                            let rec_env1 =
                              (FStar_Pervasives_Native.None,
                                (Clos (env, fix_f_i, memo, true)))
                              :: rec_env  in
                            (rec_env1, (memo :: memos),
                              (i + (Prims.parse_int "1"))))
                   (FStar_Pervasives_Native.snd lbs)
                   (env, [], (Prims.parse_int "0"))
                  in
               (match uu____16778 with
                | (rec_env,memos,uu____17202) ->
                    let uu____17255 =
                      FStar_List.map2
                        (fun lb  ->
                           fun memo  ->
                             FStar_ST.op_Colon_Equals memo
                               (FStar_Pervasives_Native.Some
                                  (rec_env, (lb.FStar_Syntax_Syntax.lbdef))))
                        (FStar_Pervasives_Native.snd lbs) memos
                       in
                    let body_env =
                      FStar_List.fold_right
                        (fun lb  ->
                           fun env1  ->
                             let uu____17578 =
                               let uu____17585 =
                                 let uu____17586 =
                                   let uu____17617 =
                                     FStar_Util.mk_ref
                                       FStar_Pervasives_Native.None
                                      in
                                   (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                     uu____17617, false)
                                    in
                                 Clos uu____17586  in
                               (FStar_Pervasives_Native.None, uu____17585)
                                in
                             uu____17578 :: env1)
                        (FStar_Pervasives_Native.snd lbs) env
                       in
                    norm cfg body_env stack body)
           | FStar_Syntax_Syntax.Tm_meta (head1,m) ->
               (log cfg
                  (fun uu____17721  ->
                     let uu____17722 =
                       FStar_Syntax_Print.metadata_to_string m  in
                     FStar_Util.print1 ">> metadata = %s\n" uu____17722);
                (match m with
                 | FStar_Syntax_Syntax.Meta_monadic (m1,t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inl m1) t2
                 | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inr (m1, m')) t2
                 | uu____17744 ->
                     if (cfg.steps).unmeta
                     then norm cfg env stack head1
                     else
                       (match stack with
                        | uu____17746::uu____17747 ->
                            (match m with
                             | FStar_Syntax_Syntax.Meta_labeled
                                 (l,r,uu____17752) ->
                                 norm cfg env ((Meta (env, m, r)) :: stack)
                                   head1
                             | FStar_Syntax_Syntax.Meta_pattern args ->
                                 let args1 = norm_pattern_args cfg env args
                                    in
                                 norm cfg env
                                   ((Meta
                                       (env,
                                         (FStar_Syntax_Syntax.Meta_pattern
                                            args1),
                                         (t1.FStar_Syntax_Syntax.pos))) ::
                                   stack) head1
                             | uu____17775 -> norm cfg env stack head1)
                        | [] ->
                            let head2 = norm cfg env [] head1  in
                            let m1 =
                              match m with
                              | FStar_Syntax_Syntax.Meta_pattern args ->
                                  let uu____17789 =
                                    norm_pattern_args cfg env args  in
                                  FStar_Syntax_Syntax.Meta_pattern
                                    uu____17789
                              | uu____17800 -> m  in
                            let t2 =
                              mk (FStar_Syntax_Syntax.Tm_meta (head2, m1))
                                t1.FStar_Syntax_Syntax.pos
                               in
                            rebuild cfg env stack t2)))
           | FStar_Syntax_Syntax.Tm_delayed uu____17806 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               norm cfg env stack t2
           | FStar_Syntax_Syntax.Tm_uvar uu____17830 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               (match t2.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_uvar uu____17844 ->
                    if (cfg.steps).check_no_uvars
                    then
                      let uu____17857 =
                        let uu____17858 =
                          FStar_Range.string_of_range
                            t2.FStar_Syntax_Syntax.pos
                           in
                        let uu____17859 =
                          FStar_Syntax_Print.term_to_string t2  in
                        FStar_Util.format2
                          "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                          uu____17858 uu____17859
                         in
                      failwith uu____17857
                    else
                      (let uu____17861 = inline_closure_env cfg env [] t2  in
                       rebuild cfg env stack uu____17861)
                | uu____17862 -> norm cfg env stack t2))

and (do_unfold_fv :
  cfg ->
    env ->
      stack_elt Prims.list ->
        FStar_Syntax_Syntax.term ->
          FStar_TypeChecker_Env.qninfo ->
            FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t0  ->
          fun qninfo  ->
            fun f  ->
              let uu____17871 =
                FStar_TypeChecker_Env.lookup_definition_qninfo
                  cfg.delta_level
                  (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                  qninfo
                 in
              match uu____17871 with
              | FStar_Pervasives_Native.None  ->
                  (log_unfolding cfg
                     (fun uu____17885  ->
                        let uu____17886 = FStar_Syntax_Print.fv_to_string f
                           in
                        FStar_Util.print1 " >> Tm_fvar case 2 for %s\n"
                          uu____17886);
                   rebuild cfg env stack t0)
              | FStar_Pervasives_Native.Some (us,t) ->
                  (log_unfolding cfg
                     (fun uu____17897  ->
                        let uu____17898 =
                          FStar_Syntax_Print.term_to_string t0  in
                        let uu____17899 = FStar_Syntax_Print.term_to_string t
                           in
                        FStar_Util.print2 " >> Unfolded %s to %s\n"
                          uu____17898 uu____17899);
                   (let t1 =
                      if
                        (cfg.steps).unfold_until =
                          (FStar_Pervasives_Native.Some
                             FStar_Syntax_Syntax.delta_constant)
                      then t
                      else
                        FStar_Syntax_Subst.set_use_range
                          t0.FStar_Syntax_Syntax.pos t
                       in
                    let n1 = FStar_List.length us  in
                    if n1 > (Prims.parse_int "0")
                    then
                      match stack with
                      | (UnivArgs (us',uu____17912))::stack1 ->
                          ((let uu____17921 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug cfg.tcenv)
                                (FStar_Options.Other "univ_norm")
                               in
                            if uu____17921
                            then
                              FStar_List.iter
                                (fun x  ->
                                   let uu____17925 =
                                     FStar_Syntax_Print.univ_to_string x  in
                                   FStar_Util.print1 "Univ (normalizer) %s\n"
                                     uu____17925) us'
                            else ());
                           (let env1 =
                              FStar_All.pipe_right us'
                                (FStar_List.fold_left
                                   (fun env1  ->
                                      fun u  ->
                                        (FStar_Pervasives_Native.None,
                                          (Univ u))
                                        :: env1) env)
                               in
                            norm cfg env1 stack1 t1))
                      | uu____17958 when
                          (cfg.steps).erase_universes ||
                            (cfg.steps).allow_unbound_universes
                          -> norm cfg env stack t1
                      | uu____17961 ->
                          let uu____17964 =
                            let uu____17965 =
                              FStar_Syntax_Print.lid_to_string
                                (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                               in
                            FStar_Util.format1
                              "Impossible: missing universe instantiation on %s"
                              uu____17965
                             in
                          failwith uu____17964
                    else norm cfg env stack t1))

and (reduce_impure_comp :
  cfg ->
    env ->
      stack ->
        FStar_Syntax_Syntax.term ->
          (FStar_Syntax_Syntax.monad_name,(FStar_Syntax_Syntax.monad_name,
                                            FStar_Syntax_Syntax.monad_name)
                                            FStar_Pervasives_Native.tuple2)
            FStar_Util.either ->
            FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun head1  ->
          fun m  ->
            fun t  ->
              let t1 = norm cfg env [] t  in
              let stack1 = (Cfg cfg) :: stack  in
              let cfg1 =
                if (cfg.steps).pure_subterms_within_computations
                then
                  let new_steps =
                    [FStar_TypeChecker_Env.PureSubtermsWithinComputations;
                    FStar_TypeChecker_Env.Primops;
                    FStar_TypeChecker_Env.AllowUnboundUniverses;
                    FStar_TypeChecker_Env.EraseUniverses;
                    FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Zeta;
                    FStar_TypeChecker_Env.Inlining]  in
                  let uu___337_17989 = cfg  in
                  let uu____17990 =
                    FStar_List.fold_right fstep_add_one new_steps cfg.steps
                     in
                  {
                    steps = uu____17990;
                    tcenv = (uu___337_17989.tcenv);
                    debug = (uu___337_17989.debug);
                    delta_level =
                      [FStar_TypeChecker_Env.InliningDelta;
                      FStar_TypeChecker_Env.Eager_unfolding_only];
                    primitive_steps = (uu___337_17989.primitive_steps);
                    strong = (uu___337_17989.strong);
                    memoize_lazy = (uu___337_17989.memoize_lazy);
                    normalize_pure_lets =
                      (uu___337_17989.normalize_pure_lets)
                  }
                else
                  (let uu___338_17992 = cfg  in
                   {
                     steps =
                       (let uu___339_17995 = cfg.steps  in
                        {
                          beta = (uu___339_17995.beta);
                          iota = (uu___339_17995.iota);
                          zeta = false;
                          weak = (uu___339_17995.weak);
                          hnf = (uu___339_17995.hnf);
                          primops = (uu___339_17995.primops);
                          do_not_unfold_pure_lets =
                            (uu___339_17995.do_not_unfold_pure_lets);
                          unfold_until = (uu___339_17995.unfold_until);
                          unfold_only = (uu___339_17995.unfold_only);
                          unfold_fully = (uu___339_17995.unfold_fully);
                          unfold_attr = (uu___339_17995.unfold_attr);
                          unfold_tac = (uu___339_17995.unfold_tac);
                          pure_subterms_within_computations =
                            (uu___339_17995.pure_subterms_within_computations);
                          simplify = (uu___339_17995.simplify);
                          erase_universes = (uu___339_17995.erase_universes);
                          allow_unbound_universes =
                            (uu___339_17995.allow_unbound_universes);
                          reify_ = (uu___339_17995.reify_);
                          compress_uvars = (uu___339_17995.compress_uvars);
                          no_full_norm = (uu___339_17995.no_full_norm);
                          check_no_uvars = (uu___339_17995.check_no_uvars);
                          unmeta = (uu___339_17995.unmeta);
                          unascribe = (uu___339_17995.unascribe);
                          in_full_norm_request =
                            (uu___339_17995.in_full_norm_request);
                          weakly_reduce_scrutinee =
                            (uu___339_17995.weakly_reduce_scrutinee);
                          nbe_step = (uu___339_17995.nbe_step)
                        });
                     tcenv = (uu___338_17992.tcenv);
                     debug = (uu___338_17992.debug);
                     delta_level = (uu___338_17992.delta_level);
                     primitive_steps = (uu___338_17992.primitive_steps);
                     strong = (uu___338_17992.strong);
                     memoize_lazy = (uu___338_17992.memoize_lazy);
                     normalize_pure_lets =
                       (uu___338_17992.normalize_pure_lets)
                   })
                 in
              let metadata =
                match m with
                | FStar_Util.Inl m1 ->
                    FStar_Syntax_Syntax.Meta_monadic (m1, t1)
                | FStar_Util.Inr (m1,m') ->
                    FStar_Syntax_Syntax.Meta_monadic_lift (m1, m', t1)
                 in
              norm cfg1 env
                ((Meta (env, metadata, (head1.FStar_Syntax_Syntax.pos))) ::
                stack1) head1

and (do_reify_monadic :
  (unit -> FStar_Syntax_Syntax.term) ->
    cfg ->
      env ->
        stack_elt Prims.list ->
          FStar_Syntax_Syntax.term ->
            FStar_Syntax_Syntax.monad_name ->
              FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term)
  =
  fun fallback  ->
    fun cfg  ->
      fun env  ->
        fun stack  ->
          fun head1  ->
            fun m  ->
              fun t  ->
                let head0 = head1  in
                let head2 = FStar_Syntax_Util.unascribe head1  in
                log cfg
                  (fun uu____18029  ->
                     let uu____18030 = FStar_Syntax_Print.tag_of_term head2
                        in
                     let uu____18031 =
                       FStar_Syntax_Print.term_to_string head2  in
                     FStar_Util.print2 "Reifying: (%s) %s\n" uu____18030
                       uu____18031);
                (let head3 = FStar_Syntax_Util.unmeta_safe head2  in
                 let uu____18033 =
                   let uu____18034 = FStar_Syntax_Subst.compress head3  in
                   uu____18034.FStar_Syntax_Syntax.n  in
                 match uu____18033 with
                 | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                     let ed =
                       let uu____18052 =
                         FStar_TypeChecker_Env.norm_eff_name cfg.tcenv m  in
                       FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                         uu____18052
                        in
                     let uu____18053 = ed.FStar_Syntax_Syntax.bind_repr  in
                     (match uu____18053 with
                      | (uu____18054,bind_repr) ->
                          (match lb.FStar_Syntax_Syntax.lbname with
                           | FStar_Util.Inr uu____18064 ->
                               failwith
                                 "Cannot reify a top-level let binding"
                           | FStar_Util.Inl x ->
                               let is_return e =
                                 let uu____18074 =
                                   let uu____18075 =
                                     FStar_Syntax_Subst.compress e  in
                                   uu____18075.FStar_Syntax_Syntax.n  in
                                 match uu____18074 with
                                 | FStar_Syntax_Syntax.Tm_meta
                                     (e1,FStar_Syntax_Syntax.Meta_monadic
                                      (uu____18081,uu____18082))
                                     ->
                                     let uu____18091 =
                                       let uu____18092 =
                                         FStar_Syntax_Subst.compress e1  in
                                       uu____18092.FStar_Syntax_Syntax.n  in
                                     (match uu____18091 with
                                      | FStar_Syntax_Syntax.Tm_meta
                                          (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                           (uu____18098,msrc,uu____18100))
                                          when
                                          FStar_Syntax_Util.is_pure_effect
                                            msrc
                                          ->
                                          let uu____18109 =
                                            FStar_Syntax_Subst.compress e2
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____18109
                                      | uu____18110 ->
                                          FStar_Pervasives_Native.None)
                                 | uu____18111 ->
                                     FStar_Pervasives_Native.None
                                  in
                               let uu____18112 =
                                 is_return lb.FStar_Syntax_Syntax.lbdef  in
                               (match uu____18112 with
                                | FStar_Pervasives_Native.Some e ->
                                    let lb1 =
                                      let uu___340_18117 = lb  in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          (uu___340_18117.FStar_Syntax_Syntax.lbname);
                                        FStar_Syntax_Syntax.lbunivs =
                                          (uu___340_18117.FStar_Syntax_Syntax.lbunivs);
                                        FStar_Syntax_Syntax.lbtyp =
                                          (uu___340_18117.FStar_Syntax_Syntax.lbtyp);
                                        FStar_Syntax_Syntax.lbeff =
                                          FStar_Parser_Const.effect_PURE_lid;
                                        FStar_Syntax_Syntax.lbdef = e;
                                        FStar_Syntax_Syntax.lbattrs =
                                          (uu___340_18117.FStar_Syntax_Syntax.lbattrs);
                                        FStar_Syntax_Syntax.lbpos =
                                          (uu___340_18117.FStar_Syntax_Syntax.lbpos)
                                      }  in
                                    let uu____18118 = FStar_List.tl stack  in
                                    let uu____18119 =
                                      let uu____18120 =
                                        let uu____18127 =
                                          let uu____18128 =
                                            let uu____18141 =
                                              FStar_Syntax_Util.mk_reify body
                                               in
                                            ((false, [lb1]), uu____18141)  in
                                          FStar_Syntax_Syntax.Tm_let
                                            uu____18128
                                           in
                                        FStar_Syntax_Syntax.mk uu____18127
                                         in
                                      uu____18120
                                        FStar_Pervasives_Native.None
                                        head3.FStar_Syntax_Syntax.pos
                                       in
                                    norm cfg env uu____18118 uu____18119
                                | FStar_Pervasives_Native.None  ->
                                    let uu____18157 =
                                      let uu____18158 = is_return body  in
                                      match uu____18158 with
                                      | FStar_Pervasives_Native.Some
                                          {
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_bvar y;
                                            FStar_Syntax_Syntax.pos =
                                              uu____18162;
                                            FStar_Syntax_Syntax.vars =
                                              uu____18163;_}
                                          -> FStar_Syntax_Syntax.bv_eq x y
                                      | uu____18166 -> false  in
                                    if uu____18157
                                    then
                                      norm cfg env stack
                                        lb.FStar_Syntax_Syntax.lbdef
                                    else
                                      (let rng =
                                         head3.FStar_Syntax_Syntax.pos  in
                                       let head4 =
                                         FStar_All.pipe_left
                                           FStar_Syntax_Util.mk_reify
                                           lb.FStar_Syntax_Syntax.lbdef
                                          in
                                       let body1 =
                                         FStar_All.pipe_left
                                           FStar_Syntax_Util.mk_reify body
                                          in
                                       let body_rc =
                                         {
                                           FStar_Syntax_Syntax.residual_effect
                                             = m;
                                           FStar_Syntax_Syntax.residual_typ =
                                             (FStar_Pervasives_Native.Some t);
                                           FStar_Syntax_Syntax.residual_flags
                                             = []
                                         }  in
                                       let body2 =
                                         let uu____18187 =
                                           let uu____18194 =
                                             let uu____18195 =
                                               let uu____18212 =
                                                 let uu____18219 =
                                                   FStar_Syntax_Syntax.mk_binder
                                                     x
                                                    in
                                                 [uu____18219]  in
                                               (uu____18212, body1,
                                                 (FStar_Pervasives_Native.Some
                                                    body_rc))
                                                in
                                             FStar_Syntax_Syntax.Tm_abs
                                               uu____18195
                                              in
                                           FStar_Syntax_Syntax.mk uu____18194
                                            in
                                         uu____18187
                                           FStar_Pervasives_Native.None
                                           body1.FStar_Syntax_Syntax.pos
                                          in
                                       let close1 = closure_as_term cfg env
                                          in
                                       let bind_inst =
                                         let uu____18253 =
                                           let uu____18254 =
                                             FStar_Syntax_Subst.compress
                                               bind_repr
                                              in
                                           uu____18254.FStar_Syntax_Syntax.n
                                            in
                                         match uu____18253 with
                                         | FStar_Syntax_Syntax.Tm_uinst
                                             (bind1,uu____18260::uu____18261::[])
                                             ->
                                             let uu____18266 =
                                               let uu____18273 =
                                                 let uu____18274 =
                                                   let uu____18281 =
                                                     let uu____18282 =
                                                       let uu____18283 =
                                                         close1
                                                           lb.FStar_Syntax_Syntax.lbtyp
                                                          in
                                                       (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                         cfg.tcenv
                                                         uu____18283
                                                        in
                                                     let uu____18284 =
                                                       let uu____18287 =
                                                         let uu____18288 =
                                                           close1 t  in
                                                         (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                           cfg.tcenv
                                                           uu____18288
                                                          in
                                                       [uu____18287]  in
                                                     uu____18282 ::
                                                       uu____18284
                                                      in
                                                   (bind1, uu____18281)  in
                                                 FStar_Syntax_Syntax.Tm_uinst
                                                   uu____18274
                                                  in
                                               FStar_Syntax_Syntax.mk
                                                 uu____18273
                                                in
                                             uu____18266
                                               FStar_Pervasives_Native.None
                                               rng
                                         | uu____18294 ->
                                             failwith
                                               "NIY : Reification of indexed effects"
                                          in
                                       let maybe_range_arg =
                                         let uu____18306 =
                                           FStar_Util.for_some
                                             (FStar_Syntax_Util.attr_eq
                                                FStar_Syntax_Util.dm4f_bind_range_attr)
                                             ed.FStar_Syntax_Syntax.eff_attrs
                                            in
                                         if uu____18306
                                         then
                                           let uu____18315 =
                                             let uu____18322 =
                                               FStar_Syntax_Embeddings.embed
                                                 FStar_Syntax_Embeddings.e_range
                                                 lb.FStar_Syntax_Syntax.lbpos
                                                 lb.FStar_Syntax_Syntax.lbpos
                                                in
                                             FStar_Syntax_Syntax.as_arg
                                               uu____18322
                                              in
                                           let uu____18323 =
                                             let uu____18332 =
                                               let uu____18339 =
                                                 FStar_Syntax_Embeddings.embed
                                                   FStar_Syntax_Embeddings.e_range
                                                   body2.FStar_Syntax_Syntax.pos
                                                   body2.FStar_Syntax_Syntax.pos
                                                  in
                                               FStar_Syntax_Syntax.as_arg
                                                 uu____18339
                                                in
                                             [uu____18332]  in
                                           uu____18315 :: uu____18323
                                         else []  in
                                       let reified =
                                         let uu____18368 =
                                           let uu____18375 =
                                             let uu____18376 =
                                               let uu____18391 =
                                                 let uu____18400 =
                                                   let uu____18409 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       lb.FStar_Syntax_Syntax.lbtyp
                                                      in
                                                   let uu____18416 =
                                                     let uu____18425 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         t
                                                        in
                                                     [uu____18425]  in
                                                   uu____18409 :: uu____18416
                                                    in
                                                 let uu____18450 =
                                                   let uu____18459 =
                                                     let uu____18468 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         FStar_Syntax_Syntax.tun
                                                        in
                                                     let uu____18475 =
                                                       let uu____18484 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           head4
                                                          in
                                                       let uu____18491 =
                                                         let uu____18500 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             FStar_Syntax_Syntax.tun
                                                            in
                                                         let uu____18507 =
                                                           let uu____18516 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               body2
                                                              in
                                                           [uu____18516]  in
                                                         uu____18500 ::
                                                           uu____18507
                                                          in
                                                       uu____18484 ::
                                                         uu____18491
                                                        in
                                                     uu____18468 ::
                                                       uu____18475
                                                      in
                                                   FStar_List.append
                                                     maybe_range_arg
                                                     uu____18459
                                                    in
                                                 FStar_List.append
                                                   uu____18400 uu____18450
                                                  in
                                               (bind_inst, uu____18391)  in
                                             FStar_Syntax_Syntax.Tm_app
                                               uu____18376
                                              in
                                           FStar_Syntax_Syntax.mk uu____18375
                                            in
                                         uu____18368
                                           FStar_Pervasives_Native.None rng
                                          in
                                       log cfg
                                         (fun uu____18582  ->
                                            let uu____18583 =
                                              FStar_Syntax_Print.term_to_string
                                                head0
                                               in
                                            let uu____18584 =
                                              FStar_Syntax_Print.term_to_string
                                                reified
                                               in
                                            FStar_Util.print2
                                              "Reified (1) <%s> to %s\n"
                                              uu____18583 uu____18584);
                                       (let uu____18585 = FStar_List.tl stack
                                           in
                                        norm cfg env uu____18585 reified)))))
                 | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                     let ed =
                       let uu____18609 =
                         FStar_TypeChecker_Env.norm_eff_name cfg.tcenv m  in
                       FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                         uu____18609
                        in
                     let uu____18610 = ed.FStar_Syntax_Syntax.bind_repr  in
                     (match uu____18610 with
                      | (uu____18611,bind_repr) ->
                          let maybe_unfold_action head4 =
                            let maybe_extract_fv t1 =
                              let t2 =
                                let uu____18648 =
                                  let uu____18649 =
                                    FStar_Syntax_Subst.compress t1  in
                                  uu____18649.FStar_Syntax_Syntax.n  in
                                match uu____18648 with
                                | FStar_Syntax_Syntax.Tm_uinst
                                    (t2,uu____18653) -> t2
                                | uu____18658 -> head4  in
                              let uu____18659 =
                                let uu____18660 =
                                  FStar_Syntax_Subst.compress t2  in
                                uu____18660.FStar_Syntax_Syntax.n  in
                              match uu____18659 with
                              | FStar_Syntax_Syntax.Tm_fvar x ->
                                  FStar_Pervasives_Native.Some x
                              | uu____18666 -> FStar_Pervasives_Native.None
                               in
                            let uu____18667 = maybe_extract_fv head4  in
                            match uu____18667 with
                            | FStar_Pervasives_Native.Some x when
                                let uu____18677 =
                                  FStar_Syntax_Syntax.lid_of_fv x  in
                                FStar_TypeChecker_Env.is_action cfg.tcenv
                                  uu____18677
                                ->
                                let head5 = norm cfg env [] head4  in
                                let action_unfolded =
                                  let uu____18682 = maybe_extract_fv head5
                                     in
                                  match uu____18682 with
                                  | FStar_Pervasives_Native.Some uu____18687
                                      -> FStar_Pervasives_Native.Some true
                                  | uu____18688 ->
                                      FStar_Pervasives_Native.Some false
                                   in
                                (head5, action_unfolded)
                            | uu____18693 ->
                                (head4, FStar_Pervasives_Native.None)
                             in
                          ((let is_arg_impure uu____18708 =
                              match uu____18708 with
                              | (e,q) ->
                                  let uu____18715 =
                                    let uu____18716 =
                                      FStar_Syntax_Subst.compress e  in
                                    uu____18716.FStar_Syntax_Syntax.n  in
                                  (match uu____18715 with
                                   | FStar_Syntax_Syntax.Tm_meta
                                       (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                        (m1,m2,t'))
                                       ->
                                       let uu____18731 =
                                         FStar_Syntax_Util.is_pure_effect m1
                                          in
                                       Prims.op_Negation uu____18731
                                   | uu____18732 -> false)
                               in
                            let uu____18733 =
                              let uu____18734 =
                                let uu____18743 =
                                  FStar_Syntax_Syntax.as_arg head_app  in
                                uu____18743 :: args  in
                              FStar_Util.for_some is_arg_impure uu____18734
                               in
                            if uu____18733
                            then
                              let uu____18762 =
                                let uu____18763 =
                                  FStar_Syntax_Print.term_to_string head3  in
                                FStar_Util.format1
                                  "Incompatibility between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                  uu____18763
                                 in
                              failwith uu____18762
                            else ());
                           (let uu____18765 = maybe_unfold_action head_app
                               in
                            match uu____18765 with
                            | (head_app1,found_action) ->
                                let mk1 tm =
                                  FStar_Syntax_Syntax.mk tm
                                    FStar_Pervasives_Native.None
                                    head3.FStar_Syntax_Syntax.pos
                                   in
                                let body =
                                  mk1
                                    (FStar_Syntax_Syntax.Tm_app
                                       (head_app1, args))
                                   in
                                let body1 =
                                  match found_action with
                                  | FStar_Pervasives_Native.None  ->
                                      FStar_Syntax_Util.mk_reify body
                                  | FStar_Pervasives_Native.Some (false ) ->
                                      mk1
                                        (FStar_Syntax_Syntax.Tm_meta
                                           (body,
                                             (FStar_Syntax_Syntax.Meta_monadic
                                                (m, t))))
                                  | FStar_Pervasives_Native.Some (true ) ->
                                      body
                                   in
                                (log cfg
                                   (fun uu____18808  ->
                                      let uu____18809 =
                                        FStar_Syntax_Print.term_to_string
                                          head0
                                         in
                                      let uu____18810 =
                                        FStar_Syntax_Print.term_to_string
                                          body1
                                         in
                                      FStar_Util.print2
                                        "Reified (2) <%s> to %s\n"
                                        uu____18809 uu____18810);
                                 (let uu____18811 = FStar_List.tl stack  in
                                  norm cfg env uu____18811 body1)))))
                 | FStar_Syntax_Syntax.Tm_meta
                     (e,FStar_Syntax_Syntax.Meta_monadic uu____18813) ->
                     do_reify_monadic fallback cfg env stack e m t
                 | FStar_Syntax_Syntax.Tm_meta
                     (e,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,t'))
                     ->
                     let lifted =
                       let uu____18837 = closure_as_term cfg env t'  in
                       reify_lift cfg e msrc mtgt uu____18837  in
                     (log cfg
                        (fun uu____18841  ->
                           let uu____18842 =
                             FStar_Syntax_Print.term_to_string lifted  in
                           FStar_Util.print1 "Reified lift to (2): %s\n"
                             uu____18842);
                      (let uu____18843 = FStar_List.tl stack  in
                       norm cfg env uu____18843 lifted))
                 | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                     let branches1 =
                       FStar_All.pipe_right branches
                         (FStar_List.map
                            (fun uu____18964  ->
                               match uu____18964 with
                               | (pat,wopt,tm) ->
                                   let uu____19012 =
                                     FStar_Syntax_Util.mk_reify tm  in
                                   (pat, wopt, uu____19012)))
                        in
                     let tm =
                       mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                         head3.FStar_Syntax_Syntax.pos
                        in
                     let uu____19044 = FStar_List.tl stack  in
                     norm cfg env uu____19044 tm
                 | uu____19045 -> fallback ())

and (reify_lift :
  cfg ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.monad_name ->
        FStar_Syntax_Syntax.monad_name ->
          FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun e  ->
      fun msrc  ->
        fun mtgt  ->
          fun t  ->
            let env = cfg.tcenv  in
            log cfg
              (fun uu____19059  ->
                 let uu____19060 = FStar_Ident.string_of_lid msrc  in
                 let uu____19061 = FStar_Ident.string_of_lid mtgt  in
                 let uu____19062 = FStar_Syntax_Print.term_to_string e  in
                 FStar_Util.print3 "Reifying lift %s -> %s: %s\n" uu____19060
                   uu____19061 uu____19062);
            (let uu____19063 =
               (FStar_Syntax_Util.is_pure_effect msrc) ||
                 (FStar_Syntax_Util.is_div_effect msrc)
                in
             if uu____19063
             then
               let ed =
                 let uu____19065 =
                   FStar_TypeChecker_Env.norm_eff_name cfg.tcenv mtgt  in
                 FStar_TypeChecker_Env.get_effect_decl env uu____19065  in
               let uu____19066 = ed.FStar_Syntax_Syntax.return_repr  in
               match uu____19066 with
               | (uu____19067,return_repr) ->
                   let return_inst =
                     let uu____19080 =
                       let uu____19081 =
                         FStar_Syntax_Subst.compress return_repr  in
                       uu____19081.FStar_Syntax_Syntax.n  in
                     match uu____19080 with
                     | FStar_Syntax_Syntax.Tm_uinst
                         (return_tm,uu____19087::[]) ->
                         let uu____19092 =
                           let uu____19099 =
                             let uu____19100 =
                               let uu____19107 =
                                 let uu____19108 =
                                   env.FStar_TypeChecker_Env.universe_of env
                                     t
                                    in
                                 [uu____19108]  in
                               (return_tm, uu____19107)  in
                             FStar_Syntax_Syntax.Tm_uinst uu____19100  in
                           FStar_Syntax_Syntax.mk uu____19099  in
                         uu____19092 FStar_Pervasives_Native.None
                           e.FStar_Syntax_Syntax.pos
                     | uu____19114 ->
                         failwith "NIY : Reification of indexed effects"
                      in
                   let uu____19117 =
                     let uu____19124 =
                       let uu____19125 =
                         let uu____19140 =
                           let uu____19149 = FStar_Syntax_Syntax.as_arg t  in
                           let uu____19156 =
                             let uu____19165 = FStar_Syntax_Syntax.as_arg e
                                in
                             [uu____19165]  in
                           uu____19149 :: uu____19156  in
                         (return_inst, uu____19140)  in
                       FStar_Syntax_Syntax.Tm_app uu____19125  in
                     FStar_Syntax_Syntax.mk uu____19124  in
                   uu____19117 FStar_Pervasives_Native.None
                     e.FStar_Syntax_Syntax.pos
             else
               (let uu____19204 =
                  FStar_TypeChecker_Env.monad_leq env msrc mtgt  in
                match uu____19204 with
                | FStar_Pervasives_Native.None  ->
                    let uu____19207 =
                      let uu____19208 = FStar_Ident.text_of_lid msrc  in
                      let uu____19209 = FStar_Ident.text_of_lid mtgt  in
                      FStar_Util.format2
                        "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                        uu____19208 uu____19209
                       in
                    failwith uu____19207
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____19210;
                      FStar_TypeChecker_Env.mtarget = uu____19211;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____19212;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.None ;_};_}
                    ->
                    let uu____19234 =
                      let uu____19235 = FStar_Ident.text_of_lid msrc  in
                      let uu____19236 = FStar_Ident.text_of_lid mtgt  in
                      FStar_Util.format2
                        "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
                        uu____19235 uu____19236
                       in
                    failwith uu____19234
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____19237;
                      FStar_TypeChecker_Env.mtarget = uu____19238;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____19239;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.Some lift;_};_}
                    ->
                    let uu____19274 =
                      env.FStar_TypeChecker_Env.universe_of env t  in
                    let uu____19275 = FStar_Syntax_Util.mk_reify e  in
                    lift uu____19274 t FStar_Syntax_Syntax.tun uu____19275))

and (norm_pattern_args :
  cfg ->
    env ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
        FStar_Pervasives_Native.tuple2 Prims.list Prims.list ->
        (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
          FStar_Pervasives_Native.tuple2 Prims.list Prims.list)
  =
  fun cfg  ->
    fun env  ->
      fun args  ->
        FStar_All.pipe_right args
          (FStar_List.map
             (FStar_List.map
                (fun uu____19331  ->
                   match uu____19331 with
                   | (a,imp) ->
                       let uu____19342 = norm cfg env [] a  in
                       (uu____19342, imp))))

and (norm_comp :
  cfg -> env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp) =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        log cfg
          (fun uu____19350  ->
             let uu____19351 = FStar_Syntax_Print.comp_to_string comp  in
             let uu____19352 =
               FStar_Util.string_of_int (FStar_List.length env)  in
             FStar_Util.print2 ">>> %s\nNormComp with with %s env elements"
               uu____19351 uu____19352);
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Total (t,uopt) ->
             let t1 = norm cfg env [] t  in
             let uopt1 =
               match uopt with
               | FStar_Pervasives_Native.Some u ->
                   let uu____19376 = norm_universe cfg env u  in
                   FStar_All.pipe_left
                     (fun _0_18  -> FStar_Pervasives_Native.Some _0_18)
                     uu____19376
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
                in
             let uu___341_19379 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Total (t1, uopt1));
               FStar_Syntax_Syntax.pos =
                 (uu___341_19379.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___341_19379.FStar_Syntax_Syntax.vars)
             }
         | FStar_Syntax_Syntax.GTotal (t,uopt) ->
             let t1 = norm cfg env [] t  in
             let uopt1 =
               match uopt with
               | FStar_Pervasives_Native.Some u ->
                   let uu____19401 = norm_universe cfg env u  in
                   FStar_All.pipe_left
                     (fun _0_19  -> FStar_Pervasives_Native.Some _0_19)
                     uu____19401
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
                in
             let uu___342_19404 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.GTotal (t1, uopt1));
               FStar_Syntax_Syntax.pos =
                 (uu___342_19404.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___342_19404.FStar_Syntax_Syntax.vars)
             }
         | FStar_Syntax_Syntax.Comp ct ->
             let norm_args =
               FStar_List.mapi
                 (fun idx  ->
                    fun uu____19441  ->
                      match uu____19441 with
                      | (a,i) ->
                          let uu____19452 = norm cfg env [] a  in
                          (uu____19452, i))
                in
             let effect_args = norm_args ct.FStar_Syntax_Syntax.effect_args
                in
             let flags1 =
               FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                 (FStar_List.map
                    (fun uu___254_19470  ->
                       match uu___254_19470 with
                       | FStar_Syntax_Syntax.DECREASES t ->
                           let uu____19474 = norm cfg env [] t  in
                           FStar_Syntax_Syntax.DECREASES uu____19474
                       | f -> f))
                in
             let comp_univs =
               FStar_List.map (norm_universe cfg env)
                 ct.FStar_Syntax_Syntax.comp_univs
                in
             let result_typ =
               norm cfg env [] ct.FStar_Syntax_Syntax.result_typ  in
             let uu___343_19482 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Comp
                    (let uu___344_19485 = ct  in
                     {
                       FStar_Syntax_Syntax.comp_univs = comp_univs;
                       FStar_Syntax_Syntax.effect_name =
                         (uu___344_19485.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ = result_typ;
                       FStar_Syntax_Syntax.effect_args = effect_args;
                       FStar_Syntax_Syntax.flags = flags1
                     }));
               FStar_Syntax_Syntax.pos =
                 (uu___343_19482.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___343_19482.FStar_Syntax_Syntax.vars)
             })

and (norm_binder :
  cfg -> env -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder) =
  fun cfg  ->
    fun env  ->
      fun uu____19488  ->
        match uu____19488 with
        | (x,imp) ->
            let uu____19491 =
              let uu___345_19492 = x  in
              let uu____19493 = norm cfg env [] x.FStar_Syntax_Syntax.sort
                 in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___345_19492.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___345_19492.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____19493
              }  in
            (uu____19491, imp)

and (norm_binders :
  cfg -> env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders) =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____19499 =
          FStar_List.fold_left
            (fun uu____19533  ->
               fun b  ->
                 match uu____19533 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b  in
                     ((b1 :: nbs'), (dummy :: env1))) ([], env) bs
           in
        match uu____19499 with | (nbs,uu____19613) -> FStar_List.rev nbs

and (norm_lcomp_opt :
  cfg ->
    env ->
      FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option ->
        FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option)
  =
  fun cfg  ->
    fun env  ->
      fun lopt  ->
        match lopt with
        | FStar_Pervasives_Native.Some rc ->
            let flags1 =
              filter_out_lcomp_cflags rc.FStar_Syntax_Syntax.residual_flags
               in
            let uu____19645 =
              let uu___346_19646 = rc  in
              let uu____19647 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (norm cfg env [])
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___346_19646.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____19647;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___346_19646.FStar_Syntax_Syntax.residual_flags)
              }  in
            FStar_Pervasives_Native.Some uu____19645
        | uu____19656 -> lopt

and (maybe_simplify :
  cfg ->
    ((FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
       FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option,
      closure) FStar_Pervasives_Native.tuple2 Prims.list ->
      stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          let tm' = maybe_simplify_aux cfg env stack tm  in
          if (cfg.debug).b380
          then
            (let uu____19677 = FStar_Syntax_Print.term_to_string tm  in
             let uu____19678 = FStar_Syntax_Print.term_to_string tm'  in
             FStar_Util.print3 "%sSimplified\n\t%s to\n\t%s\n"
               (if (cfg.steps).simplify then "" else "NOT ") uu____19677
               uu____19678)
          else ();
          tm'

and (maybe_simplify_aux :
  cfg ->
    ((FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
       FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option,
      closure) FStar_Pervasives_Native.tuple2 Prims.list ->
      stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          let tm1 = reduce_primops cfg env stack tm  in
          let uu____19700 =
            FStar_All.pipe_left Prims.op_Negation (cfg.steps).simplify  in
          if uu____19700
          then tm1
          else
            (let w t =
               let uu___347_19714 = t  in
               {
                 FStar_Syntax_Syntax.n =
                   (uu___347_19714.FStar_Syntax_Syntax.n);
                 FStar_Syntax_Syntax.pos = (tm1.FStar_Syntax_Syntax.pos);
                 FStar_Syntax_Syntax.vars =
                   (uu___347_19714.FStar_Syntax_Syntax.vars)
               }  in
             let simp_t t =
               let uu____19725 =
                 let uu____19726 = FStar_Syntax_Util.unmeta t  in
                 uu____19726.FStar_Syntax_Syntax.n  in
               match uu____19725 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_Pervasives_Native.Some true
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.false_lid
                   -> FStar_Pervasives_Native.Some false
               | uu____19733 -> FStar_Pervasives_Native.None  in
             let rec args_are_binders args bs =
               match (args, bs) with
               | ((t,uu____19782)::args1,(bv,uu____19785)::bs1) ->
                   let uu____19819 =
                     let uu____19820 = FStar_Syntax_Subst.compress t  in
                     uu____19820.FStar_Syntax_Syntax.n  in
                   (match uu____19819 with
                    | FStar_Syntax_Syntax.Tm_name bv' ->
                        (FStar_Syntax_Syntax.bv_eq bv bv') &&
                          (args_are_binders args1 bs1)
                    | uu____19824 -> false)
               | ([],[]) -> true
               | (uu____19845,uu____19846) -> false  in
             let is_applied bs t =
               if (cfg.debug).wpe
               then
                 (let uu____19887 = FStar_Syntax_Print.term_to_string t  in
                  let uu____19888 = FStar_Syntax_Print.tag_of_term t  in
                  FStar_Util.print2 "WPE> is_applied %s -- %s\n" uu____19887
                    uu____19888)
               else ();
               (let uu____19890 = FStar_Syntax_Util.head_and_args' t  in
                match uu____19890 with
                | (hd1,args) ->
                    let uu____19923 =
                      let uu____19924 = FStar_Syntax_Subst.compress hd1  in
                      uu____19924.FStar_Syntax_Syntax.n  in
                    (match uu____19923 with
                     | FStar_Syntax_Syntax.Tm_name bv when
                         args_are_binders args bs ->
                         (if (cfg.debug).wpe
                          then
                            (let uu____19931 =
                               FStar_Syntax_Print.term_to_string t  in
                             let uu____19932 =
                               FStar_Syntax_Print.bv_to_string bv  in
                             let uu____19933 =
                               FStar_Syntax_Print.term_to_string hd1  in
                             FStar_Util.print3
                               "WPE> got it\n>>>>top = %s\n>>>>b = %s\n>>>>hd = %s\n"
                               uu____19931 uu____19932 uu____19933)
                          else ();
                          FStar_Pervasives_Native.Some bv)
                     | uu____19935 -> FStar_Pervasives_Native.None))
                in
             let is_applied_maybe_squashed bs t =
               if (cfg.debug).wpe
               then
                 (let uu____19952 = FStar_Syntax_Print.term_to_string t  in
                  let uu____19953 = FStar_Syntax_Print.tag_of_term t  in
                  FStar_Util.print2
                    "WPE> is_applied_maybe_squashed %s -- %s\n" uu____19952
                    uu____19953)
               else ();
               (let uu____19955 = FStar_Syntax_Util.is_squash t  in
                match uu____19955 with
                | FStar_Pervasives_Native.Some (uu____19966,t') ->
                    is_applied bs t'
                | uu____19978 ->
                    let uu____19987 = FStar_Syntax_Util.is_auto_squash t  in
                    (match uu____19987 with
                     | FStar_Pervasives_Native.Some (uu____19998,t') ->
                         is_applied bs t'
                     | uu____20010 -> is_applied bs t))
                in
             let is_quantified_const bv phi =
               let uu____20034 =
                 FStar_Syntax_Util.destruct_typ_as_formula phi  in
               match uu____20034 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
                   (lid,(p,uu____20041)::(q,uu____20043)::[])) when
                   FStar_Ident.lid_equals lid FStar_Parser_Const.imp_lid ->
                   (if (cfg.debug).wpe
                    then
                      (let uu____20071 = FStar_Syntax_Print.term_to_string p
                          in
                       let uu____20072 = FStar_Syntax_Print.term_to_string q
                          in
                       FStar_Util.print2 "WPE> p = (%s); q = (%s)\n"
                         uu____20071 uu____20072)
                    else ();
                    (let uu____20074 =
                       FStar_Syntax_Util.destruct_typ_as_formula p  in
                     match uu____20074 with
                     | FStar_Pervasives_Native.None  ->
                         let uu____20079 =
                           let uu____20080 = FStar_Syntax_Subst.compress p
                              in
                           uu____20080.FStar_Syntax_Syntax.n  in
                         (match uu____20079 with
                          | FStar_Syntax_Syntax.Tm_bvar bv' when
                              FStar_Syntax_Syntax.bv_eq bv bv' ->
                              (if (cfg.debug).wpe
                               then FStar_Util.print_string "WPE> Case 1\n"
                               else ();
                               (let uu____20088 =
                                  FStar_Syntax_Subst.subst
                                    [FStar_Syntax_Syntax.NT
                                       (bv, FStar_Syntax_Util.t_true)] q
                                   in
                                FStar_Pervasives_Native.Some uu____20088))
                          | uu____20091 -> FStar_Pervasives_Native.None)
                     | FStar_Pervasives_Native.Some
                         (FStar_Syntax_Util.BaseConn
                         (lid1,(p1,uu____20094)::[])) when
                         FStar_Ident.lid_equals lid1
                           FStar_Parser_Const.not_lid
                         ->
                         let uu____20111 =
                           let uu____20112 = FStar_Syntax_Subst.compress p1
                              in
                           uu____20112.FStar_Syntax_Syntax.n  in
                         (match uu____20111 with
                          | FStar_Syntax_Syntax.Tm_bvar bv' when
                              FStar_Syntax_Syntax.bv_eq bv bv' ->
                              (if (cfg.debug).wpe
                               then FStar_Util.print_string "WPE> Case 2\n"
                               else ();
                               (let uu____20120 =
                                  FStar_Syntax_Subst.subst
                                    [FStar_Syntax_Syntax.NT
                                       (bv, FStar_Syntax_Util.t_false)] q
                                   in
                                FStar_Pervasives_Native.Some uu____20120))
                          | uu____20123 -> FStar_Pervasives_Native.None)
                     | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
                         (bs,pats,phi1)) ->
                         let uu____20127 =
                           FStar_Syntax_Util.destruct_typ_as_formula phi1  in
                         (match uu____20127 with
                          | FStar_Pervasives_Native.None  ->
                              let uu____20132 =
                                is_applied_maybe_squashed bs phi1  in
                              (match uu____20132 with
                               | FStar_Pervasives_Native.Some bv' when
                                   FStar_Syntax_Syntax.bv_eq bv bv' ->
                                   (if (cfg.debug).wpe
                                    then
                                      FStar_Util.print_string "WPE> Case 3\n"
                                    else ();
                                    (let ftrue =
                                       FStar_Syntax_Util.abs bs
                                         FStar_Syntax_Util.t_true
                                         (FStar_Pervasives_Native.Some
                                            (FStar_Syntax_Util.residual_tot
                                               FStar_Syntax_Util.ktype0))
                                        in
                                     let uu____20143 =
                                       FStar_Syntax_Subst.subst
                                         [FStar_Syntax_Syntax.NT (bv, ftrue)]
                                         q
                                        in
                                     FStar_Pervasives_Native.Some uu____20143))
                               | uu____20146 -> FStar_Pervasives_Native.None)
                          | FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.BaseConn
                              (lid1,(p1,uu____20151)::[])) when
                              FStar_Ident.lid_equals lid1
                                FStar_Parser_Const.not_lid
                              ->
                              let uu____20168 =
                                is_applied_maybe_squashed bs p1  in
                              (match uu____20168 with
                               | FStar_Pervasives_Native.Some bv' when
                                   FStar_Syntax_Syntax.bv_eq bv bv' ->
                                   (if (cfg.debug).wpe
                                    then
                                      FStar_Util.print_string "WPE> Case 4\n"
                                    else ();
                                    (let ffalse =
                                       FStar_Syntax_Util.abs bs
                                         FStar_Syntax_Util.t_false
                                         (FStar_Pervasives_Native.Some
                                            (FStar_Syntax_Util.residual_tot
                                               FStar_Syntax_Util.ktype0))
                                        in
                                     let uu____20179 =
                                       FStar_Syntax_Subst.subst
                                         [FStar_Syntax_Syntax.NT (bv, ffalse)]
                                         q
                                        in
                                     FStar_Pervasives_Native.Some uu____20179))
                               | uu____20182 -> FStar_Pervasives_Native.None)
                          | uu____20185 -> FStar_Pervasives_Native.None)
                     | uu____20188 -> FStar_Pervasives_Native.None))
               | uu____20191 -> FStar_Pervasives_Native.None  in
             let is_forall_const phi =
               let uu____20204 =
                 FStar_Syntax_Util.destruct_typ_as_formula phi  in
               match uu____20204 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
                   ((bv,uu____20210)::[],uu____20211,phi')) ->
                   (if (cfg.debug).wpe
                    then
                      (let uu____20222 = FStar_Syntax_Print.bv_to_string bv
                          in
                       let uu____20223 =
                         FStar_Syntax_Print.term_to_string phi'  in
                       FStar_Util.print2 "WPE> QAll [%s] %s\n" uu____20222
                         uu____20223)
                    else ();
                    is_quantified_const bv phi')
               | uu____20225 -> FStar_Pervasives_Native.None  in
             let is_const_match phi =
               let uu____20238 =
                 let uu____20239 = FStar_Syntax_Subst.compress phi  in
                 uu____20239.FStar_Syntax_Syntax.n  in
               match uu____20238 with
               | FStar_Syntax_Syntax.Tm_match (uu____20244,br::brs) ->
                   let uu____20311 = br  in
                   (match uu____20311 with
                    | (uu____20328,uu____20329,e) ->
                        let r =
                          let uu____20350 = simp_t e  in
                          match uu____20350 with
                          | FStar_Pervasives_Native.None  ->
                              FStar_Pervasives_Native.None
                          | FStar_Pervasives_Native.Some b ->
                              let uu____20356 =
                                FStar_List.for_all
                                  (fun uu____20374  ->
                                     match uu____20374 with
                                     | (uu____20387,uu____20388,e') ->
                                         let uu____20402 = simp_t e'  in
                                         uu____20402 =
                                           (FStar_Pervasives_Native.Some b))
                                  brs
                                 in
                              if uu____20356
                              then FStar_Pervasives_Native.Some b
                              else FStar_Pervasives_Native.None
                           in
                        r)
               | uu____20410 -> FStar_Pervasives_Native.None  in
             let maybe_auto_squash t =
               let uu____20419 = FStar_Syntax_Util.is_sub_singleton t  in
               if uu____20419
               then t
               else
                 FStar_Syntax_Util.mk_auto_squash FStar_Syntax_Syntax.U_zero
                   t
                in
             let squashed_head_un_auto_squash_args t =
               let maybe_un_auto_squash_arg uu____20450 =
                 match uu____20450 with
                 | (t1,q) ->
                     let uu____20463 = FStar_Syntax_Util.is_auto_squash t1
                        in
                     (match uu____20463 with
                      | FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.U_zero ,t2) -> (t2, q)
                      | uu____20491 -> (t1, q))
                  in
               let uu____20502 = FStar_Syntax_Util.head_and_args t  in
               match uu____20502 with
               | (head1,args) ->
                   let args1 = FStar_List.map maybe_un_auto_squash_arg args
                      in
                   FStar_Syntax_Syntax.mk_Tm_app head1 args1
                     FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
                in
             let rec clearly_inhabited ty =
               let uu____20568 =
                 let uu____20569 = FStar_Syntax_Util.unmeta ty  in
                 uu____20569.FStar_Syntax_Syntax.n  in
               match uu____20568 with
               | FStar_Syntax_Syntax.Tm_uinst (t,uu____20573) ->
                   clearly_inhabited t
               | FStar_Syntax_Syntax.Tm_arrow (uu____20578,c) ->
                   clearly_inhabited (FStar_Syntax_Util.comp_result c)
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   let l = FStar_Syntax_Syntax.lid_of_fv fv  in
                   (((FStar_Ident.lid_equals l FStar_Parser_Const.int_lid) ||
                       (FStar_Ident.lid_equals l FStar_Parser_Const.bool_lid))
                      ||
                      (FStar_Ident.lid_equals l FStar_Parser_Const.string_lid))
                     || (FStar_Ident.lid_equals l FStar_Parser_Const.exn_lid)
               | uu____20598 -> false  in
             let simplify1 arg =
               let uu____20623 = simp_t (FStar_Pervasives_Native.fst arg)  in
               (uu____20623, arg)  in
             let uu____20632 = is_forall_const tm1  in
             match uu____20632 with
             | FStar_Pervasives_Native.Some tm' ->
                 (if (cfg.debug).wpe
                  then
                    (let uu____20637 = FStar_Syntax_Print.term_to_string tm1
                        in
                     let uu____20638 = FStar_Syntax_Print.term_to_string tm'
                        in
                     FStar_Util.print2 "WPE> %s ~> %s\n" uu____20637
                       uu____20638)
                  else ();
                  (let uu____20640 = norm cfg env [] tm'  in
                   maybe_simplify_aux cfg env stack uu____20640))
             | FStar_Pervasives_Native.None  ->
                 let uu____20641 =
                   let uu____20642 = FStar_Syntax_Subst.compress tm1  in
                   uu____20642.FStar_Syntax_Syntax.n  in
                 (match uu____20641 with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                           ({
                              FStar_Syntax_Syntax.n =
                                FStar_Syntax_Syntax.Tm_fvar fv;
                              FStar_Syntax_Syntax.pos = uu____20646;
                              FStar_Syntax_Syntax.vars = uu____20647;_},uu____20648);
                         FStar_Syntax_Syntax.pos = uu____20649;
                         FStar_Syntax_Syntax.vars = uu____20650;_},args)
                      ->
                      let uu____20676 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid
                         in
                      if uu____20676
                      then
                        let uu____20677 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        (match uu____20677 with
                         | (FStar_Pervasives_Native.Some (true ),uu____20722)::
                             (uu____20723,(arg,uu____20725))::[] ->
                             maybe_auto_squash arg
                         | (uu____20774,(arg,uu____20776))::(FStar_Pervasives_Native.Some
                                                             (true
                                                             ),uu____20777)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____20826)::uu____20827::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____20878::(FStar_Pervasives_Native.Some (false
                                         ),uu____20879)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____20930 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____20944 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid
                            in
                         if uu____20944
                         then
                           let uu____20945 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify1)
                              in
                           match uu____20945 with
                           | (FStar_Pervasives_Native.Some (true
                              ),uu____20990)::uu____20991::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____21042::(FStar_Pervasives_Native.Some (true
                                           ),uu____21043)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false
                              ),uu____21094)::(uu____21095,(arg,uu____21097))::[]
                               -> maybe_auto_squash arg
                           | (uu____21146,(arg,uu____21148))::(FStar_Pervasives_Native.Some
                                                               (false
                                                               ),uu____21149)::[]
                               -> maybe_auto_squash arg
                           | uu____21198 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____21212 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid
                               in
                            if uu____21212
                            then
                              let uu____21213 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify1)
                                 in
                              match uu____21213 with
                              | uu____21258::(FStar_Pervasives_Native.Some
                                              (true ),uu____21259)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false
                                 ),uu____21310)::uu____21311::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true
                                 ),uu____21362)::(uu____21363,(arg,uu____21365))::[]
                                  -> maybe_auto_squash arg
                              | (uu____21414,(p,uu____21416))::(uu____21417,
                                                                (q,uu____21419))::[]
                                  ->
                                  let uu____21466 =
                                    FStar_Syntax_Util.term_eq p q  in
                                  (if uu____21466
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____21468 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____21482 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid
                                  in
                               if uu____21482
                               then
                                 let uu____21483 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify1)
                                    in
                                 match uu____21483 with
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____21528)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____21529)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____21580)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____21581)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____21632)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____21633)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____21684)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____21685)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____21736,(arg,uu____21738))::(FStar_Pervasives_Native.Some
                                                                    (true
                                                                    ),uu____21739)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____21788)::(uu____21789,(arg,uu____21791))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____21840,(arg,uu____21842))::(FStar_Pervasives_Native.Some
                                                                    (false
                                                                    ),uu____21843)::[]
                                     ->
                                     let uu____21892 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____21892
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____21893)::(uu____21894,(arg,uu____21896))::[]
                                     ->
                                     let uu____21945 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____21945
                                 | (uu____21946,(p,uu____21948))::(uu____21949,
                                                                   (q,uu____21951))::[]
                                     ->
                                     let uu____21998 =
                                       FStar_Syntax_Util.term_eq p q  in
                                     (if uu____21998
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____22000 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____22014 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid
                                     in
                                  if uu____22014
                                  then
                                    let uu____22015 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify1)
                                       in
                                    match uu____22015 with
                                    | (FStar_Pervasives_Native.Some (true
                                       ),uu____22060)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false
                                       ),uu____22091)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____22122 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____22136 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid
                                        in
                                     if uu____22136
                                     then
                                       match args with
                                       | (t,uu____22138)::[] ->
                                           let uu____22155 =
                                             let uu____22156 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____22156.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____22155 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____22159::[],body,uu____22161)
                                                ->
                                                let uu____22188 = simp_t body
                                                   in
                                                (match uu____22188 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____22191 -> tm1)
                                            | uu____22194 -> tm1)
                                       | (ty,FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____22196))::(t,uu____22198)::[]
                                           ->
                                           let uu____22225 =
                                             let uu____22226 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____22226.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____22225 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____22229::[],body,uu____22231)
                                                ->
                                                let uu____22258 = simp_t body
                                                   in
                                                (match uu____22258 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false ) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____22261 -> tm1)
                                            | uu____22264 -> tm1)
                                       | uu____22265 -> tm1
                                     else
                                       (let uu____22275 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid
                                           in
                                        if uu____22275
                                        then
                                          match args with
                                          | (t,uu____22277)::[] ->
                                              let uu____22294 =
                                                let uu____22295 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____22295.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____22294 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____22298::[],body,uu____22300)
                                                   ->
                                                   let uu____22327 =
                                                     simp_t body  in
                                                   (match uu____22327 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____22330 -> tm1)
                                               | uu____22333 -> tm1)
                                          | (ty,FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____22335))::(t,uu____22337)::[]
                                              ->
                                              let uu____22364 =
                                                let uu____22365 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____22365.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____22364 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____22368::[],body,uu____22370)
                                                   ->
                                                   let uu____22397 =
                                                     simp_t body  in
                                                   (match uu____22397 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | FStar_Pervasives_Native.Some
                                                        (true ) when
                                                        clearly_inhabited ty
                                                        ->
                                                        w
                                                          FStar_Syntax_Util.t_true
                                                    | uu____22400 -> tm1)
                                               | uu____22403 -> tm1)
                                          | uu____22404 -> tm1
                                        else
                                          (let uu____22414 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid
                                              in
                                           if uu____22414
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____22415;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____22416;_},uu____22417)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____22434;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____22435;_},uu____22436)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____22453 -> tm1
                                           else
                                             (let uu____22463 =
                                                FStar_Syntax_Util.is_auto_squash
                                                  tm1
                                                 in
                                              match uu____22463 with
                                              | FStar_Pervasives_Native.Some
                                                  (FStar_Syntax_Syntax.U_zero
                                                   ,t)
                                                  when
                                                  FStar_Syntax_Util.is_sub_singleton
                                                    t
                                                  -> t
                                              | uu____22483 ->
                                                  reduce_equality cfg env
                                                    stack tm1))))))))
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____22493;
                         FStar_Syntax_Syntax.vars = uu____22494;_},args)
                      ->
                      let uu____22516 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid
                         in
                      if uu____22516
                      then
                        let uu____22517 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        (match uu____22517 with
                         | (FStar_Pervasives_Native.Some (true ),uu____22562)::
                             (uu____22563,(arg,uu____22565))::[] ->
                             maybe_auto_squash arg
                         | (uu____22614,(arg,uu____22616))::(FStar_Pervasives_Native.Some
                                                             (true
                                                             ),uu____22617)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____22666)::uu____22667::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____22718::(FStar_Pervasives_Native.Some (false
                                         ),uu____22719)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____22770 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____22784 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid
                            in
                         if uu____22784
                         then
                           let uu____22785 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify1)
                              in
                           match uu____22785 with
                           | (FStar_Pervasives_Native.Some (true
                              ),uu____22830)::uu____22831::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____22882::(FStar_Pervasives_Native.Some (true
                                           ),uu____22883)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false
                              ),uu____22934)::(uu____22935,(arg,uu____22937))::[]
                               -> maybe_auto_squash arg
                           | (uu____22986,(arg,uu____22988))::(FStar_Pervasives_Native.Some
                                                               (false
                                                               ),uu____22989)::[]
                               -> maybe_auto_squash arg
                           | uu____23038 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____23052 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid
                               in
                            if uu____23052
                            then
                              let uu____23053 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify1)
                                 in
                              match uu____23053 with
                              | uu____23098::(FStar_Pervasives_Native.Some
                                              (true ),uu____23099)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false
                                 ),uu____23150)::uu____23151::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true
                                 ),uu____23202)::(uu____23203,(arg,uu____23205))::[]
                                  -> maybe_auto_squash arg
                              | (uu____23254,(p,uu____23256))::(uu____23257,
                                                                (q,uu____23259))::[]
                                  ->
                                  let uu____23306 =
                                    FStar_Syntax_Util.term_eq p q  in
                                  (if uu____23306
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____23308 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____23322 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid
                                  in
                               if uu____23322
                               then
                                 let uu____23323 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify1)
                                    in
                                 match uu____23323 with
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____23368)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____23369)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____23420)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____23421)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____23472)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____23473)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____23524)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____23525)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____23576,(arg,uu____23578))::(FStar_Pervasives_Native.Some
                                                                    (true
                                                                    ),uu____23579)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____23628)::(uu____23629,(arg,uu____23631))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____23680,(arg,uu____23682))::(FStar_Pervasives_Native.Some
                                                                    (false
                                                                    ),uu____23683)::[]
                                     ->
                                     let uu____23732 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____23732
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____23733)::(uu____23734,(arg,uu____23736))::[]
                                     ->
                                     let uu____23785 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____23785
                                 | (uu____23786,(p,uu____23788))::(uu____23789,
                                                                   (q,uu____23791))::[]
                                     ->
                                     let uu____23838 =
                                       FStar_Syntax_Util.term_eq p q  in
                                     (if uu____23838
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____23840 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____23854 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid
                                     in
                                  if uu____23854
                                  then
                                    let uu____23855 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify1)
                                       in
                                    match uu____23855 with
                                    | (FStar_Pervasives_Native.Some (true
                                       ),uu____23900)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false
                                       ),uu____23931)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____23962 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____23976 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid
                                        in
                                     if uu____23976
                                     then
                                       match args with
                                       | (t,uu____23978)::[] ->
                                           let uu____23995 =
                                             let uu____23996 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____23996.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____23995 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____23999::[],body,uu____24001)
                                                ->
                                                let uu____24028 = simp_t body
                                                   in
                                                (match uu____24028 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____24031 -> tm1)
                                            | uu____24034 -> tm1)
                                       | (ty,FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____24036))::(t,uu____24038)::[]
                                           ->
                                           let uu____24065 =
                                             let uu____24066 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____24066.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____24065 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____24069::[],body,uu____24071)
                                                ->
                                                let uu____24098 = simp_t body
                                                   in
                                                (match uu____24098 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false ) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____24101 -> tm1)
                                            | uu____24104 -> tm1)
                                       | uu____24105 -> tm1
                                     else
                                       (let uu____24115 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid
                                           in
                                        if uu____24115
                                        then
                                          match args with
                                          | (t,uu____24117)::[] ->
                                              let uu____24134 =
                                                let uu____24135 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____24135.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____24134 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____24138::[],body,uu____24140)
                                                   ->
                                                   let uu____24167 =
                                                     simp_t body  in
                                                   (match uu____24167 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____24170 -> tm1)
                                               | uu____24173 -> tm1)
                                          | (ty,FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____24175))::(t,uu____24177)::[]
                                              ->
                                              let uu____24204 =
                                                let uu____24205 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____24205.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____24204 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____24208::[],body,uu____24210)
                                                   ->
                                                   let uu____24237 =
                                                     simp_t body  in
                                                   (match uu____24237 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | FStar_Pervasives_Native.Some
                                                        (true ) when
                                                        clearly_inhabited ty
                                                        ->
                                                        w
                                                          FStar_Syntax_Util.t_true
                                                    | uu____24240 -> tm1)
                                               | uu____24243 -> tm1)
                                          | uu____24244 -> tm1
                                        else
                                          (let uu____24254 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid
                                              in
                                           if uu____24254
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____24255;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____24256;_},uu____24257)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____24274;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____24275;_},uu____24276)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____24293 -> tm1
                                           else
                                             (let uu____24303 =
                                                FStar_Syntax_Util.is_auto_squash
                                                  tm1
                                                 in
                                              match uu____24303 with
                                              | FStar_Pervasives_Native.Some
                                                  (FStar_Syntax_Syntax.U_zero
                                                   ,t)
                                                  when
                                                  FStar_Syntax_Util.is_sub_singleton
                                                    t
                                                  -> t
                                              | uu____24323 ->
                                                  reduce_equality cfg env
                                                    stack tm1))))))))
                  | FStar_Syntax_Syntax.Tm_refine (bv,t) ->
                      let uu____24338 = simp_t t  in
                      (match uu____24338 with
                       | FStar_Pervasives_Native.Some (true ) ->
                           bv.FStar_Syntax_Syntax.sort
                       | FStar_Pervasives_Native.Some (false ) -> tm1
                       | FStar_Pervasives_Native.None  -> tm1)
                  | FStar_Syntax_Syntax.Tm_match uu____24341 ->
                      let uu____24364 = is_const_match tm1  in
                      (match uu____24364 with
                       | FStar_Pervasives_Native.Some (true ) ->
                           w FStar_Syntax_Util.t_true
                       | FStar_Pervasives_Native.Some (false ) ->
                           w FStar_Syntax_Util.t_false
                       | FStar_Pervasives_Native.None  -> tm1)
                  | uu____24367 -> tm1))

and (rebuild :
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          log cfg
            (fun uu____24377  ->
               (let uu____24379 = FStar_Syntax_Print.tag_of_term t  in
                let uu____24380 = FStar_Syntax_Print.term_to_string t  in
                let uu____24381 =
                  FStar_Util.string_of_int (FStar_List.length env)  in
                let uu____24388 =
                  let uu____24389 =
                    let uu____24392 = firstn (Prims.parse_int "4") stack  in
                    FStar_All.pipe_left FStar_Pervasives_Native.fst
                      uu____24392
                     in
                  stack_to_string uu____24389  in
                FStar_Util.print4
                  ">>> %s\nRebuild %s with %s env elements and top of the stack %s \n"
                  uu____24379 uu____24380 uu____24381 uu____24388);
               (let uu____24415 =
                  FStar_TypeChecker_Env.debug cfg.tcenv
                    (FStar_Options.Other "NormRebuild")
                   in
                if uu____24415
                then
                  let uu____24416 = FStar_Syntax_Util.unbound_variables t  in
                  match uu____24416 with
                  | [] -> ()
                  | bvs ->
                      ((let uu____24423 = FStar_Syntax_Print.tag_of_term t
                           in
                        let uu____24424 = FStar_Syntax_Print.term_to_string t
                           in
                        let uu____24425 =
                          let uu____24426 =
                            FStar_All.pipe_right bvs
                              (FStar_List.map FStar_Syntax_Print.bv_to_string)
                             in
                          FStar_All.pipe_right uu____24426
                            (FStar_String.concat ", ")
                           in
                        FStar_Util.print3
                          "!!! Rebuild (%s) %s, free vars=%s\n" uu____24423
                          uu____24424 uu____24425);
                       failwith "DIE!")
                else ()));
          (let t1 = maybe_simplify cfg env stack t  in
           match stack with
           | [] -> t1
           | (Debug (tm,time_then))::stack1 ->
               (if (cfg.debug).print_normalized
                then
                  (let time_now = FStar_Util.now ()  in
                   let uu____24444 =
                     let uu____24445 =
                       let uu____24446 =
                         FStar_Util.time_diff time_then time_now  in
                       FStar_Pervasives_Native.snd uu____24446  in
                     FStar_Util.string_of_int uu____24445  in
                   let uu____24451 = FStar_Syntax_Print.term_to_string tm  in
                   let uu____24452 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.print3 "Normalized (%s ms) %s\n\tto %s\n"
                     uu____24444 uu____24451 uu____24452)
                else ();
                rebuild cfg env stack1 t1)
           | (Cfg cfg1)::stack1 -> rebuild cfg1 env stack1 t1
           | (Meta (uu____24458,m,r))::stack1 ->
               let t2 = mk (FStar_Syntax_Syntax.Tm_meta (t1, m)) r  in
               rebuild cfg env stack1 t2
           | (MemoLazy r)::stack1 ->
               (set_memo cfg r (env, t1);
                log cfg
                  (fun uu____24509  ->
                     let uu____24510 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 "\tSet memo %s\n" uu____24510);
                rebuild cfg env stack1 t1)
           | (Let (env',bs,lb,r))::stack1 ->
               let body = FStar_Syntax_Subst.close bs t1  in
               let t2 =
                 FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_let ((false, [lb]), body))
                   FStar_Pervasives_Native.None r
                  in
               rebuild cfg env' stack1 t2
           | (Abs (env',bs,env'',lopt,r))::stack1 ->
               let bs1 = norm_binders cfg env' bs  in
               let lopt1 = norm_lcomp_opt cfg env'' lopt  in
               let uu____24548 =
                 let uu___348_24549 = FStar_Syntax_Util.abs bs1 t1 lopt1  in
                 {
                   FStar_Syntax_Syntax.n =
                     (uu___348_24549.FStar_Syntax_Syntax.n);
                   FStar_Syntax_Syntax.pos = r;
                   FStar_Syntax_Syntax.vars =
                     (uu___348_24549.FStar_Syntax_Syntax.vars)
                 }  in
               rebuild cfg env stack1 uu____24548
           | (Arg (Univ uu____24552,uu____24553,uu____24554))::uu____24555 ->
               failwith "Impossible"
           | (Arg (Dummy ,uu____24558,uu____24559))::uu____24560 ->
               failwith "Impossible"
           | (UnivArgs (us,r))::stack1 ->
               let t2 = FStar_Syntax_Syntax.mk_Tm_uinst t1 us  in
               rebuild cfg env stack1 t2
           | (Arg (Clos (env_arg,tm,uu____24575,uu____24576),aq,r))::stack1
               when
               let uu____24626 = head_of t1  in
               FStar_Syntax_Util.is_fstar_tactics_by_tactic uu____24626 ->
               let t2 =
                 let uu____24630 =
                   let uu____24635 =
                     let uu____24636 = closure_as_term cfg env_arg tm  in
                     (uu____24636, aq)  in
                   FStar_Syntax_Syntax.extend_app t1 uu____24635  in
                 uu____24630 FStar_Pervasives_Native.None r  in
               rebuild cfg env stack1 t2
           | (Arg (Clos (env_arg,tm,m,uu____24646),aq,r))::stack1 ->
               (log cfg
                  (fun uu____24699  ->
                     let uu____24700 = FStar_Syntax_Print.term_to_string tm
                        in
                     FStar_Util.print1 "Rebuilding with arg %s\n" uu____24700);
                if Prims.op_Negation (cfg.steps).iota
                then
                  (if (cfg.steps).hnf
                   then
                     let arg = closure_as_term cfg env_arg tm  in
                     let t2 =
                       FStar_Syntax_Syntax.extend_app t1 (arg, aq)
                         FStar_Pervasives_Native.None r
                        in
                     rebuild cfg env_arg stack1 t2
                   else
                     (let stack2 = (App (env, t1, aq, r)) :: stack1  in
                      norm cfg env_arg stack2 tm))
                else
                  (let uu____24712 = FStar_ST.op_Bang m  in
                   match uu____24712 with
                   | FStar_Pervasives_Native.None  ->
                       if (cfg.steps).hnf
                       then
                         let arg = closure_as_term cfg env_arg tm  in
                         let t2 =
                           FStar_Syntax_Syntax.extend_app t1 (arg, aq)
                             FStar_Pervasives_Native.None r
                            in
                         rebuild cfg env_arg stack1 t2
                       else
                         (let stack2 = (MemoLazy m) :: (App (env, t1, aq, r))
                            :: stack1  in
                          norm cfg env_arg stack2 tm)
                   | FStar_Pervasives_Native.Some (uu____24855,a) ->
                       let t2 =
                         FStar_Syntax_Syntax.extend_app t1 (a, aq)
                           FStar_Pervasives_Native.None r
                          in
                       rebuild cfg env_arg stack1 t2))
           | (App (env1,head1,aq,r))::stack' when should_reify cfg stack ->
               let t0 = t1  in
               let fallback msg uu____24908 =
                 log cfg
                   (fun uu____24912  ->
                      let uu____24913 = FStar_Syntax_Print.term_to_string t1
                         in
                      FStar_Util.print2 "Not reifying%s: %s\n" msg
                        uu____24913);
                 (let t2 =
                    FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                      FStar_Pervasives_Native.None r
                     in
                  rebuild cfg env1 stack' t2)
                  in
               let uu____24919 =
                 let uu____24920 = FStar_Syntax_Subst.compress t1  in
                 uu____24920.FStar_Syntax_Syntax.n  in
               (match uu____24919 with
                | FStar_Syntax_Syntax.Tm_meta
                    (t2,FStar_Syntax_Syntax.Meta_monadic (m,ty)) ->
                    do_reify_monadic (fallback " (1)") cfg env1 stack t2 m ty
                | FStar_Syntax_Syntax.Tm_meta
                    (t2,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,ty))
                    ->
                    let lifted =
                      let uu____24947 = closure_as_term cfg env1 ty  in
                      reify_lift cfg t2 msrc mtgt uu____24947  in
                    (log cfg
                       (fun uu____24951  ->
                          let uu____24952 =
                            FStar_Syntax_Print.term_to_string lifted  in
                          FStar_Util.print1 "Reified lift to (1): %s\n"
                            uu____24952);
                     (let uu____24953 = FStar_List.tl stack  in
                      norm cfg env1 uu____24953 lifted))
                | FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reflect uu____24954);
                       FStar_Syntax_Syntax.pos = uu____24955;
                       FStar_Syntax_Syntax.vars = uu____24956;_},(e,uu____24958)::[])
                    -> norm cfg env1 stack' e
                | FStar_Syntax_Syntax.Tm_app uu____24987 when
                    (cfg.steps).primops ->
                    let uu____25002 = FStar_Syntax_Util.head_and_args t1  in
                    (match uu____25002 with
                     | (hd1,args) ->
                         let uu____25039 =
                           let uu____25040 = FStar_Syntax_Util.un_uinst hd1
                              in
                           uu____25040.FStar_Syntax_Syntax.n  in
                         (match uu____25039 with
                          | FStar_Syntax_Syntax.Tm_fvar fv ->
                              let uu____25044 = find_prim_step cfg fv  in
                              (match uu____25044 with
                               | FStar_Pervasives_Native.Some
                                   { name = uu____25047; arity = uu____25048;
                                     auto_reflect =
                                       FStar_Pervasives_Native.Some n1;
                                     strong_reduction_ok = uu____25050;
                                     requires_binder_substitution =
                                       uu____25051;
                                     interpretation = uu____25052;_}
                                   when (FStar_List.length args) = n1 ->
                                   norm cfg env1 stack' t1
                               | uu____25067 -> fallback " (3)" ())
                          | uu____25070 -> fallback " (4)" ()))
                | uu____25071 -> fallback " (2)" ())
           | (App (env1,head1,aq,r))::stack1 ->
               let t2 =
                 FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                   FStar_Pervasives_Native.None r
                  in
               rebuild cfg env1 stack1 t2
           | (Match (env',branches,cfg1,r))::stack1 ->
               (log cfg1
                  (fun uu____25094  ->
                     let uu____25095 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1
                       "Rebuilding with match, scrutinee is %s ...\n"
                       uu____25095);
                (let scrutinee_env = env  in
                 let env1 = env'  in
                 let scrutinee = t1  in
                 let norm_and_rebuild_match uu____25104 =
                   log cfg1
                     (fun uu____25109  ->
                        let uu____25110 =
                          FStar_Syntax_Print.term_to_string scrutinee  in
                        let uu____25111 =
                          let uu____25112 =
                            FStar_All.pipe_right branches
                              (FStar_List.map
                                 (fun uu____25139  ->
                                    match uu____25139 with
                                    | (p,uu____25149,uu____25150) ->
                                        FStar_Syntax_Print.pat_to_string p))
                             in
                          FStar_All.pipe_right uu____25112
                            (FStar_String.concat "\n\t")
                           in
                        FStar_Util.print2
                          "match is irreducible: scrutinee=%s\nbranches=%s\n"
                          uu____25110 uu____25111);
                   (let whnf = (cfg1.steps).weak || (cfg1.steps).hnf  in
                    let cfg_exclude_zeta =
                      let new_delta =
                        FStar_All.pipe_right cfg1.delta_level
                          (FStar_List.filter
                             (fun uu___255_25167  ->
                                match uu___255_25167 with
                                | FStar_TypeChecker_Env.InliningDelta  ->
                                    true
                                | FStar_TypeChecker_Env.Eager_unfolding_only 
                                    -> true
                                | uu____25168 -> false))
                         in
                      let steps =
                        let uu___349_25170 = cfg1.steps  in
                        {
                          beta = (uu___349_25170.beta);
                          iota = (uu___349_25170.iota);
                          zeta = false;
                          weak = (uu___349_25170.weak);
                          hnf = (uu___349_25170.hnf);
                          primops = (uu___349_25170.primops);
                          do_not_unfold_pure_lets =
                            (uu___349_25170.do_not_unfold_pure_lets);
                          unfold_until = FStar_Pervasives_Native.None;
                          unfold_only = FStar_Pervasives_Native.None;
                          unfold_fully = (uu___349_25170.unfold_fully);
                          unfold_attr = FStar_Pervasives_Native.None;
                          unfold_tac = false;
                          pure_subterms_within_computations =
                            (uu___349_25170.pure_subterms_within_computations);
                          simplify = (uu___349_25170.simplify);
                          erase_universes = (uu___349_25170.erase_universes);
                          allow_unbound_universes =
                            (uu___349_25170.allow_unbound_universes);
                          reify_ = (uu___349_25170.reify_);
                          compress_uvars = (uu___349_25170.compress_uvars);
                          no_full_norm = (uu___349_25170.no_full_norm);
                          check_no_uvars = (uu___349_25170.check_no_uvars);
                          unmeta = (uu___349_25170.unmeta);
                          unascribe = (uu___349_25170.unascribe);
                          in_full_norm_request =
                            (uu___349_25170.in_full_norm_request);
                          weakly_reduce_scrutinee =
                            (uu___349_25170.weakly_reduce_scrutinee);
                          nbe_step = (uu___349_25170.nbe_step)
                        }  in
                      let uu___350_25175 = cfg1  in
                      {
                        steps;
                        tcenv = (uu___350_25175.tcenv);
                        debug = (uu___350_25175.debug);
                        delta_level = new_delta;
                        primitive_steps = (uu___350_25175.primitive_steps);
                        strong = true;
                        memoize_lazy = (uu___350_25175.memoize_lazy);
                        normalize_pure_lets =
                          (uu___350_25175.normalize_pure_lets)
                      }  in
                    let norm_or_whnf env2 t2 =
                      if whnf
                      then closure_as_term cfg_exclude_zeta env2 t2
                      else norm cfg_exclude_zeta env2 [] t2  in
                    let rec norm_pat env2 p =
                      match p.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_constant uu____25247 ->
                          (p, env2)
                      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                          let uu____25276 =
                            FStar_All.pipe_right pats
                              (FStar_List.fold_left
                                 (fun uu____25360  ->
                                    fun uu____25361  ->
                                      match (uu____25360, uu____25361) with
                                      | ((pats1,env3),(p1,b)) ->
                                          let uu____25500 = norm_pat env3 p1
                                             in
                                          (match uu____25500 with
                                           | (p2,env4) ->
                                               (((p2, b) :: pats1), env4)))
                                 ([], env2))
                             in
                          (match uu____25276 with
                           | (pats1,env3) ->
                               ((let uu___351_25662 = p  in
                                 {
                                   FStar_Syntax_Syntax.v =
                                     (FStar_Syntax_Syntax.Pat_cons
                                        (fv, (FStar_List.rev pats1)));
                                   FStar_Syntax_Syntax.p =
                                     (uu___351_25662.FStar_Syntax_Syntax.p)
                                 }), env3))
                      | FStar_Syntax_Syntax.Pat_var x ->
                          let x1 =
                            let uu___352_25681 = x  in
                            let uu____25682 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___352_25681.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___352_25681.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____25682
                            }  in
                          ((let uu___353_25696 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_var x1);
                              FStar_Syntax_Syntax.p =
                                (uu___353_25696.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_wild x ->
                          let x1 =
                            let uu___354_25707 = x  in
                            let uu____25708 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___354_25707.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___354_25707.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____25708
                            }  in
                          ((let uu___355_25722 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_wild x1);
                              FStar_Syntax_Syntax.p =
                                (uu___355_25722.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                          let x1 =
                            let uu___356_25738 = x  in
                            let uu____25739 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___356_25738.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___356_25738.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____25739
                            }  in
                          let t3 = norm_or_whnf env2 t2  in
                          ((let uu___357_25754 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_dot_term (x1, t3));
                              FStar_Syntax_Syntax.p =
                                (uu___357_25754.FStar_Syntax_Syntax.p)
                            }), env2)
                       in
                    let branches1 =
                      match env1 with
                      | [] when whnf -> branches
                      | uu____25798 ->
                          FStar_All.pipe_right branches
                            (FStar_List.map
                               (fun branch1  ->
                                  let uu____25828 =
                                    FStar_Syntax_Subst.open_branch branch1
                                     in
                                  match uu____25828 with
                                  | (p,wopt,e) ->
                                      let uu____25848 = norm_pat env1 p  in
                                      (match uu____25848 with
                                       | (p1,env2) ->
                                           let wopt1 =
                                             match wopt with
                                             | FStar_Pervasives_Native.None 
                                                 ->
                                                 FStar_Pervasives_Native.None
                                             | FStar_Pervasives_Native.Some w
                                                 ->
                                                 let uu____25903 =
                                                   norm_or_whnf env2 w  in
                                                 FStar_Pervasives_Native.Some
                                                   uu____25903
                                              in
                                           let e1 = norm_or_whnf env2 e  in
                                           FStar_Syntax_Util.branch
                                             (p1, wopt1, e1))))
                       in
                    let scrutinee1 =
                      let uu____25920 =
                        ((((cfg1.steps).iota &&
                             (Prims.op_Negation (cfg1.steps).weak))
                            &&
                            (Prims.op_Negation (cfg1.steps).compress_uvars))
                           && (cfg1.steps).weakly_reduce_scrutinee)
                          && (maybe_weakly_reduced scrutinee)
                         in
                      if uu____25920
                      then
                        norm
                          (let uu___358_25925 = cfg1  in
                           {
                             steps =
                               (let uu___359_25928 = cfg1.steps  in
                                {
                                  beta = (uu___359_25928.beta);
                                  iota = (uu___359_25928.iota);
                                  zeta = (uu___359_25928.zeta);
                                  weak = (uu___359_25928.weak);
                                  hnf = (uu___359_25928.hnf);
                                  primops = (uu___359_25928.primops);
                                  do_not_unfold_pure_lets =
                                    (uu___359_25928.do_not_unfold_pure_lets);
                                  unfold_until =
                                    (uu___359_25928.unfold_until);
                                  unfold_only = (uu___359_25928.unfold_only);
                                  unfold_fully =
                                    (uu___359_25928.unfold_fully);
                                  unfold_attr = (uu___359_25928.unfold_attr);
                                  unfold_tac = (uu___359_25928.unfold_tac);
                                  pure_subterms_within_computations =
                                    (uu___359_25928.pure_subterms_within_computations);
                                  simplify = (uu___359_25928.simplify);
                                  erase_universes =
                                    (uu___359_25928.erase_universes);
                                  allow_unbound_universes =
                                    (uu___359_25928.allow_unbound_universes);
                                  reify_ = (uu___359_25928.reify_);
                                  compress_uvars =
                                    (uu___359_25928.compress_uvars);
                                  no_full_norm =
                                    (uu___359_25928.no_full_norm);
                                  check_no_uvars =
                                    (uu___359_25928.check_no_uvars);
                                  unmeta = (uu___359_25928.unmeta);
                                  unascribe = (uu___359_25928.unascribe);
                                  in_full_norm_request =
                                    (uu___359_25928.in_full_norm_request);
                                  weakly_reduce_scrutinee = false;
                                  nbe_step = (uu___359_25928.nbe_step)
                                });
                             tcenv = (uu___358_25925.tcenv);
                             debug = (uu___358_25925.debug);
                             delta_level = (uu___358_25925.delta_level);
                             primitive_steps =
                               (uu___358_25925.primitive_steps);
                             strong = (uu___358_25925.strong);
                             memoize_lazy = (uu___358_25925.memoize_lazy);
                             normalize_pure_lets =
                               (uu___358_25925.normalize_pure_lets)
                           }) scrutinee_env [] scrutinee
                      else scrutinee  in
                    let uu____25930 =
                      mk
                        (FStar_Syntax_Syntax.Tm_match (scrutinee1, branches1))
                        r
                       in
                    rebuild cfg1 env1 stack1 uu____25930)
                    in
                 let rec is_cons head1 =
                   let uu____25955 =
                     let uu____25956 = FStar_Syntax_Subst.compress head1  in
                     uu____25956.FStar_Syntax_Syntax.n  in
                   match uu____25955 with
                   | FStar_Syntax_Syntax.Tm_uinst (h,uu____25960) ->
                       is_cons h
                   | FStar_Syntax_Syntax.Tm_constant uu____25965 -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____25966;
                         FStar_Syntax_Syntax.fv_delta = uu____25967;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Data_ctor );_}
                       -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____25968;
                         FStar_Syntax_Syntax.fv_delta = uu____25969;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Record_ctor uu____25970);_}
                       -> true
                   | uu____25977 -> false  in
                 let guard_when_clause wopt b rest =
                   match wopt with
                   | FStar_Pervasives_Native.None  -> b
                   | FStar_Pervasives_Native.Some w ->
                       let then_branch = b  in
                       let else_branch =
                         mk (FStar_Syntax_Syntax.Tm_match (scrutinee, rest))
                           r
                          in
                       FStar_Syntax_Util.if_then_else w then_branch
                         else_branch
                    in
                 let rec matches_pat scrutinee_orig p =
                   let scrutinee1 = FStar_Syntax_Util.unmeta scrutinee_orig
                      in
                   let uu____26140 =
                     FStar_Syntax_Util.head_and_args scrutinee1  in
                   match uu____26140 with
                   | (head1,args) ->
                       (match p.FStar_Syntax_Syntax.v with
                        | FStar_Syntax_Syntax.Pat_var bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_wild bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_dot_term uu____26227 ->
                            FStar_Util.Inl []
                        | FStar_Syntax_Syntax.Pat_constant s ->
                            (match scrutinee1.FStar_Syntax_Syntax.n with
                             | FStar_Syntax_Syntax.Tm_constant s' when
                                 FStar_Const.eq_const s s' ->
                                 FStar_Util.Inl []
                             | uu____26266 ->
                                 let uu____26267 =
                                   let uu____26268 = is_cons head1  in
                                   Prims.op_Negation uu____26268  in
                                 FStar_Util.Inr uu____26267)
                        | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                            let uu____26293 =
                              let uu____26294 =
                                FStar_Syntax_Util.un_uinst head1  in
                              uu____26294.FStar_Syntax_Syntax.n  in
                            (match uu____26293 with
                             | FStar_Syntax_Syntax.Tm_fvar fv' when
                                 FStar_Syntax_Syntax.fv_eq fv fv' ->
                                 matches_args [] args arg_pats
                             | uu____26312 ->
                                 let uu____26313 =
                                   let uu____26314 = is_cons head1  in
                                   Prims.op_Negation uu____26314  in
                                 FStar_Util.Inr uu____26313))
                 
                 and matches_args out a p =
                   match (a, p) with
                   | ([],[]) -> FStar_Util.Inl out
                   | ((t2,uu____26391)::rest_a,(p1,uu____26394)::rest_p) ->
                       let uu____26438 = matches_pat t2 p1  in
                       (match uu____26438 with
                        | FStar_Util.Inl s ->
                            matches_args (FStar_List.append out s) rest_a
                              rest_p
                        | m -> m)
                   | uu____26487 -> FStar_Util.Inr false
                  in
                 let rec matches scrutinee1 p =
                   match p with
                   | [] -> norm_and_rebuild_match ()
                   | (p1,wopt,b)::rest ->
                       let uu____26605 = matches_pat scrutinee1 p1  in
                       (match uu____26605 with
                        | FStar_Util.Inr (false ) -> matches scrutinee1 rest
                        | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                        | FStar_Util.Inl s ->
                            (log cfg1
                               (fun uu____26645  ->
                                  let uu____26646 =
                                    FStar_Syntax_Print.pat_to_string p1  in
                                  let uu____26647 =
                                    let uu____26648 =
                                      FStar_List.map
                                        (fun uu____26658  ->
                                           match uu____26658 with
                                           | (uu____26663,t2) ->
                                               FStar_Syntax_Print.term_to_string
                                                 t2) s
                                       in
                                    FStar_All.pipe_right uu____26648
                                      (FStar_String.concat "; ")
                                     in
                                  FStar_Util.print2
                                    "Matches pattern %s with subst = %s\n"
                                    uu____26646 uu____26647);
                             (let env0 = env1  in
                              let env2 =
                                FStar_List.fold_left
                                  (fun env2  ->
                                     fun uu____26695  ->
                                       match uu____26695 with
                                       | (bv,t2) ->
                                           let uu____26718 =
                                             let uu____26725 =
                                               let uu____26728 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   bv
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 uu____26728
                                                in
                                             let uu____26729 =
                                               let uu____26730 =
                                                 let uu____26761 =
                                                   FStar_Util.mk_ref
                                                     (FStar_Pervasives_Native.Some
                                                        ([], t2))
                                                    in
                                                 ([], t2, uu____26761, false)
                                                  in
                                               Clos uu____26730  in
                                             (uu____26725, uu____26729)  in
                                           uu____26718 :: env2) env1 s
                                 in
                              let uu____26874 = guard_when_clause wopt b rest
                                 in
                              norm cfg1 env2 stack1 uu____26874)))
                    in
                 if (cfg1.steps).iota
                 then matches scrutinee branches
                 else norm_and_rebuild_match ())))

let (plugins :
  (primitive_step -> unit,unit -> primitive_step Prims.list)
    FStar_Pervasives_Native.tuple2)
  =
  let plugins = FStar_Util.mk_ref []  in
  let register p =
    let uu____26901 =
      let uu____26904 = FStar_ST.op_Bang plugins  in p :: uu____26904  in
    FStar_ST.op_Colon_Equals plugins uu____26901  in
  let retrieve uu____27012 = FStar_ST.op_Bang plugins  in
  (register, retrieve) 
let (register_plugin : primitive_step -> unit) =
  fun p  -> FStar_Pervasives_Native.fst plugins p 
let (retrieve_plugins : unit -> primitive_step Prims.list) =
  fun uu____27089  -> FStar_Pervasives_Native.snd plugins () 
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
               (fun uu___256_27130  ->
                  match uu___256_27130 with
                  | FStar_TypeChecker_Env.UnfoldUntil k ->
                      [FStar_TypeChecker_Env.Unfold k]
                  | FStar_TypeChecker_Env.Eager_unfolding  ->
                      [FStar_TypeChecker_Env.Eager_unfolding_only]
                  | FStar_TypeChecker_Env.Inlining  ->
                      [FStar_TypeChecker_Env.InliningDelta]
                  | FStar_TypeChecker_Env.UnfoldTac  ->
                      [FStar_TypeChecker_Env.UnfoldTacDelta]
                  | uu____27134 -> []))
           in
        let d1 =
          match d with
          | [] -> [FStar_TypeChecker_Env.NoDelta]
          | uu____27140 -> d  in
        let uu____27143 = to_fsteps s  in
        let uu____27144 =
          let uu____27145 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Norm")  in
          let uu____27146 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Primops")  in
          let uu____27147 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Unfolding")
             in
          let uu____27148 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "380")  in
          let uu____27149 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "WPE")  in
          let uu____27150 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "NormDelayed")
             in
          let uu____27151 =
            FStar_TypeChecker_Env.debug e
              (FStar_Options.Other "print_normalized_terms")
             in
          {
            gen = uu____27145;
            primop = uu____27146;
            unfolding = uu____27147;
            b380 = uu____27148;
            wpe = uu____27149;
            norm_delayed = uu____27150;
            print_normalized = uu____27151
          }  in
        let uu____27152 =
          let uu____27155 =
            let uu____27158 = retrieve_plugins ()  in
            FStar_List.append uu____27158 psteps  in
          add_steps built_in_primitive_steps uu____27155  in
        let uu____27161 =
          (FStar_Options.normalize_pure_terms_for_extraction ()) ||
            (let uu____27163 =
               FStar_All.pipe_right s
                 (FStar_List.contains
                    FStar_TypeChecker_Env.PureSubtermsWithinComputations)
                in
             Prims.op_Negation uu____27163)
           in
        {
          steps = uu____27143;
          tcenv = e;
          debug = uu____27144;
          delta_level = d1;
          primitive_steps = uu____27152;
          strong = false;
          memoize_lazy = true;
          normalize_pure_lets = uu____27161
        }
  
let (config :
  FStar_TypeChecker_Env.step Prims.list -> FStar_TypeChecker_Env.env -> cfg)
  = fun s  -> fun e  -> config' [] s e 
let (normalize_with_primitive_steps :
  primitive_step Prims.list ->
    FStar_TypeChecker_Env.steps ->
      FStar_TypeChecker_Env.env ->
        FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun ps  ->
    fun s  -> fun e  -> fun t  -> let c = config' ps s e  in norm c [] [] t
  
let (normalize :
  FStar_TypeChecker_Env.steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  = fun s  -> fun e  -> fun t  -> normalize_with_primitive_steps [] s e t 
let (normalize_comp :
  FStar_TypeChecker_Env.steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun s  ->
    fun e  ->
      fun t  -> let uu____27241 = config s e  in norm_comp uu____27241 [] t
  
let (normalize_universe :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun u  ->
      let uu____27258 = config [] env  in norm_universe uu____27258 [] u
  
let (ghost_to_pure :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun env  ->
    fun c  ->
      let cfg =
        config
          [FStar_TypeChecker_Env.UnfoldUntil
             FStar_Syntax_Syntax.delta_constant;
          FStar_TypeChecker_Env.AllowUnboundUniverses;
          FStar_TypeChecker_Env.EraseUniverses] env
         in
      let non_info t =
        let uu____27282 = norm cfg [] [] t  in
        FStar_Syntax_Util.non_informative uu____27282  in
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____27289 -> c
      | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
          let uu___360_27308 = c  in
          {
            FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
            FStar_Syntax_Syntax.pos =
              (uu___360_27308.FStar_Syntax_Syntax.pos);
            FStar_Syntax_Syntax.vars =
              (uu___360_27308.FStar_Syntax_Syntax.vars)
          }
      | FStar_Syntax_Syntax.Comp ct ->
          let l =
            FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
              ct.FStar_Syntax_Syntax.effect_name
             in
          let uu____27315 =
            (FStar_Syntax_Util.is_ghost_effect l) &&
              (non_info ct.FStar_Syntax_Syntax.result_typ)
             in
          if uu____27315
          then
            let ct1 =
              let uu____27317 =
                downgrade_ghost_effect_name
                  ct.FStar_Syntax_Syntax.effect_name
                 in
              match uu____27317 with
              | FStar_Pervasives_Native.Some pure_eff ->
                  let flags1 =
                    let uu____27324 =
                      FStar_Ident.lid_equals pure_eff
                        FStar_Parser_Const.effect_Tot_lid
                       in
                    if uu____27324
                    then FStar_Syntax_Syntax.TOTAL ::
                      (ct.FStar_Syntax_Syntax.flags)
                    else ct.FStar_Syntax_Syntax.flags  in
                  let uu___361_27328 = ct  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___361_27328.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name = pure_eff;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___361_27328.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___361_27328.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags = flags1
                  }
              | FStar_Pervasives_Native.None  ->
                  let ct1 =
                    FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c
                     in
                  let uu___362_27330 = ct1  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___362_27330.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name =
                      FStar_Parser_Const.effect_PURE_lid;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___362_27330.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___362_27330.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags =
                      (uu___362_27330.FStar_Syntax_Syntax.flags)
                  }
               in
            let uu___363_27331 = c  in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
              FStar_Syntax_Syntax.pos =
                (uu___363_27331.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___363_27331.FStar_Syntax_Syntax.vars)
            }
          else c
      | uu____27333 -> c
  
let (ghost_to_pure_lcomp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.lcomp -> FStar_Syntax_Syntax.lcomp)
  =
  fun env  ->
    fun lc  ->
      let cfg =
        config
          [FStar_TypeChecker_Env.Eager_unfolding;
          FStar_TypeChecker_Env.UnfoldUntil
            FStar_Syntax_Syntax.delta_constant;
          FStar_TypeChecker_Env.EraseUniverses;
          FStar_TypeChecker_Env.AllowUnboundUniverses] env
         in
      let non_info t =
        let uu____27351 = norm cfg [] [] t  in
        FStar_Syntax_Util.non_informative uu____27351  in
      let uu____27358 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ)
         in
      if uu____27358
      then
        let uu____27359 =
          downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name  in
        match uu____27359 with
        | FStar_Pervasives_Native.Some pure_eff ->
            FStar_Syntax_Syntax.mk_lcomp pure_eff
              lc.FStar_Syntax_Syntax.res_typ lc.FStar_Syntax_Syntax.cflags
              (fun uu____27365  ->
                 let uu____27366 = FStar_Syntax_Syntax.lcomp_comp lc  in
                 ghost_to_pure env uu____27366)
        | FStar_Pervasives_Native.None  -> lc
      else lc
  
let (term_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.string) =
  fun env  ->
    fun t  ->
      let t1 =
        try normalize [FStar_TypeChecker_Env.AllowUnboundUniverses] env t
        with
        | e ->
            ((let uu____27387 =
                let uu____27392 =
                  let uu____27393 = FStar_Util.message_of_exn e  in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____27393
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____27392)  in
              FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____27387);
             t)
         in
      FStar_Syntax_Print.term_to_string' env.FStar_TypeChecker_Env.dsenv t1
  
let (comp_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string) =
  fun env  ->
    fun c  ->
      let c1 =
        try
          let uu____27408 =
            config [FStar_TypeChecker_Env.AllowUnboundUniverses] env  in
          norm_comp uu____27408 [] c
        with
        | e ->
            ((let uu____27421 =
                let uu____27426 =
                  let uu____27427 = FStar_Util.message_of_exn e  in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____27427
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____27426)  in
              FStar_Errors.log_issue c.FStar_Syntax_Syntax.pos uu____27421);
             c)
         in
      FStar_Syntax_Print.comp_to_string' env.FStar_TypeChecker_Env.dsenv c1
  
let (normalize_refinement :
  FStar_TypeChecker_Env.steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ)
  =
  fun steps  ->
    fun env  ->
      fun t0  ->
        let t =
          normalize (FStar_List.append steps [FStar_TypeChecker_Env.Beta])
            env t0
           in
        let rec aux t1 =
          let t2 = FStar_Syntax_Subst.compress t1  in
          match t2.FStar_Syntax_Syntax.n with
          | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
              let t01 = aux x.FStar_Syntax_Syntax.sort  in
              (match t01.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_refine (y,phi1) ->
                   let uu____27472 =
                     let uu____27473 =
                       let uu____27480 =
                         FStar_Syntax_Util.mk_conj_simp phi1 phi  in
                       (y, uu____27480)  in
                     FStar_Syntax_Syntax.Tm_refine uu____27473  in
                   mk uu____27472 t01.FStar_Syntax_Syntax.pos
               | uu____27485 -> t2)
          | uu____27486 -> t2  in
        aux t
  
let (unfold_whnf :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      normalize
        [FStar_TypeChecker_Env.Primops;
        FStar_TypeChecker_Env.Weak;
        FStar_TypeChecker_Env.HNF;
        FStar_TypeChecker_Env.UnfoldUntil FStar_Syntax_Syntax.delta_constant;
        FStar_TypeChecker_Env.Beta] env t
  
let (reduce_or_remove_uvar_solutions :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun remove  ->
    fun env  ->
      fun t  ->
        normalize
          (FStar_List.append
             (if remove then [FStar_TypeChecker_Env.CheckNoUvars] else [])
             [FStar_TypeChecker_Env.Beta;
             FStar_TypeChecker_Env.DoNotUnfoldPureLets;
             FStar_TypeChecker_Env.CompressUvars;
             FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Zeta;
             FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Iota;
             FStar_TypeChecker_Env.NoFullNorm]) env t
  
let (reduce_uvar_solutions :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  = fun env  -> fun t  -> reduce_or_remove_uvar_solutions false env t 
let (remove_uvar_solutions :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  = fun env  -> fun t  -> reduce_or_remove_uvar_solutions true env t 
let (eta_expand_with_type :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun e  ->
      fun t_e  ->
        let uu____27550 = FStar_Syntax_Util.arrow_formals_comp t_e  in
        match uu____27550 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____27579 ->
                 let uu____27586 = FStar_Syntax_Util.abs_formals e  in
                 (match uu____27586 with
                  | (actuals,uu____27596,uu____27597) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____27611 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders
                            in
                         match uu____27611 with
                         | (binders,args) ->
                             let uu____27622 =
                               FStar_Syntax_Syntax.mk_Tm_app e args
                                 FStar_Pervasives_Native.None
                                 e.FStar_Syntax_Syntax.pos
                                in
                             FStar_Syntax_Util.abs binders uu____27622
                               (FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.residual_comp_of_comp c)))))
  
let (eta_expand :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_name x ->
          eta_expand_with_type env t x.FStar_Syntax_Syntax.sort
      | uu____27636 ->
          let uu____27637 = FStar_Syntax_Util.head_and_args t  in
          (match uu____27637 with
           | (head1,args) ->
               let uu____27674 =
                 let uu____27675 = FStar_Syntax_Subst.compress head1  in
                 uu____27675.FStar_Syntax_Syntax.n  in
               (match uu____27674 with
                | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
                    let uu____27696 =
                      let uu____27709 =
                        FStar_Syntax_Subst.subst' s
                          u.FStar_Syntax_Syntax.ctx_uvar_typ
                         in
                      FStar_Syntax_Util.arrow_formals uu____27709  in
                    (match uu____27696 with
                     | (formals,_tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____27739 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___368_27747 = env  in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___368_27747.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___368_27747.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___368_27747.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___368_27747.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_sig =
                                     (uu___368_27747.FStar_TypeChecker_Env.gamma_sig);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___368_27747.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___368_27747.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___368_27747.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___368_27747.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___368_27747.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___368_27747.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___368_27747.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___368_27747.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___368_27747.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___368_27747.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___368_27747.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___368_27747.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___368_27747.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___368_27747.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___368_27747.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___368_27747.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.uvar_subtyping =
                                     (uu___368_27747.FStar_TypeChecker_Env.uvar_subtyping);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___368_27747.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___368_27747.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___368_27747.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___368_27747.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                     =
                                     (uu___368_27747.FStar_TypeChecker_Env.qtbl_name_and_index);
                                   FStar_TypeChecker_Env.normalized_eff_names
                                     =
                                     (uu___368_27747.FStar_TypeChecker_Env.normalized_eff_names);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___368_27747.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth_hook =
                                     (uu___368_27747.FStar_TypeChecker_Env.synth_hook);
                                   FStar_TypeChecker_Env.splice =
                                     (uu___368_27747.FStar_TypeChecker_Env.splice);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___368_27747.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___368_27747.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___368_27747.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___368_27747.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.dep_graph =
                                     (uu___368_27747.FStar_TypeChecker_Env.dep_graph);
                                   FStar_TypeChecker_Env.nbe =
                                     (uu___368_27747.FStar_TypeChecker_Env.nbe)
                                 }) t
                               in
                            match uu____27739 with
                            | (uu____27748,ty,uu____27750) ->
                                eta_expand_with_type env t ty))
                | uu____27751 ->
                    let uu____27752 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___369_27760 = env  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___369_27760.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___369_27760.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___369_27760.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___369_27760.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_sig =
                             (uu___369_27760.FStar_TypeChecker_Env.gamma_sig);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___369_27760.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___369_27760.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___369_27760.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___369_27760.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___369_27760.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___369_27760.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___369_27760.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___369_27760.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___369_27760.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___369_27760.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___369_27760.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___369_27760.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___369_27760.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___369_27760.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.failhard =
                             (uu___369_27760.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___369_27760.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.uvar_subtyping =
                             (uu___369_27760.FStar_TypeChecker_Env.uvar_subtyping);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___369_27760.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___369_27760.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___369_27760.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___369_27760.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qtbl_name_and_index =
                             (uu___369_27760.FStar_TypeChecker_Env.qtbl_name_and_index);
                           FStar_TypeChecker_Env.normalized_eff_names =
                             (uu___369_27760.FStar_TypeChecker_Env.normalized_eff_names);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___369_27760.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth_hook =
                             (uu___369_27760.FStar_TypeChecker_Env.synth_hook);
                           FStar_TypeChecker_Env.splice =
                             (uu___369_27760.FStar_TypeChecker_Env.splice);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___369_27760.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___369_27760.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___369_27760.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___369_27760.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.dep_graph =
                             (uu___369_27760.FStar_TypeChecker_Env.dep_graph);
                           FStar_TypeChecker_Env.nbe =
                             (uu___369_27760.FStar_TypeChecker_Env.nbe)
                         }) t
                       in
                    (match uu____27752 with
                     | (uu____27761,ty,uu____27763) ->
                         eta_expand_with_type env t ty)))
  
let rec (elim_delayed_subst_term :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let mk1 x =
      FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
        t.FStar_Syntax_Syntax.pos
       in
    let t1 = FStar_Syntax_Subst.compress t  in
    let elim_bv x =
      let uu___370_27836 = x  in
      let uu____27837 = elim_delayed_subst_term x.FStar_Syntax_Syntax.sort
         in
      {
        FStar_Syntax_Syntax.ppname =
          (uu___370_27836.FStar_Syntax_Syntax.ppname);
        FStar_Syntax_Syntax.index =
          (uu___370_27836.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = uu____27837
      }  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____27840 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_bvar uu____27863 -> t1
    | FStar_Syntax_Syntax.Tm_name uu____27864 -> t1
    | FStar_Syntax_Syntax.Tm_fvar uu____27865 -> t1
    | FStar_Syntax_Syntax.Tm_uinst uu____27866 -> t1
    | FStar_Syntax_Syntax.Tm_constant uu____27873 -> t1
    | FStar_Syntax_Syntax.Tm_type uu____27874 -> t1
    | FStar_Syntax_Syntax.Tm_lazy uu____27875 -> t1
    | FStar_Syntax_Syntax.Tm_unknown  -> t1
    | FStar_Syntax_Syntax.Tm_abs (bs,t2,rc_opt) ->
        let elim_rc rc =
          let uu___371_27905 = rc  in
          let uu____27906 =
            FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
              elim_delayed_subst_term
             in
          let uu____27915 =
            elim_delayed_subst_cflags rc.FStar_Syntax_Syntax.residual_flags
             in
          {
            FStar_Syntax_Syntax.residual_effect =
              (uu___371_27905.FStar_Syntax_Syntax.residual_effect);
            FStar_Syntax_Syntax.residual_typ = uu____27906;
            FStar_Syntax_Syntax.residual_flags = uu____27915
          }  in
        let uu____27918 =
          let uu____27919 =
            let uu____27936 = elim_delayed_subst_binders bs  in
            let uu____27943 = elim_delayed_subst_term t2  in
            let uu____27946 = FStar_Util.map_opt rc_opt elim_rc  in
            (uu____27936, uu____27943, uu____27946)  in
          FStar_Syntax_Syntax.Tm_abs uu____27919  in
        mk1 uu____27918
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____27977 =
          let uu____27978 =
            let uu____27991 = elim_delayed_subst_binders bs  in
            let uu____27998 = elim_delayed_subst_comp c  in
            (uu____27991, uu____27998)  in
          FStar_Syntax_Syntax.Tm_arrow uu____27978  in
        mk1 uu____27977
    | FStar_Syntax_Syntax.Tm_refine (bv,phi) ->
        let uu____28015 =
          let uu____28016 =
            let uu____28023 = elim_bv bv  in
            let uu____28024 = elim_delayed_subst_term phi  in
            (uu____28023, uu____28024)  in
          FStar_Syntax_Syntax.Tm_refine uu____28016  in
        mk1 uu____28015
    | FStar_Syntax_Syntax.Tm_app (t2,args) ->
        let uu____28051 =
          let uu____28052 =
            let uu____28067 = elim_delayed_subst_term t2  in
            let uu____28070 = elim_delayed_subst_args args  in
            (uu____28067, uu____28070)  in
          FStar_Syntax_Syntax.Tm_app uu____28052  in
        mk1 uu____28051
    | FStar_Syntax_Syntax.Tm_match (t2,branches) ->
        let rec elim_pat p =
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_var x ->
              let uu___372_28138 = p  in
              let uu____28139 =
                let uu____28140 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_var uu____28140  in
              {
                FStar_Syntax_Syntax.v = uu____28139;
                FStar_Syntax_Syntax.p =
                  (uu___372_28138.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_wild x ->
              let uu___373_28142 = p  in
              let uu____28143 =
                let uu____28144 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_wild uu____28144  in
              {
                FStar_Syntax_Syntax.v = uu____28143;
                FStar_Syntax_Syntax.p =
                  (uu___373_28142.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
              let uu___374_28151 = p  in
              let uu____28152 =
                let uu____28153 =
                  let uu____28160 = elim_bv x  in
                  let uu____28161 = elim_delayed_subst_term t0  in
                  (uu____28160, uu____28161)  in
                FStar_Syntax_Syntax.Pat_dot_term uu____28153  in
              {
                FStar_Syntax_Syntax.v = uu____28152;
                FStar_Syntax_Syntax.p =
                  (uu___374_28151.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
              let uu___375_28184 = p  in
              let uu____28185 =
                let uu____28186 =
                  let uu____28199 =
                    FStar_List.map
                      (fun uu____28222  ->
                         match uu____28222 with
                         | (x,b) ->
                             let uu____28235 = elim_pat x  in
                             (uu____28235, b)) pats
                     in
                  (fv, uu____28199)  in
                FStar_Syntax_Syntax.Pat_cons uu____28186  in
              {
                FStar_Syntax_Syntax.v = uu____28185;
                FStar_Syntax_Syntax.p =
                  (uu___375_28184.FStar_Syntax_Syntax.p)
              }
          | uu____28248 -> p  in
        let elim_branch uu____28272 =
          match uu____28272 with
          | (pat,wopt,t3) ->
              let uu____28298 = elim_pat pat  in
              let uu____28301 =
                FStar_Util.map_opt wopt elim_delayed_subst_term  in
              let uu____28304 = elim_delayed_subst_term t3  in
              (uu____28298, uu____28301, uu____28304)
           in
        let uu____28309 =
          let uu____28310 =
            let uu____28333 = elim_delayed_subst_term t2  in
            let uu____28336 = FStar_List.map elim_branch branches  in
            (uu____28333, uu____28336)  in
          FStar_Syntax_Syntax.Tm_match uu____28310  in
        mk1 uu____28309
    | FStar_Syntax_Syntax.Tm_ascribed (t2,a,lopt) ->
        let elim_ascription uu____28467 =
          match uu____28467 with
          | (tc,topt) ->
              let uu____28502 =
                match tc with
                | FStar_Util.Inl t3 ->
                    let uu____28512 = elim_delayed_subst_term t3  in
                    FStar_Util.Inl uu____28512
                | FStar_Util.Inr c ->
                    let uu____28514 = elim_delayed_subst_comp c  in
                    FStar_Util.Inr uu____28514
                 in
              let uu____28515 =
                FStar_Util.map_opt topt elim_delayed_subst_term  in
              (uu____28502, uu____28515)
           in
        let uu____28524 =
          let uu____28525 =
            let uu____28552 = elim_delayed_subst_term t2  in
            let uu____28555 = elim_ascription a  in
            (uu____28552, uu____28555, lopt)  in
          FStar_Syntax_Syntax.Tm_ascribed uu____28525  in
        mk1 uu____28524
    | FStar_Syntax_Syntax.Tm_let (lbs,t2) ->
        let elim_lb lb =
          let uu___376_28616 = lb  in
          let uu____28617 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbtyp  in
          let uu____28620 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbdef  in
          {
            FStar_Syntax_Syntax.lbname =
              (uu___376_28616.FStar_Syntax_Syntax.lbname);
            FStar_Syntax_Syntax.lbunivs =
              (uu___376_28616.FStar_Syntax_Syntax.lbunivs);
            FStar_Syntax_Syntax.lbtyp = uu____28617;
            FStar_Syntax_Syntax.lbeff =
              (uu___376_28616.FStar_Syntax_Syntax.lbeff);
            FStar_Syntax_Syntax.lbdef = uu____28620;
            FStar_Syntax_Syntax.lbattrs =
              (uu___376_28616.FStar_Syntax_Syntax.lbattrs);
            FStar_Syntax_Syntax.lbpos =
              (uu___376_28616.FStar_Syntax_Syntax.lbpos)
          }  in
        let uu____28623 =
          let uu____28624 =
            let uu____28637 =
              let uu____28644 =
                FStar_List.map elim_lb (FStar_Pervasives_Native.snd lbs)  in
              ((FStar_Pervasives_Native.fst lbs), uu____28644)  in
            let uu____28653 = elim_delayed_subst_term t2  in
            (uu____28637, uu____28653)  in
          FStar_Syntax_Syntax.Tm_let uu____28624  in
        mk1 uu____28623
    | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
        mk1 (FStar_Syntax_Syntax.Tm_uvar (u, s))
    | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
        let qi1 =
          FStar_Syntax_Syntax.on_antiquoted elim_delayed_subst_term qi  in
        let uu____28697 =
          let uu____28698 =
            let uu____28705 = elim_delayed_subst_term tm  in
            (uu____28705, qi1)  in
          FStar_Syntax_Syntax.Tm_quoted uu____28698  in
        mk1 uu____28697
    | FStar_Syntax_Syntax.Tm_meta (t2,md) ->
        let uu____28716 =
          let uu____28717 =
            let uu____28724 = elim_delayed_subst_term t2  in
            let uu____28727 = elim_delayed_subst_meta md  in
            (uu____28724, uu____28727)  in
          FStar_Syntax_Syntax.Tm_meta uu____28717  in
        mk1 uu____28716

and (elim_delayed_subst_cflags :
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun flags1  ->
    FStar_List.map
      (fun uu___257_28736  ->
         match uu___257_28736 with
         | FStar_Syntax_Syntax.DECREASES t ->
             let uu____28740 = elim_delayed_subst_term t  in
             FStar_Syntax_Syntax.DECREASES uu____28740
         | f -> f) flags1

and (elim_delayed_subst_comp :
  FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp) =
  fun c  ->
    let mk1 x =
      FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
        c.FStar_Syntax_Syntax.pos
       in
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uopt) ->
        let uu____28763 =
          let uu____28764 =
            let uu____28773 = elim_delayed_subst_term t  in
            (uu____28773, uopt)  in
          FStar_Syntax_Syntax.Total uu____28764  in
        mk1 uu____28763
    | FStar_Syntax_Syntax.GTotal (t,uopt) ->
        let uu____28790 =
          let uu____28791 =
            let uu____28800 = elim_delayed_subst_term t  in
            (uu____28800, uopt)  in
          FStar_Syntax_Syntax.GTotal uu____28791  in
        mk1 uu____28790
    | FStar_Syntax_Syntax.Comp ct ->
        let ct1 =
          let uu___377_28809 = ct  in
          let uu____28810 =
            elim_delayed_subst_term ct.FStar_Syntax_Syntax.result_typ  in
          let uu____28813 =
            elim_delayed_subst_args ct.FStar_Syntax_Syntax.effect_args  in
          let uu____28822 =
            elim_delayed_subst_cflags ct.FStar_Syntax_Syntax.flags  in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___377_28809.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___377_28809.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ = uu____28810;
            FStar_Syntax_Syntax.effect_args = uu____28813;
            FStar_Syntax_Syntax.flags = uu____28822
          }  in
        mk1 (FStar_Syntax_Syntax.Comp ct1)

and (elim_delayed_subst_meta :
  FStar_Syntax_Syntax.metadata -> FStar_Syntax_Syntax.metadata) =
  fun uu___258_28825  ->
    match uu___258_28825 with
    | FStar_Syntax_Syntax.Meta_pattern args ->
        let uu____28837 = FStar_List.map elim_delayed_subst_args args  in
        FStar_Syntax_Syntax.Meta_pattern uu____28837
    | FStar_Syntax_Syntax.Meta_monadic (m,t) ->
        let uu____28870 =
          let uu____28877 = elim_delayed_subst_term t  in (m, uu____28877)
           in
        FStar_Syntax_Syntax.Meta_monadic uu____28870
    | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,t) ->
        let uu____28889 =
          let uu____28898 = elim_delayed_subst_term t  in
          (m1, m2, uu____28898)  in
        FStar_Syntax_Syntax.Meta_monadic_lift uu____28889
    | m -> m

and (elim_delayed_subst_args :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun args  ->
    FStar_List.map
      (fun uu____28925  ->
         match uu____28925 with
         | (t,q) ->
             let uu____28936 = elim_delayed_subst_term t  in (uu____28936, q))
      args

and (elim_delayed_subst_binders :
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun bs  ->
    FStar_List.map
      (fun uu____28956  ->
         match uu____28956 with
         | (x,q) ->
             let uu____28967 =
               let uu___378_28968 = x  in
               let uu____28969 =
                 elim_delayed_subst_term x.FStar_Syntax_Syntax.sort  in
               {
                 FStar_Syntax_Syntax.ppname =
                   (uu___378_28968.FStar_Syntax_Syntax.ppname);
                 FStar_Syntax_Syntax.index =
                   (uu___378_28968.FStar_Syntax_Syntax.index);
                 FStar_Syntax_Syntax.sort = uu____28969
               }  in
             (uu____28967, q)) bs

let (elim_uvars_aux_tc :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.univ_names ->
      FStar_Syntax_Syntax.binders ->
        (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.comp) FStar_Util.either
          ->
          (FStar_Syntax_Syntax.univ_names,(FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
                                            FStar_Pervasives_Native.tuple2
                                            Prims.list,(FStar_Syntax_Syntax.term'
                                                          FStar_Syntax_Syntax.syntax,
                                                         FStar_Syntax_Syntax.comp'
                                                           FStar_Syntax_Syntax.syntax)
                                                         FStar_Util.either)
            FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun univ_names  ->
      fun binders  ->
        fun tc  ->
          let t =
            match (binders, tc) with
            | ([],FStar_Util.Inl t) -> t
            | ([],FStar_Util.Inr c) ->
                failwith "Impossible: empty bindes with a comp"
            | (uu____29061,FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c))
                  FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
            | (uu____29087,FStar_Util.Inl t) ->
                let uu____29105 =
                  let uu____29112 =
                    let uu____29113 =
                      let uu____29126 = FStar_Syntax_Syntax.mk_Total t  in
                      (binders, uu____29126)  in
                    FStar_Syntax_Syntax.Tm_arrow uu____29113  in
                  FStar_Syntax_Syntax.mk uu____29112  in
                uu____29105 FStar_Pervasives_Native.None
                  t.FStar_Syntax_Syntax.pos
             in
          let uu____29140 = FStar_Syntax_Subst.open_univ_vars univ_names t
             in
          match uu____29140 with
          | (univ_names1,t1) ->
              let t2 = remove_uvar_solutions env t1  in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2  in
              let t4 = elim_delayed_subst_term t3  in
              let uu____29170 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t4))
                | uu____29233 ->
                    let uu____29234 =
                      let uu____29243 =
                        let uu____29244 = FStar_Syntax_Subst.compress t4  in
                        uu____29244.FStar_Syntax_Syntax.n  in
                      (uu____29243, tc)  in
                    (match uu____29234 with
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inr uu____29271) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inl uu____29312) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____29351,FStar_Util.Inl uu____29352) ->
                         ([], (FStar_Util.Inl t4))
                     | uu____29379 -> failwith "Impossible")
                 in
              (match uu____29170 with
               | (binders1,tc1) -> (univ_names1, binders1, tc1))
  
let (elim_uvars_aux_t :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.univ_names ->
      FStar_Syntax_Syntax.binders ->
        FStar_Syntax_Syntax.typ ->
          (FStar_Syntax_Syntax.univ_names,(FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
                                            FStar_Pervasives_Native.tuple2
                                            Prims.list,FStar_Syntax_Syntax.term'
                                                         FStar_Syntax_Syntax.syntax)
            FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun univ_names  ->
      fun binders  ->
        fun t  ->
          let uu____29504 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl t)  in
          match uu____29504 with
          | (univ_names1,binders1,tc) ->
              let uu____29570 = FStar_Util.left tc  in
              (univ_names1, binders1, uu____29570)
  
let (elim_uvars_aux_c :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.univ_names ->
      FStar_Syntax_Syntax.binders ->
        FStar_Syntax_Syntax.comp ->
          (FStar_Syntax_Syntax.univ_names,(FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
                                            FStar_Pervasives_Native.tuple2
                                            Prims.list,FStar_Syntax_Syntax.comp'
                                                         FStar_Syntax_Syntax.syntax)
            FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun univ_names  ->
      fun binders  ->
        fun c  ->
          let uu____29619 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr c)  in
          match uu____29619 with
          | (univ_names1,binders1,tc) ->
              let uu____29685 = FStar_Util.right tc  in
              (univ_names1, binders1, uu____29685)
  
let rec (elim_uvars :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt)
  =
  fun env  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univ_names,binders,typ,lids,lids') ->
          let uu____29724 = elim_uvars_aux_t env univ_names binders typ  in
          (match uu____29724 with
           | (univ_names1,binders1,typ1) ->
               let uu___379_29758 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___379_29758.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___379_29758.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___379_29758.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___379_29758.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
          let uu___380_29773 = s  in
          let uu____29774 =
            let uu____29775 =
              let uu____29784 = FStar_List.map (elim_uvars env) sigs  in
              (uu____29784, lids)  in
            FStar_Syntax_Syntax.Sig_bundle uu____29775  in
          {
            FStar_Syntax_Syntax.sigel = uu____29774;
            FStar_Syntax_Syntax.sigrng =
              (uu___380_29773.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___380_29773.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___380_29773.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___380_29773.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_datacon (lid,univ_names,typ,lident,i,lids) ->
          let uu____29801 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____29801 with
           | (univ_names1,uu____29821,typ1) ->
               let uu___381_29839 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___381_29839.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___381_29839.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___381_29839.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___381_29839.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univ_names,typ) ->
          let uu____29845 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____29845 with
           | (univ_names1,uu____29865,typ1) ->
               let uu___382_29883 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___382_29883.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___382_29883.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___382_29883.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___382_29883.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____29911 =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs
                       in
                    match uu____29911 with
                    | (opening,lbunivs) ->
                        let elim t =
                          let uu____29936 =
                            let uu____29937 =
                              let uu____29938 =
                                FStar_Syntax_Subst.subst opening t  in
                              remove_uvar_solutions env uu____29938  in
                            FStar_Syntax_Subst.close_univ_vars lbunivs
                              uu____29937
                             in
                          elim_delayed_subst_term uu____29936  in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp  in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef  in
                        let uu___383_29941 = lb  in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___383_29941.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___383_29941.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___383_29941.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___383_29941.FStar_Syntax_Syntax.lbpos)
                        }))
             in
          let uu___384_29942 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids));
            FStar_Syntax_Syntax.sigrng =
              (uu___384_29942.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___384_29942.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___384_29942.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___384_29942.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_main t ->
          let uu___385_29948 = s  in
          let uu____29949 =
            let uu____29950 = remove_uvar_solutions env t  in
            FStar_Syntax_Syntax.Sig_main uu____29950  in
          {
            FStar_Syntax_Syntax.sigel = uu____29949;
            FStar_Syntax_Syntax.sigrng =
              (uu___385_29948.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___385_29948.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___385_29948.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___385_29948.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_assume (l,us,t) ->
          let uu____29954 = elim_uvars_aux_t env us [] t  in
          (match uu____29954 with
           | (us1,uu____29974,t1) ->
               let uu___386_29992 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___386_29992.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___386_29992.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___386_29992.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___386_29992.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____29993 ->
          failwith "Impossible: should have been desugared already"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____29995 =
            elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature
             in
          (match uu____29995 with
           | (univs1,binders,signature) ->
               let uu____30029 =
                 let uu____30034 = FStar_Syntax_Subst.univ_var_opening univs1
                    in
                 match uu____30034 with
                 | (univs_opening,univs2) ->
                     let uu____30057 =
                       FStar_Syntax_Subst.univ_var_closing univs2  in
                     (univs_opening, uu____30057)
                  in
               (match uu____30029 with
                | (univs_opening,univs_closing) ->
                    let uu____30060 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders
                         in
                      let uu____30066 =
                        FStar_Syntax_Subst.opening_of_binders binders1  in
                      let uu____30067 =
                        FStar_Syntax_Subst.closing_of_binders binders1  in
                      (uu____30066, uu____30067)  in
                    (match uu____30060 with
                     | (b_opening,b_closing) ->
                         let n1 = FStar_List.length univs1  in
                         let n_binders = FStar_List.length binders  in
                         let elim_tscheme uu____30091 =
                           match uu____30091 with
                           | (us,t) ->
                               let n_us = FStar_List.length us  in
                               let uu____30109 =
                                 FStar_Syntax_Subst.open_univ_vars us t  in
                               (match uu____30109 with
                                | (us1,t1) ->
                                    let uu____30120 =
                                      let uu____30129 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      let uu____30140 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      (uu____30129, uu____30140)  in
                                    (match uu____30120 with
                                     | (b_opening1,b_closing1) ->
                                         let uu____30169 =
                                           let uu____30178 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us)
                                              in
                                           let uu____30189 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us)
                                              in
                                           (uu____30178, uu____30189)  in
                                         (match uu____30169 with
                                          | (univs_opening1,univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____30219 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1
                                                   in
                                                FStar_Syntax_Subst.subst
                                                  univs_opening1 uu____30219
                                                 in
                                              let uu____30220 =
                                                elim_uvars_aux_t env [] [] t2
                                                 in
                                              (match uu____30220 with
                                               | (uu____30243,uu____30244,t3)
                                                   ->
                                                   let t4 =
                                                     let uu____30263 =
                                                       let uu____30264 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3
                                                          in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
                                                         uu____30264
                                                        in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____30263
                                                      in
                                                   (us1, t4)))))
                            in
                         let elim_term t =
                           let uu____30273 =
                             elim_uvars_aux_t env univs1 binders t  in
                           match uu____30273 with
                           | (uu____30290,uu____30291,t1) -> t1  in
                         let elim_action a =
                           let action_typ_templ =
                             let body =
                               FStar_Syntax_Syntax.mk
                                 (FStar_Syntax_Syntax.Tm_ascribed
                                    ((a.FStar_Syntax_Syntax.action_defn),
                                      ((FStar_Util.Inl
                                          (a.FStar_Syntax_Syntax.action_typ)),
                                        FStar_Pervasives_Native.None),
                                      FStar_Pervasives_Native.None))
                                 FStar_Pervasives_Native.None
                                 (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                                in
                             match a.FStar_Syntax_Syntax.action_params with
                             | [] -> body
                             | uu____30361 ->
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_abs
                                      ((a.FStar_Syntax_Syntax.action_params),
                                        body, FStar_Pervasives_Native.None))
                                   FStar_Pervasives_Native.None
                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                              in
                           let destruct_action_body body =
                             let uu____30386 =
                               let uu____30387 =
                                 FStar_Syntax_Subst.compress body  in
                               uu____30387.FStar_Syntax_Syntax.n  in
                             match uu____30386 with
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,(FStar_Util.Inl
                                        typ,FStar_Pervasives_Native.None ),FStar_Pervasives_Native.None
                                  )
                                 -> (defn, typ)
                             | uu____30446 -> failwith "Impossible"  in
                           let destruct_action_typ_templ t =
                             let uu____30477 =
                               let uu____30478 =
                                 FStar_Syntax_Subst.compress t  in
                               uu____30478.FStar_Syntax_Syntax.n  in
                             match uu____30477 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (pars,body,uu____30499) ->
                                 let uu____30520 = destruct_action_body body
                                    in
                                 (match uu____30520 with
                                  | (defn,typ) -> (pars, defn, typ))
                             | uu____30565 ->
                                 let uu____30566 = destruct_action_body t  in
                                 (match uu____30566 with
                                  | (defn,typ) -> ([], defn, typ))
                              in
                           let uu____30615 =
                             elim_tscheme
                               ((a.FStar_Syntax_Syntax.action_univs),
                                 action_typ_templ)
                              in
                           match uu____30615 with
                           | (action_univs,t) ->
                               let uu____30624 = destruct_action_typ_templ t
                                  in
                               (match uu____30624 with
                                | (action_params,action_defn,action_typ) ->
                                    let a' =
                                      let uu___387_30665 = a  in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___387_30665.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___387_30665.FStar_Syntax_Syntax.action_unqualified_name);
                                        FStar_Syntax_Syntax.action_univs =
                                          action_univs;
                                        FStar_Syntax_Syntax.action_params =
                                          action_params;
                                        FStar_Syntax_Syntax.action_defn =
                                          action_defn;
                                        FStar_Syntax_Syntax.action_typ =
                                          action_typ
                                      }  in
                                    a')
                            in
                         let ed1 =
                           let uu___388_30667 = ed  in
                           let uu____30668 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ret_wp  in
                           let uu____30669 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_wp  in
                           let uu____30670 =
                             elim_tscheme ed.FStar_Syntax_Syntax.if_then_else
                              in
                           let uu____30671 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ite_wp  in
                           let uu____30672 =
                             elim_tscheme ed.FStar_Syntax_Syntax.stronger  in
                           let uu____30673 =
                             elim_tscheme ed.FStar_Syntax_Syntax.close_wp  in
                           let uu____30674 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assert_p  in
                           let uu____30675 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assume_p  in
                           let uu____30676 =
                             elim_tscheme ed.FStar_Syntax_Syntax.null_wp  in
                           let uu____30677 =
                             elim_tscheme ed.FStar_Syntax_Syntax.trivial  in
                           let uu____30678 =
                             elim_term ed.FStar_Syntax_Syntax.repr  in
                           let uu____30679 =
                             elim_tscheme ed.FStar_Syntax_Syntax.return_repr
                              in
                           let uu____30680 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_repr
                              in
                           let uu____30681 =
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions
                              in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___388_30667.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___388_30667.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs = univs1;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp = uu____30668;
                             FStar_Syntax_Syntax.bind_wp = uu____30669;
                             FStar_Syntax_Syntax.if_then_else = uu____30670;
                             FStar_Syntax_Syntax.ite_wp = uu____30671;
                             FStar_Syntax_Syntax.stronger = uu____30672;
                             FStar_Syntax_Syntax.close_wp = uu____30673;
                             FStar_Syntax_Syntax.assert_p = uu____30674;
                             FStar_Syntax_Syntax.assume_p = uu____30675;
                             FStar_Syntax_Syntax.null_wp = uu____30676;
                             FStar_Syntax_Syntax.trivial = uu____30677;
                             FStar_Syntax_Syntax.repr = uu____30678;
                             FStar_Syntax_Syntax.return_repr = uu____30679;
                             FStar_Syntax_Syntax.bind_repr = uu____30680;
                             FStar_Syntax_Syntax.actions = uu____30681;
                             FStar_Syntax_Syntax.eff_attrs =
                               (uu___388_30667.FStar_Syntax_Syntax.eff_attrs)
                           }  in
                         let uu___389_30684 = s  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___389_30684.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___389_30684.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___389_30684.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___389_30684.FStar_Syntax_Syntax.sigattrs)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___259_30705 =
            match uu___259_30705 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (us,t) ->
                let uu____30736 = elim_uvars_aux_t env us [] t  in
                (match uu____30736 with
                 | (us1,uu____30764,t1) ->
                     FStar_Pervasives_Native.Some (us1, t1))
             in
          let sub_eff1 =
            let uu___390_30791 = sub_eff  in
            let uu____30792 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp  in
            let uu____30795 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift  in
            {
              FStar_Syntax_Syntax.source =
                (uu___390_30791.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___390_30791.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____30792;
              FStar_Syntax_Syntax.lift = uu____30795
            }  in
          let uu___391_30798 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___391_30798.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___391_30798.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___391_30798.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___391_30798.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,univ_names,binders,comp,flags1) ->
          let uu____30808 = elim_uvars_aux_c env univ_names binders comp  in
          (match uu____30808 with
           | (univ_names1,binders1,comp1) ->
               let uu___392_30842 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___392_30842.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___392_30842.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___392_30842.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___392_30842.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____30845 -> s
      | FStar_Syntax_Syntax.Sig_splice uu____30846 -> s
  
let (erase_universes :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      normalize
        [FStar_TypeChecker_Env.EraseUniverses;
        FStar_TypeChecker_Env.AllowUnboundUniverses] env t
  