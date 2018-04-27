open Prims
type step =
  | Beta 
  | Iota 
  | Zeta 
  | Exclude of step 
  | Weak 
  | HNF 
  | Primops 
  | Eager_unfolding 
  | Inlining 
  | DoNotUnfoldPureLets 
  | UnfoldUntil of FStar_Syntax_Syntax.delta_depth 
  | UnfoldOnly of FStar_Ident.lid Prims.list 
  | UnfoldFully of FStar_Ident.lid Prims.list 
  | UnfoldAttr of FStar_Syntax_Syntax.attribute 
  | UnfoldTac 
  | PureSubtermsWithinComputations 
  | Simplify 
  | EraseUniverses 
  | AllowUnboundUniverses 
  | Reify 
  | CompressUvars 
  | NoFullNorm 
  | CheckNoUvars 
  | Unmeta 
  | Unascribe [@@deriving show]
let (uu___is_Beta : step -> Prims.bool) =
  fun projectee  -> match projectee with | Beta  -> true | uu____35 -> false 
let (uu___is_Iota : step -> Prims.bool) =
  fun projectee  -> match projectee with | Iota  -> true | uu____41 -> false 
let (uu___is_Zeta : step -> Prims.bool) =
  fun projectee  -> match projectee with | Zeta  -> true | uu____47 -> false 
let (uu___is_Exclude : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Exclude _0 -> true | uu____54 -> false
  
let (__proj__Exclude__item___0 : step -> step) =
  fun projectee  -> match projectee with | Exclude _0 -> _0 
let (uu___is_Weak : step -> Prims.bool) =
  fun projectee  -> match projectee with | Weak  -> true | uu____67 -> false 
let (uu___is_HNF : step -> Prims.bool) =
  fun projectee  -> match projectee with | HNF  -> true | uu____73 -> false 
let (uu___is_Primops : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Primops  -> true | uu____79 -> false
  
let (uu___is_Eager_unfolding : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Eager_unfolding  -> true | uu____85 -> false
  
let (uu___is_Inlining : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Inlining  -> true | uu____91 -> false
  
let (uu___is_DoNotUnfoldPureLets : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | DoNotUnfoldPureLets  -> true | uu____97 -> false
  
let (uu___is_UnfoldUntil : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldUntil _0 -> true | uu____104 -> false
  
let (__proj__UnfoldUntil__item___0 : step -> FStar_Syntax_Syntax.delta_depth)
  = fun projectee  -> match projectee with | UnfoldUntil _0 -> _0 
let (uu___is_UnfoldOnly : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldOnly _0 -> true | uu____120 -> false
  
let (__proj__UnfoldOnly__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldOnly _0 -> _0 
let (uu___is_UnfoldFully : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldFully _0 -> true | uu____142 -> false
  
let (__proj__UnfoldFully__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldFully _0 -> _0 
let (uu___is_UnfoldAttr : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldAttr _0 -> true | uu____162 -> false
  
let (__proj__UnfoldAttr__item___0 : step -> FStar_Syntax_Syntax.attribute) =
  fun projectee  -> match projectee with | UnfoldAttr _0 -> _0 
let (uu___is_UnfoldTac : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldTac  -> true | uu____175 -> false
  
let (uu___is_PureSubtermsWithinComputations : step -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | PureSubtermsWithinComputations  -> true
    | uu____181 -> false
  
let (uu___is_Simplify : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Simplify  -> true | uu____187 -> false
  
let (uu___is_EraseUniverses : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | EraseUniverses  -> true | uu____193 -> false
  
let (uu___is_AllowUnboundUniverses : step -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | AllowUnboundUniverses  -> true
    | uu____199 -> false
  
let (uu___is_Reify : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reify  -> true | uu____205 -> false
  
let (uu___is_CompressUvars : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | CompressUvars  -> true | uu____211 -> false
  
let (uu___is_NoFullNorm : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoFullNorm  -> true | uu____217 -> false
  
let (uu___is_CheckNoUvars : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | CheckNoUvars  -> true | uu____223 -> false
  
let (uu___is_Unmeta : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unmeta  -> true | uu____229 -> false
  
let (uu___is_Unascribe : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unascribe  -> true | uu____235 -> false
  
type steps = step Prims.list[@@deriving show]
let cases :
  'Auu____248 'Auu____249 .
    ('Auu____248 -> 'Auu____249) ->
      'Auu____249 ->
        'Auu____248 FStar_Pervasives_Native.option -> 'Auu____249
  =
  fun f  ->
    fun d  ->
      fun uu___79_269  ->
        match uu___79_269 with
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
  weakly_reduce_scrutinee: Prims.bool }[@@deriving show]
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
        weakly_reduce_scrutinee = __fname__weakly_reduce_scrutinee;_} ->
        __fname__beta
  
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
        weakly_reduce_scrutinee = __fname__weakly_reduce_scrutinee;_} ->
        __fname__iota
  
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
        weakly_reduce_scrutinee = __fname__weakly_reduce_scrutinee;_} ->
        __fname__zeta
  
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
        weakly_reduce_scrutinee = __fname__weakly_reduce_scrutinee;_} ->
        __fname__weak
  
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
        weakly_reduce_scrutinee = __fname__weakly_reduce_scrutinee;_} ->
        __fname__hnf
  
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
        weakly_reduce_scrutinee = __fname__weakly_reduce_scrutinee;_} ->
        __fname__primops
  
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
        weakly_reduce_scrutinee = __fname__weakly_reduce_scrutinee;_} ->
        __fname__do_not_unfold_pure_lets
  
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
        weakly_reduce_scrutinee = __fname__weakly_reduce_scrutinee;_} ->
        __fname__unfold_until
  
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
        weakly_reduce_scrutinee = __fname__weakly_reduce_scrutinee;_} ->
        __fname__unfold_only
  
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
        weakly_reduce_scrutinee = __fname__weakly_reduce_scrutinee;_} ->
        __fname__unfold_fully
  
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
        weakly_reduce_scrutinee = __fname__weakly_reduce_scrutinee;_} ->
        __fname__unfold_attr
  
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
        weakly_reduce_scrutinee = __fname__weakly_reduce_scrutinee;_} ->
        __fname__unfold_tac
  
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
        weakly_reduce_scrutinee = __fname__weakly_reduce_scrutinee;_} ->
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
        weakly_reduce_scrutinee = __fname__weakly_reduce_scrutinee;_} ->
        __fname__simplify
  
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
        weakly_reduce_scrutinee = __fname__weakly_reduce_scrutinee;_} ->
        __fname__erase_universes
  
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
        weakly_reduce_scrutinee = __fname__weakly_reduce_scrutinee;_} ->
        __fname__allow_unbound_universes
  
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
        weakly_reduce_scrutinee = __fname__weakly_reduce_scrutinee;_} ->
        __fname__reify_
  
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
        weakly_reduce_scrutinee = __fname__weakly_reduce_scrutinee;_} ->
        __fname__compress_uvars
  
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
        weakly_reduce_scrutinee = __fname__weakly_reduce_scrutinee;_} ->
        __fname__no_full_norm
  
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
        weakly_reduce_scrutinee = __fname__weakly_reduce_scrutinee;_} ->
        __fname__check_no_uvars
  
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
        weakly_reduce_scrutinee = __fname__weakly_reduce_scrutinee;_} ->
        __fname__unmeta
  
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
        weakly_reduce_scrutinee = __fname__weakly_reduce_scrutinee;_} ->
        __fname__unascribe
  
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
        weakly_reduce_scrutinee = __fname__weakly_reduce_scrutinee;_} ->
        __fname__in_full_norm_request
  
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
        weakly_reduce_scrutinee = __fname__weakly_reduce_scrutinee;_} ->
        __fname__weakly_reduce_scrutinee
  
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
    weakly_reduce_scrutinee = true
  } 
let (fstep_add_one : step -> fsteps -> fsteps) =
  fun s  ->
    fun fs  ->
      let add_opt x uu___80_1503 =
        match uu___80_1503 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.Some [x]
        | FStar_Pervasives_Native.Some xs ->
            FStar_Pervasives_Native.Some (x :: xs)
         in
      match s with
      | Beta  ->
          let uu___98_1523 = fs  in
          {
            beta = true;
            iota = (uu___98_1523.iota);
            zeta = (uu___98_1523.zeta);
            weak = (uu___98_1523.weak);
            hnf = (uu___98_1523.hnf);
            primops = (uu___98_1523.primops);
            do_not_unfold_pure_lets = (uu___98_1523.do_not_unfold_pure_lets);
            unfold_until = (uu___98_1523.unfold_until);
            unfold_only = (uu___98_1523.unfold_only);
            unfold_fully = (uu___98_1523.unfold_fully);
            unfold_attr = (uu___98_1523.unfold_attr);
            unfold_tac = (uu___98_1523.unfold_tac);
            pure_subterms_within_computations =
              (uu___98_1523.pure_subterms_within_computations);
            simplify = (uu___98_1523.simplify);
            erase_universes = (uu___98_1523.erase_universes);
            allow_unbound_universes = (uu___98_1523.allow_unbound_universes);
            reify_ = (uu___98_1523.reify_);
            compress_uvars = (uu___98_1523.compress_uvars);
            no_full_norm = (uu___98_1523.no_full_norm);
            check_no_uvars = (uu___98_1523.check_no_uvars);
            unmeta = (uu___98_1523.unmeta);
            unascribe = (uu___98_1523.unascribe);
            in_full_norm_request = (uu___98_1523.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___98_1523.weakly_reduce_scrutinee)
          }
      | Iota  ->
          let uu___99_1524 = fs  in
          {
            beta = (uu___99_1524.beta);
            iota = true;
            zeta = (uu___99_1524.zeta);
            weak = (uu___99_1524.weak);
            hnf = (uu___99_1524.hnf);
            primops = (uu___99_1524.primops);
            do_not_unfold_pure_lets = (uu___99_1524.do_not_unfold_pure_lets);
            unfold_until = (uu___99_1524.unfold_until);
            unfold_only = (uu___99_1524.unfold_only);
            unfold_fully = (uu___99_1524.unfold_fully);
            unfold_attr = (uu___99_1524.unfold_attr);
            unfold_tac = (uu___99_1524.unfold_tac);
            pure_subterms_within_computations =
              (uu___99_1524.pure_subterms_within_computations);
            simplify = (uu___99_1524.simplify);
            erase_universes = (uu___99_1524.erase_universes);
            allow_unbound_universes = (uu___99_1524.allow_unbound_universes);
            reify_ = (uu___99_1524.reify_);
            compress_uvars = (uu___99_1524.compress_uvars);
            no_full_norm = (uu___99_1524.no_full_norm);
            check_no_uvars = (uu___99_1524.check_no_uvars);
            unmeta = (uu___99_1524.unmeta);
            unascribe = (uu___99_1524.unascribe);
            in_full_norm_request = (uu___99_1524.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___99_1524.weakly_reduce_scrutinee)
          }
      | Zeta  ->
          let uu___100_1525 = fs  in
          {
            beta = (uu___100_1525.beta);
            iota = (uu___100_1525.iota);
            zeta = true;
            weak = (uu___100_1525.weak);
            hnf = (uu___100_1525.hnf);
            primops = (uu___100_1525.primops);
            do_not_unfold_pure_lets = (uu___100_1525.do_not_unfold_pure_lets);
            unfold_until = (uu___100_1525.unfold_until);
            unfold_only = (uu___100_1525.unfold_only);
            unfold_fully = (uu___100_1525.unfold_fully);
            unfold_attr = (uu___100_1525.unfold_attr);
            unfold_tac = (uu___100_1525.unfold_tac);
            pure_subterms_within_computations =
              (uu___100_1525.pure_subterms_within_computations);
            simplify = (uu___100_1525.simplify);
            erase_universes = (uu___100_1525.erase_universes);
            allow_unbound_universes = (uu___100_1525.allow_unbound_universes);
            reify_ = (uu___100_1525.reify_);
            compress_uvars = (uu___100_1525.compress_uvars);
            no_full_norm = (uu___100_1525.no_full_norm);
            check_no_uvars = (uu___100_1525.check_no_uvars);
            unmeta = (uu___100_1525.unmeta);
            unascribe = (uu___100_1525.unascribe);
            in_full_norm_request = (uu___100_1525.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___100_1525.weakly_reduce_scrutinee)
          }
      | Exclude (Beta ) ->
          let uu___101_1526 = fs  in
          {
            beta = false;
            iota = (uu___101_1526.iota);
            zeta = (uu___101_1526.zeta);
            weak = (uu___101_1526.weak);
            hnf = (uu___101_1526.hnf);
            primops = (uu___101_1526.primops);
            do_not_unfold_pure_lets = (uu___101_1526.do_not_unfold_pure_lets);
            unfold_until = (uu___101_1526.unfold_until);
            unfold_only = (uu___101_1526.unfold_only);
            unfold_fully = (uu___101_1526.unfold_fully);
            unfold_attr = (uu___101_1526.unfold_attr);
            unfold_tac = (uu___101_1526.unfold_tac);
            pure_subterms_within_computations =
              (uu___101_1526.pure_subterms_within_computations);
            simplify = (uu___101_1526.simplify);
            erase_universes = (uu___101_1526.erase_universes);
            allow_unbound_universes = (uu___101_1526.allow_unbound_universes);
            reify_ = (uu___101_1526.reify_);
            compress_uvars = (uu___101_1526.compress_uvars);
            no_full_norm = (uu___101_1526.no_full_norm);
            check_no_uvars = (uu___101_1526.check_no_uvars);
            unmeta = (uu___101_1526.unmeta);
            unascribe = (uu___101_1526.unascribe);
            in_full_norm_request = (uu___101_1526.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___101_1526.weakly_reduce_scrutinee)
          }
      | Exclude (Iota ) ->
          let uu___102_1527 = fs  in
          {
            beta = (uu___102_1527.beta);
            iota = false;
            zeta = (uu___102_1527.zeta);
            weak = (uu___102_1527.weak);
            hnf = (uu___102_1527.hnf);
            primops = (uu___102_1527.primops);
            do_not_unfold_pure_lets = (uu___102_1527.do_not_unfold_pure_lets);
            unfold_until = (uu___102_1527.unfold_until);
            unfold_only = (uu___102_1527.unfold_only);
            unfold_fully = (uu___102_1527.unfold_fully);
            unfold_attr = (uu___102_1527.unfold_attr);
            unfold_tac = (uu___102_1527.unfold_tac);
            pure_subterms_within_computations =
              (uu___102_1527.pure_subterms_within_computations);
            simplify = (uu___102_1527.simplify);
            erase_universes = (uu___102_1527.erase_universes);
            allow_unbound_universes = (uu___102_1527.allow_unbound_universes);
            reify_ = (uu___102_1527.reify_);
            compress_uvars = (uu___102_1527.compress_uvars);
            no_full_norm = (uu___102_1527.no_full_norm);
            check_no_uvars = (uu___102_1527.check_no_uvars);
            unmeta = (uu___102_1527.unmeta);
            unascribe = (uu___102_1527.unascribe);
            in_full_norm_request = (uu___102_1527.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___102_1527.weakly_reduce_scrutinee)
          }
      | Exclude (Zeta ) ->
          let uu___103_1528 = fs  in
          {
            beta = (uu___103_1528.beta);
            iota = (uu___103_1528.iota);
            zeta = false;
            weak = (uu___103_1528.weak);
            hnf = (uu___103_1528.hnf);
            primops = (uu___103_1528.primops);
            do_not_unfold_pure_lets = (uu___103_1528.do_not_unfold_pure_lets);
            unfold_until = (uu___103_1528.unfold_until);
            unfold_only = (uu___103_1528.unfold_only);
            unfold_fully = (uu___103_1528.unfold_fully);
            unfold_attr = (uu___103_1528.unfold_attr);
            unfold_tac = (uu___103_1528.unfold_tac);
            pure_subterms_within_computations =
              (uu___103_1528.pure_subterms_within_computations);
            simplify = (uu___103_1528.simplify);
            erase_universes = (uu___103_1528.erase_universes);
            allow_unbound_universes = (uu___103_1528.allow_unbound_universes);
            reify_ = (uu___103_1528.reify_);
            compress_uvars = (uu___103_1528.compress_uvars);
            no_full_norm = (uu___103_1528.no_full_norm);
            check_no_uvars = (uu___103_1528.check_no_uvars);
            unmeta = (uu___103_1528.unmeta);
            unascribe = (uu___103_1528.unascribe);
            in_full_norm_request = (uu___103_1528.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___103_1528.weakly_reduce_scrutinee)
          }
      | Exclude uu____1529 -> failwith "Bad exclude"
      | Weak  ->
          let uu___104_1530 = fs  in
          {
            beta = (uu___104_1530.beta);
            iota = (uu___104_1530.iota);
            zeta = (uu___104_1530.zeta);
            weak = true;
            hnf = (uu___104_1530.hnf);
            primops = (uu___104_1530.primops);
            do_not_unfold_pure_lets = (uu___104_1530.do_not_unfold_pure_lets);
            unfold_until = (uu___104_1530.unfold_until);
            unfold_only = (uu___104_1530.unfold_only);
            unfold_fully = (uu___104_1530.unfold_fully);
            unfold_attr = (uu___104_1530.unfold_attr);
            unfold_tac = (uu___104_1530.unfold_tac);
            pure_subterms_within_computations =
              (uu___104_1530.pure_subterms_within_computations);
            simplify = (uu___104_1530.simplify);
            erase_universes = (uu___104_1530.erase_universes);
            allow_unbound_universes = (uu___104_1530.allow_unbound_universes);
            reify_ = (uu___104_1530.reify_);
            compress_uvars = (uu___104_1530.compress_uvars);
            no_full_norm = (uu___104_1530.no_full_norm);
            check_no_uvars = (uu___104_1530.check_no_uvars);
            unmeta = (uu___104_1530.unmeta);
            unascribe = (uu___104_1530.unascribe);
            in_full_norm_request = (uu___104_1530.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___104_1530.weakly_reduce_scrutinee)
          }
      | HNF  ->
          let uu___105_1531 = fs  in
          {
            beta = (uu___105_1531.beta);
            iota = (uu___105_1531.iota);
            zeta = (uu___105_1531.zeta);
            weak = (uu___105_1531.weak);
            hnf = true;
            primops = (uu___105_1531.primops);
            do_not_unfold_pure_lets = (uu___105_1531.do_not_unfold_pure_lets);
            unfold_until = (uu___105_1531.unfold_until);
            unfold_only = (uu___105_1531.unfold_only);
            unfold_fully = (uu___105_1531.unfold_fully);
            unfold_attr = (uu___105_1531.unfold_attr);
            unfold_tac = (uu___105_1531.unfold_tac);
            pure_subterms_within_computations =
              (uu___105_1531.pure_subterms_within_computations);
            simplify = (uu___105_1531.simplify);
            erase_universes = (uu___105_1531.erase_universes);
            allow_unbound_universes = (uu___105_1531.allow_unbound_universes);
            reify_ = (uu___105_1531.reify_);
            compress_uvars = (uu___105_1531.compress_uvars);
            no_full_norm = (uu___105_1531.no_full_norm);
            check_no_uvars = (uu___105_1531.check_no_uvars);
            unmeta = (uu___105_1531.unmeta);
            unascribe = (uu___105_1531.unascribe);
            in_full_norm_request = (uu___105_1531.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___105_1531.weakly_reduce_scrutinee)
          }
      | Primops  ->
          let uu___106_1532 = fs  in
          {
            beta = (uu___106_1532.beta);
            iota = (uu___106_1532.iota);
            zeta = (uu___106_1532.zeta);
            weak = (uu___106_1532.weak);
            hnf = (uu___106_1532.hnf);
            primops = true;
            do_not_unfold_pure_lets = (uu___106_1532.do_not_unfold_pure_lets);
            unfold_until = (uu___106_1532.unfold_until);
            unfold_only = (uu___106_1532.unfold_only);
            unfold_fully = (uu___106_1532.unfold_fully);
            unfold_attr = (uu___106_1532.unfold_attr);
            unfold_tac = (uu___106_1532.unfold_tac);
            pure_subterms_within_computations =
              (uu___106_1532.pure_subterms_within_computations);
            simplify = (uu___106_1532.simplify);
            erase_universes = (uu___106_1532.erase_universes);
            allow_unbound_universes = (uu___106_1532.allow_unbound_universes);
            reify_ = (uu___106_1532.reify_);
            compress_uvars = (uu___106_1532.compress_uvars);
            no_full_norm = (uu___106_1532.no_full_norm);
            check_no_uvars = (uu___106_1532.check_no_uvars);
            unmeta = (uu___106_1532.unmeta);
            unascribe = (uu___106_1532.unascribe);
            in_full_norm_request = (uu___106_1532.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___106_1532.weakly_reduce_scrutinee)
          }
      | Eager_unfolding  -> fs
      | Inlining  -> fs
      | DoNotUnfoldPureLets  ->
          let uu___107_1533 = fs  in
          {
            beta = (uu___107_1533.beta);
            iota = (uu___107_1533.iota);
            zeta = (uu___107_1533.zeta);
            weak = (uu___107_1533.weak);
            hnf = (uu___107_1533.hnf);
            primops = (uu___107_1533.primops);
            do_not_unfold_pure_lets = true;
            unfold_until = (uu___107_1533.unfold_until);
            unfold_only = (uu___107_1533.unfold_only);
            unfold_fully = (uu___107_1533.unfold_fully);
            unfold_attr = (uu___107_1533.unfold_attr);
            unfold_tac = (uu___107_1533.unfold_tac);
            pure_subterms_within_computations =
              (uu___107_1533.pure_subterms_within_computations);
            simplify = (uu___107_1533.simplify);
            erase_universes = (uu___107_1533.erase_universes);
            allow_unbound_universes = (uu___107_1533.allow_unbound_universes);
            reify_ = (uu___107_1533.reify_);
            compress_uvars = (uu___107_1533.compress_uvars);
            no_full_norm = (uu___107_1533.no_full_norm);
            check_no_uvars = (uu___107_1533.check_no_uvars);
            unmeta = (uu___107_1533.unmeta);
            unascribe = (uu___107_1533.unascribe);
            in_full_norm_request = (uu___107_1533.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___107_1533.weakly_reduce_scrutinee)
          }
      | UnfoldUntil d ->
          let uu___108_1535 = fs  in
          {
            beta = (uu___108_1535.beta);
            iota = (uu___108_1535.iota);
            zeta = (uu___108_1535.zeta);
            weak = (uu___108_1535.weak);
            hnf = (uu___108_1535.hnf);
            primops = (uu___108_1535.primops);
            do_not_unfold_pure_lets = (uu___108_1535.do_not_unfold_pure_lets);
            unfold_until = (FStar_Pervasives_Native.Some d);
            unfold_only = (uu___108_1535.unfold_only);
            unfold_fully = (uu___108_1535.unfold_fully);
            unfold_attr = (uu___108_1535.unfold_attr);
            unfold_tac = (uu___108_1535.unfold_tac);
            pure_subterms_within_computations =
              (uu___108_1535.pure_subterms_within_computations);
            simplify = (uu___108_1535.simplify);
            erase_universes = (uu___108_1535.erase_universes);
            allow_unbound_universes = (uu___108_1535.allow_unbound_universes);
            reify_ = (uu___108_1535.reify_);
            compress_uvars = (uu___108_1535.compress_uvars);
            no_full_norm = (uu___108_1535.no_full_norm);
            check_no_uvars = (uu___108_1535.check_no_uvars);
            unmeta = (uu___108_1535.unmeta);
            unascribe = (uu___108_1535.unascribe);
            in_full_norm_request = (uu___108_1535.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___108_1535.weakly_reduce_scrutinee)
          }
      | UnfoldOnly lids ->
          let uu___109_1539 = fs  in
          {
            beta = (uu___109_1539.beta);
            iota = (uu___109_1539.iota);
            zeta = (uu___109_1539.zeta);
            weak = (uu___109_1539.weak);
            hnf = (uu___109_1539.hnf);
            primops = (uu___109_1539.primops);
            do_not_unfold_pure_lets = (uu___109_1539.do_not_unfold_pure_lets);
            unfold_until = (uu___109_1539.unfold_until);
            unfold_only = (FStar_Pervasives_Native.Some lids);
            unfold_fully = (uu___109_1539.unfold_fully);
            unfold_attr = (uu___109_1539.unfold_attr);
            unfold_tac = (uu___109_1539.unfold_tac);
            pure_subterms_within_computations =
              (uu___109_1539.pure_subterms_within_computations);
            simplify = (uu___109_1539.simplify);
            erase_universes = (uu___109_1539.erase_universes);
            allow_unbound_universes = (uu___109_1539.allow_unbound_universes);
            reify_ = (uu___109_1539.reify_);
            compress_uvars = (uu___109_1539.compress_uvars);
            no_full_norm = (uu___109_1539.no_full_norm);
            check_no_uvars = (uu___109_1539.check_no_uvars);
            unmeta = (uu___109_1539.unmeta);
            unascribe = (uu___109_1539.unascribe);
            in_full_norm_request = (uu___109_1539.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___109_1539.weakly_reduce_scrutinee)
          }
      | UnfoldFully lids ->
          let uu___110_1545 = fs  in
          {
            beta = (uu___110_1545.beta);
            iota = (uu___110_1545.iota);
            zeta = (uu___110_1545.zeta);
            weak = (uu___110_1545.weak);
            hnf = (uu___110_1545.hnf);
            primops = (uu___110_1545.primops);
            do_not_unfold_pure_lets = (uu___110_1545.do_not_unfold_pure_lets);
            unfold_until = (uu___110_1545.unfold_until);
            unfold_only = (uu___110_1545.unfold_only);
            unfold_fully = (FStar_Pervasives_Native.Some lids);
            unfold_attr = (uu___110_1545.unfold_attr);
            unfold_tac = (uu___110_1545.unfold_tac);
            pure_subterms_within_computations =
              (uu___110_1545.pure_subterms_within_computations);
            simplify = (uu___110_1545.simplify);
            erase_universes = (uu___110_1545.erase_universes);
            allow_unbound_universes = (uu___110_1545.allow_unbound_universes);
            reify_ = (uu___110_1545.reify_);
            compress_uvars = (uu___110_1545.compress_uvars);
            no_full_norm = (uu___110_1545.no_full_norm);
            check_no_uvars = (uu___110_1545.check_no_uvars);
            unmeta = (uu___110_1545.unmeta);
            unascribe = (uu___110_1545.unascribe);
            in_full_norm_request = (uu___110_1545.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___110_1545.weakly_reduce_scrutinee)
          }
      | UnfoldAttr attr ->
          let uu___111_1549 = fs  in
          {
            beta = (uu___111_1549.beta);
            iota = (uu___111_1549.iota);
            zeta = (uu___111_1549.zeta);
            weak = (uu___111_1549.weak);
            hnf = (uu___111_1549.hnf);
            primops = (uu___111_1549.primops);
            do_not_unfold_pure_lets = (uu___111_1549.do_not_unfold_pure_lets);
            unfold_until = (uu___111_1549.unfold_until);
            unfold_only = (uu___111_1549.unfold_only);
            unfold_fully = (uu___111_1549.unfold_fully);
            unfold_attr = (add_opt attr fs.unfold_attr);
            unfold_tac = (uu___111_1549.unfold_tac);
            pure_subterms_within_computations =
              (uu___111_1549.pure_subterms_within_computations);
            simplify = (uu___111_1549.simplify);
            erase_universes = (uu___111_1549.erase_universes);
            allow_unbound_universes = (uu___111_1549.allow_unbound_universes);
            reify_ = (uu___111_1549.reify_);
            compress_uvars = (uu___111_1549.compress_uvars);
            no_full_norm = (uu___111_1549.no_full_norm);
            check_no_uvars = (uu___111_1549.check_no_uvars);
            unmeta = (uu___111_1549.unmeta);
            unascribe = (uu___111_1549.unascribe);
            in_full_norm_request = (uu___111_1549.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___111_1549.weakly_reduce_scrutinee)
          }
      | UnfoldTac  ->
          let uu___112_1550 = fs  in
          {
            beta = (uu___112_1550.beta);
            iota = (uu___112_1550.iota);
            zeta = (uu___112_1550.zeta);
            weak = (uu___112_1550.weak);
            hnf = (uu___112_1550.hnf);
            primops = (uu___112_1550.primops);
            do_not_unfold_pure_lets = (uu___112_1550.do_not_unfold_pure_lets);
            unfold_until = (uu___112_1550.unfold_until);
            unfold_only = (uu___112_1550.unfold_only);
            unfold_fully = (uu___112_1550.unfold_fully);
            unfold_attr = (uu___112_1550.unfold_attr);
            unfold_tac = true;
            pure_subterms_within_computations =
              (uu___112_1550.pure_subterms_within_computations);
            simplify = (uu___112_1550.simplify);
            erase_universes = (uu___112_1550.erase_universes);
            allow_unbound_universes = (uu___112_1550.allow_unbound_universes);
            reify_ = (uu___112_1550.reify_);
            compress_uvars = (uu___112_1550.compress_uvars);
            no_full_norm = (uu___112_1550.no_full_norm);
            check_no_uvars = (uu___112_1550.check_no_uvars);
            unmeta = (uu___112_1550.unmeta);
            unascribe = (uu___112_1550.unascribe);
            in_full_norm_request = (uu___112_1550.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___112_1550.weakly_reduce_scrutinee)
          }
      | PureSubtermsWithinComputations  ->
          let uu___113_1551 = fs  in
          {
            beta = (uu___113_1551.beta);
            iota = (uu___113_1551.iota);
            zeta = (uu___113_1551.zeta);
            weak = (uu___113_1551.weak);
            hnf = (uu___113_1551.hnf);
            primops = (uu___113_1551.primops);
            do_not_unfold_pure_lets = (uu___113_1551.do_not_unfold_pure_lets);
            unfold_until = (uu___113_1551.unfold_until);
            unfold_only = (uu___113_1551.unfold_only);
            unfold_fully = (uu___113_1551.unfold_fully);
            unfold_attr = (uu___113_1551.unfold_attr);
            unfold_tac = (uu___113_1551.unfold_tac);
            pure_subterms_within_computations = true;
            simplify = (uu___113_1551.simplify);
            erase_universes = (uu___113_1551.erase_universes);
            allow_unbound_universes = (uu___113_1551.allow_unbound_universes);
            reify_ = (uu___113_1551.reify_);
            compress_uvars = (uu___113_1551.compress_uvars);
            no_full_norm = (uu___113_1551.no_full_norm);
            check_no_uvars = (uu___113_1551.check_no_uvars);
            unmeta = (uu___113_1551.unmeta);
            unascribe = (uu___113_1551.unascribe);
            in_full_norm_request = (uu___113_1551.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___113_1551.weakly_reduce_scrutinee)
          }
      | Simplify  ->
          let uu___114_1552 = fs  in
          {
            beta = (uu___114_1552.beta);
            iota = (uu___114_1552.iota);
            zeta = (uu___114_1552.zeta);
            weak = (uu___114_1552.weak);
            hnf = (uu___114_1552.hnf);
            primops = (uu___114_1552.primops);
            do_not_unfold_pure_lets = (uu___114_1552.do_not_unfold_pure_lets);
            unfold_until = (uu___114_1552.unfold_until);
            unfold_only = (uu___114_1552.unfold_only);
            unfold_fully = (uu___114_1552.unfold_fully);
            unfold_attr = (uu___114_1552.unfold_attr);
            unfold_tac = (uu___114_1552.unfold_tac);
            pure_subterms_within_computations =
              (uu___114_1552.pure_subterms_within_computations);
            simplify = true;
            erase_universes = (uu___114_1552.erase_universes);
            allow_unbound_universes = (uu___114_1552.allow_unbound_universes);
            reify_ = (uu___114_1552.reify_);
            compress_uvars = (uu___114_1552.compress_uvars);
            no_full_norm = (uu___114_1552.no_full_norm);
            check_no_uvars = (uu___114_1552.check_no_uvars);
            unmeta = (uu___114_1552.unmeta);
            unascribe = (uu___114_1552.unascribe);
            in_full_norm_request = (uu___114_1552.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___114_1552.weakly_reduce_scrutinee)
          }
      | EraseUniverses  ->
          let uu___115_1553 = fs  in
          {
            beta = (uu___115_1553.beta);
            iota = (uu___115_1553.iota);
            zeta = (uu___115_1553.zeta);
            weak = (uu___115_1553.weak);
            hnf = (uu___115_1553.hnf);
            primops = (uu___115_1553.primops);
            do_not_unfold_pure_lets = (uu___115_1553.do_not_unfold_pure_lets);
            unfold_until = (uu___115_1553.unfold_until);
            unfold_only = (uu___115_1553.unfold_only);
            unfold_fully = (uu___115_1553.unfold_fully);
            unfold_attr = (uu___115_1553.unfold_attr);
            unfold_tac = (uu___115_1553.unfold_tac);
            pure_subterms_within_computations =
              (uu___115_1553.pure_subterms_within_computations);
            simplify = (uu___115_1553.simplify);
            erase_universes = true;
            allow_unbound_universes = (uu___115_1553.allow_unbound_universes);
            reify_ = (uu___115_1553.reify_);
            compress_uvars = (uu___115_1553.compress_uvars);
            no_full_norm = (uu___115_1553.no_full_norm);
            check_no_uvars = (uu___115_1553.check_no_uvars);
            unmeta = (uu___115_1553.unmeta);
            unascribe = (uu___115_1553.unascribe);
            in_full_norm_request = (uu___115_1553.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___115_1553.weakly_reduce_scrutinee)
          }
      | AllowUnboundUniverses  ->
          let uu___116_1554 = fs  in
          {
            beta = (uu___116_1554.beta);
            iota = (uu___116_1554.iota);
            zeta = (uu___116_1554.zeta);
            weak = (uu___116_1554.weak);
            hnf = (uu___116_1554.hnf);
            primops = (uu___116_1554.primops);
            do_not_unfold_pure_lets = (uu___116_1554.do_not_unfold_pure_lets);
            unfold_until = (uu___116_1554.unfold_until);
            unfold_only = (uu___116_1554.unfold_only);
            unfold_fully = (uu___116_1554.unfold_fully);
            unfold_attr = (uu___116_1554.unfold_attr);
            unfold_tac = (uu___116_1554.unfold_tac);
            pure_subterms_within_computations =
              (uu___116_1554.pure_subterms_within_computations);
            simplify = (uu___116_1554.simplify);
            erase_universes = (uu___116_1554.erase_universes);
            allow_unbound_universes = true;
            reify_ = (uu___116_1554.reify_);
            compress_uvars = (uu___116_1554.compress_uvars);
            no_full_norm = (uu___116_1554.no_full_norm);
            check_no_uvars = (uu___116_1554.check_no_uvars);
            unmeta = (uu___116_1554.unmeta);
            unascribe = (uu___116_1554.unascribe);
            in_full_norm_request = (uu___116_1554.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___116_1554.weakly_reduce_scrutinee)
          }
      | Reify  ->
          let uu___117_1555 = fs  in
          {
            beta = (uu___117_1555.beta);
            iota = (uu___117_1555.iota);
            zeta = (uu___117_1555.zeta);
            weak = (uu___117_1555.weak);
            hnf = (uu___117_1555.hnf);
            primops = (uu___117_1555.primops);
            do_not_unfold_pure_lets = (uu___117_1555.do_not_unfold_pure_lets);
            unfold_until = (uu___117_1555.unfold_until);
            unfold_only = (uu___117_1555.unfold_only);
            unfold_fully = (uu___117_1555.unfold_fully);
            unfold_attr = (uu___117_1555.unfold_attr);
            unfold_tac = (uu___117_1555.unfold_tac);
            pure_subterms_within_computations =
              (uu___117_1555.pure_subterms_within_computations);
            simplify = (uu___117_1555.simplify);
            erase_universes = (uu___117_1555.erase_universes);
            allow_unbound_universes = (uu___117_1555.allow_unbound_universes);
            reify_ = true;
            compress_uvars = (uu___117_1555.compress_uvars);
            no_full_norm = (uu___117_1555.no_full_norm);
            check_no_uvars = (uu___117_1555.check_no_uvars);
            unmeta = (uu___117_1555.unmeta);
            unascribe = (uu___117_1555.unascribe);
            in_full_norm_request = (uu___117_1555.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___117_1555.weakly_reduce_scrutinee)
          }
      | CompressUvars  ->
          let uu___118_1556 = fs  in
          {
            beta = (uu___118_1556.beta);
            iota = (uu___118_1556.iota);
            zeta = (uu___118_1556.zeta);
            weak = (uu___118_1556.weak);
            hnf = (uu___118_1556.hnf);
            primops = (uu___118_1556.primops);
            do_not_unfold_pure_lets = (uu___118_1556.do_not_unfold_pure_lets);
            unfold_until = (uu___118_1556.unfold_until);
            unfold_only = (uu___118_1556.unfold_only);
            unfold_fully = (uu___118_1556.unfold_fully);
            unfold_attr = (uu___118_1556.unfold_attr);
            unfold_tac = (uu___118_1556.unfold_tac);
            pure_subterms_within_computations =
              (uu___118_1556.pure_subterms_within_computations);
            simplify = (uu___118_1556.simplify);
            erase_universes = (uu___118_1556.erase_universes);
            allow_unbound_universes = (uu___118_1556.allow_unbound_universes);
            reify_ = (uu___118_1556.reify_);
            compress_uvars = true;
            no_full_norm = (uu___118_1556.no_full_norm);
            check_no_uvars = (uu___118_1556.check_no_uvars);
            unmeta = (uu___118_1556.unmeta);
            unascribe = (uu___118_1556.unascribe);
            in_full_norm_request = (uu___118_1556.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___118_1556.weakly_reduce_scrutinee)
          }
      | NoFullNorm  ->
          let uu___119_1557 = fs  in
          {
            beta = (uu___119_1557.beta);
            iota = (uu___119_1557.iota);
            zeta = (uu___119_1557.zeta);
            weak = (uu___119_1557.weak);
            hnf = (uu___119_1557.hnf);
            primops = (uu___119_1557.primops);
            do_not_unfold_pure_lets = (uu___119_1557.do_not_unfold_pure_lets);
            unfold_until = (uu___119_1557.unfold_until);
            unfold_only = (uu___119_1557.unfold_only);
            unfold_fully = (uu___119_1557.unfold_fully);
            unfold_attr = (uu___119_1557.unfold_attr);
            unfold_tac = (uu___119_1557.unfold_tac);
            pure_subterms_within_computations =
              (uu___119_1557.pure_subterms_within_computations);
            simplify = (uu___119_1557.simplify);
            erase_universes = (uu___119_1557.erase_universes);
            allow_unbound_universes = (uu___119_1557.allow_unbound_universes);
            reify_ = (uu___119_1557.reify_);
            compress_uvars = (uu___119_1557.compress_uvars);
            no_full_norm = true;
            check_no_uvars = (uu___119_1557.check_no_uvars);
            unmeta = (uu___119_1557.unmeta);
            unascribe = (uu___119_1557.unascribe);
            in_full_norm_request = (uu___119_1557.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___119_1557.weakly_reduce_scrutinee)
          }
      | CheckNoUvars  ->
          let uu___120_1558 = fs  in
          {
            beta = (uu___120_1558.beta);
            iota = (uu___120_1558.iota);
            zeta = (uu___120_1558.zeta);
            weak = (uu___120_1558.weak);
            hnf = (uu___120_1558.hnf);
            primops = (uu___120_1558.primops);
            do_not_unfold_pure_lets = (uu___120_1558.do_not_unfold_pure_lets);
            unfold_until = (uu___120_1558.unfold_until);
            unfold_only = (uu___120_1558.unfold_only);
            unfold_fully = (uu___120_1558.unfold_fully);
            unfold_attr = (uu___120_1558.unfold_attr);
            unfold_tac = (uu___120_1558.unfold_tac);
            pure_subterms_within_computations =
              (uu___120_1558.pure_subterms_within_computations);
            simplify = (uu___120_1558.simplify);
            erase_universes = (uu___120_1558.erase_universes);
            allow_unbound_universes = (uu___120_1558.allow_unbound_universes);
            reify_ = (uu___120_1558.reify_);
            compress_uvars = (uu___120_1558.compress_uvars);
            no_full_norm = (uu___120_1558.no_full_norm);
            check_no_uvars = true;
            unmeta = (uu___120_1558.unmeta);
            unascribe = (uu___120_1558.unascribe);
            in_full_norm_request = (uu___120_1558.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___120_1558.weakly_reduce_scrutinee)
          }
      | Unmeta  ->
          let uu___121_1559 = fs  in
          {
            beta = (uu___121_1559.beta);
            iota = (uu___121_1559.iota);
            zeta = (uu___121_1559.zeta);
            weak = (uu___121_1559.weak);
            hnf = (uu___121_1559.hnf);
            primops = (uu___121_1559.primops);
            do_not_unfold_pure_lets = (uu___121_1559.do_not_unfold_pure_lets);
            unfold_until = (uu___121_1559.unfold_until);
            unfold_only = (uu___121_1559.unfold_only);
            unfold_fully = (uu___121_1559.unfold_fully);
            unfold_attr = (uu___121_1559.unfold_attr);
            unfold_tac = (uu___121_1559.unfold_tac);
            pure_subterms_within_computations =
              (uu___121_1559.pure_subterms_within_computations);
            simplify = (uu___121_1559.simplify);
            erase_universes = (uu___121_1559.erase_universes);
            allow_unbound_universes = (uu___121_1559.allow_unbound_universes);
            reify_ = (uu___121_1559.reify_);
            compress_uvars = (uu___121_1559.compress_uvars);
            no_full_norm = (uu___121_1559.no_full_norm);
            check_no_uvars = (uu___121_1559.check_no_uvars);
            unmeta = true;
            unascribe = (uu___121_1559.unascribe);
            in_full_norm_request = (uu___121_1559.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___121_1559.weakly_reduce_scrutinee)
          }
      | Unascribe  ->
          let uu___122_1560 = fs  in
          {
            beta = (uu___122_1560.beta);
            iota = (uu___122_1560.iota);
            zeta = (uu___122_1560.zeta);
            weak = (uu___122_1560.weak);
            hnf = (uu___122_1560.hnf);
            primops = (uu___122_1560.primops);
            do_not_unfold_pure_lets = (uu___122_1560.do_not_unfold_pure_lets);
            unfold_until = (uu___122_1560.unfold_until);
            unfold_only = (uu___122_1560.unfold_only);
            unfold_fully = (uu___122_1560.unfold_fully);
            unfold_attr = (uu___122_1560.unfold_attr);
            unfold_tac = (uu___122_1560.unfold_tac);
            pure_subterms_within_computations =
              (uu___122_1560.pure_subterms_within_computations);
            simplify = (uu___122_1560.simplify);
            erase_universes = (uu___122_1560.erase_universes);
            allow_unbound_universes = (uu___122_1560.allow_unbound_universes);
            reify_ = (uu___122_1560.reify_);
            compress_uvars = (uu___122_1560.compress_uvars);
            no_full_norm = (uu___122_1560.no_full_norm);
            check_no_uvars = (uu___122_1560.check_no_uvars);
            unmeta = (uu___122_1560.unmeta);
            unascribe = true;
            in_full_norm_request = (uu___122_1560.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___122_1560.weakly_reduce_scrutinee)
          }
  
let rec (to_fsteps : step Prims.list -> fsteps) =
  fun s  -> FStar_List.fold_right fstep_add_one s default_steps 
type psc =
  {
  psc_range: FStar_Range.range ;
  psc_subst: unit -> FStar_Syntax_Syntax.subst_t }[@@deriving show]
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
  { psc_range = FStar_Range.dummyRange; psc_subst = (fun uu____1613  -> []) } 
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
    }[@@deriving show]
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
  | Dummy [@@deriving show]
let (uu___is_Clos : closure -> Prims.bool) =
  fun projectee  ->
    match projectee with | Clos _0 -> true | uu____1902 -> false
  
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
    match projectee with | Univ _0 -> true | uu____2006 -> false
  
let (__proj__Univ__item___0 : closure -> FStar_Syntax_Syntax.universe) =
  fun projectee  -> match projectee with | Univ _0 -> _0 
let (uu___is_Dummy : closure -> Prims.bool) =
  fun projectee  ->
    match projectee with | Dummy  -> true | uu____2019 -> false
  
type env =
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
    FStar_Pervasives_Native.tuple2 Prims.list[@@deriving show]
let (dummy :
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
    FStar_Pervasives_Native.tuple2)
  = (FStar_Pervasives_Native.None, Dummy) 
type debug_switches =
  {
  gen: Prims.bool ;
  primop: Prims.bool ;
  b380: Prims.bool ;
  norm_delayed: Prims.bool ;
  print_normalized: Prims.bool }[@@deriving show]
let (__proj__Mkdebug_switches__item__gen : debug_switches -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { gen = __fname__gen; primop = __fname__primop; b380 = __fname__b380;
        norm_delayed = __fname__norm_delayed;
        print_normalized = __fname__print_normalized;_} -> __fname__gen
  
let (__proj__Mkdebug_switches__item__primop : debug_switches -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { gen = __fname__gen; primop = __fname__primop; b380 = __fname__b380;
        norm_delayed = __fname__norm_delayed;
        print_normalized = __fname__print_normalized;_} -> __fname__primop
  
let (__proj__Mkdebug_switches__item__b380 : debug_switches -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { gen = __fname__gen; primop = __fname__primop; b380 = __fname__b380;
        norm_delayed = __fname__norm_delayed;
        print_normalized = __fname__print_normalized;_} -> __fname__b380
  
let (__proj__Mkdebug_switches__item__norm_delayed :
  debug_switches -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { gen = __fname__gen; primop = __fname__primop; b380 = __fname__b380;
        norm_delayed = __fname__norm_delayed;
        print_normalized = __fname__print_normalized;_} ->
        __fname__norm_delayed
  
let (__proj__Mkdebug_switches__item__print_normalized :
  debug_switches -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { gen = __fname__gen; primop = __fname__primop; b380 = __fname__b380;
        norm_delayed = __fname__norm_delayed;
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
  normalize_pure_lets: Prims.bool }[@@deriving show]
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
  
let (add_steps :
  primitive_step FStar_Util.psmap ->
    primitive_step Prims.list -> primitive_step FStar_Util.psmap)
  =
  fun m  ->
    fun l  ->
      FStar_List.fold_right
        (fun p  ->
           fun m1  ->
             let uu____2330 = FStar_Ident.text_of_lid p.name  in
             FStar_Util.psmap_add m1 uu____2330 p) l m
  
let (prim_from_list :
  primitive_step Prims.list -> primitive_step FStar_Util.psmap) =
  fun l  ->
    let uu____2344 = FStar_Util.psmap_empty ()  in add_steps uu____2344 l
  
let (find_prim_step :
  cfg ->
    FStar_Syntax_Syntax.fv -> primitive_step FStar_Pervasives_Native.option)
  =
  fun cfg  ->
    fun fv  ->
      let uu____2359 =
        FStar_Ident.text_of_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
         in
      FStar_Util.psmap_try_find cfg.primitive_steps uu____2359
  
type branches =
  (FStar_Syntax_Syntax.pat,FStar_Syntax_Syntax.term
                             FStar_Pervasives_Native.option,FStar_Syntax_Syntax.term)
    FStar_Pervasives_Native.tuple3 Prims.list[@@deriving show]
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
  FStar_Pervasives_Native.tuple2 [@@deriving show]
let (uu___is_Arg : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Arg _0 -> true | uu____2517 -> false
  
let (__proj__Arg__item___0 :
  stack_elt ->
    (closure,FStar_Syntax_Syntax.aqual,FStar_Range.range)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | Arg _0 -> _0 
let (uu___is_UnivArgs : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnivArgs _0 -> true | uu____2555 -> false
  
let (__proj__UnivArgs__item___0 :
  stack_elt ->
    (FStar_Syntax_Syntax.universe Prims.list,FStar_Range.range)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | UnivArgs _0 -> _0 
let (uu___is_MemoLazy : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | MemoLazy _0 -> true | uu____2593 -> false
  
let (__proj__MemoLazy__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.term) FStar_Pervasives_Native.tuple2
      FStar_Syntax_Syntax.memo)
  = fun projectee  -> match projectee with | MemoLazy _0 -> _0 
let (uu___is_Match : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____2666 -> false
  
let (__proj__Match__item___0 :
  stack_elt ->
    (env,branches,cfg,FStar_Range.range) FStar_Pervasives_Native.tuple4)
  = fun projectee  -> match projectee with | Match _0 -> _0 
let (uu___is_Abs : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Abs _0 -> true | uu____2716 -> false
  
let (__proj__Abs__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.binders,env,FStar_Syntax_Syntax.residual_comp
                                           FStar_Pervasives_Native.option,
      FStar_Range.range) FStar_Pervasives_Native.tuple5)
  = fun projectee  -> match projectee with | Abs _0 -> _0 
let (uu___is_App : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____2774 -> false
  
let (__proj__App__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual,FStar_Range.range)
      FStar_Pervasives_Native.tuple4)
  = fun projectee  -> match projectee with | App _0 -> _0 
let (uu___is_Meta : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Meta _0 -> true | uu____2818 -> false
  
let (__proj__Meta__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.metadata,FStar_Range.range)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | Meta _0 -> _0 
let (uu___is_Let : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Let _0 -> true | uu____2858 -> false
  
let (__proj__Let__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.letbinding,FStar_Range.range)
      FStar_Pervasives_Native.tuple4)
  = fun projectee  -> match projectee with | Let _0 -> _0 
let (uu___is_Cfg : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Cfg _0 -> true | uu____2896 -> false
  
let (__proj__Cfg__item___0 : stack_elt -> cfg) =
  fun projectee  -> match projectee with | Cfg _0 -> _0 
let (uu___is_Debug : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Debug _0 -> true | uu____2914 -> false
  
let (__proj__Debug__item___0 :
  stack_elt ->
    (FStar_Syntax_Syntax.term,FStar_Util.time) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Debug _0 -> _0 
type stack = stack_elt Prims.list[@@deriving show]
let (head_of : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____2941 = FStar_Syntax_Util.head_and_args' t  in
    match uu____2941 with | (hd1,uu____2955) -> hd1
  
let mk :
  'Auu____2978 .
    'Auu____2978 ->
      FStar_Range.range -> 'Auu____2978 FStar_Syntax_Syntax.syntax
  =
  fun t  -> fun r  -> FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None r 
let set_memo : 'a . cfg -> 'a FStar_Syntax_Syntax.memo -> 'a -> unit =
  fun cfg  ->
    fun r  ->
      fun t  ->
        if cfg.memoize_lazy
        then
          let uu____3041 = FStar_ST.op_Bang r  in
          match uu____3041 with
          | FStar_Pervasives_Native.Some uu____3093 ->
              failwith "Unexpected set_memo: thunk already evaluated"
          | FStar_Pervasives_Native.None  ->
              FStar_ST.op_Colon_Equals r (FStar_Pervasives_Native.Some t)
        else ()
  
let rec (env_to_string :
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
    FStar_Pervasives_Native.tuple2 Prims.list -> Prims.string)
  =
  fun env  ->
    let uu____3169 =
      FStar_List.map
        (fun uu____3183  ->
           match uu____3183 with
           | (bopt,c) ->
               let uu____3196 =
                 match bopt with
                 | FStar_Pervasives_Native.None  -> "."
                 | FStar_Pervasives_Native.Some x ->
                     FStar_Syntax_Print.binder_to_string x
                  in
               let uu____3198 = closure_to_string c  in
               FStar_Util.format2 "(%s, %s)" uu____3196 uu____3198) env
       in
    FStar_All.pipe_right uu____3169 (FStar_String.concat "; ")

and (closure_to_string : closure -> Prims.string) =
  fun uu___81_3201  ->
    match uu___81_3201 with
    | Clos (env,t,uu____3204,uu____3205) ->
        let uu____3250 =
          FStar_All.pipe_right (FStar_List.length env)
            FStar_Util.string_of_int
           in
        let uu____3257 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format2 "(env=%s elts; %s)" uu____3250 uu____3257
    | Univ uu____3258 -> "Univ"
    | Dummy  -> "dummy"

let (stack_elt_to_string : stack_elt -> Prims.string) =
  fun uu___82_3263  ->
    match uu___82_3263 with
    | Arg (c,uu____3265,uu____3266) ->
        let uu____3267 = closure_to_string c  in
        FStar_Util.format1 "Closure %s" uu____3267
    | MemoLazy uu____3268 -> "MemoLazy"
    | Abs (uu____3275,bs,uu____3277,uu____3278,uu____3279) ->
        let uu____3284 =
          FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs)
           in
        FStar_Util.format1 "Abs %s" uu____3284
    | UnivArgs uu____3289 -> "UnivArgs"
    | Match uu____3296 -> "Match"
    | App (uu____3305,t,uu____3307,uu____3308) ->
        let uu____3309 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "App %s" uu____3309
    | Meta (uu____3310,m,uu____3312) -> "Meta"
    | Let uu____3313 -> "Let"
    | Cfg uu____3322 -> "Cfg"
    | Debug (t,uu____3324) ->
        let uu____3325 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "Debug %s" uu____3325
  
let (stack_to_string : stack_elt Prims.list -> Prims.string) =
  fun s  ->
    let uu____3335 = FStar_List.map stack_elt_to_string s  in
    FStar_All.pipe_right uu____3335 (FStar_String.concat "; ")
  
let (log : cfg -> (unit -> unit) -> unit) =
  fun cfg  -> fun f  -> if (cfg.debug).gen then f () else () 
let (log_primops : cfg -> (unit -> unit) -> unit) =
  fun cfg  -> fun f  -> if (cfg.debug).primop then f () else () 
let is_empty : 'Auu____3376 . 'Auu____3376 Prims.list -> Prims.bool =
  fun uu___83_3383  ->
    match uu___83_3383 with | [] -> true | uu____3386 -> false
  
let (lookup_bvar :
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    FStar_Syntax_Syntax.bv -> closure)
  =
  fun env  ->
    fun x  ->
      try
        let uu____3418 = FStar_List.nth env x.FStar_Syntax_Syntax.index  in
        FStar_Pervasives_Native.snd uu____3418
      with
      | uu____3437 ->
          let uu____3438 =
            let uu____3439 = FStar_Syntax_Print.db_to_string x  in
            let uu____3440 = env_to_string env  in
            FStar_Util.format2 "Failed to find %s\nEnv is %s\n" uu____3439
              uu____3440
             in
          failwith uu____3438
  
let (downgrade_ghost_effect_name :
  FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option) =
  fun l  ->
    let uu____3448 =
      FStar_Ident.lid_equals l FStar_Parser_Const.effect_Ghost_lid  in
    if uu____3448
    then FStar_Pervasives_Native.Some FStar_Parser_Const.effect_Pure_lid
    else
      (let uu____3452 =
         FStar_Ident.lid_equals l FStar_Parser_Const.effect_GTot_lid  in
       if uu____3452
       then FStar_Pervasives_Native.Some FStar_Parser_Const.effect_Tot_lid
       else
         (let uu____3456 =
            FStar_Ident.lid_equals l FStar_Parser_Const.effect_GHOST_lid  in
          if uu____3456
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
          let uu____3490 =
            FStar_List.fold_left
              (fun uu____3516  ->
                 fun u1  ->
                   match uu____3516 with
                   | (cur_kernel,cur_max,out) ->
                       let uu____3541 = FStar_Syntax_Util.univ_kernel u1  in
                       (match uu____3541 with
                        | (k_u,n1) ->
                            let uu____3556 =
                              FStar_Syntax_Util.eq_univs cur_kernel k_u  in
                            if uu____3556
                            then (cur_kernel, u1, out)
                            else (k_u, u1, (cur_max :: out))))
              (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero, [])
              us1
             in
          match uu____3490 with
          | (uu____3574,u1,out) -> FStar_List.rev (u1 :: out)  in
        let rec aux u1 =
          let u2 = FStar_Syntax_Subst.compress_univ u1  in
          match u2 with
          | FStar_Syntax_Syntax.U_bvar x ->
              (try
                 let uu____3601 =
                   let uu____3602 = FStar_List.nth env x  in
                   FStar_Pervasives_Native.snd uu____3602  in
                 match uu____3601 with
                 | Univ u3 -> aux u3
                 | Dummy  -> [u2]
                 | uu____3620 ->
                     failwith "Impossible: universe variable bound to a term"
               with
               | uu____3628 ->
                   if (cfg.steps).allow_unbound_universes
                   then [FStar_Syntax_Syntax.U_unknown]
                   else failwith "Universe variable not found")
          | FStar_Syntax_Syntax.U_unif uu____3634 when
              (cfg.steps).check_no_uvars -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_zero  -> [u2]
          | FStar_Syntax_Syntax.U_unif uu____3643 -> [u2]
          | FStar_Syntax_Syntax.U_name uu____3652 -> [u2]
          | FStar_Syntax_Syntax.U_unknown  -> [u2]
          | FStar_Syntax_Syntax.U_max [] -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_max us ->
              let us1 =
                let uu____3659 = FStar_List.collect aux us  in
                FStar_All.pipe_right uu____3659 norm_univs  in
              (match us1 with
               | u_k::hd1::rest ->
                   let rest1 = hd1 :: rest  in
                   let uu____3676 = FStar_Syntax_Util.univ_kernel u_k  in
                   (match uu____3676 with
                    | (FStar_Syntax_Syntax.U_zero ,n1) ->
                        let uu____3684 =
                          FStar_All.pipe_right rest1
                            (FStar_List.for_all
                               (fun u3  ->
                                  let uu____3692 =
                                    FStar_Syntax_Util.univ_kernel u3  in
                                  match uu____3692 with
                                  | (uu____3697,m) -> n1 <= m))
                           in
                        if uu____3684 then rest1 else us1
                    | uu____3702 -> us1)
               | uu____3707 -> us1)
          | FStar_Syntax_Syntax.U_succ u3 ->
              let uu____3711 = aux u3  in
              FStar_List.map (fun _0_17  -> FStar_Syntax_Syntax.U_succ _0_17)
                uu____3711
           in
        if (cfg.steps).erase_universes
        then FStar_Syntax_Syntax.U_unknown
        else
          (let uu____3715 = aux u  in
           match uu____3715 with
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
            (fun uu____3863  ->
               let uu____3864 = FStar_Syntax_Print.tag_of_term t  in
               let uu____3865 = env_to_string env  in
               let uu____3866 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print3 "\n>>> %s (env=%s) Closure_as_term %s\n"
                 uu____3864 uu____3865 uu____3866);
          (match env with
           | [] when
               FStar_All.pipe_left Prims.op_Negation
                 (cfg.steps).compress_uvars
               -> rebuild_closure cfg env stack t
           | uu____3875 ->
               (match t.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_delayed uu____3878 ->
                    let uu____3903 = FStar_Syntax_Subst.compress t  in
                    inline_closure_env cfg env stack uu____3903
                | FStar_Syntax_Syntax.Tm_unknown  ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_constant uu____3904 ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_name uu____3905 ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_lazy uu____3906 ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_fvar uu____3907 ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_uvar uu____3908 ->
                    if (cfg.steps).check_no_uvars
                    then
                      let t1 = FStar_Syntax_Subst.compress t  in
                      (match t1.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_uvar uu____3914 ->
                           let uu____3915 =
                             let uu____3916 =
                               FStar_Range.string_of_range
                                 t1.FStar_Syntax_Syntax.pos
                                in
                             let uu____3917 =
                               FStar_Syntax_Print.term_to_string t1  in
                             FStar_Util.format2
                               "(%s): CheckNoUvars: Unexpected unification variable remains: %s"
                               uu____3916 uu____3917
                              in
                           failwith uu____3915
                       | uu____3920 -> inline_closure_env cfg env stack t1)
                    else rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_type u ->
                    let t1 =
                      let uu____3926 =
                        let uu____3927 = norm_universe cfg env u  in
                        FStar_Syntax_Syntax.Tm_type uu____3927  in
                      mk uu____3926 t.FStar_Syntax_Syntax.pos  in
                    rebuild_closure cfg env stack t1
                | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
                    let t1 =
                      let uu____3935 =
                        FStar_List.map (norm_universe cfg env) us  in
                      FStar_Syntax_Syntax.mk_Tm_uinst t' uu____3935  in
                    rebuild_closure cfg env stack t1
                | FStar_Syntax_Syntax.Tm_bvar x ->
                    let uu____3937 = lookup_bvar env x  in
                    (match uu____3937 with
                     | Univ uu____3940 ->
                         failwith
                           "Impossible: term variable is bound to a universe"
                     | Dummy  ->
                         let x1 =
                           let uu___127_3944 = x  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___127_3944.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___127_3944.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort =
                               FStar_Syntax_Syntax.tun
                           }  in
                         let t1 =
                           mk (FStar_Syntax_Syntax.Tm_bvar x1)
                             t.FStar_Syntax_Syntax.pos
                            in
                         rebuild_closure cfg env stack t1
                     | Clos (env1,t0,uu____3950,uu____3951) ->
                         inline_closure_env cfg env1 stack t0)
                | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                    let stack1 =
                      FStar_All.pipe_right stack
                        (FStar_List.fold_right
                           (fun uu____4036  ->
                              fun stack1  ->
                                match uu____4036 with
                                | (a,aq) ->
                                    let uu____4048 =
                                      let uu____4049 =
                                        let uu____4056 =
                                          let uu____4057 =
                                            let uu____4088 =
                                              FStar_Util.mk_ref
                                                FStar_Pervasives_Native.None
                                               in
                                            (env, a, uu____4088, false)  in
                                          Clos uu____4057  in
                                        (uu____4056, aq,
                                          (t.FStar_Syntax_Syntax.pos))
                                         in
                                      Arg uu____4049  in
                                    uu____4048 :: stack1) args)
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
                    let uu____4264 = close_binders cfg env bs  in
                    (match uu____4264 with
                     | (bs1,env') ->
                         let c1 = close_comp cfg env' c  in
                         let t1 =
                           mk (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
                             t.FStar_Syntax_Syntax.pos
                            in
                         rebuild_closure cfg env stack t1)
                | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
                    let uu____4311 =
                      let uu____4322 =
                        let uu____4329 = FStar_Syntax_Syntax.mk_binder x  in
                        [uu____4329]  in
                      close_binders cfg env uu____4322  in
                    (match uu____4311 with
                     | (x1,env1) ->
                         let phi1 = non_tail_inline_closure_env cfg env1 phi
                            in
                         let t1 =
                           let uu____4352 =
                             let uu____4353 =
                               let uu____4360 =
                                 let uu____4361 = FStar_List.hd x1  in
                                 FStar_All.pipe_right uu____4361
                                   FStar_Pervasives_Native.fst
                                  in
                               (uu____4360, phi1)  in
                             FStar_Syntax_Syntax.Tm_refine uu____4353  in
                           mk uu____4352 t.FStar_Syntax_Syntax.pos  in
                         rebuild_closure cfg env1 stack t1)
                | FStar_Syntax_Syntax.Tm_ascribed (t1,(annot,tacopt),lopt) ->
                    let annot1 =
                      match annot with
                      | FStar_Util.Inl t2 ->
                          let uu____4452 =
                            non_tail_inline_closure_env cfg env t2  in
                          FStar_Util.Inl uu____4452
                      | FStar_Util.Inr c ->
                          let uu____4466 = close_comp cfg env c  in
                          FStar_Util.Inr uu____4466
                       in
                    let tacopt1 =
                      FStar_Util.map_opt tacopt
                        (non_tail_inline_closure_env cfg env)
                       in
                    let t2 =
                      let uu____4485 =
                        let uu____4486 =
                          let uu____4513 =
                            non_tail_inline_closure_env cfg env t1  in
                          (uu____4513, (annot1, tacopt1), lopt)  in
                        FStar_Syntax_Syntax.Tm_ascribed uu____4486  in
                      mk uu____4485 t.FStar_Syntax_Syntax.pos  in
                    rebuild_closure cfg env stack t2
                | FStar_Syntax_Syntax.Tm_quoted (t',qi) ->
                    let t1 =
                      match qi.FStar_Syntax_Syntax.qkind with
                      | FStar_Syntax_Syntax.Quote_dynamic  ->
                          let uu____4559 =
                            let uu____4560 =
                              let uu____4567 =
                                non_tail_inline_closure_env cfg env t'  in
                              (uu____4567, qi)  in
                            FStar_Syntax_Syntax.Tm_quoted uu____4560  in
                          mk uu____4559 t.FStar_Syntax_Syntax.pos
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
                        (fun env1  -> fun uu____4619  -> dummy :: env1) env
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
                    let uu____4640 =
                      let uu____4651 = FStar_Syntax_Syntax.is_top_level [lb]
                         in
                      if uu____4651
                      then ((lb.FStar_Syntax_Syntax.lbname), body)
                      else
                        (let x =
                           FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                         let uu____4670 =
                           non_tail_inline_closure_env cfg (dummy :: env0)
                             body
                            in
                         ((FStar_Util.Inl
                             (let uu___128_4686 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___128_4686.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___128_4686.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = typ
                              })), uu____4670))
                       in
                    (match uu____4640 with
                     | (nm,body1) ->
                         let lb1 =
                           let uu___129_4704 = lb  in
                           {
                             FStar_Syntax_Syntax.lbname = nm;
                             FStar_Syntax_Syntax.lbunivs =
                               (uu___129_4704.FStar_Syntax_Syntax.lbunivs);
                             FStar_Syntax_Syntax.lbtyp = typ;
                             FStar_Syntax_Syntax.lbeff =
                               (uu___129_4704.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = def;
                             FStar_Syntax_Syntax.lbattrs =
                               (uu___129_4704.FStar_Syntax_Syntax.lbattrs);
                             FStar_Syntax_Syntax.lbpos =
                               (uu___129_4704.FStar_Syntax_Syntax.lbpos)
                           }  in
                         let t1 =
                           mk
                             (FStar_Syntax_Syntax.Tm_let
                                ((false, [lb1]), body1))
                             t.FStar_Syntax_Syntax.pos
                            in
                         rebuild_closure cfg env0 stack t1)
                | FStar_Syntax_Syntax.Tm_let ((uu____4718,lbs),body) ->
                    let norm_one_lb env1 lb =
                      let env_univs =
                        FStar_List.fold_right
                          (fun uu____4781  -> fun env2  -> dummy :: env2)
                          lb.FStar_Syntax_Syntax.lbunivs env1
                         in
                      let env2 =
                        let uu____4798 = FStar_Syntax_Syntax.is_top_level lbs
                           in
                        if uu____4798
                        then env_univs
                        else
                          FStar_List.fold_right
                            (fun uu____4810  -> fun env2  -> dummy :: env2)
                            lbs env_univs
                         in
                      let ty =
                        non_tail_inline_closure_env cfg env_univs
                          lb.FStar_Syntax_Syntax.lbtyp
                         in
                      let nm =
                        let uu____4834 = FStar_Syntax_Syntax.is_top_level lbs
                           in
                        if uu____4834
                        then lb.FStar_Syntax_Syntax.lbname
                        else
                          (let x =
                             FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                              in
                           FStar_Util.Inl
                             (let uu___130_4842 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___130_4842.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___130_4842.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = ty
                              }))
                         in
                      let uu___131_4843 = lb  in
                      let uu____4844 =
                        non_tail_inline_closure_env cfg env2
                          lb.FStar_Syntax_Syntax.lbdef
                         in
                      {
                        FStar_Syntax_Syntax.lbname = nm;
                        FStar_Syntax_Syntax.lbunivs =
                          (uu___131_4843.FStar_Syntax_Syntax.lbunivs);
                        FStar_Syntax_Syntax.lbtyp = ty;
                        FStar_Syntax_Syntax.lbeff =
                          (uu___131_4843.FStar_Syntax_Syntax.lbeff);
                        FStar_Syntax_Syntax.lbdef = uu____4844;
                        FStar_Syntax_Syntax.lbattrs =
                          (uu___131_4843.FStar_Syntax_Syntax.lbattrs);
                        FStar_Syntax_Syntax.lbpos =
                          (uu___131_4843.FStar_Syntax_Syntax.lbpos)
                      }  in
                    let lbs1 =
                      FStar_All.pipe_right lbs
                        (FStar_List.map (norm_one_lb env))
                       in
                    let body1 =
                      let body_env =
                        FStar_List.fold_right
                          (fun uu____4876  -> fun env1  -> dummy :: env1)
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
            (fun uu____4965  ->
               let uu____4966 = FStar_Syntax_Print.tag_of_term t  in
               let uu____4967 = env_to_string env  in
               let uu____4968 = stack_to_string stack  in
               let uu____4969 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print4
                 "\n>>> %s (env=%s, stack=%s) Rebuild closure_as_term %s\n"
                 uu____4966 uu____4967 uu____4968 uu____4969);
          (match stack with
           | [] -> t
           | (Arg (Clos (env_arg,tm,uu____4974,uu____4975),aq,r))::stack1 ->
               let stack2 = (App (env, t, aq, r)) :: stack1  in
               inline_closure_env cfg env_arg stack2 tm
           | (App (env1,head1,aq,r))::stack1 ->
               let t1 =
                 FStar_Syntax_Syntax.extend_app head1 (t, aq)
                   FStar_Pervasives_Native.None r
                  in
               rebuild_closure cfg env1 stack1 t1
           | (Abs (env',bs,env'',lopt,r))::stack1 ->
               let uu____5052 = close_binders cfg env' bs  in
               (match uu____5052 with
                | (bs1,uu____5066) ->
                    let lopt1 = close_lcomp_opt cfg env'' lopt  in
                    let uu____5082 =
                      let uu___132_5085 = FStar_Syntax_Util.abs bs1 t lopt1
                         in
                      {
                        FStar_Syntax_Syntax.n =
                          (uu___132_5085.FStar_Syntax_Syntax.n);
                        FStar_Syntax_Syntax.pos = r;
                        FStar_Syntax_Syntax.vars =
                          (uu___132_5085.FStar_Syntax_Syntax.vars)
                      }  in
                    rebuild_closure cfg env stack1 uu____5082)
           | (Match (env1,branches,cfg1,r))::stack1 ->
               let close_one_branch env2 uu____5141 =
                 match uu____5141 with
                 | (pat,w_opt,tm) ->
                     let rec norm_pat env3 p =
                       match p.FStar_Syntax_Syntax.v with
                       | FStar_Syntax_Syntax.Pat_constant uu____5256 ->
                           (p, env3)
                       | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                           let uu____5285 =
                             FStar_All.pipe_right pats
                               (FStar_List.fold_left
                                  (fun uu____5369  ->
                                     fun uu____5370  ->
                                       match (uu____5369, uu____5370) with
                                       | ((pats1,env4),(p1,b)) ->
                                           let uu____5509 = norm_pat env4 p1
                                              in
                                           (match uu____5509 with
                                            | (p2,env5) ->
                                                (((p2, b) :: pats1), env5)))
                                  ([], env3))
                              in
                           (match uu____5285 with
                            | (pats1,env4) ->
                                ((let uu___133_5671 = p  in
                                  {
                                    FStar_Syntax_Syntax.v =
                                      (FStar_Syntax_Syntax.Pat_cons
                                         (fv, (FStar_List.rev pats1)));
                                    FStar_Syntax_Syntax.p =
                                      (uu___133_5671.FStar_Syntax_Syntax.p)
                                  }), env4))
                       | FStar_Syntax_Syntax.Pat_var x ->
                           let x1 =
                             let uu___134_5690 = x  in
                             let uu____5691 =
                               non_tail_inline_closure_env cfg1 env3
                                 x.FStar_Syntax_Syntax.sort
                                in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___134_5690.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___134_5690.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____5691
                             }  in
                           ((let uu___135_5705 = p  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_var x1);
                               FStar_Syntax_Syntax.p =
                                 (uu___135_5705.FStar_Syntax_Syntax.p)
                             }), (dummy :: env3))
                       | FStar_Syntax_Syntax.Pat_wild x ->
                           let x1 =
                             let uu___136_5716 = x  in
                             let uu____5717 =
                               non_tail_inline_closure_env cfg1 env3
                                 x.FStar_Syntax_Syntax.sort
                                in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___136_5716.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___136_5716.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____5717
                             }  in
                           ((let uu___137_5731 = p  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_wild x1);
                               FStar_Syntax_Syntax.p =
                                 (uu___137_5731.FStar_Syntax_Syntax.p)
                             }), (dummy :: env3))
                       | FStar_Syntax_Syntax.Pat_dot_term (x,t1) ->
                           let x1 =
                             let uu___138_5747 = x  in
                             let uu____5748 =
                               non_tail_inline_closure_env cfg1 env3
                                 x.FStar_Syntax_Syntax.sort
                                in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___138_5747.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___138_5747.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____5748
                             }  in
                           let t2 = non_tail_inline_closure_env cfg1 env3 t1
                              in
                           ((let uu___139_5765 = p  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_dot_term (x1, t2));
                               FStar_Syntax_Syntax.p =
                                 (uu___139_5765.FStar_Syntax_Syntax.p)
                             }), env3)
                        in
                     let uu____5770 = norm_pat env2 pat  in
                     (match uu____5770 with
                      | (pat1,env3) ->
                          let w_opt1 =
                            match w_opt with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Pervasives_Native.None
                            | FStar_Pervasives_Native.Some w ->
                                let uu____5839 =
                                  non_tail_inline_closure_env cfg1 env3 w  in
                                FStar_Pervasives_Native.Some uu____5839
                             in
                          let tm1 = non_tail_inline_closure_env cfg1 env3 tm
                             in
                          (pat1, w_opt1, tm1))
                  in
               let t1 =
                 let uu____5858 =
                   let uu____5859 =
                     let uu____5882 =
                       FStar_All.pipe_right branches
                         (FStar_List.map (close_one_branch env1))
                        in
                     (t, uu____5882)  in
                   FStar_Syntax_Syntax.Tm_match uu____5859  in
                 mk uu____5858 t.FStar_Syntax_Syntax.pos  in
               rebuild_closure cfg1 env1 stack1 t1
           | (Meta (env_m,m,r))::stack1 ->
               let m1 =
                 match m with
                 | FStar_Syntax_Syntax.Meta_pattern args ->
                     let uu____5995 =
                       FStar_All.pipe_right args
                         (FStar_List.map
                            (fun args1  ->
                               FStar_All.pipe_right args1
                                 (FStar_List.map
                                    (fun uu____6084  ->
                                       match uu____6084 with
                                       | (a,q) ->
                                           let uu____6103 =
                                             non_tail_inline_closure_env cfg
                                               env_m a
                                              in
                                           (uu____6103, q)))))
                        in
                     FStar_Syntax_Syntax.Meta_pattern uu____5995
                 | FStar_Syntax_Syntax.Meta_monadic (m1,tbody) ->
                     let uu____6114 =
                       let uu____6121 =
                         non_tail_inline_closure_env cfg env_m tbody  in
                       (m1, uu____6121)  in
                     FStar_Syntax_Syntax.Meta_monadic uu____6114
                 | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,tbody) ->
                     let uu____6133 =
                       let uu____6142 =
                         non_tail_inline_closure_env cfg env_m tbody  in
                       (m1, m2, uu____6142)  in
                     FStar_Syntax_Syntax.Meta_monadic_lift uu____6133
                 | uu____6147 -> m  in
               let t1 = mk (FStar_Syntax_Syntax.Tm_meta (t, m1)) r  in
               rebuild_closure cfg env stack1 t1
           | uu____6153 -> failwith "Impossible: unexpected stack element")

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
        let uu____6167 =
          FStar_All.pipe_right bs
            (FStar_List.fold_left
               (fun uu____6240  ->
                  fun uu____6241  ->
                    match (uu____6240, uu____6241) with
                    | ((env1,out),(b,imp)) ->
                        let b1 =
                          let uu___140_6359 = b  in
                          let uu____6360 =
                            inline_closure_env cfg env1 []
                              b.FStar_Syntax_Syntax.sort
                             in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___140_6359.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___140_6359.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = uu____6360
                          }  in
                        let env2 = dummy :: env1  in
                        (env2, ((b1, imp) :: out))) (env, []))
           in
        match uu____6167 with | (env1,bs1) -> ((FStar_List.rev bs1), env1)

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
        | uu____6477 ->
            (match c.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Total (t,uopt) ->
                 let uu____6490 = inline_closure_env cfg env [] t  in
                 let uu____6491 =
                   FStar_Option.map (norm_universe cfg env) uopt  in
                 FStar_Syntax_Syntax.mk_Total' uu____6490 uu____6491
             | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                 let uu____6504 = inline_closure_env cfg env [] t  in
                 let uu____6505 =
                   FStar_Option.map (norm_universe cfg env) uopt  in
                 FStar_Syntax_Syntax.mk_GTotal' uu____6504 uu____6505
             | FStar_Syntax_Syntax.Comp c1 ->
                 let rt =
                   inline_closure_env cfg env []
                     c1.FStar_Syntax_Syntax.result_typ
                    in
                 let args =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args
                     (FStar_List.map
                        (fun uu____6549  ->
                           match uu____6549 with
                           | (a,q) ->
                               let uu____6562 =
                                 inline_closure_env cfg env [] a  in
                               (uu____6562, q)))
                    in
                 let flags1 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_List.map
                        (fun uu___84_6577  ->
                           match uu___84_6577 with
                           | FStar_Syntax_Syntax.DECREASES t ->
                               let uu____6581 =
                                 inline_closure_env cfg env [] t  in
                               FStar_Syntax_Syntax.DECREASES uu____6581
                           | f -> f))
                    in
                 let uu____6585 =
                   let uu___141_6586 = c1  in
                   let uu____6587 =
                     FStar_List.map (norm_universe cfg env)
                       c1.FStar_Syntax_Syntax.comp_univs
                      in
                   {
                     FStar_Syntax_Syntax.comp_univs = uu____6587;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___141_6586.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ = rt;
                     FStar_Syntax_Syntax.effect_args = args;
                     FStar_Syntax_Syntax.flags = flags1
                   }  in
                 FStar_Syntax_Syntax.mk_Comp uu____6585)

and (filter_out_lcomp_cflags :
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun flags1  ->
    FStar_All.pipe_right flags1
      (FStar_List.filter
         (fun uu___85_6597  ->
            match uu___85_6597 with
            | FStar_Syntax_Syntax.DECREASES uu____6598 -> false
            | uu____6601 -> true))

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
                   (fun uu___86_6619  ->
                      match uu___86_6619 with
                      | FStar_Syntax_Syntax.DECREASES uu____6620 -> false
                      | uu____6623 -> true))
               in
            let rc1 =
              let uu___142_6625 = rc  in
              let uu____6626 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (inline_closure_env cfg env [])
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___142_6625.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____6626;
                FStar_Syntax_Syntax.residual_flags = flags1
              }  in
            FStar_Pervasives_Native.Some rc1
        | uu____6635 -> lopt

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
    let uu____6740 =
      let uu____6749 = FStar_Syntax_Embeddings.e_list e  in
      FStar_Syntax_Embeddings.try_unembed uu____6749  in
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a) uu____6740  in
  let arg_as_bounded_int uu____6775 =
    match uu____6775 with
    | (a,uu____6787) ->
        let uu____6794 =
          let uu____6795 = FStar_Syntax_Subst.compress a  in
          uu____6795.FStar_Syntax_Syntax.n  in
        (match uu____6794 with
         | FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv1;
                FStar_Syntax_Syntax.pos = uu____6805;
                FStar_Syntax_Syntax.vars = uu____6806;_},({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_constant
                                                              (FStar_Const.Const_int
                                                              (i,FStar_Pervasives_Native.None
                                                               ));
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____6808;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____6809;_},uu____6810)::[])
             when
             let uu____6849 =
               FStar_Ident.text_of_lid
                 (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                in
             FStar_Util.ends_with uu____6849 "int_to_t" ->
             let uu____6850 =
               let uu____6855 = FStar_BigInt.big_int_of_string i  in
               (fv1, uu____6855)  in
             FStar_Pervasives_Native.Some uu____6850
         | uu____6860 -> FStar_Pervasives_Native.None)
     in
  let lift_unary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a)::[] ->
        let uu____6908 = f a  in FStar_Pervasives_Native.Some uu____6908
    | uu____6909 -> FStar_Pervasives_Native.None  in
  let lift_binary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a0)::(FStar_Pervasives_Native.Some
        a1)::[] ->
        let uu____6965 = f a0 a1  in FStar_Pervasives_Native.Some uu____6965
    | uu____6966 -> FStar_Pervasives_Native.None  in
  let unary_op as_a f res args =
    let uu____7024 = FStar_List.map as_a args  in
    lift_unary (f res.psc_range) uu____7024  in
  let binary_op as_a f res args =
    let uu____7095 = FStar_List.map as_a args  in
    lift_binary (f res.psc_range) uu____7095  in
  let as_primitive_step is_strong uu____7132 =
    match uu____7132 with
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
           let uu____7192 = f x  in
           FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_int r
             uu____7192)
     in
  let binary_int_op f =
    binary_op arg_as_int
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____7228 = f x y  in
             FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_int r
               uu____7228)
     in
  let unary_bool_op f =
    unary_op arg_as_bool
      (fun r  ->
         fun x  ->
           let uu____7257 = f x  in
           FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_bool r
             uu____7257)
     in
  let binary_bool_op f =
    binary_op arg_as_bool
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____7293 = f x y  in
             FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_bool r
               uu____7293)
     in
  let binary_string_op f =
    binary_op arg_as_string
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____7329 = f x y  in
             FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_string r
               uu____7329)
     in
  let mixed_binary_op as_a as_b embed_c f res args =
    match args with
    | a::b::[] ->
        let uu____7461 =
          let uu____7470 = as_a a  in
          let uu____7473 = as_b b  in (uu____7470, uu____7473)  in
        (match uu____7461 with
         | (FStar_Pervasives_Native.Some a1,FStar_Pervasives_Native.Some b1)
             ->
             let uu____7488 =
               let uu____7489 = f res.psc_range a1 b1  in
               embed_c res.psc_range uu____7489  in
             FStar_Pervasives_Native.Some uu____7488
         | uu____7490 -> FStar_Pervasives_Native.None)
    | uu____7499 -> FStar_Pervasives_Native.None  in
  let list_of_string' rng s =
    let name l =
      let uu____7519 =
        let uu____7520 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant
            FStar_Pervasives_Native.None
           in
        FStar_Syntax_Syntax.Tm_fvar uu____7520  in
      mk uu____7519 rng  in
    let char_t = name FStar_Parser_Const.char_lid  in
    let charterm c =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c)) rng  in
    let uu____7532 =
      let uu____7535 = FStar_String.list_of_string s  in
      FStar_List.map charterm uu____7535  in
    FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu____7532  in
  let string_of_list' rng l =
    let s = FStar_String.string_of_list l  in FStar_Syntax_Util.exp_string s
     in
  let string_compare' rng s1 s2 =
    let r = FStar_String.compare s1 s2  in
    let uu____7577 =
      let uu____7578 = FStar_Util.string_of_int r  in
      FStar_BigInt.big_int_of_string uu____7578  in
    FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_int rng
      uu____7577
     in
  let string_concat' psc args =
    match args with
    | a1::a2::[] ->
        let uu____7642 = arg_as_string a1  in
        (match uu____7642 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____7648 = arg_as_list FStar_Syntax_Embeddings.e_string a2
                in
             (match uu____7648 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2  in
                  let uu____7661 =
                    FStar_Syntax_Embeddings.embed
                      FStar_Syntax_Embeddings.e_string psc.psc_range r
                     in
                  FStar_Pervasives_Native.Some uu____7661
              | uu____7662 -> FStar_Pervasives_Native.None)
         | uu____7667 -> FStar_Pervasives_Native.None)
    | uu____7670 -> FStar_Pervasives_Native.None  in
  let string_of_int1 rng i =
    let uu____7690 = FStar_BigInt.string_of_big_int i  in
    FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_string rng
      uu____7690
     in
  let string_of_bool1 rng b =
    FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_string rng
      (if b then "true" else "false")
     in
  let mk_range1 psc args =
    match args with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____7727 =
          let uu____7748 = arg_as_string fn  in
          let uu____7751 = arg_as_int from_line  in
          let uu____7754 = arg_as_int from_col  in
          let uu____7757 = arg_as_int to_line  in
          let uu____7760 = arg_as_int to_col  in
          (uu____7748, uu____7751, uu____7754, uu____7757, uu____7760)  in
        (match uu____7727 with
         | (FStar_Pervasives_Native.Some fn1,FStar_Pervasives_Native.Some
            from_l,FStar_Pervasives_Native.Some
            from_c,FStar_Pervasives_Native.Some
            to_l,FStar_Pervasives_Native.Some to_c) ->
             let r =
               let uu____7791 =
                 let uu____7792 = FStar_BigInt.to_int_fs from_l  in
                 let uu____7793 = FStar_BigInt.to_int_fs from_c  in
                 FStar_Range.mk_pos uu____7792 uu____7793  in
               let uu____7794 =
                 let uu____7795 = FStar_BigInt.to_int_fs to_l  in
                 let uu____7796 = FStar_BigInt.to_int_fs to_c  in
                 FStar_Range.mk_pos uu____7795 uu____7796  in
               FStar_Range.mk_range fn1 uu____7791 uu____7794  in
             let uu____7797 =
               FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_range
                 psc.psc_range r
                in
             FStar_Pervasives_Native.Some uu____7797
         | uu____7798 -> FStar_Pervasives_Native.None)
    | uu____7819 -> FStar_Pervasives_Native.None  in
  let decidable_eq neg psc args =
    let r = psc.psc_range  in
    let tru =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool true)) r
       in
    let fal =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool false)) r
       in
    match args with
    | (_typ,uu____7852)::(a1,uu____7854)::(a2,uu____7856)::[] ->
        let uu____7893 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____7893 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some (if neg then fal else tru)
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some (if neg then tru else fal)
         | uu____7898 -> FStar_Pervasives_Native.None)
    | uu____7899 -> failwith "Unexpected number of arguments"  in
  let prims_to_fstar_range_step psc args =
    match args with
    | (a1,uu____7930)::[] ->
        let uu____7939 =
          FStar_Syntax_Embeddings.try_unembed FStar_Syntax_Embeddings.e_range
            a1
           in
        (match uu____7939 with
         | FStar_Pervasives_Native.Some r ->
             let uu____7945 =
               FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_range
                 psc.psc_range r
                in
             FStar_Pervasives_Native.Some uu____7945
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
    | uu____7946 -> failwith "Unexpected number of arguments"  in
  let basic_ops =
    let uu____7972 =
      let uu____7989 =
        let uu____8006 =
          let uu____8023 =
            let uu____8040 =
              let uu____8057 =
                let uu____8074 =
                  let uu____8091 =
                    let uu____8108 =
                      let uu____8125 =
                        let uu____8142 =
                          let uu____8159 =
                            let uu____8176 =
                              let uu____8193 =
                                let uu____8210 =
                                  let uu____8227 =
                                    let uu____8244 =
                                      let uu____8261 =
                                        let uu____8278 =
                                          let uu____8295 =
                                            let uu____8312 =
                                              let uu____8329 =
                                                let uu____8344 =
                                                  FStar_Parser_Const.p2l
                                                    ["FStar";
                                                    "String";
                                                    "list_of_string"]
                                                   in
                                                (uu____8344,
                                                  (Prims.parse_int "1"),
                                                  (unary_op arg_as_string
                                                     list_of_string'))
                                                 in
                                              let uu____8353 =
                                                let uu____8370 =
                                                  let uu____8385 =
                                                    FStar_Parser_Const.p2l
                                                      ["FStar";
                                                      "String";
                                                      "string_of_list"]
                                                     in
                                                  (uu____8385,
                                                    (Prims.parse_int "1"),
                                                    (unary_op
                                                       (arg_as_list
                                                          FStar_Syntax_Embeddings.e_char)
                                                       string_of_list'))
                                                   in
                                                let uu____8398 =
                                                  let uu____8415 =
                                                    let uu____8430 =
                                                      FStar_Parser_Const.p2l
                                                        ["FStar";
                                                        "String";
                                                        "concat"]
                                                       in
                                                    (uu____8430,
                                                      (Prims.parse_int "2"),
                                                      string_concat')
                                                     in
                                                  let uu____8439 =
                                                    let uu____8456 =
                                                      let uu____8471 =
                                                        FStar_Parser_Const.p2l
                                                          ["Prims";
                                                          "mk_range"]
                                                         in
                                                      (uu____8471,
                                                        (Prims.parse_int "5"),
                                                        mk_range1)
                                                       in
                                                    [uu____8456]  in
                                                  uu____8415 :: uu____8439
                                                   in
                                                uu____8370 :: uu____8398  in
                                              uu____8329 :: uu____8353  in
                                            (FStar_Parser_Const.op_notEq,
                                              (Prims.parse_int "3"),
                                              (decidable_eq true)) ::
                                              uu____8312
                                             in
                                          (FStar_Parser_Const.op_Eq,
                                            (Prims.parse_int "3"),
                                            (decidable_eq false)) ::
                                            uu____8295
                                           in
                                        (FStar_Parser_Const.string_compare,
                                          (Prims.parse_int "2"),
                                          (binary_op arg_as_string
                                             string_compare'))
                                          :: uu____8278
                                         in
                                      (FStar_Parser_Const.string_of_bool_lid,
                                        (Prims.parse_int "1"),
                                        (unary_op arg_as_bool string_of_bool1))
                                        :: uu____8261
                                       in
                                    (FStar_Parser_Const.string_of_int_lid,
                                      (Prims.parse_int "1"),
                                      (unary_op arg_as_int string_of_int1))
                                      :: uu____8244
                                     in
                                  (FStar_Parser_Const.str_make_lid,
                                    (Prims.parse_int "2"),
                                    (mixed_binary_op arg_as_int arg_as_char
                                       (FStar_Syntax_Embeddings.embed
                                          FStar_Syntax_Embeddings.e_string)
                                       (fun r  ->
                                          fun x  ->
                                            fun y  ->
                                              let uu____8691 =
                                                FStar_BigInt.to_int_fs x  in
                                              FStar_String.make uu____8691 y)))
                                    :: uu____8227
                                   in
                                (FStar_Parser_Const.strcat_lid',
                                  (Prims.parse_int "2"),
                                  (binary_string_op
                                     (fun x  -> fun y  -> Prims.strcat x y)))
                                  :: uu____8210
                                 in
                              (FStar_Parser_Const.strcat_lid,
                                (Prims.parse_int "2"),
                                (binary_string_op
                                   (fun x  -> fun y  -> Prims.strcat x y)))
                                :: uu____8193
                               in
                            (FStar_Parser_Const.op_Or, (Prims.parse_int "2"),
                              (binary_bool_op (fun x  -> fun y  -> x || y)))
                              :: uu____8176
                             in
                          (FStar_Parser_Const.op_And, (Prims.parse_int "2"),
                            (binary_bool_op (fun x  -> fun y  -> x && y))) ::
                            uu____8159
                           in
                        (FStar_Parser_Const.op_Negation,
                          (Prims.parse_int "1"),
                          (unary_bool_op (fun x  -> Prims.op_Negation x))) ::
                          uu____8142
                         in
                      (FStar_Parser_Const.op_Modulus, (Prims.parse_int "2"),
                        (binary_int_op
                           (fun x  -> fun y  -> FStar_BigInt.mod_big_int x y)))
                        :: uu____8125
                       in
                    (FStar_Parser_Const.op_GTE, (Prims.parse_int "2"),
                      (binary_op arg_as_int
                         (fun r  ->
                            fun x  ->
                              fun y  ->
                                let uu____8886 = FStar_BigInt.ge_big_int x y
                                   in
                                FStar_Syntax_Embeddings.embed
                                  FStar_Syntax_Embeddings.e_bool r uu____8886)))
                      :: uu____8108
                     in
                  (FStar_Parser_Const.op_GT, (Prims.parse_int "2"),
                    (binary_op arg_as_int
                       (fun r  ->
                          fun x  ->
                            fun y  ->
                              let uu____8916 = FStar_BigInt.gt_big_int x y
                                 in
                              FStar_Syntax_Embeddings.embed
                                FStar_Syntax_Embeddings.e_bool r uu____8916)))
                    :: uu____8091
                   in
                (FStar_Parser_Const.op_LTE, (Prims.parse_int "2"),
                  (binary_op arg_as_int
                     (fun r  ->
                        fun x  ->
                          fun y  ->
                            let uu____8946 = FStar_BigInt.le_big_int x y  in
                            FStar_Syntax_Embeddings.embed
                              FStar_Syntax_Embeddings.e_bool r uu____8946)))
                  :: uu____8074
                 in
              (FStar_Parser_Const.op_LT, (Prims.parse_int "2"),
                (binary_op arg_as_int
                   (fun r  ->
                      fun x  ->
                        fun y  ->
                          let uu____8976 = FStar_BigInt.lt_big_int x y  in
                          FStar_Syntax_Embeddings.embed
                            FStar_Syntax_Embeddings.e_bool r uu____8976)))
                :: uu____8057
               in
            (FStar_Parser_Const.op_Division, (Prims.parse_int "2"),
              (binary_int_op
                 (fun x  -> fun y  -> FStar_BigInt.div_big_int x y)))
              :: uu____8040
             in
          (FStar_Parser_Const.op_Multiply, (Prims.parse_int "2"),
            (binary_int_op
               (fun x  -> fun y  -> FStar_BigInt.mult_big_int x y)))
            :: uu____8023
           in
        (FStar_Parser_Const.op_Subtraction, (Prims.parse_int "2"),
          (binary_int_op (fun x  -> fun y  -> FStar_BigInt.sub_big_int x y)))
          :: uu____8006
         in
      (FStar_Parser_Const.op_Addition, (Prims.parse_int "2"),
        (binary_int_op (fun x  -> fun y  -> FStar_BigInt.add_big_int x y)))
        :: uu____7989
       in
    (FStar_Parser_Const.op_Minus, (Prims.parse_int "1"),
      (unary_int_op (fun x  -> FStar_BigInt.minus_big_int x))) :: uu____7972
     in
  let weak_ops =
    let uu____9131 =
      let uu____9146 =
        FStar_Parser_Const.p2l ["FStar"; "Range"; "prims_to_fstar_range"]  in
      (uu____9146, (Prims.parse_int "1"), prims_to_fstar_range_step)  in
    [uu____9131]  in
  let bounded_arith_ops =
    let bounded_signed_int_types = ["Int8"; "Int16"; "Int32"; "Int64"]  in
    let bounded_unsigned_int_types =
      ["UInt8"; "UInt16"; "UInt32"; "UInt64"; "UInt128"]  in
    let int_as_bounded r int_to_t1 n1 =
      let c =
        FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_int r n1  in
      let int_to_t2 = FStar_Syntax_Syntax.fv_to_tm int_to_t1  in
      let uu____9226 =
        let uu____9231 =
          let uu____9232 = FStar_Syntax_Syntax.as_arg c  in [uu____9232]  in
        FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____9231  in
      uu____9226 FStar_Pervasives_Native.None r  in
    let add_sub_mul_v =
      FStar_All.pipe_right
        (FStar_List.append bounded_signed_int_types
           bounded_unsigned_int_types)
        (FStar_List.collect
           (fun m  ->
              let uu____9306 =
                let uu____9321 = FStar_Parser_Const.p2l ["FStar"; m; "add"]
                   in
                (uu____9321, (Prims.parse_int "2"),
                  (binary_op arg_as_bounded_int
                     (fun r  ->
                        fun uu____9343  ->
                          fun uu____9344  ->
                            match (uu____9343, uu____9344) with
                            | ((int_to_t1,x),(uu____9363,y)) ->
                                let uu____9373 = FStar_BigInt.add_big_int x y
                                   in
                                int_as_bounded r int_to_t1 uu____9373)))
                 in
              let uu____9374 =
                let uu____9391 =
                  let uu____9406 = FStar_Parser_Const.p2l ["FStar"; m; "sub"]
                     in
                  (uu____9406, (Prims.parse_int "2"),
                    (binary_op arg_as_bounded_int
                       (fun r  ->
                          fun uu____9428  ->
                            fun uu____9429  ->
                              match (uu____9428, uu____9429) with
                              | ((int_to_t1,x),(uu____9448,y)) ->
                                  let uu____9458 =
                                    FStar_BigInt.sub_big_int x y  in
                                  int_as_bounded r int_to_t1 uu____9458)))
                   in
                let uu____9459 =
                  let uu____9476 =
                    let uu____9491 =
                      FStar_Parser_Const.p2l ["FStar"; m; "mul"]  in
                    (uu____9491, (Prims.parse_int "2"),
                      (binary_op arg_as_bounded_int
                         (fun r  ->
                            fun uu____9513  ->
                              fun uu____9514  ->
                                match (uu____9513, uu____9514) with
                                | ((int_to_t1,x),(uu____9533,y)) ->
                                    let uu____9543 =
                                      FStar_BigInt.mult_big_int x y  in
                                    int_as_bounded r int_to_t1 uu____9543)))
                     in
                  let uu____9544 =
                    let uu____9561 =
                      let uu____9576 =
                        FStar_Parser_Const.p2l ["FStar"; m; "v"]  in
                      (uu____9576, (Prims.parse_int "1"),
                        (unary_op arg_as_bounded_int
                           (fun r  ->
                              fun uu____9594  ->
                                match uu____9594 with
                                | (int_to_t1,x) ->
                                    FStar_Syntax_Embeddings.embed
                                      FStar_Syntax_Embeddings.e_int r x)))
                       in
                    [uu____9561]  in
                  uu____9476 :: uu____9544  in
                uu____9391 :: uu____9459  in
              uu____9306 :: uu____9374))
       in
    let div_mod_unsigned =
      FStar_All.pipe_right bounded_unsigned_int_types
        (FStar_List.collect
           (fun m  ->
              let uu____9724 =
                let uu____9739 = FStar_Parser_Const.p2l ["FStar"; m; "div"]
                   in
                (uu____9739, (Prims.parse_int "2"),
                  (binary_op arg_as_bounded_int
                     (fun r  ->
                        fun uu____9761  ->
                          fun uu____9762  ->
                            match (uu____9761, uu____9762) with
                            | ((int_to_t1,x),(uu____9781,y)) ->
                                let uu____9791 = FStar_BigInt.div_big_int x y
                                   in
                                int_as_bounded r int_to_t1 uu____9791)))
                 in
              let uu____9792 =
                let uu____9809 =
                  let uu____9824 = FStar_Parser_Const.p2l ["FStar"; m; "rem"]
                     in
                  (uu____9824, (Prims.parse_int "2"),
                    (binary_op arg_as_bounded_int
                       (fun r  ->
                          fun uu____9846  ->
                            fun uu____9847  ->
                              match (uu____9846, uu____9847) with
                              | ((int_to_t1,x),(uu____9866,y)) ->
                                  let uu____9876 =
                                    FStar_BigInt.mod_big_int x y  in
                                  int_as_bounded r int_to_t1 uu____9876)))
                   in
                [uu____9809]  in
              uu____9724 :: uu____9792))
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
    | (_typ,uu____10006)::(a1,uu____10008)::(a2,uu____10010)::[] ->
        let uu____10047 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____10047 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___143_10051 = FStar_Syntax_Util.t_true  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___143_10051.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___143_10051.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___144_10053 = FStar_Syntax_Util.t_false  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___144_10053.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___144_10053.FStar_Syntax_Syntax.vars)
                })
         | uu____10054 -> FStar_Pervasives_Native.None)
    | (_typ,uu____10056)::uu____10057::(a1,uu____10059)::(a2,uu____10061)::[]
        ->
        let uu____10110 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____10110 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___143_10114 = FStar_Syntax_Util.t_true  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___143_10114.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___143_10114.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___144_10116 = FStar_Syntax_Util.t_false  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___144_10116.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___144_10116.FStar_Syntax_Syntax.vars)
                })
         | uu____10117 -> FStar_Pervasives_Native.None)
    | uu____10118 -> failwith "Unexpected number of arguments"  in
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
    let uu____10172 = FStar_ST.op_Bang unembed_binder_knot  in
    match uu____10172 with
    | FStar_Pervasives_Native.Some e -> FStar_Syntax_Embeddings.unembed e t
    | FStar_Pervasives_Native.None  ->
        (FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos
           (FStar_Errors.Warning_UnembedBinderKnot,
             "unembed_binder_knot is unset!");
         FStar_Pervasives_Native.None)
  
let mk_psc_subst :
  'Auu____10224 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____10224) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_Syntax_Syntax.subst_elt Prims.list
  =
  fun cfg  ->
    fun env  ->
      FStar_List.fold_right
        (fun uu____10286  ->
           fun subst1  ->
             match uu____10286 with
             | (binder_opt,closure) ->
                 (match (binder_opt, closure) with
                  | (FStar_Pervasives_Native.Some b,Clos
                     (env1,term,uu____10327,uu____10328)) ->
                      let uu____10387 = b  in
                      (match uu____10387 with
                       | (bv,uu____10395) ->
                           let uu____10396 =
                             let uu____10397 =
                               FStar_Syntax_Util.is_constructed_typ
                                 bv.FStar_Syntax_Syntax.sort
                                 FStar_Parser_Const.binder_lid
                                in
                             Prims.op_Negation uu____10397  in
                           if uu____10396
                           then subst1
                           else
                             (let term1 = closure_as_term cfg env1 term  in
                              let uu____10402 = unembed_binder term1  in
                              match uu____10402 with
                              | FStar_Pervasives_Native.None  -> subst1
                              | FStar_Pervasives_Native.Some x ->
                                  let b1 =
                                    let uu____10409 =
                                      let uu___145_10410 = bv  in
                                      let uu____10411 =
                                        FStar_Syntax_Subst.subst subst1
                                          (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort
                                         in
                                      {
                                        FStar_Syntax_Syntax.ppname =
                                          (uu___145_10410.FStar_Syntax_Syntax.ppname);
                                        FStar_Syntax_Syntax.index =
                                          (uu___145_10410.FStar_Syntax_Syntax.index);
                                        FStar_Syntax_Syntax.sort =
                                          uu____10411
                                      }  in
                                    FStar_Syntax_Syntax.freshen_bv
                                      uu____10409
                                     in
                                  let b_for_x =
                                    let uu____10415 =
                                      let uu____10422 =
                                        FStar_Syntax_Syntax.bv_to_name b1  in
                                      ((FStar_Pervasives_Native.fst x),
                                        uu____10422)
                                       in
                                    FStar_Syntax_Syntax.NT uu____10415  in
                                  let subst2 =
                                    FStar_List.filter
                                      (fun uu___87_10436  ->
                                         match uu___87_10436 with
                                         | FStar_Syntax_Syntax.NT
                                             (uu____10437,{
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_name
                                                              b';
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____10439;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____10440;_})
                                             ->
                                             let uu____10445 =
                                               FStar_Ident.ident_equals
                                                 b1.FStar_Syntax_Syntax.ppname
                                                 b'.FStar_Syntax_Syntax.ppname
                                                in
                                             Prims.op_Negation uu____10445
                                         | uu____10446 -> true) subst1
                                     in
                                  b_for_x :: subst2))
                  | uu____10447 -> subst1)) env []
  
let reduce_primops :
  'Auu____10470 'Auu____10471 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____10470) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____10471 ->
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
            (let uu____10519 = FStar_Syntax_Util.head_and_args tm  in
             match uu____10519 with
             | (head1,args) ->
                 let uu____10552 =
                   let uu____10553 = FStar_Syntax_Util.un_uinst head1  in
                   uu____10553.FStar_Syntax_Syntax.n  in
                 (match uu____10552 with
                  | FStar_Syntax_Syntax.Tm_fvar fv ->
                      let uu____10559 = find_prim_step cfg fv  in
                      (match uu____10559 with
                       | FStar_Pervasives_Native.Some prim_step when
                           prim_step.strong_reduction_ok ||
                             (Prims.op_Negation cfg.strong)
                           ->
                           let l = FStar_List.length args  in
                           if l < prim_step.arity
                           then
                             (log_primops cfg
                                (fun uu____10585  ->
                                   let uu____10586 =
                                     FStar_Syntax_Print.lid_to_string
                                       prim_step.name
                                      in
                                   let uu____10587 =
                                     FStar_Util.string_of_int l  in
                                   let uu____10594 =
                                     FStar_Util.string_of_int prim_step.arity
                                      in
                                   FStar_Util.print3
                                     "primop: found partially applied %s (%s/%s args)\n"
                                     uu____10586 uu____10587 uu____10594);
                              tm)
                           else
                             (let uu____10596 =
                                if l = prim_step.arity
                                then (args, [])
                                else FStar_List.splitAt prim_step.arity args
                                 in
                              match uu____10596 with
                              | (args_1,args_2) ->
                                  (log_primops cfg
                                     (fun uu____10710  ->
                                        let uu____10711 =
                                          FStar_Syntax_Print.term_to_string
                                            tm
                                           in
                                        FStar_Util.print1
                                          "primop: trying to reduce <%s>\n"
                                          uu____10711);
                                   (let psc =
                                      {
                                        psc_range =
                                          (head1.FStar_Syntax_Syntax.pos);
                                        psc_subst =
                                          (fun uu____10714  ->
                                             if
                                               prim_step.requires_binder_substitution
                                             then mk_psc_subst cfg env
                                             else [])
                                      }  in
                                    let uu____10716 =
                                      prim_step.interpretation psc args_1  in
                                    match uu____10716 with
                                    | FStar_Pervasives_Native.None  ->
                                        (log_primops cfg
                                           (fun uu____10724  ->
                                              let uu____10725 =
                                                FStar_Syntax_Print.term_to_string
                                                  tm
                                                 in
                                              FStar_Util.print1
                                                "primop: <%s> did not reduce\n"
                                                uu____10725);
                                         tm)
                                    | FStar_Pervasives_Native.Some reduced ->
                                        (log_primops cfg
                                           (fun uu____10731  ->
                                              let uu____10732 =
                                                FStar_Syntax_Print.term_to_string
                                                  tm
                                                 in
                                              let uu____10733 =
                                                FStar_Syntax_Print.term_to_string
                                                  reduced
                                                 in
                                              FStar_Util.print2
                                                "primop: <%s> reduced to <%s>\n"
                                                uu____10732 uu____10733);
                                         FStar_Syntax_Util.mk_app reduced
                                           args_2))))
                       | FStar_Pervasives_Native.Some uu____10734 ->
                           (log_primops cfg
                              (fun uu____10738  ->
                                 let uu____10739 =
                                   FStar_Syntax_Print.term_to_string tm  in
                                 FStar_Util.print1
                                   "primop: not reducing <%s> since we're doing strong reduction\n"
                                   uu____10739);
                            tm)
                       | FStar_Pervasives_Native.None  -> tm)
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_range_of ) when
                      Prims.op_Negation cfg.strong ->
                      (log_primops cfg
                         (fun uu____10743  ->
                            let uu____10744 =
                              FStar_Syntax_Print.term_to_string tm  in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____10744);
                       (match args with
                        | (a1,uu____10748)::[] ->
                            FStar_Syntax_Embeddings.embed
                              FStar_Syntax_Embeddings.e_range
                              tm.FStar_Syntax_Syntax.pos
                              a1.FStar_Syntax_Syntax.pos
                        | uu____10765 -> tm))
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_set_range_of ) when
                      Prims.op_Negation cfg.strong ->
                      (log_primops cfg
                         (fun uu____10777  ->
                            let uu____10778 =
                              FStar_Syntax_Print.term_to_string tm  in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____10778);
                       (match args with
                        | (t,uu____10782)::(r,uu____10784)::[] ->
                            let uu____10811 =
                              FStar_Syntax_Embeddings.unembed
                                FStar_Syntax_Embeddings.e_range r
                               in
                            (match uu____10811 with
                             | FStar_Pervasives_Native.Some rng ->
                                 let uu___146_10817 = t  in
                                 {
                                   FStar_Syntax_Syntax.n =
                                     (uu___146_10817.FStar_Syntax_Syntax.n);
                                   FStar_Syntax_Syntax.pos = rng;
                                   FStar_Syntax_Syntax.vars =
                                     (uu___146_10817.FStar_Syntax_Syntax.vars)
                                 }
                             | FStar_Pervasives_Native.None  -> tm)
                        | uu____10820 -> tm))
                  | uu____10829 -> tm))
  
let reduce_equality :
  'Auu____10840 'Auu____10841 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____10840) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____10841 ->
          FStar_Syntax_Syntax.term ->
            FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun cfg  ->
    fun tm  ->
      reduce_primops
        (let uu___147_10887 = cfg  in
         {
           steps =
             (let uu___148_10890 = default_steps  in
              {
                beta = (uu___148_10890.beta);
                iota = (uu___148_10890.iota);
                zeta = (uu___148_10890.zeta);
                weak = (uu___148_10890.weak);
                hnf = (uu___148_10890.hnf);
                primops = true;
                do_not_unfold_pure_lets =
                  (uu___148_10890.do_not_unfold_pure_lets);
                unfold_until = (uu___148_10890.unfold_until);
                unfold_only = (uu___148_10890.unfold_only);
                unfold_fully = (uu___148_10890.unfold_fully);
                unfold_attr = (uu___148_10890.unfold_attr);
                unfold_tac = (uu___148_10890.unfold_tac);
                pure_subterms_within_computations =
                  (uu___148_10890.pure_subterms_within_computations);
                simplify = (uu___148_10890.simplify);
                erase_universes = (uu___148_10890.erase_universes);
                allow_unbound_universes =
                  (uu___148_10890.allow_unbound_universes);
                reify_ = (uu___148_10890.reify_);
                compress_uvars = (uu___148_10890.compress_uvars);
                no_full_norm = (uu___148_10890.no_full_norm);
                check_no_uvars = (uu___148_10890.check_no_uvars);
                unmeta = (uu___148_10890.unmeta);
                unascribe = (uu___148_10890.unascribe);
                in_full_norm_request = (uu___148_10890.in_full_norm_request);
                weakly_reduce_scrutinee =
                  (uu___148_10890.weakly_reduce_scrutinee)
              });
           tcenv = (uu___147_10887.tcenv);
           debug = (uu___147_10887.debug);
           delta_level = (uu___147_10887.delta_level);
           primitive_steps = equality_ops;
           strong = (uu___147_10887.strong);
           memoize_lazy = (uu___147_10887.memoize_lazy);
           normalize_pure_lets = (uu___147_10887.normalize_pure_lets)
         }) tm
  
let is_norm_request :
  'Auu____10897 .
    FStar_Syntax_Syntax.term -> 'Auu____10897 Prims.list -> Prims.bool
  =
  fun hd1  ->
    fun args  ->
      let uu____10912 =
        let uu____10919 =
          let uu____10920 = FStar_Syntax_Util.un_uinst hd1  in
          uu____10920.FStar_Syntax_Syntax.n  in
        (uu____10919, args)  in
      match uu____10912 with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____10926::uu____10927::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____10931::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize
      | (FStar_Syntax_Syntax.Tm_fvar fv,steps::uu____10936::uu____10937::[])
          -> FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm
      | uu____10940 -> false
  
let (tr_norm_step : FStar_Syntax_Embeddings.norm_step -> step Prims.list) =
  fun uu___88_10953  ->
    match uu___88_10953 with
    | FStar_Syntax_Embeddings.Zeta  -> [Zeta]
    | FStar_Syntax_Embeddings.Iota  -> [Iota]
    | FStar_Syntax_Embeddings.Delta  ->
        [UnfoldUntil FStar_Syntax_Syntax.Delta_constant]
    | FStar_Syntax_Embeddings.Simpl  -> [Simplify]
    | FStar_Syntax_Embeddings.Weak  -> [Weak]
    | FStar_Syntax_Embeddings.HNF  -> [HNF]
    | FStar_Syntax_Embeddings.Primops  -> [Primops]
    | FStar_Syntax_Embeddings.UnfoldOnly names1 ->
        let uu____10959 =
          let uu____10962 =
            let uu____10963 = FStar_List.map FStar_Ident.lid_of_str names1
               in
            UnfoldOnly uu____10963  in
          [uu____10962]  in
        (UnfoldUntil FStar_Syntax_Syntax.Delta_constant) :: uu____10959
    | FStar_Syntax_Embeddings.UnfoldFully names1 ->
        let uu____10969 =
          let uu____10972 =
            let uu____10973 = FStar_List.map FStar_Ident.lid_of_str names1
               in
            UnfoldFully uu____10973  in
          [uu____10972]  in
        (UnfoldUntil FStar_Syntax_Syntax.Delta_constant) :: uu____10969
    | FStar_Syntax_Embeddings.UnfoldAttr t ->
        [UnfoldUntil FStar_Syntax_Syntax.Delta_constant; UnfoldAttr t]
  
let (tr_norm_steps :
  FStar_Syntax_Embeddings.norm_step Prims.list -> step Prims.list) =
  fun s  -> FStar_List.concatMap tr_norm_step s 
let get_norm_request :
  'Auu____10994 .
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
      (FStar_Syntax_Syntax.term,'Auu____10994) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (step Prims.list,FStar_Syntax_Syntax.term)
          FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun full_norm  ->
    fun args  ->
      let parse_steps s =
        let uu____11040 =
          let uu____11045 =
            FStar_Syntax_Embeddings.e_list
              FStar_Syntax_Embeddings.e_norm_step
             in
          FStar_Syntax_Embeddings.try_unembed uu____11045 s  in
        match uu____11040 with
        | FStar_Pervasives_Native.Some steps ->
            let uu____11061 = tr_norm_steps steps  in
            FStar_Pervasives_Native.Some uu____11061
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None  in
      match args with
      | uu____11078::(tm,uu____11080)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify]  in
          FStar_Pervasives_Native.Some (s, tm)
      | (tm,uu____11109)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify]  in
          FStar_Pervasives_Native.Some (s, tm)
      | (steps,uu____11130)::uu____11131::(tm,uu____11133)::[] ->
          let add_exclude s z =
            if FStar_List.contains z s then s else (Exclude z) :: s  in
          let uu____11174 =
            let uu____11179 = full_norm steps  in parse_steps uu____11179  in
          (match uu____11174 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some s ->
               let s1 = Beta :: s  in
               let s2 = add_exclude s1 Zeta  in
               let s3 = add_exclude s2 Iota  in
               FStar_Pervasives_Native.Some (s3, tm))
      | uu____11218 -> FStar_Pervasives_Native.None
  
let (is_reify_head : stack_elt Prims.list -> Prims.bool) =
  fun uu___89_11237  ->
    match uu___89_11237 with
    | (App
        (uu____11240,{
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reify );
                       FStar_Syntax_Syntax.pos = uu____11241;
                       FStar_Syntax_Syntax.vars = uu____11242;_},uu____11243,uu____11244))::uu____11245
        -> true
    | uu____11250 -> false
  
let firstn :
  'Auu____11259 .
    Prims.int ->
      'Auu____11259 Prims.list ->
        ('Auu____11259 Prims.list,'Auu____11259 Prims.list)
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
          (uu____11301,{
                         FStar_Syntax_Syntax.n =
                           FStar_Syntax_Syntax.Tm_constant
                           (FStar_Const.Const_reify );
                         FStar_Syntax_Syntax.pos = uu____11302;
                         FStar_Syntax_Syntax.vars = uu____11303;_},uu____11304,uu____11305))::uu____11306
          -> (cfg.steps).reify_
      | uu____11311 -> false
  
let rec (maybe_weakly_reduced :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun tm  ->
    let aux_comp c =
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.GTotal (t,uu____11334) -> maybe_weakly_reduced t
      | FStar_Syntax_Syntax.Total (t,uu____11344) -> maybe_weakly_reduced t
      | FStar_Syntax_Syntax.Comp ct ->
          (maybe_weakly_reduced ct.FStar_Syntax_Syntax.result_typ) ||
            (FStar_Util.for_some
               (fun uu____11363  ->
                  match uu____11363 with
                  | (a,uu____11371) -> maybe_weakly_reduced a)
               ct.FStar_Syntax_Syntax.effect_args)
       in
    let t = FStar_Syntax_Subst.compress tm  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____11377 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_name uu____11402 -> false
    | FStar_Syntax_Syntax.Tm_uvar uu____11403 -> false
    | FStar_Syntax_Syntax.Tm_type uu____11404 -> false
    | FStar_Syntax_Syntax.Tm_bvar uu____11405 -> false
    | FStar_Syntax_Syntax.Tm_fvar uu____11406 -> false
    | FStar_Syntax_Syntax.Tm_constant uu____11407 -> false
    | FStar_Syntax_Syntax.Tm_lazy uu____11408 -> false
    | FStar_Syntax_Syntax.Tm_unknown  -> false
    | FStar_Syntax_Syntax.Tm_uinst uu____11409 -> false
    | FStar_Syntax_Syntax.Tm_quoted uu____11416 -> false
    | FStar_Syntax_Syntax.Tm_let uu____11423 -> true
    | FStar_Syntax_Syntax.Tm_abs uu____11436 -> true
    | FStar_Syntax_Syntax.Tm_arrow uu____11453 -> true
    | FStar_Syntax_Syntax.Tm_refine uu____11466 -> true
    | FStar_Syntax_Syntax.Tm_match uu____11473 -> true
    | FStar_Syntax_Syntax.Tm_app (t1,args) ->
        (maybe_weakly_reduced t1) ||
          (FStar_All.pipe_right args
             (FStar_Util.for_some
                (fun uu____11535  ->
                   match uu____11535 with
                   | (a,uu____11543) -> maybe_weakly_reduced a)))
    | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,uu____11550) ->
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
                     (fun uu____11672  ->
                        match uu____11672 with
                        | (a,uu____11680) -> maybe_weakly_reduced a)) args
            | FStar_Syntax_Syntax.Meta_monadic_lift
                (uu____11685,uu____11686,t') -> maybe_weakly_reduced t'
            | FStar_Syntax_Syntax.Meta_monadic (uu____11692,t') ->
                maybe_weakly_reduced t'
            | FStar_Syntax_Syntax.Meta_labeled uu____11698 -> false
            | FStar_Syntax_Syntax.Meta_desugared uu____11705 -> false
            | FStar_Syntax_Syntax.Meta_named uu____11706 -> false))
  
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
               | FStar_Syntax_Syntax.Tm_delayed uu____11998 ->
                   let uu____12023 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print1 "NORM delayed: %s\n" uu____12023
               | uu____12024 -> ())
            else ();
            FStar_Syntax_Subst.compress t  in
          log cfg
            (fun uu____12032  ->
               let uu____12033 = FStar_Syntax_Print.tag_of_term t1  in
               let uu____12034 = FStar_Syntax_Print.term_to_string t1  in
               let uu____12035 =
                 FStar_Util.string_of_int (FStar_List.length env)  in
               let uu____12042 =
                 let uu____12043 =
                   let uu____12046 = firstn (Prims.parse_int "4") stack  in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____12046
                    in
                 stack_to_string uu____12043  in
               FStar_Util.print4
                 ">>> %s\nNorm %s with with %s env elements top of the stack %s \n"
                 uu____12033 uu____12034 uu____12035 uu____12042);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_constant uu____12069 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_name uu____12070 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_lazy uu____12071 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____12072;
                 FStar_Syntax_Syntax.fv_delta =
                   FStar_Syntax_Syntax.Delta_constant ;
                 FStar_Syntax_Syntax.fv_qual = uu____12073;_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____12076;
                 FStar_Syntax_Syntax.fv_delta = uu____12077;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Data_ctor );_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____12078;
                 FStar_Syntax_Syntax.fv_delta = uu____12079;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor uu____12080);_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_quoted uu____12087 ->
               let uu____12094 = closure_as_term cfg env t1  in
               rebuild cfg env stack uu____12094
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               ((Prims.op_Negation (cfg.steps).no_full_norm) &&
                  (is_norm_request hd1 args))
                 &&
                 (let uu____12124 =
                    FStar_Ident.lid_equals
                      (cfg.tcenv).FStar_TypeChecker_Env.curmodule
                      FStar_Parser_Const.prims_lid
                     in
                  Prims.op_Negation uu____12124)
               ->
               let cfg' =
                 let uu___149_12126 = cfg  in
                 {
                   steps =
                     (let uu___150_12129 = cfg.steps  in
                      {
                        beta = (uu___150_12129.beta);
                        iota = (uu___150_12129.iota);
                        zeta = (uu___150_12129.zeta);
                        weak = (uu___150_12129.weak);
                        hnf = (uu___150_12129.hnf);
                        primops = (uu___150_12129.primops);
                        do_not_unfold_pure_lets = false;
                        unfold_until = (uu___150_12129.unfold_until);
                        unfold_only = FStar_Pervasives_Native.None;
                        unfold_fully = FStar_Pervasives_Native.None;
                        unfold_attr = (uu___150_12129.unfold_attr);
                        unfold_tac = (uu___150_12129.unfold_tac);
                        pure_subterms_within_computations =
                          (uu___150_12129.pure_subterms_within_computations);
                        simplify = (uu___150_12129.simplify);
                        erase_universes = (uu___150_12129.erase_universes);
                        allow_unbound_universes =
                          (uu___150_12129.allow_unbound_universes);
                        reify_ = (uu___150_12129.reify_);
                        compress_uvars = (uu___150_12129.compress_uvars);
                        no_full_norm = (uu___150_12129.no_full_norm);
                        check_no_uvars = (uu___150_12129.check_no_uvars);
                        unmeta = (uu___150_12129.unmeta);
                        unascribe = (uu___150_12129.unascribe);
                        in_full_norm_request =
                          (uu___150_12129.in_full_norm_request);
                        weakly_reduce_scrutinee =
                          (uu___150_12129.weakly_reduce_scrutinee)
                      });
                   tcenv = (uu___149_12126.tcenv);
                   debug = (uu___149_12126.debug);
                   delta_level =
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.Delta_constant];
                   primitive_steps = (uu___149_12126.primitive_steps);
                   strong = (uu___149_12126.strong);
                   memoize_lazy = (uu___149_12126.memoize_lazy);
                   normalize_pure_lets = true
                 }  in
               let uu____12134 = get_norm_request (norm cfg' env []) args  in
               (match uu____12134 with
                | FStar_Pervasives_Native.None  ->
                    let stack1 =
                      FStar_All.pipe_right stack
                        (FStar_List.fold_right
                           (fun uu____12163  ->
                              fun stack1  ->
                                match uu____12163 with
                                | (a,aq) ->
                                    let uu____12175 =
                                      let uu____12176 =
                                        let uu____12183 =
                                          let uu____12184 =
                                            let uu____12215 =
                                              FStar_Util.mk_ref
                                                FStar_Pervasives_Native.None
                                               in
                                            (env, a, uu____12215, false)  in
                                          Clos uu____12184  in
                                        (uu____12183, aq,
                                          (t1.FStar_Syntax_Syntax.pos))
                                         in
                                      Arg uu____12176  in
                                    uu____12175 :: stack1) args)
                       in
                    (log cfg
                       (fun uu____12303  ->
                          let uu____12304 =
                            FStar_All.pipe_left FStar_Util.string_of_int
                              (FStar_List.length args)
                             in
                          FStar_Util.print1 "\tPushed %s arguments\n"
                            uu____12304);
                     norm cfg env stack1 hd1)
                | FStar_Pervasives_Native.Some (s,tm) ->
                    let delta_level =
                      let uu____12326 =
                        FStar_All.pipe_right s
                          (FStar_Util.for_some
                             (fun uu___90_12331  ->
                                match uu___90_12331 with
                                | UnfoldUntil uu____12332 -> true
                                | UnfoldOnly uu____12333 -> true
                                | UnfoldFully uu____12336 -> true
                                | uu____12339 -> false))
                         in
                      if uu____12326
                      then
                        [FStar_TypeChecker_Env.Unfold
                           FStar_Syntax_Syntax.Delta_constant]
                      else [FStar_TypeChecker_Env.NoDelta]  in
                    let cfg'1 =
                      let uu___151_12344 = cfg  in
                      let uu____12345 =
                        let uu___152_12346 = to_fsteps s  in
                        {
                          beta = (uu___152_12346.beta);
                          iota = (uu___152_12346.iota);
                          zeta = (uu___152_12346.zeta);
                          weak = (uu___152_12346.weak);
                          hnf = (uu___152_12346.hnf);
                          primops = (uu___152_12346.primops);
                          do_not_unfold_pure_lets =
                            (uu___152_12346.do_not_unfold_pure_lets);
                          unfold_until = (uu___152_12346.unfold_until);
                          unfold_only = (uu___152_12346.unfold_only);
                          unfold_fully = (uu___152_12346.unfold_fully);
                          unfold_attr = (uu___152_12346.unfold_attr);
                          unfold_tac = (uu___152_12346.unfold_tac);
                          pure_subterms_within_computations =
                            (uu___152_12346.pure_subterms_within_computations);
                          simplify = (uu___152_12346.simplify);
                          erase_universes = (uu___152_12346.erase_universes);
                          allow_unbound_universes =
                            (uu___152_12346.allow_unbound_universes);
                          reify_ = (uu___152_12346.reify_);
                          compress_uvars = (uu___152_12346.compress_uvars);
                          no_full_norm = (uu___152_12346.no_full_norm);
                          check_no_uvars = (uu___152_12346.check_no_uvars);
                          unmeta = (uu___152_12346.unmeta);
                          unascribe = (uu___152_12346.unascribe);
                          in_full_norm_request = true;
                          weakly_reduce_scrutinee =
                            (uu___152_12346.weakly_reduce_scrutinee)
                        }  in
                      {
                        steps = uu____12345;
                        tcenv = (uu___151_12344.tcenv);
                        debug = (uu___151_12344.debug);
                        delta_level;
                        primitive_steps = (uu___151_12344.primitive_steps);
                        strong = (uu___151_12344.strong);
                        memoize_lazy = (uu___151_12344.memoize_lazy);
                        normalize_pure_lets = true
                      }  in
                    let stack' =
                      let tail1 = (Cfg cfg) :: stack  in
                      if (cfg.debug).print_normalized
                      then
                        let uu____12355 =
                          let uu____12356 =
                            let uu____12361 = FStar_Util.now ()  in
                            (t1, uu____12361)  in
                          Debug uu____12356  in
                        uu____12355 :: tail1
                      else tail1  in
                    norm cfg'1 env stack' tm)
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u  in
               let uu____12365 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack uu____12365
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               if (cfg.steps).erase_universes
               then norm cfg env stack t'
               else
                 (let us1 =
                    let uu____12374 =
                      let uu____12381 =
                        FStar_List.map (norm_universe cfg env) us  in
                      (uu____12381, (t1.FStar_Syntax_Syntax.pos))  in
                    UnivArgs uu____12374  in
                  let stack1 = us1 :: stack  in norm cfg env stack1 t')
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let qninfo =
                 let uu____12391 = FStar_Syntax_Syntax.lid_of_fv fv  in
                 FStar_TypeChecker_Env.lookup_qname cfg.tcenv uu____12391  in
               let uu____12392 =
                 FStar_TypeChecker_Env.qninfo_is_action qninfo  in
               if uu____12392
               then
                 let b = should_reify cfg stack  in
                 (log cfg
                    (fun uu____12398  ->
                       let uu____12399 = FStar_Syntax_Print.term_to_string t1
                          in
                       let uu____12400 = FStar_Util.string_of_bool b  in
                       FStar_Util.print2
                         ">>> For DM4F action %s, should_reify = %s\n"
                         uu____12399 uu____12400);
                  if b
                  then
                    (let uu____12401 = FStar_List.tl stack  in
                     do_unfold_fv cfg env uu____12401 t1 qninfo fv)
                  else rebuild cfg env stack t1)
               else
                 (let should_delta =
                    ((let uu____12409 = find_prim_step cfg fv  in
                      FStar_Option.isNone uu____12409) &&
                       (match qninfo with
                        | FStar_Pervasives_Native.Some
                            (FStar_Util.Inr
                             ({
                                FStar_Syntax_Syntax.sigel =
                                  FStar_Syntax_Syntax.Sig_let
                                  ((is_rec,uu____12422),uu____12423);
                                FStar_Syntax_Syntax.sigrng = uu____12424;
                                FStar_Syntax_Syntax.sigquals = qs;
                                FStar_Syntax_Syntax.sigmeta = uu____12426;
                                FStar_Syntax_Syntax.sigattrs = uu____12427;_},uu____12428),uu____12429)
                            ->
                            (Prims.op_Negation
                               (FStar_List.contains
                                  FStar_Syntax_Syntax.HasMaskedEffect qs))
                              &&
                              ((Prims.op_Negation is_rec) || (cfg.steps).zeta)
                        | uu____12488 -> true))
                      &&
                      (FStar_All.pipe_right cfg.delta_level
                         (FStar_Util.for_some
                            (fun uu___91_12492  ->
                               match uu___91_12492 with
                               | FStar_TypeChecker_Env.UnfoldTac  -> false
                               | FStar_TypeChecker_Env.NoDelta  -> false
                               | FStar_TypeChecker_Env.Inlining  -> true
                               | FStar_TypeChecker_Env.Eager_unfolding_only 
                                   -> true
                               | FStar_TypeChecker_Env.Unfold l ->
                                   FStar_TypeChecker_Common.delta_depth_greater_than
                                     fv.FStar_Syntax_Syntax.fv_delta l)))
                     in
                  let should_delta1 =
                    should_delta &&
                      (let attrs =
                         FStar_TypeChecker_Env.attrs_of_qninfo qninfo  in
                       ((Prims.op_Negation (cfg.steps).unfold_tac) ||
                          (let uu____12502 =
                             cases
                               (FStar_Util.for_some
                                  (FStar_Syntax_Util.attr_eq
                                     FStar_Syntax_Util.tac_opaque_attr))
                               false attrs
                              in
                           Prims.op_Negation uu____12502))
                         &&
                         ((match (cfg.steps).unfold_only with
                           | FStar_Pervasives_Native.None  -> true
                           | FStar_Pervasives_Native.Some lids ->
                               FStar_Util.for_some
                                 (FStar_Syntax_Syntax.fv_eq_lid fv) lids)
                            ||
                            (match (attrs, ((cfg.steps).unfold_attr)) with
                             | (FStar_Pervasives_Native.None
                                ,FStar_Pervasives_Native.Some uu____12521) ->
                                 false
                             | (FStar_Pervasives_Native.Some
                                ats,FStar_Pervasives_Native.Some ats') ->
                                 FStar_Util.for_some
                                   (fun at  ->
                                      FStar_Util.for_some
                                        (FStar_Syntax_Util.attr_eq at) ats')
                                   ats
                             | (uu____12556,uu____12557) -> false)))
                     in
                  let uu____12574 =
                    match (cfg.steps).unfold_fully with
                    | FStar_Pervasives_Native.None  -> (should_delta1, false)
                    | FStar_Pervasives_Native.Some lids ->
                        let uu____12590 =
                          FStar_Util.for_some
                            (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                           in
                        if uu____12590 then (true, true) else (false, false)
                     in
                  match uu____12574 with
                  | (should_delta2,fully) ->
                      (log cfg
                         (fun uu____12603  ->
                            let uu____12604 =
                              FStar_Syntax_Print.term_to_string t1  in
                            let uu____12605 =
                              FStar_Range.string_of_range
                                t1.FStar_Syntax_Syntax.pos
                               in
                            let uu____12606 =
                              FStar_Util.string_of_bool should_delta2  in
                            FStar_Util.print3
                              ">>> For %s (%s), should_delta = %s\n"
                              uu____12604 uu____12605 uu____12606);
                       if should_delta2
                       then
                         (let uu____12607 =
                            if fully
                            then
                              (((Cfg cfg) :: stack),
                                (let uu___153_12617 = cfg  in
                                 {
                                   steps =
                                     (let uu___154_12620 = cfg.steps  in
                                      {
                                        beta = (uu___154_12620.beta);
                                        iota = false;
                                        zeta = false;
                                        weak = false;
                                        hnf = false;
                                        primops = false;
                                        do_not_unfold_pure_lets =
                                          (uu___154_12620.do_not_unfold_pure_lets);
                                        unfold_until =
                                          (FStar_Pervasives_Native.Some
                                             FStar_Syntax_Syntax.Delta_constant);
                                        unfold_only =
                                          FStar_Pervasives_Native.None;
                                        unfold_fully =
                                          FStar_Pervasives_Native.None;
                                        unfold_attr =
                                          (uu___154_12620.unfold_attr);
                                        unfold_tac =
                                          (uu___154_12620.unfold_tac);
                                        pure_subterms_within_computations =
                                          (uu___154_12620.pure_subterms_within_computations);
                                        simplify = false;
                                        erase_universes =
                                          (uu___154_12620.erase_universes);
                                        allow_unbound_universes =
                                          (uu___154_12620.allow_unbound_universes);
                                        reify_ = (uu___154_12620.reify_);
                                        compress_uvars =
                                          (uu___154_12620.compress_uvars);
                                        no_full_norm =
                                          (uu___154_12620.no_full_norm);
                                        check_no_uvars =
                                          (uu___154_12620.check_no_uvars);
                                        unmeta = (uu___154_12620.unmeta);
                                        unascribe =
                                          (uu___154_12620.unascribe);
                                        in_full_norm_request =
                                          (uu___154_12620.in_full_norm_request);
                                        weakly_reduce_scrutinee =
                                          (uu___154_12620.weakly_reduce_scrutinee)
                                      });
                                   tcenv = (uu___153_12617.tcenv);
                                   debug = (uu___153_12617.debug);
                                   delta_level = (uu___153_12617.delta_level);
                                   primitive_steps =
                                     (uu___153_12617.primitive_steps);
                                   strong = (uu___153_12617.strong);
                                   memoize_lazy =
                                     (uu___153_12617.memoize_lazy);
                                   normalize_pure_lets =
                                     (uu___153_12617.normalize_pure_lets)
                                 }))
                            else (stack, cfg)  in
                          match uu____12607 with
                          | (stack1,cfg1) ->
                              do_unfold_fv cfg1 env stack1 t1 qninfo fv)
                       else rebuild cfg env stack t1))
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____12630 = lookup_bvar env x  in
               (match uu____12630 with
                | Univ uu____12631 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if (Prims.op_Negation fix) || (cfg.steps).zeta
                    then
                      let uu____12680 = FStar_ST.op_Bang r  in
                      (match uu____12680 with
                       | FStar_Pervasives_Native.Some (env2,t') ->
                           (log cfg
                              (fun uu____12802  ->
                                 let uu____12803 =
                                   FStar_Syntax_Print.term_to_string t1  in
                                 let uu____12804 =
                                   FStar_Syntax_Print.term_to_string t'  in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____12803
                                   uu____12804);
                            (let uu____12805 = maybe_weakly_reduced t'  in
                             if uu____12805
                             then
                               match stack with
                               | [] when
                                   (cfg.steps).weak ||
                                     (cfg.steps).compress_uvars
                                   -> rebuild cfg env2 stack t'
                               | uu____12806 -> norm cfg env2 stack t'
                             else rebuild cfg env2 stack t'))
                       | FStar_Pervasives_Native.None  ->
                           norm cfg env1 ((MemoLazy r) :: stack) t0)
                    else norm cfg env1 stack t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack with
                | (UnivArgs uu____12877)::uu____12878 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Match uu____12887)::uu____12888 ->
                    failwith
                      "Ill-typed term: cannot pattern match an abstraction"
                | (Arg (c,uu____12900,uu____12901))::stack_rest ->
                    (match c with
                     | Univ uu____12905 ->
                         norm cfg ((FStar_Pervasives_Native.None, c) :: env)
                           stack_rest t1
                     | uu____12914 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | b::[] ->
                              (log cfg
                                 (fun uu____12935  ->
                                    let uu____12936 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____12936);
                               norm cfg
                                 (((FStar_Pervasives_Native.Some b), c) ::
                                 env) stack_rest body)
                          | b::tl1 ->
                              (log cfg
                                 (fun uu____12964  ->
                                    let uu____12965 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____12965);
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
                       (fun uu____13031  ->
                          let uu____13032 =
                            FStar_Syntax_Print.term_to_string t1  in
                          FStar_Util.print1 "\tSet memo %s\n" uu____13032);
                     norm cfg env stack1 t1)
                | (Debug uu____13033)::uu____13034 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___155_13044 = cfg.steps  in
                             {
                               beta = (uu___155_13044.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___155_13044.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___155_13044.unfold_until);
                               unfold_only = (uu___155_13044.unfold_only);
                               unfold_fully = (uu___155_13044.unfold_fully);
                               unfold_attr = (uu___155_13044.unfold_attr);
                               unfold_tac = (uu___155_13044.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___155_13044.erase_universes);
                               allow_unbound_universes =
                                 (uu___155_13044.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___155_13044.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___155_13044.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___155_13044.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___155_13044.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___156_13046 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___156_13046.tcenv);
                               debug = (uu___156_13046.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___156_13046.primitive_steps);
                               strong = (uu___156_13046.strong);
                               memoize_lazy = (uu___156_13046.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___156_13046.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____13048 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____13048 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____13080  -> dummy :: env1) env)
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
                                          let uu____13121 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____13121)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___157_13126 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___157_13126.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___157_13126.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____13127 -> lopt  in
                           (log cfg
                              (fun uu____13133  ->
                                 let uu____13134 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____13134);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___158_13143 = cfg  in
                               {
                                 steps = (uu___158_13143.steps);
                                 tcenv = (uu___158_13143.tcenv);
                                 debug = (uu___158_13143.debug);
                                 delta_level = (uu___158_13143.delta_level);
                                 primitive_steps =
                                   (uu___158_13143.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___158_13143.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___158_13143.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Meta uu____13146)::uu____13147 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___155_13159 = cfg.steps  in
                             {
                               beta = (uu___155_13159.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___155_13159.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___155_13159.unfold_until);
                               unfold_only = (uu___155_13159.unfold_only);
                               unfold_fully = (uu___155_13159.unfold_fully);
                               unfold_attr = (uu___155_13159.unfold_attr);
                               unfold_tac = (uu___155_13159.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___155_13159.erase_universes);
                               allow_unbound_universes =
                                 (uu___155_13159.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___155_13159.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___155_13159.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___155_13159.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___155_13159.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___156_13161 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___156_13161.tcenv);
                               debug = (uu___156_13161.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___156_13161.primitive_steps);
                               strong = (uu___156_13161.strong);
                               memoize_lazy = (uu___156_13161.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___156_13161.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____13163 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____13163 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____13195  -> dummy :: env1) env)
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
                                          let uu____13236 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____13236)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___157_13241 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___157_13241.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___157_13241.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____13242 -> lopt  in
                           (log cfg
                              (fun uu____13248  ->
                                 let uu____13249 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____13249);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___158_13258 = cfg  in
                               {
                                 steps = (uu___158_13258.steps);
                                 tcenv = (uu___158_13258.tcenv);
                                 debug = (uu___158_13258.debug);
                                 delta_level = (uu___158_13258.delta_level);
                                 primitive_steps =
                                   (uu___158_13258.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___158_13258.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___158_13258.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Let uu____13261)::uu____13262 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___155_13276 = cfg.steps  in
                             {
                               beta = (uu___155_13276.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___155_13276.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___155_13276.unfold_until);
                               unfold_only = (uu___155_13276.unfold_only);
                               unfold_fully = (uu___155_13276.unfold_fully);
                               unfold_attr = (uu___155_13276.unfold_attr);
                               unfold_tac = (uu___155_13276.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___155_13276.erase_universes);
                               allow_unbound_universes =
                                 (uu___155_13276.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___155_13276.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___155_13276.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___155_13276.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___155_13276.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___156_13278 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___156_13278.tcenv);
                               debug = (uu___156_13278.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___156_13278.primitive_steps);
                               strong = (uu___156_13278.strong);
                               memoize_lazy = (uu___156_13278.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___156_13278.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____13280 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____13280 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____13312  -> dummy :: env1) env)
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
                                          let uu____13353 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____13353)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___157_13358 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___157_13358.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___157_13358.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____13359 -> lopt  in
                           (log cfg
                              (fun uu____13365  ->
                                 let uu____13366 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____13366);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___158_13375 = cfg  in
                               {
                                 steps = (uu___158_13375.steps);
                                 tcenv = (uu___158_13375.tcenv);
                                 debug = (uu___158_13375.debug);
                                 delta_level = (uu___158_13375.delta_level);
                                 primitive_steps =
                                   (uu___158_13375.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___158_13375.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___158_13375.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (App uu____13378)::uu____13379 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___155_13393 = cfg.steps  in
                             {
                               beta = (uu___155_13393.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___155_13393.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___155_13393.unfold_until);
                               unfold_only = (uu___155_13393.unfold_only);
                               unfold_fully = (uu___155_13393.unfold_fully);
                               unfold_attr = (uu___155_13393.unfold_attr);
                               unfold_tac = (uu___155_13393.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___155_13393.erase_universes);
                               allow_unbound_universes =
                                 (uu___155_13393.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___155_13393.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___155_13393.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___155_13393.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___155_13393.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___156_13395 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___156_13395.tcenv);
                               debug = (uu___156_13395.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___156_13395.primitive_steps);
                               strong = (uu___156_13395.strong);
                               memoize_lazy = (uu___156_13395.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___156_13395.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____13397 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____13397 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____13429  -> dummy :: env1) env)
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
                                          let uu____13470 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____13470)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___157_13475 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___157_13475.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___157_13475.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____13476 -> lopt  in
                           (log cfg
                              (fun uu____13482  ->
                                 let uu____13483 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____13483);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___158_13492 = cfg  in
                               {
                                 steps = (uu___158_13492.steps);
                                 tcenv = (uu___158_13492.tcenv);
                                 debug = (uu___158_13492.debug);
                                 delta_level = (uu___158_13492.delta_level);
                                 primitive_steps =
                                   (uu___158_13492.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___158_13492.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___158_13492.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Abs uu____13495)::uu____13496 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___155_13514 = cfg.steps  in
                             {
                               beta = (uu___155_13514.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___155_13514.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___155_13514.unfold_until);
                               unfold_only = (uu___155_13514.unfold_only);
                               unfold_fully = (uu___155_13514.unfold_fully);
                               unfold_attr = (uu___155_13514.unfold_attr);
                               unfold_tac = (uu___155_13514.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___155_13514.erase_universes);
                               allow_unbound_universes =
                                 (uu___155_13514.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___155_13514.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___155_13514.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___155_13514.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___155_13514.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___156_13516 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___156_13516.tcenv);
                               debug = (uu___156_13516.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___156_13516.primitive_steps);
                               strong = (uu___156_13516.strong);
                               memoize_lazy = (uu___156_13516.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___156_13516.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____13518 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____13518 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____13550  -> dummy :: env1) env)
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
                                          let uu____13591 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____13591)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___157_13596 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___157_13596.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___157_13596.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____13597 -> lopt  in
                           (log cfg
                              (fun uu____13603  ->
                                 let uu____13604 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____13604);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___158_13613 = cfg  in
                               {
                                 steps = (uu___158_13613.steps);
                                 tcenv = (uu___158_13613.tcenv);
                                 debug = (uu___158_13613.debug);
                                 delta_level = (uu___158_13613.delta_level);
                                 primitive_steps =
                                   (uu___158_13613.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___158_13613.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___158_13613.normalize_pure_lets)
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
                             let uu___155_13619 = cfg.steps  in
                             {
                               beta = (uu___155_13619.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___155_13619.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___155_13619.unfold_until);
                               unfold_only = (uu___155_13619.unfold_only);
                               unfold_fully = (uu___155_13619.unfold_fully);
                               unfold_attr = (uu___155_13619.unfold_attr);
                               unfold_tac = (uu___155_13619.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___155_13619.erase_universes);
                               allow_unbound_universes =
                                 (uu___155_13619.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___155_13619.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___155_13619.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___155_13619.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___155_13619.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___156_13621 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___156_13621.tcenv);
                               debug = (uu___156_13621.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___156_13621.primitive_steps);
                               strong = (uu___156_13621.strong);
                               memoize_lazy = (uu___156_13621.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___156_13621.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____13623 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____13623 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____13655  -> dummy :: env1) env)
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
                                          let uu____13696 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____13696)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___157_13701 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___157_13701.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___157_13701.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____13702 -> lopt  in
                           (log cfg
                              (fun uu____13708  ->
                                 let uu____13709 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____13709);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___158_13718 = cfg  in
                               {
                                 steps = (uu___158_13718.steps);
                                 tcenv = (uu___158_13718.tcenv);
                                 debug = (uu___158_13718.debug);
                                 delta_level = (uu___158_13718.delta_level);
                                 primitive_steps =
                                   (uu___158_13718.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___158_13718.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___158_13718.normalize_pure_lets)
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
                      (fun uu____13757  ->
                         fun stack1  ->
                           match uu____13757 with
                           | (a,aq) ->
                               let uu____13769 =
                                 let uu____13770 =
                                   let uu____13777 =
                                     let uu____13778 =
                                       let uu____13809 =
                                         FStar_Util.mk_ref
                                           FStar_Pervasives_Native.None
                                          in
                                       (env, a, uu____13809, false)  in
                                     Clos uu____13778  in
                                   (uu____13777, aq,
                                     (t1.FStar_Syntax_Syntax.pos))
                                    in
                                 Arg uu____13770  in
                               uu____13769 :: stack1) args)
                  in
               (log cfg
                  (fun uu____13897  ->
                     let uu____13898 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args)
                        in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____13898);
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
                             ((let uu___159_13944 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___159_13944.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___159_13944.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos
                         in
                      rebuild cfg env stack t2
                  | uu____13945 ->
                      let uu____13960 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____13960)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort  in
                  let uu____13963 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] f
                     in
                  match uu____13963 with
                  | (closing,f1) ->
                      let f2 = norm cfg (dummy :: env) [] f1  in
                      let t2 =
                        let uu____13988 =
                          let uu____13989 =
                            let uu____13996 =
                              FStar_Syntax_Subst.close closing f2  in
                            ((let uu___160_14002 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___160_14002.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___160_14002.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____13996)
                             in
                          FStar_Syntax_Syntax.Tm_refine uu____13989  in
                        mk uu____13988 t1.FStar_Syntax_Syntax.pos  in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if (cfg.steps).weak
               then
                 let uu____14021 = closure_as_term cfg env t1  in
                 rebuild cfg env stack uu____14021
               else
                 (let uu____14023 = FStar_Syntax_Subst.open_comp bs c  in
                  match uu____14023 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____14031 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun uu____14053  -> dummy :: env1) env)
                           in
                        norm_comp cfg uu____14031 c1  in
                      let t2 =
                        let uu____14075 = norm_binders cfg env bs1  in
                        FStar_Syntax_Util.arrow uu____14075 c2  in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) when
               (cfg.steps).unascribe -> norm cfg env stack t11
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack with
                | (Match uu____14186)::uu____14187 ->
                    (log cfg
                       (fun uu____14200  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (Arg uu____14201)::uu____14202 ->
                    (log cfg
                       (fun uu____14213  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (App
                    (uu____14214,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_constant
                                     (FStar_Const.Const_reify );
                                   FStar_Syntax_Syntax.pos = uu____14215;
                                   FStar_Syntax_Syntax.vars = uu____14216;_},uu____14217,uu____14218))::uu____14219
                    ->
                    (log cfg
                       (fun uu____14226  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (MemoLazy uu____14227)::uu____14228 ->
                    (log cfg
                       (fun uu____14239  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | uu____14240 ->
                    (log cfg
                       (fun uu____14243  ->
                          FStar_Util.print_string "+++ Keeping ascription \n");
                     (let t12 = norm cfg env [] t11  in
                      log cfg
                        (fun uu____14247  ->
                           FStar_Util.print_string
                             "+++ Normalizing ascription \n");
                      (let tc1 =
                         match tc with
                         | FStar_Util.Inl t2 ->
                             let uu____14272 = norm cfg env [] t2  in
                             FStar_Util.Inl uu____14272
                         | FStar_Util.Inr c ->
                             let uu____14282 = norm_comp cfg env c  in
                             FStar_Util.Inr uu____14282
                          in
                       let tacopt1 =
                         FStar_Util.map_opt tacopt (norm cfg env [])  in
                       match stack with
                       | (Cfg cfg1)::stack1 ->
                           let t2 =
                             let uu____14301 =
                               let uu____14302 =
                                 let uu____14329 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____14329, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____14302
                                in
                             mk uu____14301 t1.FStar_Syntax_Syntax.pos  in
                           norm cfg1 env stack1 t2
                       | uu____14364 ->
                           let uu____14365 =
                             let uu____14366 =
                               let uu____14367 =
                                 let uu____14394 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____14394, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____14367
                                in
                             mk uu____14366 t1.FStar_Syntax_Syntax.pos  in
                           rebuild cfg env stack uu____14365))))
           | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
               let stack1 =
                 (Match (env, branches, cfg, (t1.FStar_Syntax_Syntax.pos)))
                 :: stack  in
               let cfg1 =
                 if
                   ((cfg.steps).iota && (cfg.steps).weakly_reduce_scrutinee)
                     && (Prims.op_Negation (cfg.steps).weak)
                 then
                   let uu___161_14471 = cfg  in
                   {
                     steps =
                       (let uu___162_14474 = cfg.steps  in
                        {
                          beta = (uu___162_14474.beta);
                          iota = (uu___162_14474.iota);
                          zeta = (uu___162_14474.zeta);
                          weak = true;
                          hnf = (uu___162_14474.hnf);
                          primops = (uu___162_14474.primops);
                          do_not_unfold_pure_lets =
                            (uu___162_14474.do_not_unfold_pure_lets);
                          unfold_until = (uu___162_14474.unfold_until);
                          unfold_only = (uu___162_14474.unfold_only);
                          unfold_fully = (uu___162_14474.unfold_fully);
                          unfold_attr = (uu___162_14474.unfold_attr);
                          unfold_tac = (uu___162_14474.unfold_tac);
                          pure_subterms_within_computations =
                            (uu___162_14474.pure_subterms_within_computations);
                          simplify = (uu___162_14474.simplify);
                          erase_universes = (uu___162_14474.erase_universes);
                          allow_unbound_universes =
                            (uu___162_14474.allow_unbound_universes);
                          reify_ = (uu___162_14474.reify_);
                          compress_uvars = (uu___162_14474.compress_uvars);
                          no_full_norm = (uu___162_14474.no_full_norm);
                          check_no_uvars = (uu___162_14474.check_no_uvars);
                          unmeta = (uu___162_14474.unmeta);
                          unascribe = (uu___162_14474.unascribe);
                          in_full_norm_request =
                            (uu___162_14474.in_full_norm_request);
                          weakly_reduce_scrutinee =
                            (uu___162_14474.weakly_reduce_scrutinee)
                        });
                     tcenv = (uu___161_14471.tcenv);
                     debug = (uu___161_14471.debug);
                     delta_level = (uu___161_14471.delta_level);
                     primitive_steps = (uu___161_14471.primitive_steps);
                     strong = (uu___161_14471.strong);
                     memoize_lazy = (uu___161_14471.memoize_lazy);
                     normalize_pure_lets =
                       (uu___161_14471.normalize_pure_lets)
                   }
                 else cfg  in
               norm cfg1 env stack1 head1
           | FStar_Syntax_Syntax.Tm_let ((b,lbs),lbody) when
               (FStar_Syntax_Syntax.is_top_level lbs) &&
                 (cfg.steps).compress_uvars
               ->
               let lbs1 =
                 FStar_All.pipe_right lbs
                   (FStar_List.map
                      (fun lb  ->
                         let uu____14510 =
                           FStar_Syntax_Subst.univ_var_opening
                             lb.FStar_Syntax_Syntax.lbunivs
                            in
                         match uu____14510 with
                         | (openings,lbunivs) ->
                             let cfg1 =
                               let uu___163_14530 = cfg  in
                               let uu____14531 =
                                 FStar_TypeChecker_Env.push_univ_vars
                                   cfg.tcenv lbunivs
                                  in
                               {
                                 steps = (uu___163_14530.steps);
                                 tcenv = uu____14531;
                                 debug = (uu___163_14530.debug);
                                 delta_level = (uu___163_14530.delta_level);
                                 primitive_steps =
                                   (uu___163_14530.primitive_steps);
                                 strong = (uu___163_14530.strong);
                                 memoize_lazy = (uu___163_14530.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___163_14530.normalize_pure_lets)
                               }  in
                             let norm1 t2 =
                               let uu____14538 =
                                 let uu____14539 =
                                   FStar_Syntax_Subst.subst openings t2  in
                                 norm cfg1 env [] uu____14539  in
                               FStar_Syntax_Subst.close_univ_vars lbunivs
                                 uu____14538
                                in
                             let lbtyp = norm1 lb.FStar_Syntax_Syntax.lbtyp
                                in
                             let lbdef = norm1 lb.FStar_Syntax_Syntax.lbdef
                                in
                             let uu___164_14542 = lb  in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___164_14542.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs = lbunivs;
                               FStar_Syntax_Syntax.lbtyp = lbtyp;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___164_14542.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = lbdef;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___164_14542.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___164_14542.FStar_Syntax_Syntax.lbpos)
                             }))
                  in
               let uu____14543 =
                 mk (FStar_Syntax_Syntax.Tm_let ((b, lbs1), lbody))
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack uu____14543
           | FStar_Syntax_Syntax.Tm_let
               ((uu____14554,{
                               FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                 uu____14555;
                               FStar_Syntax_Syntax.lbunivs = uu____14556;
                               FStar_Syntax_Syntax.lbtyp = uu____14557;
                               FStar_Syntax_Syntax.lbeff = uu____14558;
                               FStar_Syntax_Syntax.lbdef = uu____14559;
                               FStar_Syntax_Syntax.lbattrs = uu____14560;
                               FStar_Syntax_Syntax.lbpos = uu____14561;_}::uu____14562),uu____14563)
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff
                  in
               let uu____14603 =
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
               if uu____14603
               then
                 let binder =
                   let uu____14605 =
                     FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                   FStar_Syntax_Syntax.mk_binder uu____14605  in
                 let env1 =
                   let uu____14615 =
                     let uu____14622 =
                       let uu____14623 =
                         let uu____14654 =
                           FStar_Util.mk_ref FStar_Pervasives_Native.None  in
                         (env, (lb.FStar_Syntax_Syntax.lbdef), uu____14654,
                           false)
                          in
                       Clos uu____14623  in
                     ((FStar_Pervasives_Native.Some binder), uu____14622)  in
                   uu____14615 :: env  in
                 (log cfg
                    (fun uu____14749  ->
                       FStar_Util.print_string "+++ Reducing Tm_let\n");
                  norm cfg env1 stack body)
               else
                 if (cfg.steps).weak
                 then
                   (log cfg
                      (fun uu____14753  ->
                         FStar_Util.print_string "+++ Not touching Tm_let\n");
                    (let uu____14754 = closure_as_term cfg env t1  in
                     rebuild cfg env stack uu____14754))
                 else
                   (let uu____14756 =
                      let uu____14761 =
                        let uu____14762 =
                          let uu____14767 =
                            FStar_All.pipe_right
                              lb.FStar_Syntax_Syntax.lbname FStar_Util.left
                             in
                          FStar_All.pipe_right uu____14767
                            FStar_Syntax_Syntax.mk_binder
                           in
                        [uu____14762]  in
                      FStar_Syntax_Subst.open_term uu____14761 body  in
                    match uu____14756 with
                    | (bs,body1) ->
                        (log cfg
                           (fun uu____14788  ->
                              FStar_Util.print_string
                                "+++ Normalizing Tm_let -- type");
                         (let ty =
                            norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                          let lbname =
                            let x =
                              let uu____14796 = FStar_List.hd bs  in
                              FStar_Pervasives_Native.fst uu____14796  in
                            FStar_Util.Inl
                              (let uu___165_14806 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___165_14806.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___165_14806.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               })
                             in
                          log cfg
                            (fun uu____14809  ->
                               FStar_Util.print_string
                                 "+++ Normalizing Tm_let -- definiens\n");
                          (let lb1 =
                             let uu___166_14811 = lb  in
                             let uu____14812 =
                               norm cfg env [] lb.FStar_Syntax_Syntax.lbdef
                                in
                             {
                               FStar_Syntax_Syntax.lbname = lbname;
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___166_14811.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp = ty;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___166_14811.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = uu____14812;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___166_14811.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___166_14811.FStar_Syntax_Syntax.lbpos)
                             }  in
                           let env' =
                             FStar_All.pipe_right bs
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____14837  -> dummy :: env1) env)
                              in
                           let stack1 = (Cfg cfg) :: stack  in
                           let cfg1 =
                             let uu___167_14860 = cfg  in
                             {
                               steps = (uu___167_14860.steps);
                               tcenv = (uu___167_14860.tcenv);
                               debug = (uu___167_14860.debug);
                               delta_level = (uu___167_14860.delta_level);
                               primitive_steps =
                                 (uu___167_14860.primitive_steps);
                               strong = true;
                               memoize_lazy = (uu___167_14860.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___167_14860.normalize_pure_lets)
                             }  in
                           log cfg1
                             (fun uu____14863  ->
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
               let uu____14880 = FStar_Syntax_Subst.open_let_rec lbs body  in
               (match uu____14880 with
                | (lbs1,body1) ->
                    let lbs2 =
                      FStar_List.map
                        (fun lb  ->
                           let ty =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                           let lbname =
                             let uu____14916 =
                               let uu___168_14917 =
                                 FStar_Util.left
                                   lb.FStar_Syntax_Syntax.lbname
                                  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___168_14917.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___168_14917.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               }  in
                             FStar_Util.Inl uu____14916  in
                           let uu____14918 =
                             FStar_Syntax_Util.abs_formals
                               lb.FStar_Syntax_Syntax.lbdef
                              in
                           match uu____14918 with
                           | (xs,def_body,lopt) ->
                               let xs1 = norm_binders cfg env xs  in
                               let env1 =
                                 let uu____14944 =
                                   FStar_List.map (fun uu____14960  -> dummy)
                                     lbs1
                                    in
                                 let uu____14961 =
                                   let uu____14970 =
                                     FStar_List.map
                                       (fun uu____14990  -> dummy) xs1
                                      in
                                   FStar_List.append uu____14970 env  in
                                 FStar_List.append uu____14944 uu____14961
                                  in
                               let def_body1 = norm cfg env1 [] def_body  in
                               let lopt1 =
                                 match lopt with
                                 | FStar_Pervasives_Native.Some rc ->
                                     let uu____15014 =
                                       let uu___169_15015 = rc  in
                                       let uu____15016 =
                                         FStar_Util.map_opt
                                           rc.FStar_Syntax_Syntax.residual_typ
                                           (norm cfg env1 [])
                                          in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___169_15015.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           uu____15016;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___169_15015.FStar_Syntax_Syntax.residual_flags)
                                       }  in
                                     FStar_Pervasives_Native.Some uu____15014
                                 | uu____15025 -> lopt  in
                               let def =
                                 FStar_Syntax_Util.abs xs1 def_body1 lopt1
                                  in
                               let uu___170_15031 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname = lbname;
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___170_15031.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp = ty;
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___170_15031.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___170_15031.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___170_15031.FStar_Syntax_Syntax.lbpos)
                               }) lbs1
                       in
                    let env' =
                      let uu____15041 =
                        FStar_List.map (fun uu____15057  -> dummy) lbs2  in
                      FStar_List.append uu____15041 env  in
                    let body2 = norm cfg env' [] body1  in
                    let uu____15065 =
                      FStar_Syntax_Subst.close_let_rec lbs2 body2  in
                    (match uu____15065 with
                     | (lbs3,body3) ->
                         let t2 =
                           let uu___171_15081 = t1  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_let
                                  ((true, lbs3), body3));
                             FStar_Syntax_Syntax.pos =
                               (uu___171_15081.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___171_15081.FStar_Syntax_Syntax.vars)
                           }  in
                         rebuild cfg env stack t2))
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               Prims.op_Negation (cfg.steps).zeta ->
               let uu____15110 = closure_as_term cfg env t1  in
               rebuild cfg env stack uu____15110
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____15129 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____15205  ->
                        match uu____15205 with
                        | (rec_env,memos,i) ->
                            let bv =
                              let uu___172_15326 =
                                FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                                 in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___172_15326.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index = i;
                                FStar_Syntax_Syntax.sort =
                                  (uu___172_15326.FStar_Syntax_Syntax.sort)
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
               (match uu____15129 with
                | (rec_env,memos,uu____15553) ->
                    let uu____15606 =
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
                             let uu____15929 =
                               let uu____15936 =
                                 let uu____15937 =
                                   let uu____15968 =
                                     FStar_Util.mk_ref
                                       FStar_Pervasives_Native.None
                                      in
                                   (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                     uu____15968, false)
                                    in
                                 Clos uu____15937  in
                               (FStar_Pervasives_Native.None, uu____15936)
                                in
                             uu____15929 :: env1)
                        (FStar_Pervasives_Native.snd lbs) env
                       in
                    norm cfg body_env stack body)
           | FStar_Syntax_Syntax.Tm_meta (head1,m) ->
               (log cfg
                  (fun uu____16072  ->
                     let uu____16073 =
                       FStar_Syntax_Print.metadata_to_string m  in
                     FStar_Util.print1 ">> metadata = %s\n" uu____16073);
                (match m with
                 | FStar_Syntax_Syntax.Meta_monadic (m1,t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inl m1) t2
                 | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inr (m1, m')) t2
                 | uu____16095 ->
                     if (cfg.steps).unmeta
                     then norm cfg env stack head1
                     else
                       (match stack with
                        | uu____16097::uu____16098 ->
                            (match m with
                             | FStar_Syntax_Syntax.Meta_labeled
                                 (l,r,uu____16103) ->
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
                             | uu____16126 -> norm cfg env stack head1)
                        | [] ->
                            let head2 = norm cfg env [] head1  in
                            let m1 =
                              match m with
                              | FStar_Syntax_Syntax.Meta_pattern args ->
                                  let uu____16140 =
                                    norm_pattern_args cfg env args  in
                                  FStar_Syntax_Syntax.Meta_pattern
                                    uu____16140
                              | uu____16151 -> m  in
                            let t2 =
                              mk (FStar_Syntax_Syntax.Tm_meta (head2, m1))
                                t1.FStar_Syntax_Syntax.pos
                               in
                            rebuild cfg env stack t2)))
           | FStar_Syntax_Syntax.Tm_delayed uu____16157 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               norm cfg env stack t2
           | FStar_Syntax_Syntax.Tm_uvar uu____16183 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               (match t2.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_uvar uu____16185 ->
                    if (cfg.steps).check_no_uvars
                    then
                      let uu____16186 =
                        let uu____16187 =
                          FStar_Range.string_of_range
                            t2.FStar_Syntax_Syntax.pos
                           in
                        let uu____16188 =
                          FStar_Syntax_Print.term_to_string t2  in
                        FStar_Util.format2
                          "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                          uu____16187 uu____16188
                         in
                      failwith uu____16186
                    else rebuild cfg env stack t2
                | uu____16190 -> norm cfg env stack t2))

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
              let r_env =
                let uu____16200 = FStar_Syntax_Syntax.range_of_fv f  in
                FStar_TypeChecker_Env.set_range cfg.tcenv uu____16200  in
              let uu____16201 =
                FStar_TypeChecker_Env.lookup_definition_qninfo
                  cfg.delta_level
                  (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                  qninfo
                 in
              match uu____16201 with
              | FStar_Pervasives_Native.None  ->
                  (log cfg
                     (fun uu____16214  ->
                        FStar_Util.print "Tm_fvar case 2\n" []);
                   rebuild cfg env stack t0)
              | FStar_Pervasives_Native.Some (us,t) ->
                  (log cfg
                     (fun uu____16225  ->
                        let uu____16226 =
                          FStar_Syntax_Print.term_to_string t0  in
                        let uu____16227 = FStar_Syntax_Print.term_to_string t
                           in
                        FStar_Util.print2 ">>> Unfolded %s to %s\n"
                          uu____16226 uu____16227);
                   (let t1 =
                      if
                        ((cfg.steps).unfold_until =
                           (FStar_Pervasives_Native.Some
                              FStar_Syntax_Syntax.Delta_constant))
                          && (Prims.op_Negation (cfg.steps).unfold_tac)
                      then t
                      else
                        (let uu____16232 =
                           FStar_Ident.range_of_lid
                             (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                            in
                         FStar_Syntax_Subst.set_use_range uu____16232 t)
                       in
                    let n1 = FStar_List.length us  in
                    if n1 > (Prims.parse_int "0")
                    then
                      match stack with
                      | (UnivArgs (us',uu____16241))::stack1 ->
                          let env1 =
                            FStar_All.pipe_right us'
                              (FStar_List.fold_left
                                 (fun env1  ->
                                    fun u  ->
                                      (FStar_Pervasives_Native.None,
                                        (Univ u))
                                      :: env1) env)
                             in
                          norm cfg env1 stack1 t1
                      | uu____16280 when
                          (cfg.steps).erase_universes ||
                            (cfg.steps).allow_unbound_universes
                          -> norm cfg env stack t1
                      | uu____16283 ->
                          let uu____16286 =
                            let uu____16287 =
                              FStar_Syntax_Print.lid_to_string
                                (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                               in
                            FStar_Util.format1
                              "Impossible: missing universe instantiation on %s"
                              uu____16287
                             in
                          failwith uu____16286
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
                    [PureSubtermsWithinComputations;
                    Primops;
                    AllowUnboundUniverses;
                    EraseUniverses;
                    Exclude Zeta;
                    Inlining]  in
                  let uu___173_16311 = cfg  in
                  let uu____16312 =
                    FStar_List.fold_right fstep_add_one new_steps cfg.steps
                     in
                  {
                    steps = uu____16312;
                    tcenv = (uu___173_16311.tcenv);
                    debug = (uu___173_16311.debug);
                    delta_level =
                      [FStar_TypeChecker_Env.Inlining;
                      FStar_TypeChecker_Env.Eager_unfolding_only];
                    primitive_steps = (uu___173_16311.primitive_steps);
                    strong = (uu___173_16311.strong);
                    memoize_lazy = (uu___173_16311.memoize_lazy);
                    normalize_pure_lets =
                      (uu___173_16311.normalize_pure_lets)
                  }
                else
                  (let uu___174_16314 = cfg  in
                   {
                     steps =
                       (let uu___175_16317 = cfg.steps  in
                        {
                          beta = (uu___175_16317.beta);
                          iota = (uu___175_16317.iota);
                          zeta = false;
                          weak = (uu___175_16317.weak);
                          hnf = (uu___175_16317.hnf);
                          primops = (uu___175_16317.primops);
                          do_not_unfold_pure_lets =
                            (uu___175_16317.do_not_unfold_pure_lets);
                          unfold_until = (uu___175_16317.unfold_until);
                          unfold_only = (uu___175_16317.unfold_only);
                          unfold_fully = (uu___175_16317.unfold_fully);
                          unfold_attr = (uu___175_16317.unfold_attr);
                          unfold_tac = (uu___175_16317.unfold_tac);
                          pure_subterms_within_computations =
                            (uu___175_16317.pure_subterms_within_computations);
                          simplify = (uu___175_16317.simplify);
                          erase_universes = (uu___175_16317.erase_universes);
                          allow_unbound_universes =
                            (uu___175_16317.allow_unbound_universes);
                          reify_ = (uu___175_16317.reify_);
                          compress_uvars = (uu___175_16317.compress_uvars);
                          no_full_norm = (uu___175_16317.no_full_norm);
                          check_no_uvars = (uu___175_16317.check_no_uvars);
                          unmeta = (uu___175_16317.unmeta);
                          unascribe = (uu___175_16317.unascribe);
                          in_full_norm_request =
                            (uu___175_16317.in_full_norm_request);
                          weakly_reduce_scrutinee =
                            (uu___175_16317.weakly_reduce_scrutinee)
                        });
                     tcenv = (uu___174_16314.tcenv);
                     debug = (uu___174_16314.debug);
                     delta_level = (uu___174_16314.delta_level);
                     primitive_steps = (uu___174_16314.primitive_steps);
                     strong = (uu___174_16314.strong);
                     memoize_lazy = (uu___174_16314.memoize_lazy);
                     normalize_pure_lets =
                       (uu___174_16314.normalize_pure_lets)
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
                  (fun uu____16351  ->
                     let uu____16352 = FStar_Syntax_Print.tag_of_term head2
                        in
                     let uu____16353 =
                       FStar_Syntax_Print.term_to_string head2  in
                     FStar_Util.print2 "Reifying: (%s) %s\n" uu____16352
                       uu____16353);
                (let head3 = FStar_Syntax_Util.unmeta_safe head2  in
                 let uu____16355 =
                   let uu____16356 = FStar_Syntax_Subst.compress head3  in
                   uu____16356.FStar_Syntax_Syntax.n  in
                 match uu____16355 with
                 | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                     let ed =
                       let uu____16374 =
                         FStar_TypeChecker_Env.norm_eff_name cfg.tcenv m  in
                       FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                         uu____16374
                        in
                     let uu____16375 = ed.FStar_Syntax_Syntax.bind_repr  in
                     (match uu____16375 with
                      | (uu____16376,bind_repr) ->
                          (match lb.FStar_Syntax_Syntax.lbname with
                           | FStar_Util.Inr uu____16386 ->
                               failwith
                                 "Cannot reify a top-level let binding"
                           | FStar_Util.Inl x ->
                               let is_return e =
                                 let uu____16396 =
                                   let uu____16397 =
                                     FStar_Syntax_Subst.compress e  in
                                   uu____16397.FStar_Syntax_Syntax.n  in
                                 match uu____16396 with
                                 | FStar_Syntax_Syntax.Tm_meta
                                     (e1,FStar_Syntax_Syntax.Meta_monadic
                                      (uu____16403,uu____16404))
                                     ->
                                     let uu____16413 =
                                       let uu____16414 =
                                         FStar_Syntax_Subst.compress e1  in
                                       uu____16414.FStar_Syntax_Syntax.n  in
                                     (match uu____16413 with
                                      | FStar_Syntax_Syntax.Tm_meta
                                          (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                           (uu____16420,msrc,uu____16422))
                                          when
                                          FStar_Syntax_Util.is_pure_effect
                                            msrc
                                          ->
                                          let uu____16431 =
                                            FStar_Syntax_Subst.compress e2
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____16431
                                      | uu____16432 ->
                                          FStar_Pervasives_Native.None)
                                 | uu____16433 ->
                                     FStar_Pervasives_Native.None
                                  in
                               let uu____16434 =
                                 is_return lb.FStar_Syntax_Syntax.lbdef  in
                               (match uu____16434 with
                                | FStar_Pervasives_Native.Some e ->
                                    let lb1 =
                                      let uu___176_16439 = lb  in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          (uu___176_16439.FStar_Syntax_Syntax.lbname);
                                        FStar_Syntax_Syntax.lbunivs =
                                          (uu___176_16439.FStar_Syntax_Syntax.lbunivs);
                                        FStar_Syntax_Syntax.lbtyp =
                                          (uu___176_16439.FStar_Syntax_Syntax.lbtyp);
                                        FStar_Syntax_Syntax.lbeff =
                                          FStar_Parser_Const.effect_PURE_lid;
                                        FStar_Syntax_Syntax.lbdef = e;
                                        FStar_Syntax_Syntax.lbattrs =
                                          (uu___176_16439.FStar_Syntax_Syntax.lbattrs);
                                        FStar_Syntax_Syntax.lbpos =
                                          (uu___176_16439.FStar_Syntax_Syntax.lbpos)
                                      }  in
                                    let uu____16440 = FStar_List.tl stack  in
                                    let uu____16441 =
                                      let uu____16442 =
                                        let uu____16449 =
                                          let uu____16450 =
                                            let uu____16463 =
                                              FStar_Syntax_Util.mk_reify body
                                               in
                                            ((false, [lb1]), uu____16463)  in
                                          FStar_Syntax_Syntax.Tm_let
                                            uu____16450
                                           in
                                        FStar_Syntax_Syntax.mk uu____16449
                                         in
                                      uu____16442
                                        FStar_Pervasives_Native.None
                                        head3.FStar_Syntax_Syntax.pos
                                       in
                                    norm cfg env uu____16440 uu____16441
                                | FStar_Pervasives_Native.None  ->
                                    let uu____16479 =
                                      let uu____16480 = is_return body  in
                                      match uu____16480 with
                                      | FStar_Pervasives_Native.Some
                                          {
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_bvar y;
                                            FStar_Syntax_Syntax.pos =
                                              uu____16484;
                                            FStar_Syntax_Syntax.vars =
                                              uu____16485;_}
                                          -> FStar_Syntax_Syntax.bv_eq x y
                                      | uu____16488 -> false  in
                                    if uu____16479
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
                                         let uu____16509 =
                                           let uu____16516 =
                                             let uu____16517 =
                                               let uu____16534 =
                                                 let uu____16541 =
                                                   FStar_Syntax_Syntax.mk_binder
                                                     x
                                                    in
                                                 [uu____16541]  in
                                               (uu____16534, body1,
                                                 (FStar_Pervasives_Native.Some
                                                    body_rc))
                                                in
                                             FStar_Syntax_Syntax.Tm_abs
                                               uu____16517
                                              in
                                           FStar_Syntax_Syntax.mk uu____16516
                                            in
                                         uu____16509
                                           FStar_Pervasives_Native.None
                                           body1.FStar_Syntax_Syntax.pos
                                          in
                                       let close1 = closure_as_term cfg env
                                          in
                                       let bind_inst =
                                         let uu____16575 =
                                           let uu____16576 =
                                             FStar_Syntax_Subst.compress
                                               bind_repr
                                              in
                                           uu____16576.FStar_Syntax_Syntax.n
                                            in
                                         match uu____16575 with
                                         | FStar_Syntax_Syntax.Tm_uinst
                                             (bind1,uu____16582::uu____16583::[])
                                             ->
                                             let uu____16588 =
                                               let uu____16595 =
                                                 let uu____16596 =
                                                   let uu____16603 =
                                                     let uu____16604 =
                                                       let uu____16605 =
                                                         close1
                                                           lb.FStar_Syntax_Syntax.lbtyp
                                                          in
                                                       (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                         cfg.tcenv
                                                         uu____16605
                                                        in
                                                     let uu____16606 =
                                                       let uu____16609 =
                                                         let uu____16610 =
                                                           close1 t  in
                                                         (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                           cfg.tcenv
                                                           uu____16610
                                                          in
                                                       [uu____16609]  in
                                                     uu____16604 ::
                                                       uu____16606
                                                      in
                                                   (bind1, uu____16603)  in
                                                 FStar_Syntax_Syntax.Tm_uinst
                                                   uu____16596
                                                  in
                                               FStar_Syntax_Syntax.mk
                                                 uu____16595
                                                in
                                             uu____16588
                                               FStar_Pervasives_Native.None
                                               rng
                                         | uu____16616 ->
                                             failwith
                                               "NIY : Reification of indexed effects"
                                          in
                                       let maybe_range_arg =
                                         let uu____16628 =
                                           FStar_Util.for_some
                                             (FStar_Syntax_Util.attr_eq
                                                FStar_Syntax_Util.dm4f_bind_range_attr)
                                             ed.FStar_Syntax_Syntax.eff_attrs
                                            in
                                         if uu____16628
                                         then
                                           let uu____16637 =
                                             let uu____16644 =
                                               FStar_Syntax_Embeddings.embed
                                                 FStar_Syntax_Embeddings.e_range
                                                 lb.FStar_Syntax_Syntax.lbpos
                                                 lb.FStar_Syntax_Syntax.lbpos
                                                in
                                             FStar_Syntax_Syntax.as_arg
                                               uu____16644
                                              in
                                           let uu____16645 =
                                             let uu____16654 =
                                               let uu____16661 =
                                                 FStar_Syntax_Embeddings.embed
                                                   FStar_Syntax_Embeddings.e_range
                                                   body2.FStar_Syntax_Syntax.pos
                                                   body2.FStar_Syntax_Syntax.pos
                                                  in
                                               FStar_Syntax_Syntax.as_arg
                                                 uu____16661
                                                in
                                             [uu____16654]  in
                                           uu____16637 :: uu____16645
                                         else []  in
                                       let reified =
                                         let uu____16690 =
                                           let uu____16697 =
                                             let uu____16698 =
                                               let uu____16713 =
                                                 let uu____16722 =
                                                   let uu____16731 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       lb.FStar_Syntax_Syntax.lbtyp
                                                      in
                                                   let uu____16738 =
                                                     let uu____16747 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         t
                                                        in
                                                     [uu____16747]  in
                                                   uu____16731 :: uu____16738
                                                    in
                                                 let uu____16772 =
                                                   let uu____16781 =
                                                     let uu____16790 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         FStar_Syntax_Syntax.tun
                                                        in
                                                     let uu____16797 =
                                                       let uu____16806 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           head4
                                                          in
                                                       let uu____16813 =
                                                         let uu____16822 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             FStar_Syntax_Syntax.tun
                                                            in
                                                         let uu____16829 =
                                                           let uu____16838 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               body2
                                                              in
                                                           [uu____16838]  in
                                                         uu____16822 ::
                                                           uu____16829
                                                          in
                                                       uu____16806 ::
                                                         uu____16813
                                                        in
                                                     uu____16790 ::
                                                       uu____16797
                                                      in
                                                   FStar_List.append
                                                     maybe_range_arg
                                                     uu____16781
                                                    in
                                                 FStar_List.append
                                                   uu____16722 uu____16772
                                                  in
                                               (bind_inst, uu____16713)  in
                                             FStar_Syntax_Syntax.Tm_app
                                               uu____16698
                                              in
                                           FStar_Syntax_Syntax.mk uu____16697
                                            in
                                         uu____16690
                                           FStar_Pervasives_Native.None rng
                                          in
                                       log cfg
                                         (fun uu____16904  ->
                                            let uu____16905 =
                                              FStar_Syntax_Print.term_to_string
                                                head0
                                               in
                                            let uu____16906 =
                                              FStar_Syntax_Print.term_to_string
                                                reified
                                               in
                                            FStar_Util.print2
                                              "Reified (1) <%s> to %s\n"
                                              uu____16905 uu____16906);
                                       (let uu____16907 = FStar_List.tl stack
                                           in
                                        norm cfg env uu____16907 reified)))))
                 | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                     let ed =
                       let uu____16931 =
                         FStar_TypeChecker_Env.norm_eff_name cfg.tcenv m  in
                       FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                         uu____16931
                        in
                     let uu____16932 = ed.FStar_Syntax_Syntax.bind_repr  in
                     (match uu____16932 with
                      | (uu____16933,bind_repr) ->
                          let maybe_unfold_action head4 =
                            let maybe_extract_fv t1 =
                              let t2 =
                                let uu____16970 =
                                  let uu____16971 =
                                    FStar_Syntax_Subst.compress t1  in
                                  uu____16971.FStar_Syntax_Syntax.n  in
                                match uu____16970 with
                                | FStar_Syntax_Syntax.Tm_uinst
                                    (t2,uu____16975) -> t2
                                | uu____16980 -> head4  in
                              let uu____16981 =
                                let uu____16982 =
                                  FStar_Syntax_Subst.compress t2  in
                                uu____16982.FStar_Syntax_Syntax.n  in
                              match uu____16981 with
                              | FStar_Syntax_Syntax.Tm_fvar x ->
                                  FStar_Pervasives_Native.Some x
                              | uu____16988 -> FStar_Pervasives_Native.None
                               in
                            let uu____16989 = maybe_extract_fv head4  in
                            match uu____16989 with
                            | FStar_Pervasives_Native.Some x when
                                let uu____16999 =
                                  FStar_Syntax_Syntax.lid_of_fv x  in
                                FStar_TypeChecker_Env.is_action cfg.tcenv
                                  uu____16999
                                ->
                                let head5 = norm cfg env [] head4  in
                                let action_unfolded =
                                  let uu____17004 = maybe_extract_fv head5
                                     in
                                  match uu____17004 with
                                  | FStar_Pervasives_Native.Some uu____17009
                                      -> FStar_Pervasives_Native.Some true
                                  | uu____17010 ->
                                      FStar_Pervasives_Native.Some false
                                   in
                                (head5, action_unfolded)
                            | uu____17015 ->
                                (head4, FStar_Pervasives_Native.None)
                             in
                          ((let is_arg_impure uu____17030 =
                              match uu____17030 with
                              | (e,q) ->
                                  let uu____17037 =
                                    let uu____17038 =
                                      FStar_Syntax_Subst.compress e  in
                                    uu____17038.FStar_Syntax_Syntax.n  in
                                  (match uu____17037 with
                                   | FStar_Syntax_Syntax.Tm_meta
                                       (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                        (m1,m2,t'))
                                       ->
                                       let uu____17053 =
                                         FStar_Syntax_Util.is_pure_effect m1
                                          in
                                       Prims.op_Negation uu____17053
                                   | uu____17054 -> false)
                               in
                            let uu____17055 =
                              let uu____17056 =
                                let uu____17065 =
                                  FStar_Syntax_Syntax.as_arg head_app  in
                                uu____17065 :: args  in
                              FStar_Util.for_some is_arg_impure uu____17056
                               in
                            if uu____17055
                            then
                              let uu____17084 =
                                let uu____17085 =
                                  FStar_Syntax_Print.term_to_string head3  in
                                FStar_Util.format1
                                  "Incompatibility between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                  uu____17085
                                 in
                              failwith uu____17084
                            else ());
                           (let uu____17087 = maybe_unfold_action head_app
                               in
                            match uu____17087 with
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
                                   (fun uu____17130  ->
                                      let uu____17131 =
                                        FStar_Syntax_Print.term_to_string
                                          head0
                                         in
                                      let uu____17132 =
                                        FStar_Syntax_Print.term_to_string
                                          body1
                                         in
                                      FStar_Util.print2
                                        "Reified (2) <%s> to %s\n"
                                        uu____17131 uu____17132);
                                 (let uu____17133 = FStar_List.tl stack  in
                                  norm cfg env uu____17133 body1)))))
                 | FStar_Syntax_Syntax.Tm_meta
                     (e,FStar_Syntax_Syntax.Meta_monadic uu____17135) ->
                     do_reify_monadic fallback cfg env stack e m t
                 | FStar_Syntax_Syntax.Tm_meta
                     (e,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,t'))
                     ->
                     let lifted =
                       let uu____17159 = closure_as_term cfg env t'  in
                       reify_lift cfg e msrc mtgt uu____17159  in
                     (log cfg
                        (fun uu____17163  ->
                           let uu____17164 =
                             FStar_Syntax_Print.term_to_string lifted  in
                           FStar_Util.print1 "Reified lift to (2): %s\n"
                             uu____17164);
                      (let uu____17165 = FStar_List.tl stack  in
                       norm cfg env uu____17165 lifted))
                 | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                     let branches1 =
                       FStar_All.pipe_right branches
                         (FStar_List.map
                            (fun uu____17286  ->
                               match uu____17286 with
                               | (pat,wopt,tm) ->
                                   let uu____17334 =
                                     FStar_Syntax_Util.mk_reify tm  in
                                   (pat, wopt, uu____17334)))
                        in
                     let tm =
                       mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                         head3.FStar_Syntax_Syntax.pos
                        in
                     let uu____17366 = FStar_List.tl stack  in
                     norm cfg env uu____17366 tm
                 | uu____17367 -> fallback ())

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
              (fun uu____17381  ->
                 let uu____17382 = FStar_Ident.string_of_lid msrc  in
                 let uu____17383 = FStar_Ident.string_of_lid mtgt  in
                 let uu____17384 = FStar_Syntax_Print.term_to_string e  in
                 FStar_Util.print3 "Reifying lift %s -> %s: %s\n" uu____17382
                   uu____17383 uu____17384);
            (let uu____17385 =
               (FStar_Syntax_Util.is_pure_effect msrc) ||
                 (FStar_Syntax_Util.is_div_effect msrc)
                in
             if uu____17385
             then
               let ed =
                 let uu____17387 =
                   FStar_TypeChecker_Env.norm_eff_name cfg.tcenv mtgt  in
                 FStar_TypeChecker_Env.get_effect_decl env uu____17387  in
               let uu____17388 = ed.FStar_Syntax_Syntax.return_repr  in
               match uu____17388 with
               | (uu____17389,return_repr) ->
                   let return_inst =
                     let uu____17402 =
                       let uu____17403 =
                         FStar_Syntax_Subst.compress return_repr  in
                       uu____17403.FStar_Syntax_Syntax.n  in
                     match uu____17402 with
                     | FStar_Syntax_Syntax.Tm_uinst
                         (return_tm,uu____17409::[]) ->
                         let uu____17414 =
                           let uu____17421 =
                             let uu____17422 =
                               let uu____17429 =
                                 let uu____17430 =
                                   env.FStar_TypeChecker_Env.universe_of env
                                     t
                                    in
                                 [uu____17430]  in
                               (return_tm, uu____17429)  in
                             FStar_Syntax_Syntax.Tm_uinst uu____17422  in
                           FStar_Syntax_Syntax.mk uu____17421  in
                         uu____17414 FStar_Pervasives_Native.None
                           e.FStar_Syntax_Syntax.pos
                     | uu____17436 ->
                         failwith "NIY : Reification of indexed effects"
                      in
                   let uu____17439 =
                     let uu____17446 =
                       let uu____17447 =
                         let uu____17462 =
                           let uu____17471 = FStar_Syntax_Syntax.as_arg t  in
                           let uu____17478 =
                             let uu____17487 = FStar_Syntax_Syntax.as_arg e
                                in
                             [uu____17487]  in
                           uu____17471 :: uu____17478  in
                         (return_inst, uu____17462)  in
                       FStar_Syntax_Syntax.Tm_app uu____17447  in
                     FStar_Syntax_Syntax.mk uu____17446  in
                   uu____17439 FStar_Pervasives_Native.None
                     e.FStar_Syntax_Syntax.pos
             else
               (let uu____17526 =
                  FStar_TypeChecker_Env.monad_leq env msrc mtgt  in
                match uu____17526 with
                | FStar_Pervasives_Native.None  ->
                    let uu____17529 =
                      let uu____17530 = FStar_Ident.text_of_lid msrc  in
                      let uu____17531 = FStar_Ident.text_of_lid mtgt  in
                      FStar_Util.format2
                        "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                        uu____17530 uu____17531
                       in
                    failwith uu____17529
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____17532;
                      FStar_TypeChecker_Env.mtarget = uu____17533;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____17534;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.None ;_};_}
                    ->
                    let uu____17556 =
                      let uu____17557 = FStar_Ident.text_of_lid msrc  in
                      let uu____17558 = FStar_Ident.text_of_lid mtgt  in
                      FStar_Util.format2
                        "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
                        uu____17557 uu____17558
                       in
                    failwith uu____17556
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____17559;
                      FStar_TypeChecker_Env.mtarget = uu____17560;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____17561;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.Some lift;_};_}
                    ->
                    let uu____17596 =
                      env.FStar_TypeChecker_Env.universe_of env t  in
                    let uu____17597 = FStar_Syntax_Util.mk_reify e  in
                    lift uu____17596 t FStar_Syntax_Syntax.tun uu____17597))

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
                (fun uu____17653  ->
                   match uu____17653 with
                   | (a,imp) ->
                       let uu____17664 = norm cfg env [] a  in
                       (uu____17664, imp))))

and (norm_comp :
  cfg -> env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp) =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        log cfg
          (fun uu____17672  ->
             let uu____17673 = FStar_Syntax_Print.comp_to_string comp  in
             let uu____17674 =
               FStar_Util.string_of_int (FStar_List.length env)  in
             FStar_Util.print2 ">>> %s\nNormComp with with %s env elements"
               uu____17673 uu____17674);
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Total (t,uopt) ->
             let t1 = norm cfg env [] t  in
             let uopt1 =
               match uopt with
               | FStar_Pervasives_Native.Some u ->
                   let uu____17698 = norm_universe cfg env u  in
                   FStar_All.pipe_left
                     (fun _0_18  -> FStar_Pervasives_Native.Some _0_18)
                     uu____17698
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
                in
             let uu___177_17701 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Total (t1, uopt1));
               FStar_Syntax_Syntax.pos =
                 (uu___177_17701.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___177_17701.FStar_Syntax_Syntax.vars)
             }
         | FStar_Syntax_Syntax.GTotal (t,uopt) ->
             let t1 = norm cfg env [] t  in
             let uopt1 =
               match uopt with
               | FStar_Pervasives_Native.Some u ->
                   let uu____17723 = norm_universe cfg env u  in
                   FStar_All.pipe_left
                     (fun _0_19  -> FStar_Pervasives_Native.Some _0_19)
                     uu____17723
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
                in
             let uu___178_17726 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.GTotal (t1, uopt1));
               FStar_Syntax_Syntax.pos =
                 (uu___178_17726.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___178_17726.FStar_Syntax_Syntax.vars)
             }
         | FStar_Syntax_Syntax.Comp ct ->
             let norm_args =
               FStar_List.mapi
                 (fun idx  ->
                    fun uu____17763  ->
                      match uu____17763 with
                      | (a,i) ->
                          let uu____17774 = norm cfg env [] a  in
                          (uu____17774, i))
                in
             let effect_args = norm_args ct.FStar_Syntax_Syntax.effect_args
                in
             let flags1 =
               FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                 (FStar_List.map
                    (fun uu___92_17792  ->
                       match uu___92_17792 with
                       | FStar_Syntax_Syntax.DECREASES t ->
                           let uu____17796 = norm cfg env [] t  in
                           FStar_Syntax_Syntax.DECREASES uu____17796
                       | f -> f))
                in
             let comp_univs =
               FStar_List.map (norm_universe cfg env)
                 ct.FStar_Syntax_Syntax.comp_univs
                in
             let result_typ =
               norm cfg env [] ct.FStar_Syntax_Syntax.result_typ  in
             let uu___179_17804 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Comp
                    (let uu___180_17807 = ct  in
                     {
                       FStar_Syntax_Syntax.comp_univs = comp_univs;
                       FStar_Syntax_Syntax.effect_name =
                         (uu___180_17807.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ = result_typ;
                       FStar_Syntax_Syntax.effect_args = effect_args;
                       FStar_Syntax_Syntax.flags = flags1
                     }));
               FStar_Syntax_Syntax.pos =
                 (uu___179_17804.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___179_17804.FStar_Syntax_Syntax.vars)
             })

and (norm_binder :
  cfg -> env -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder) =
  fun cfg  ->
    fun env  ->
      fun uu____17810  ->
        match uu____17810 with
        | (x,imp) ->
            let uu____17813 =
              let uu___181_17814 = x  in
              let uu____17815 = norm cfg env [] x.FStar_Syntax_Syntax.sort
                 in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___181_17814.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___181_17814.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____17815
              }  in
            (uu____17813, imp)

and (norm_binders :
  cfg -> env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders) =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____17821 =
          FStar_List.fold_left
            (fun uu____17855  ->
               fun b  ->
                 match uu____17855 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b  in
                     ((b1 :: nbs'), (dummy :: env1))) ([], env) bs
           in
        match uu____17821 with | (nbs,uu____17935) -> FStar_List.rev nbs

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
            let uu____17967 =
              let uu___182_17968 = rc  in
              let uu____17969 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (norm cfg env [])
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___182_17968.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____17969;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___182_17968.FStar_Syntax_Syntax.residual_flags)
              }  in
            FStar_Pervasives_Native.Some uu____17967
        | uu____17978 -> lopt

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
            (let uu____17999 = FStar_Syntax_Print.term_to_string tm  in
             let uu____18000 = FStar_Syntax_Print.term_to_string tm'  in
             FStar_Util.print3 "%sSimplified\n\t%s to\n\t%s\n"
               (if (cfg.steps).simplify then "" else "NOT ") uu____17999
               uu____18000)
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
          let uu____18022 =
            FStar_All.pipe_left Prims.op_Negation (cfg.steps).simplify  in
          if uu____18022
          then tm1
          else
            (let w t =
               let uu___183_18036 = t  in
               {
                 FStar_Syntax_Syntax.n =
                   (uu___183_18036.FStar_Syntax_Syntax.n);
                 FStar_Syntax_Syntax.pos = (tm1.FStar_Syntax_Syntax.pos);
                 FStar_Syntax_Syntax.vars =
                   (uu___183_18036.FStar_Syntax_Syntax.vars)
               }  in
             let simp_t t =
               let uu____18047 =
                 let uu____18048 = FStar_Syntax_Util.unmeta t  in
                 uu____18048.FStar_Syntax_Syntax.n  in
               match uu____18047 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_Pervasives_Native.Some true
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.false_lid
                   -> FStar_Pervasives_Native.Some false
               | uu____18055 -> FStar_Pervasives_Native.None  in
             let rec args_are_binders args bs =
               match (args, bs) with
               | ((t,uu____18104)::args1,(bv,uu____18107)::bs1) ->
                   let uu____18141 =
                     let uu____18142 = FStar_Syntax_Subst.compress t  in
                     uu____18142.FStar_Syntax_Syntax.n  in
                   (match uu____18141 with
                    | FStar_Syntax_Syntax.Tm_name bv' ->
                        (FStar_Syntax_Syntax.bv_eq bv bv') &&
                          (args_are_binders args1 bs1)
                    | uu____18146 -> false)
               | ([],[]) -> true
               | (uu____18167,uu____18168) -> false  in
             let is_applied bs t =
               let uu____18208 = FStar_Syntax_Util.head_and_args' t  in
               match uu____18208 with
               | (hd1,args) ->
                   let uu____18241 =
                     let uu____18242 = FStar_Syntax_Subst.compress hd1  in
                     uu____18242.FStar_Syntax_Syntax.n  in
                   (match uu____18241 with
                    | FStar_Syntax_Syntax.Tm_name bv when
                        args_are_binders args bs ->
                        FStar_Pervasives_Native.Some bv
                    | uu____18248 -> FStar_Pervasives_Native.None)
                in
             let is_applied_maybe_squashed bs t =
               let uu____18264 = FStar_Syntax_Util.is_squash t  in
               match uu____18264 with
               | FStar_Pervasives_Native.Some (uu____18275,t') ->
                   is_applied bs t'
               | uu____18287 ->
                   let uu____18296 = FStar_Syntax_Util.is_auto_squash t  in
                   (match uu____18296 with
                    | FStar_Pervasives_Native.Some (uu____18307,t') ->
                        is_applied bs t'
                    | uu____18319 -> is_applied bs t)
                in
             let is_quantified_const phi =
               let uu____18338 =
                 FStar_Syntax_Util.destruct_typ_as_formula phi  in
               match uu____18338 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
                   (lid,(p,uu____18345)::(q,uu____18347)::[])) when
                   FStar_Ident.lid_equals lid FStar_Parser_Const.imp_lid ->
                   let uu____18374 =
                     FStar_Syntax_Util.destruct_typ_as_formula p  in
                   (match uu____18374 with
                    | FStar_Pervasives_Native.None  ->
                        let uu____18379 =
                          let uu____18380 = FStar_Syntax_Subst.compress p  in
                          uu____18380.FStar_Syntax_Syntax.n  in
                        (match uu____18379 with
                         | FStar_Syntax_Syntax.Tm_bvar bv ->
                             let uu____18386 =
                               FStar_Syntax_Subst.subst
                                 [FStar_Syntax_Syntax.NT
                                    (bv, FStar_Syntax_Util.t_true)] q
                                in
                             FStar_Pervasives_Native.Some uu____18386
                         | uu____18389 -> FStar_Pervasives_Native.None)
                    | FStar_Pervasives_Native.Some
                        (FStar_Syntax_Util.BaseConn
                        (lid1,(p1,uu____18392)::[])) when
                        FStar_Ident.lid_equals lid1
                          FStar_Parser_Const.not_lid
                        ->
                        let uu____18409 =
                          let uu____18410 = FStar_Syntax_Subst.compress p1
                             in
                          uu____18410.FStar_Syntax_Syntax.n  in
                        (match uu____18409 with
                         | FStar_Syntax_Syntax.Tm_bvar bv ->
                             let uu____18416 =
                               FStar_Syntax_Subst.subst
                                 [FStar_Syntax_Syntax.NT
                                    (bv, FStar_Syntax_Util.t_false)] q
                                in
                             FStar_Pervasives_Native.Some uu____18416
                         | uu____18419 -> FStar_Pervasives_Native.None)
                    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
                        (bs,pats,phi1)) ->
                        let uu____18423 =
                          FStar_Syntax_Util.destruct_typ_as_formula phi1  in
                        (match uu____18423 with
                         | FStar_Pervasives_Native.None  ->
                             let uu____18428 =
                               is_applied_maybe_squashed bs phi1  in
                             (match uu____18428 with
                              | FStar_Pervasives_Native.Some bv ->
                                  let ftrue =
                                    FStar_Syntax_Util.abs bs
                                      FStar_Syntax_Util.t_true
                                      (FStar_Pervasives_Native.Some
                                         (FStar_Syntax_Util.residual_tot
                                            FStar_Syntax_Util.ktype0))
                                     in
                                  let uu____18437 =
                                    FStar_Syntax_Subst.subst
                                      [FStar_Syntax_Syntax.NT (bv, ftrue)] q
                                     in
                                  FStar_Pervasives_Native.Some uu____18437
                              | FStar_Pervasives_Native.None  ->
                                  FStar_Pervasives_Native.None)
                         | FStar_Pervasives_Native.Some
                             (FStar_Syntax_Util.BaseConn
                             (lid1,(p1,uu____18442)::[])) when
                             FStar_Ident.lid_equals lid1
                               FStar_Parser_Const.not_lid
                             ->
                             let uu____18459 =
                               is_applied_maybe_squashed bs p1  in
                             (match uu____18459 with
                              | FStar_Pervasives_Native.Some bv ->
                                  let ffalse =
                                    FStar_Syntax_Util.abs bs
                                      FStar_Syntax_Util.t_false
                                      (FStar_Pervasives_Native.Some
                                         (FStar_Syntax_Util.residual_tot
                                            FStar_Syntax_Util.ktype0))
                                     in
                                  let uu____18468 =
                                    FStar_Syntax_Subst.subst
                                      [FStar_Syntax_Syntax.NT (bv, ffalse)] q
                                     in
                                  FStar_Pervasives_Native.Some uu____18468
                              | uu____18471 -> FStar_Pervasives_Native.None)
                         | uu____18474 -> FStar_Pervasives_Native.None)
                    | uu____18477 -> FStar_Pervasives_Native.None)
               | uu____18480 -> FStar_Pervasives_Native.None  in
             let is_const_match phi =
               let uu____18493 =
                 let uu____18494 = FStar_Syntax_Subst.compress phi  in
                 uu____18494.FStar_Syntax_Syntax.n  in
               match uu____18493 with
               | FStar_Syntax_Syntax.Tm_match (uu____18499,br::brs) ->
                   let uu____18566 = br  in
                   (match uu____18566 with
                    | (uu____18583,uu____18584,e) ->
                        let r =
                          let uu____18605 = simp_t e  in
                          match uu____18605 with
                          | FStar_Pervasives_Native.None  ->
                              FStar_Pervasives_Native.None
                          | FStar_Pervasives_Native.Some b ->
                              let uu____18611 =
                                FStar_List.for_all
                                  (fun uu____18629  ->
                                     match uu____18629 with
                                     | (uu____18642,uu____18643,e') ->
                                         let uu____18657 = simp_t e'  in
                                         uu____18657 =
                                           (FStar_Pervasives_Native.Some b))
                                  brs
                                 in
                              if uu____18611
                              then FStar_Pervasives_Native.Some b
                              else FStar_Pervasives_Native.None
                           in
                        r)
               | uu____18665 -> FStar_Pervasives_Native.None  in
             let maybe_auto_squash t =
               let uu____18674 = FStar_Syntax_Util.is_sub_singleton t  in
               if uu____18674
               then t
               else
                 FStar_Syntax_Util.mk_auto_squash FStar_Syntax_Syntax.U_zero
                   t
                in
             let squashed_head_un_auto_squash_args t =
               let maybe_un_auto_squash_arg uu____18705 =
                 match uu____18705 with
                 | (t1,q) ->
                     let uu____18718 = FStar_Syntax_Util.is_auto_squash t1
                        in
                     (match uu____18718 with
                      | FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.U_zero ,t2) -> (t2, q)
                      | uu____18746 -> (t1, q))
                  in
               let uu____18755 = FStar_Syntax_Util.head_and_args t  in
               match uu____18755 with
               | (head1,args) ->
                   let args1 = FStar_List.map maybe_un_auto_squash_arg args
                      in
                   FStar_Syntax_Syntax.mk_Tm_app head1 args1
                     FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
                in
             let rec clearly_inhabited ty =
               let uu____18815 =
                 let uu____18816 = FStar_Syntax_Util.unmeta ty  in
                 uu____18816.FStar_Syntax_Syntax.n  in
               match uu____18815 with
               | FStar_Syntax_Syntax.Tm_uinst (t,uu____18820) ->
                   clearly_inhabited t
               | FStar_Syntax_Syntax.Tm_arrow (uu____18825,c) ->
                   clearly_inhabited (FStar_Syntax_Util.comp_result c)
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   let l = FStar_Syntax_Syntax.lid_of_fv fv  in
                   (((FStar_Ident.lid_equals l FStar_Parser_Const.int_lid) ||
                       (FStar_Ident.lid_equals l FStar_Parser_Const.bool_lid))
                      ||
                      (FStar_Ident.lid_equals l FStar_Parser_Const.string_lid))
                     || (FStar_Ident.lid_equals l FStar_Parser_Const.exn_lid)
               | uu____18845 -> false  in
             let simplify1 arg =
               let uu____18870 = simp_t (FStar_Pervasives_Native.fst arg)  in
               (uu____18870, arg)  in
             let uu____18879 = is_quantified_const tm1  in
             match uu____18879 with
             | FStar_Pervasives_Native.Some tm2 ->
                 let uu____18883 = norm cfg env [] tm2  in
                 maybe_simplify_aux cfg env stack uu____18883
             | FStar_Pervasives_Native.None  ->
                 let uu____18884 =
                   let uu____18885 = FStar_Syntax_Subst.compress tm1  in
                   uu____18885.FStar_Syntax_Syntax.n  in
                 (match uu____18884 with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                           ({
                              FStar_Syntax_Syntax.n =
                                FStar_Syntax_Syntax.Tm_fvar fv;
                              FStar_Syntax_Syntax.pos = uu____18889;
                              FStar_Syntax_Syntax.vars = uu____18890;_},uu____18891);
                         FStar_Syntax_Syntax.pos = uu____18892;
                         FStar_Syntax_Syntax.vars = uu____18893;_},args)
                      ->
                      let uu____18919 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid
                         in
                      if uu____18919
                      then
                        let uu____18920 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        (match uu____18920 with
                         | (FStar_Pervasives_Native.Some (true ),uu____18965)::
                             (uu____18966,(arg,uu____18968))::[] ->
                             maybe_auto_squash arg
                         | (uu____19017,(arg,uu____19019))::(FStar_Pervasives_Native.Some
                                                             (true
                                                             ),uu____19020)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____19069)::uu____19070::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____19121::(FStar_Pervasives_Native.Some (false
                                         ),uu____19122)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____19173 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____19187 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid
                            in
                         if uu____19187
                         then
                           let uu____19188 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify1)
                              in
                           match uu____19188 with
                           | (FStar_Pervasives_Native.Some (true
                              ),uu____19233)::uu____19234::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____19285::(FStar_Pervasives_Native.Some (true
                                           ),uu____19286)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false
                              ),uu____19337)::(uu____19338,(arg,uu____19340))::[]
                               -> maybe_auto_squash arg
                           | (uu____19389,(arg,uu____19391))::(FStar_Pervasives_Native.Some
                                                               (false
                                                               ),uu____19392)::[]
                               -> maybe_auto_squash arg
                           | uu____19441 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____19455 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid
                               in
                            if uu____19455
                            then
                              let uu____19456 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify1)
                                 in
                              match uu____19456 with
                              | uu____19501::(FStar_Pervasives_Native.Some
                                              (true ),uu____19502)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false
                                 ),uu____19553)::uu____19554::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true
                                 ),uu____19605)::(uu____19606,(arg,uu____19608))::[]
                                  -> maybe_auto_squash arg
                              | (uu____19657,(p,uu____19659))::(uu____19660,
                                                                (q,uu____19662))::[]
                                  ->
                                  let uu____19709 =
                                    FStar_Syntax_Util.term_eq p q  in
                                  (if uu____19709
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____19711 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____19725 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid
                                  in
                               if uu____19725
                               then
                                 let uu____19726 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify1)
                                    in
                                 match uu____19726 with
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____19771)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____19772)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____19823)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____19824)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____19875)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____19876)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____19927)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____19928)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____19979,(arg,uu____19981))::(FStar_Pervasives_Native.Some
                                                                    (true
                                                                    ),uu____19982)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____20031)::(uu____20032,(arg,uu____20034))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____20083,(arg,uu____20085))::(FStar_Pervasives_Native.Some
                                                                    (false
                                                                    ),uu____20086)::[]
                                     ->
                                     let uu____20135 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____20135
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____20136)::(uu____20137,(arg,uu____20139))::[]
                                     ->
                                     let uu____20188 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____20188
                                 | (uu____20189,(p,uu____20191))::(uu____20192,
                                                                   (q,uu____20194))::[]
                                     ->
                                     let uu____20241 =
                                       FStar_Syntax_Util.term_eq p q  in
                                     (if uu____20241
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____20243 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____20257 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid
                                     in
                                  if uu____20257
                                  then
                                    let uu____20258 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify1)
                                       in
                                    match uu____20258 with
                                    | (FStar_Pervasives_Native.Some (true
                                       ),uu____20303)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false
                                       ),uu____20334)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____20365 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____20379 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid
                                        in
                                     if uu____20379
                                     then
                                       match args with
                                       | (t,uu____20381)::[] ->
                                           let uu____20398 =
                                             let uu____20399 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____20399.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____20398 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____20402::[],body,uu____20404)
                                                ->
                                                let uu____20431 = simp_t body
                                                   in
                                                (match uu____20431 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____20434 -> tm1)
                                            | uu____20437 -> tm1)
                                       | (ty,FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____20439))::(t,uu____20441)::[]
                                           ->
                                           let uu____20468 =
                                             let uu____20469 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____20469.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____20468 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____20472::[],body,uu____20474)
                                                ->
                                                let uu____20501 = simp_t body
                                                   in
                                                (match uu____20501 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false ) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____20504 -> tm1)
                                            | uu____20507 -> tm1)
                                       | uu____20508 -> tm1
                                     else
                                       (let uu____20518 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid
                                           in
                                        if uu____20518
                                        then
                                          match args with
                                          | (t,uu____20520)::[] ->
                                              let uu____20537 =
                                                let uu____20538 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____20538.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____20537 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____20541::[],body,uu____20543)
                                                   ->
                                                   let uu____20570 =
                                                     simp_t body  in
                                                   (match uu____20570 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____20573 -> tm1)
                                               | uu____20576 -> tm1)
                                          | (ty,FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____20578))::(t,uu____20580)::[]
                                              ->
                                              let uu____20607 =
                                                let uu____20608 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____20608.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____20607 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____20611::[],body,uu____20613)
                                                   ->
                                                   let uu____20640 =
                                                     simp_t body  in
                                                   (match uu____20640 with
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
                                                    | uu____20643 -> tm1)
                                               | uu____20646 -> tm1)
                                          | uu____20647 -> tm1
                                        else
                                          (let uu____20657 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid
                                              in
                                           if uu____20657
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____20658;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____20659;_},uu____20660)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____20677;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____20678;_},uu____20679)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____20696 -> tm1
                                           else
                                             (let uu____20706 =
                                                FStar_Syntax_Util.is_auto_squash
                                                  tm1
                                                 in
                                              match uu____20706 with
                                              | FStar_Pervasives_Native.Some
                                                  (FStar_Syntax_Syntax.U_zero
                                                   ,t)
                                                  when
                                                  FStar_Syntax_Util.is_sub_singleton
                                                    t
                                                  -> t
                                              | uu____20726 ->
                                                  reduce_equality cfg env
                                                    stack tm1))))))))
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____20736;
                         FStar_Syntax_Syntax.vars = uu____20737;_},args)
                      ->
                      let uu____20759 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid
                         in
                      if uu____20759
                      then
                        let uu____20760 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        (match uu____20760 with
                         | (FStar_Pervasives_Native.Some (true ),uu____20805)::
                             (uu____20806,(arg,uu____20808))::[] ->
                             maybe_auto_squash arg
                         | (uu____20857,(arg,uu____20859))::(FStar_Pervasives_Native.Some
                                                             (true
                                                             ),uu____20860)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____20909)::uu____20910::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____20961::(FStar_Pervasives_Native.Some (false
                                         ),uu____20962)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____21013 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____21027 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid
                            in
                         if uu____21027
                         then
                           let uu____21028 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify1)
                              in
                           match uu____21028 with
                           | (FStar_Pervasives_Native.Some (true
                              ),uu____21073)::uu____21074::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____21125::(FStar_Pervasives_Native.Some (true
                                           ),uu____21126)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false
                              ),uu____21177)::(uu____21178,(arg,uu____21180))::[]
                               -> maybe_auto_squash arg
                           | (uu____21229,(arg,uu____21231))::(FStar_Pervasives_Native.Some
                                                               (false
                                                               ),uu____21232)::[]
                               -> maybe_auto_squash arg
                           | uu____21281 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____21295 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid
                               in
                            if uu____21295
                            then
                              let uu____21296 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify1)
                                 in
                              match uu____21296 with
                              | uu____21341::(FStar_Pervasives_Native.Some
                                              (true ),uu____21342)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false
                                 ),uu____21393)::uu____21394::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true
                                 ),uu____21445)::(uu____21446,(arg,uu____21448))::[]
                                  -> maybe_auto_squash arg
                              | (uu____21497,(p,uu____21499))::(uu____21500,
                                                                (q,uu____21502))::[]
                                  ->
                                  let uu____21549 =
                                    FStar_Syntax_Util.term_eq p q  in
                                  (if uu____21549
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____21551 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____21565 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid
                                  in
                               if uu____21565
                               then
                                 let uu____21566 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify1)
                                    in
                                 match uu____21566 with
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____21611)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____21612)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____21663)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____21664)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____21715)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____21716)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____21767)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____21768)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____21819,(arg,uu____21821))::(FStar_Pervasives_Native.Some
                                                                    (true
                                                                    ),uu____21822)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____21871)::(uu____21872,(arg,uu____21874))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____21923,(arg,uu____21925))::(FStar_Pervasives_Native.Some
                                                                    (false
                                                                    ),uu____21926)::[]
                                     ->
                                     let uu____21975 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____21975
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____21976)::(uu____21977,(arg,uu____21979))::[]
                                     ->
                                     let uu____22028 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____22028
                                 | (uu____22029,(p,uu____22031))::(uu____22032,
                                                                   (q,uu____22034))::[]
                                     ->
                                     let uu____22081 =
                                       FStar_Syntax_Util.term_eq p q  in
                                     (if uu____22081
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____22083 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____22097 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid
                                     in
                                  if uu____22097
                                  then
                                    let uu____22098 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify1)
                                       in
                                    match uu____22098 with
                                    | (FStar_Pervasives_Native.Some (true
                                       ),uu____22143)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false
                                       ),uu____22174)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____22205 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____22219 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid
                                        in
                                     if uu____22219
                                     then
                                       match args with
                                       | (t,uu____22221)::[] ->
                                           let uu____22238 =
                                             let uu____22239 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____22239.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____22238 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____22242::[],body,uu____22244)
                                                ->
                                                let uu____22271 = simp_t body
                                                   in
                                                (match uu____22271 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____22274 -> tm1)
                                            | uu____22277 -> tm1)
                                       | (ty,FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____22279))::(t,uu____22281)::[]
                                           ->
                                           let uu____22308 =
                                             let uu____22309 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____22309.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____22308 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____22312::[],body,uu____22314)
                                                ->
                                                let uu____22341 = simp_t body
                                                   in
                                                (match uu____22341 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false ) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____22344 -> tm1)
                                            | uu____22347 -> tm1)
                                       | uu____22348 -> tm1
                                     else
                                       (let uu____22358 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid
                                           in
                                        if uu____22358
                                        then
                                          match args with
                                          | (t,uu____22360)::[] ->
                                              let uu____22377 =
                                                let uu____22378 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____22378.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____22377 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____22381::[],body,uu____22383)
                                                   ->
                                                   let uu____22410 =
                                                     simp_t body  in
                                                   (match uu____22410 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____22413 -> tm1)
                                               | uu____22416 -> tm1)
                                          | (ty,FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____22418))::(t,uu____22420)::[]
                                              ->
                                              let uu____22447 =
                                                let uu____22448 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____22448.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____22447 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____22451::[],body,uu____22453)
                                                   ->
                                                   let uu____22480 =
                                                     simp_t body  in
                                                   (match uu____22480 with
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
                                                    | uu____22483 -> tm1)
                                               | uu____22486 -> tm1)
                                          | uu____22487 -> tm1
                                        else
                                          (let uu____22497 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid
                                              in
                                           if uu____22497
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____22498;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____22499;_},uu____22500)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____22517;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____22518;_},uu____22519)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____22536 -> tm1
                                           else
                                             (let uu____22546 =
                                                FStar_Syntax_Util.is_auto_squash
                                                  tm1
                                                 in
                                              match uu____22546 with
                                              | FStar_Pervasives_Native.Some
                                                  (FStar_Syntax_Syntax.U_zero
                                                   ,t)
                                                  when
                                                  FStar_Syntax_Util.is_sub_singleton
                                                    t
                                                  -> t
                                              | uu____22566 ->
                                                  reduce_equality cfg env
                                                    stack tm1))))))))
                  | FStar_Syntax_Syntax.Tm_refine (bv,t) ->
                      let uu____22581 = simp_t t  in
                      (match uu____22581 with
                       | FStar_Pervasives_Native.Some (true ) ->
                           bv.FStar_Syntax_Syntax.sort
                       | FStar_Pervasives_Native.Some (false ) -> tm1
                       | FStar_Pervasives_Native.None  -> tm1)
                  | FStar_Syntax_Syntax.Tm_match uu____22584 ->
                      let uu____22607 = is_const_match tm1  in
                      (match uu____22607 with
                       | FStar_Pervasives_Native.Some (true ) ->
                           w FStar_Syntax_Util.t_true
                       | FStar_Pervasives_Native.Some (false ) ->
                           w FStar_Syntax_Util.t_false
                       | FStar_Pervasives_Native.None  -> tm1)
                  | uu____22610 -> tm1))

and (rebuild :
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          log cfg
            (fun uu____22620  ->
               (let uu____22622 = FStar_Syntax_Print.tag_of_term t  in
                let uu____22623 = FStar_Syntax_Print.term_to_string t  in
                let uu____22624 =
                  FStar_Util.string_of_int (FStar_List.length env)  in
                let uu____22631 =
                  let uu____22632 =
                    let uu____22635 = firstn (Prims.parse_int "4") stack  in
                    FStar_All.pipe_left FStar_Pervasives_Native.fst
                      uu____22635
                     in
                  stack_to_string uu____22632  in
                FStar_Util.print4
                  ">>> %s\nRebuild %s with %s env elements and top of the stack %s \n"
                  uu____22622 uu____22623 uu____22624 uu____22631);
               (let uu____22658 =
                  FStar_TypeChecker_Env.debug cfg.tcenv
                    (FStar_Options.Other "NormRebuild")
                   in
                if uu____22658
                then
                  let uu____22659 = FStar_Syntax_Util.unbound_variables t  in
                  match uu____22659 with
                  | [] -> ()
                  | bvs ->
                      ((let uu____22666 = FStar_Syntax_Print.tag_of_term t
                           in
                        let uu____22667 = FStar_Syntax_Print.term_to_string t
                           in
                        let uu____22668 =
                          let uu____22669 =
                            FStar_All.pipe_right bvs
                              (FStar_List.map FStar_Syntax_Print.bv_to_string)
                             in
                          FStar_All.pipe_right uu____22669
                            (FStar_String.concat ", ")
                           in
                        FStar_Util.print3
                          "!!! Rebuild (%s) %s, free vars=%s\n" uu____22666
                          uu____22667 uu____22668);
                       failwith "DIE!")
                else ()));
          (let t1 = maybe_simplify cfg env stack t  in
           match stack with
           | [] -> t1
           | (Debug (tm,time_then))::stack1 ->
               (if (cfg.debug).print_normalized
                then
                  (let time_now = FStar_Util.now ()  in
                   let uu____22687 =
                     let uu____22688 =
                       let uu____22689 =
                         FStar_Util.time_diff time_then time_now  in
                       FStar_Pervasives_Native.snd uu____22689  in
                     FStar_Util.string_of_int uu____22688  in
                   let uu____22694 = FStar_Syntax_Print.term_to_string tm  in
                   let uu____22695 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.print3 "Normalized (%s ms) %s\n\tto %s\n"
                     uu____22687 uu____22694 uu____22695)
                else ();
                rebuild cfg env stack1 t1)
           | (Cfg cfg1)::stack1 -> rebuild cfg1 env stack1 t1
           | (Meta (uu____22701,m,r))::stack1 ->
               let t2 = mk (FStar_Syntax_Syntax.Tm_meta (t1, m)) r  in
               rebuild cfg env stack1 t2
           | (MemoLazy r)::stack1 ->
               (set_memo cfg r (env, t1);
                log cfg
                  (fun uu____22752  ->
                     let uu____22753 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 "\tSet memo %s\n" uu____22753);
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
               let uu____22791 =
                 let uu___184_22792 = FStar_Syntax_Util.abs bs1 t1 lopt1  in
                 {
                   FStar_Syntax_Syntax.n =
                     (uu___184_22792.FStar_Syntax_Syntax.n);
                   FStar_Syntax_Syntax.pos = r;
                   FStar_Syntax_Syntax.vars =
                     (uu___184_22792.FStar_Syntax_Syntax.vars)
                 }  in
               rebuild cfg env stack1 uu____22791
           | (Arg (Univ uu____22795,uu____22796,uu____22797))::uu____22798 ->
               failwith "Impossible"
           | (Arg (Dummy ,uu____22801,uu____22802))::uu____22803 ->
               failwith "Impossible"
           | (UnivArgs (us,r))::stack1 ->
               let t2 = FStar_Syntax_Syntax.mk_Tm_uinst t1 us  in
               rebuild cfg env stack1 t2
           | (Arg (Clos (env_arg,tm,uu____22818,uu____22819),aq,r))::stack1
               when
               let uu____22869 = head_of t1  in
               FStar_Syntax_Util.is_fstar_tactics_by_tactic uu____22869 ->
               let t2 =
                 let uu____22873 =
                   let uu____22878 =
                     let uu____22879 = closure_as_term cfg env_arg tm  in
                     (uu____22879, aq)  in
                   FStar_Syntax_Syntax.extend_app t1 uu____22878  in
                 uu____22873 FStar_Pervasives_Native.None r  in
               rebuild cfg env stack1 t2
           | (Arg (Clos (env_arg,tm,m,uu____22889),aq,r))::stack1 ->
               (log cfg
                  (fun uu____22942  ->
                     let uu____22943 = FStar_Syntax_Print.term_to_string tm
                        in
                     FStar_Util.print1 "Rebuilding with arg %s\n" uu____22943);
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
                  (let uu____22955 = FStar_ST.op_Bang m  in
                   match uu____22955 with
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
                   | FStar_Pervasives_Native.Some (uu____23098,a) ->
                       let t2 =
                         FStar_Syntax_Syntax.extend_app t1 (a, aq)
                           FStar_Pervasives_Native.None r
                          in
                       rebuild cfg env_arg stack1 t2))
           | (App (env1,head1,aq,r))::stack' when should_reify cfg stack ->
               let t0 = t1  in
               let fallback msg uu____23151 =
                 log cfg
                   (fun uu____23155  ->
                      let uu____23156 = FStar_Syntax_Print.term_to_string t1
                         in
                      FStar_Util.print2 "Not reifying%s: %s\n" msg
                        uu____23156);
                 (let t2 =
                    FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                      FStar_Pervasives_Native.None r
                     in
                  rebuild cfg env1 stack' t2)
                  in
               let uu____23162 =
                 let uu____23163 = FStar_Syntax_Subst.compress t1  in
                 uu____23163.FStar_Syntax_Syntax.n  in
               (match uu____23162 with
                | FStar_Syntax_Syntax.Tm_meta
                    (t2,FStar_Syntax_Syntax.Meta_monadic (m,ty)) ->
                    do_reify_monadic (fallback " (1)") cfg env1 stack t2 m ty
                | FStar_Syntax_Syntax.Tm_meta
                    (t2,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,ty))
                    ->
                    let lifted =
                      let uu____23190 = closure_as_term cfg env1 ty  in
                      reify_lift cfg t2 msrc mtgt uu____23190  in
                    (log cfg
                       (fun uu____23194  ->
                          let uu____23195 =
                            FStar_Syntax_Print.term_to_string lifted  in
                          FStar_Util.print1 "Reified lift to (1): %s\n"
                            uu____23195);
                     (let uu____23196 = FStar_List.tl stack  in
                      norm cfg env1 uu____23196 lifted))
                | FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reflect uu____23197);
                       FStar_Syntax_Syntax.pos = uu____23198;
                       FStar_Syntax_Syntax.vars = uu____23199;_},(e,uu____23201)::[])
                    -> norm cfg env1 stack' e
                | FStar_Syntax_Syntax.Tm_app uu____23230 when
                    (cfg.steps).primops ->
                    let uu____23245 = FStar_Syntax_Util.head_and_args t1  in
                    (match uu____23245 with
                     | (hd1,args) ->
                         let uu____23276 =
                           let uu____23277 = FStar_Syntax_Util.un_uinst hd1
                              in
                           uu____23277.FStar_Syntax_Syntax.n  in
                         (match uu____23276 with
                          | FStar_Syntax_Syntax.Tm_fvar fv ->
                              let uu____23281 = find_prim_step cfg fv  in
                              (match uu____23281 with
                               | FStar_Pervasives_Native.Some
                                   { name = uu____23284; arity = uu____23285;
                                     auto_reflect =
                                       FStar_Pervasives_Native.Some n1;
                                     strong_reduction_ok = uu____23287;
                                     requires_binder_substitution =
                                       uu____23288;
                                     interpretation = uu____23289;_}
                                   when (FStar_List.length args) = n1 ->
                                   norm cfg env1 stack' t1
                               | uu____23305 -> fallback " (3)" ())
                          | uu____23308 -> fallback " (4)" ()))
                | uu____23309 -> fallback " (2)" ())
           | (App (env1,head1,aq,r))::stack1 ->
               let t2 =
                 FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                   FStar_Pervasives_Native.None r
                  in
               rebuild cfg env1 stack1 t2
           | (Match (env',branches,cfg1,r))::stack1 ->
               (log cfg1
                  (fun uu____23332  ->
                     let uu____23333 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1
                       "Rebuilding with match, scrutinee is %s ...\n"
                       uu____23333);
                (let scrutinee_env = env  in
                 let env1 = env'  in
                 let scrutinee = t1  in
                 let norm_and_rebuild_match uu____23342 =
                   log cfg1
                     (fun uu____23347  ->
                        let uu____23348 =
                          FStar_Syntax_Print.term_to_string scrutinee  in
                        let uu____23349 =
                          let uu____23350 =
                            FStar_All.pipe_right branches
                              (FStar_List.map
                                 (fun uu____23377  ->
                                    match uu____23377 with
                                    | (p,uu____23387,uu____23388) ->
                                        FStar_Syntax_Print.pat_to_string p))
                             in
                          FStar_All.pipe_right uu____23350
                            (FStar_String.concat "\n\t")
                           in
                        FStar_Util.print2
                          "match is irreducible: scrutinee=%s\nbranches=%s\n"
                          uu____23348 uu____23349);
                   (let whnf = (cfg1.steps).weak || (cfg1.steps).hnf  in
                    let cfg_exclude_zeta =
                      let new_delta =
                        FStar_All.pipe_right cfg1.delta_level
                          (FStar_List.filter
                             (fun uu___93_23405  ->
                                match uu___93_23405 with
                                | FStar_TypeChecker_Env.Inlining  -> true
                                | FStar_TypeChecker_Env.Eager_unfolding_only 
                                    -> true
                                | uu____23406 -> false))
                         in
                      let steps =
                        let uu___185_23408 = cfg1.steps  in
                        {
                          beta = (uu___185_23408.beta);
                          iota = (uu___185_23408.iota);
                          zeta = false;
                          weak = (uu___185_23408.weak);
                          hnf = (uu___185_23408.hnf);
                          primops = (uu___185_23408.primops);
                          do_not_unfold_pure_lets =
                            (uu___185_23408.do_not_unfold_pure_lets);
                          unfold_until = FStar_Pervasives_Native.None;
                          unfold_only = FStar_Pervasives_Native.None;
                          unfold_fully = (uu___185_23408.unfold_fully);
                          unfold_attr = FStar_Pervasives_Native.None;
                          unfold_tac = false;
                          pure_subterms_within_computations =
                            (uu___185_23408.pure_subterms_within_computations);
                          simplify = (uu___185_23408.simplify);
                          erase_universes = (uu___185_23408.erase_universes);
                          allow_unbound_universes =
                            (uu___185_23408.allow_unbound_universes);
                          reify_ = (uu___185_23408.reify_);
                          compress_uvars = (uu___185_23408.compress_uvars);
                          no_full_norm = (uu___185_23408.no_full_norm);
                          check_no_uvars = (uu___185_23408.check_no_uvars);
                          unmeta = (uu___185_23408.unmeta);
                          unascribe = (uu___185_23408.unascribe);
                          in_full_norm_request =
                            (uu___185_23408.in_full_norm_request);
                          weakly_reduce_scrutinee =
                            (uu___185_23408.weakly_reduce_scrutinee)
                        }  in
                      let uu___186_23413 = cfg1  in
                      {
                        steps;
                        tcenv = (uu___186_23413.tcenv);
                        debug = (uu___186_23413.debug);
                        delta_level = new_delta;
                        primitive_steps = (uu___186_23413.primitive_steps);
                        strong = true;
                        memoize_lazy = (uu___186_23413.memoize_lazy);
                        normalize_pure_lets =
                          (uu___186_23413.normalize_pure_lets)
                      }  in
                    let norm_or_whnf env2 t2 =
                      if whnf
                      then closure_as_term cfg_exclude_zeta env2 t2
                      else norm cfg_exclude_zeta env2 [] t2  in
                    let rec norm_pat env2 p =
                      match p.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_constant uu____23485 ->
                          (p, env2)
                      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                          let uu____23514 =
                            FStar_All.pipe_right pats
                              (FStar_List.fold_left
                                 (fun uu____23598  ->
                                    fun uu____23599  ->
                                      match (uu____23598, uu____23599) with
                                      | ((pats1,env3),(p1,b)) ->
                                          let uu____23738 = norm_pat env3 p1
                                             in
                                          (match uu____23738 with
                                           | (p2,env4) ->
                                               (((p2, b) :: pats1), env4)))
                                 ([], env2))
                             in
                          (match uu____23514 with
                           | (pats1,env3) ->
                               ((let uu___187_23900 = p  in
                                 {
                                   FStar_Syntax_Syntax.v =
                                     (FStar_Syntax_Syntax.Pat_cons
                                        (fv, (FStar_List.rev pats1)));
                                   FStar_Syntax_Syntax.p =
                                     (uu___187_23900.FStar_Syntax_Syntax.p)
                                 }), env3))
                      | FStar_Syntax_Syntax.Pat_var x ->
                          let x1 =
                            let uu___188_23919 = x  in
                            let uu____23920 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___188_23919.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___188_23919.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____23920
                            }  in
                          ((let uu___189_23934 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_var x1);
                              FStar_Syntax_Syntax.p =
                                (uu___189_23934.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_wild x ->
                          let x1 =
                            let uu___190_23945 = x  in
                            let uu____23946 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___190_23945.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___190_23945.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____23946
                            }  in
                          ((let uu___191_23960 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_wild x1);
                              FStar_Syntax_Syntax.p =
                                (uu___191_23960.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                          let x1 =
                            let uu___192_23976 = x  in
                            let uu____23977 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___192_23976.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___192_23976.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____23977
                            }  in
                          let t3 = norm_or_whnf env2 t2  in
                          ((let uu___193_23992 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_dot_term (x1, t3));
                              FStar_Syntax_Syntax.p =
                                (uu___193_23992.FStar_Syntax_Syntax.p)
                            }), env2)
                       in
                    let branches1 =
                      match env1 with
                      | [] when whnf -> branches
                      | uu____24008 ->
                          FStar_All.pipe_right branches
                            (FStar_List.map
                               (fun branch1  ->
                                  let uu____24024 =
                                    FStar_Syntax_Subst.open_branch branch1
                                     in
                                  match uu____24024 with
                                  | (p,wopt,e) ->
                                      let uu____24044 = norm_pat env1 p  in
                                      (match uu____24044 with
                                       | (p1,env2) ->
                                           let wopt1 =
                                             match wopt with
                                             | FStar_Pervasives_Native.None 
                                                 ->
                                                 FStar_Pervasives_Native.None
                                             | FStar_Pervasives_Native.Some w
                                                 ->
                                                 let uu____24099 =
                                                   norm_or_whnf env2 w  in
                                                 FStar_Pervasives_Native.Some
                                                   uu____24099
                                              in
                                           let e1 = norm_or_whnf env2 e  in
                                           FStar_Syntax_Util.branch
                                             (p1, wopt1, e1))))
                       in
                    let scrutinee1 =
                      let uu____24112 =
                        ((((cfg1.steps).iota &&
                             (Prims.op_Negation (cfg1.steps).weak))
                            &&
                            (Prims.op_Negation (cfg1.steps).compress_uvars))
                           && (cfg1.steps).weakly_reduce_scrutinee)
                          && (maybe_weakly_reduced scrutinee)
                         in
                      if uu____24112
                      then
                        norm
                          (let uu___194_24117 = cfg1  in
                           {
                             steps =
                               (let uu___195_24120 = cfg1.steps  in
                                {
                                  beta = (uu___195_24120.beta);
                                  iota = (uu___195_24120.iota);
                                  zeta = (uu___195_24120.zeta);
                                  weak = (uu___195_24120.weak);
                                  hnf = (uu___195_24120.hnf);
                                  primops = (uu___195_24120.primops);
                                  do_not_unfold_pure_lets =
                                    (uu___195_24120.do_not_unfold_pure_lets);
                                  unfold_until =
                                    (uu___195_24120.unfold_until);
                                  unfold_only = (uu___195_24120.unfold_only);
                                  unfold_fully =
                                    (uu___195_24120.unfold_fully);
                                  unfold_attr = (uu___195_24120.unfold_attr);
                                  unfold_tac = (uu___195_24120.unfold_tac);
                                  pure_subterms_within_computations =
                                    (uu___195_24120.pure_subterms_within_computations);
                                  simplify = (uu___195_24120.simplify);
                                  erase_universes =
                                    (uu___195_24120.erase_universes);
                                  allow_unbound_universes =
                                    (uu___195_24120.allow_unbound_universes);
                                  reify_ = (uu___195_24120.reify_);
                                  compress_uvars =
                                    (uu___195_24120.compress_uvars);
                                  no_full_norm =
                                    (uu___195_24120.no_full_norm);
                                  check_no_uvars =
                                    (uu___195_24120.check_no_uvars);
                                  unmeta = (uu___195_24120.unmeta);
                                  unascribe = (uu___195_24120.unascribe);
                                  in_full_norm_request =
                                    (uu___195_24120.in_full_norm_request);
                                  weakly_reduce_scrutinee = false
                                });
                             tcenv = (uu___194_24117.tcenv);
                             debug = (uu___194_24117.debug);
                             delta_level = (uu___194_24117.delta_level);
                             primitive_steps =
                               (uu___194_24117.primitive_steps);
                             strong = (uu___194_24117.strong);
                             memoize_lazy = (uu___194_24117.memoize_lazy);
                             normalize_pure_lets =
                               (uu___194_24117.normalize_pure_lets)
                           }) scrutinee_env [] scrutinee
                      else scrutinee  in
                    let uu____24122 =
                      mk
                        (FStar_Syntax_Syntax.Tm_match (scrutinee1, branches1))
                        r
                       in
                    rebuild cfg1 env1 stack1 uu____24122)
                    in
                 let rec is_cons head1 =
                   let uu____24147 =
                     let uu____24148 = FStar_Syntax_Subst.compress head1  in
                     uu____24148.FStar_Syntax_Syntax.n  in
                   match uu____24147 with
                   | FStar_Syntax_Syntax.Tm_uinst (h,uu____24152) ->
                       is_cons h
                   | FStar_Syntax_Syntax.Tm_constant uu____24157 -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____24158;
                         FStar_Syntax_Syntax.fv_delta = uu____24159;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Data_ctor );_}
                       -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____24160;
                         FStar_Syntax_Syntax.fv_delta = uu____24161;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Record_ctor uu____24162);_}
                       -> true
                   | uu____24169 -> false  in
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
                   let uu____24332 =
                     FStar_Syntax_Util.head_and_args scrutinee1  in
                   match uu____24332 with
                   | (head1,args) ->
                       (match p.FStar_Syntax_Syntax.v with
                        | FStar_Syntax_Syntax.Pat_var bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_wild bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_dot_term uu____24413 ->
                            FStar_Util.Inl []
                        | FStar_Syntax_Syntax.Pat_constant s ->
                            (match scrutinee1.FStar_Syntax_Syntax.n with
                             | FStar_Syntax_Syntax.Tm_constant s' when
                                 FStar_Const.eq_const s s' ->
                                 FStar_Util.Inl []
                             | uu____24452 ->
                                 let uu____24453 =
                                   let uu____24454 = is_cons head1  in
                                   Prims.op_Negation uu____24454  in
                                 FStar_Util.Inr uu____24453)
                        | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                            let uu____24479 =
                              let uu____24480 =
                                FStar_Syntax_Util.un_uinst head1  in
                              uu____24480.FStar_Syntax_Syntax.n  in
                            (match uu____24479 with
                             | FStar_Syntax_Syntax.Tm_fvar fv' when
                                 FStar_Syntax_Syntax.fv_eq fv fv' ->
                                 matches_args [] args arg_pats
                             | uu____24498 ->
                                 let uu____24499 =
                                   let uu____24500 = is_cons head1  in
                                   Prims.op_Negation uu____24500  in
                                 FStar_Util.Inr uu____24499))
                 
                 and matches_args out a p =
                   match (a, p) with
                   | ([],[]) -> FStar_Util.Inl out
                   | ((t2,uu____24577)::rest_a,(p1,uu____24580)::rest_p) ->
                       let uu____24624 = matches_pat t2 p1  in
                       (match uu____24624 with
                        | FStar_Util.Inl s ->
                            matches_args (FStar_List.append out s) rest_a
                              rest_p
                        | m -> m)
                   | uu____24673 -> FStar_Util.Inr false
                  in
                 let rec matches scrutinee1 p =
                   match p with
                   | [] -> norm_and_rebuild_match ()
                   | (p1,wopt,b)::rest ->
                       let uu____24791 = matches_pat scrutinee1 p1  in
                       (match uu____24791 with
                        | FStar_Util.Inr (false ) -> matches scrutinee1 rest
                        | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                        | FStar_Util.Inl s ->
                            (log cfg1
                               (fun uu____24831  ->
                                  let uu____24832 =
                                    FStar_Syntax_Print.pat_to_string p1  in
                                  let uu____24833 =
                                    let uu____24834 =
                                      FStar_List.map
                                        (fun uu____24844  ->
                                           match uu____24844 with
                                           | (uu____24849,t2) ->
                                               FStar_Syntax_Print.term_to_string
                                                 t2) s
                                       in
                                    FStar_All.pipe_right uu____24834
                                      (FStar_String.concat "; ")
                                     in
                                  FStar_Util.print2
                                    "Matches pattern %s with subst = %s\n"
                                    uu____24832 uu____24833);
                             (let env0 = env1  in
                              let env2 =
                                FStar_List.fold_left
                                  (fun env2  ->
                                     fun uu____24881  ->
                                       match uu____24881 with
                                       | (bv,t2) ->
                                           let uu____24904 =
                                             let uu____24911 =
                                               let uu____24914 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   bv
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 uu____24914
                                                in
                                             let uu____24915 =
                                               let uu____24916 =
                                                 let uu____24947 =
                                                   FStar_Util.mk_ref
                                                     (FStar_Pervasives_Native.Some
                                                        ([], t2))
                                                    in
                                                 ([], t2, uu____24947, false)
                                                  in
                                               Clos uu____24916  in
                                             (uu____24911, uu____24915)  in
                                           uu____24904 :: env2) env1 s
                                 in
                              let uu____25060 = guard_when_clause wopt b rest
                                 in
                              norm cfg1 env2 stack1 uu____25060)))
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
    let uu____25087 =
      let uu____25090 = FStar_ST.op_Bang plugins  in p :: uu____25090  in
    FStar_ST.op_Colon_Equals plugins uu____25087  in
  let retrieve uu____25198 = FStar_ST.op_Bang plugins  in
  (register, retrieve) 
let (register_plugin : primitive_step -> unit) =
  fun p  -> FStar_Pervasives_Native.fst plugins p 
let (retrieve_plugins : unit -> primitive_step Prims.list) =
  fun uu____25275  -> FStar_Pervasives_Native.snd plugins () 
let (config' :
  primitive_step Prims.list ->
    step Prims.list -> FStar_TypeChecker_Env.env -> cfg)
  =
  fun psteps  ->
    fun s  ->
      fun e  ->
        let d =
          FStar_All.pipe_right s
            (FStar_List.collect
               (fun uu___94_25316  ->
                  match uu___94_25316 with
                  | UnfoldUntil k -> [FStar_TypeChecker_Env.Unfold k]
                  | Eager_unfolding  ->
                      [FStar_TypeChecker_Env.Eager_unfolding_only]
                  | Inlining  -> [FStar_TypeChecker_Env.Inlining]
                  | UnfoldTac  -> [FStar_TypeChecker_Env.UnfoldTac]
                  | uu____25320 -> []))
           in
        let d1 =
          match d with
          | [] -> [FStar_TypeChecker_Env.NoDelta]
          | uu____25326 -> d  in
        let uu____25329 = to_fsteps s  in
        let uu____25330 =
          let uu____25331 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Norm")  in
          let uu____25332 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Primops")  in
          let uu____25333 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "380")  in
          let uu____25334 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "NormDelayed")
             in
          let uu____25335 =
            FStar_TypeChecker_Env.debug e
              (FStar_Options.Other "print_normalized_terms")
             in
          {
            gen = uu____25331;
            primop = uu____25332;
            b380 = uu____25333;
            norm_delayed = uu____25334;
            print_normalized = uu____25335
          }  in
        let uu____25336 =
          let uu____25339 =
            let uu____25342 = retrieve_plugins ()  in
            FStar_List.append uu____25342 psteps  in
          add_steps built_in_primitive_steps uu____25339  in
        let uu____25345 =
          (FStar_Options.normalize_pure_terms_for_extraction ()) ||
            (let uu____25347 =
               FStar_All.pipe_right s
                 (FStar_List.contains PureSubtermsWithinComputations)
                in
             Prims.op_Negation uu____25347)
           in
        {
          steps = uu____25329;
          tcenv = e;
          debug = uu____25330;
          delta_level = d1;
          primitive_steps = uu____25336;
          strong = false;
          memoize_lazy = true;
          normalize_pure_lets = uu____25345
        }
  
let (config : step Prims.list -> FStar_TypeChecker_Env.env -> cfg) =
  fun s  -> fun e  -> config' [] s e 
let (normalize_with_primitive_steps :
  primitive_step Prims.list ->
    step Prims.list ->
      FStar_TypeChecker_Env.env ->
        FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun ps  ->
    fun s  -> fun e  -> fun t  -> let c = config' ps s e  in norm c [] [] t
  
let (normalize :
  steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  = fun s  -> fun e  -> fun t  -> normalize_with_primitive_steps [] s e t 
let (normalize_comp :
  steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun s  ->
    fun e  ->
      fun t  -> let uu____25429 = config s e  in norm_comp uu____25429 [] t
  
let (normalize_universe :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun u  ->
      let uu____25446 = config [] env  in norm_universe uu____25446 [] u
  
let (ghost_to_pure :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun env  ->
    fun c  ->
      let cfg =
        config
          [UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
          AllowUnboundUniverses;
          EraseUniverses] env
         in
      let non_info t =
        let uu____25470 = norm cfg [] [] t  in
        FStar_Syntax_Util.non_informative uu____25470  in
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____25477 -> c
      | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
          let uu___196_25496 = c  in
          {
            FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
            FStar_Syntax_Syntax.pos =
              (uu___196_25496.FStar_Syntax_Syntax.pos);
            FStar_Syntax_Syntax.vars =
              (uu___196_25496.FStar_Syntax_Syntax.vars)
          }
      | FStar_Syntax_Syntax.Comp ct ->
          let l =
            FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
              ct.FStar_Syntax_Syntax.effect_name
             in
          let uu____25503 =
            (FStar_Syntax_Util.is_ghost_effect l) &&
              (non_info ct.FStar_Syntax_Syntax.result_typ)
             in
          if uu____25503
          then
            let ct1 =
              let uu____25505 =
                downgrade_ghost_effect_name
                  ct.FStar_Syntax_Syntax.effect_name
                 in
              match uu____25505 with
              | FStar_Pervasives_Native.Some pure_eff ->
                  let flags1 =
                    let uu____25512 =
                      FStar_Ident.lid_equals pure_eff
                        FStar_Parser_Const.effect_Tot_lid
                       in
                    if uu____25512
                    then FStar_Syntax_Syntax.TOTAL ::
                      (ct.FStar_Syntax_Syntax.flags)
                    else ct.FStar_Syntax_Syntax.flags  in
                  let uu___197_25516 = ct  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___197_25516.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name = pure_eff;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___197_25516.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___197_25516.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags = flags1
                  }
              | FStar_Pervasives_Native.None  ->
                  let ct1 =
                    FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c
                     in
                  let uu___198_25518 = ct1  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___198_25518.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name =
                      FStar_Parser_Const.effect_PURE_lid;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___198_25518.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___198_25518.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags =
                      (uu___198_25518.FStar_Syntax_Syntax.flags)
                  }
               in
            let uu___199_25519 = c  in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
              FStar_Syntax_Syntax.pos =
                (uu___199_25519.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___199_25519.FStar_Syntax_Syntax.vars)
            }
          else c
      | uu____25521 -> c
  
let (ghost_to_pure_lcomp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.lcomp -> FStar_Syntax_Syntax.lcomp)
  =
  fun env  ->
    fun lc  ->
      let cfg =
        config
          [Eager_unfolding;
          UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
          EraseUniverses;
          AllowUnboundUniverses] env
         in
      let non_info t =
        let uu____25539 = norm cfg [] [] t  in
        FStar_Syntax_Util.non_informative uu____25539  in
      let uu____25546 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ)
         in
      if uu____25546
      then
        let uu____25547 =
          downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name  in
        match uu____25547 with
        | FStar_Pervasives_Native.Some pure_eff ->
            FStar_Syntax_Syntax.mk_lcomp pure_eff
              lc.FStar_Syntax_Syntax.res_typ lc.FStar_Syntax_Syntax.cflags
              (fun uu____25553  ->
                 let uu____25554 = FStar_Syntax_Syntax.lcomp_comp lc  in
                 ghost_to_pure env uu____25554)
        | FStar_Pervasives_Native.None  -> lc
      else lc
  
let (term_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.string) =
  fun env  ->
    fun t  ->
      let t1 =
        try normalize [AllowUnboundUniverses] env t
        with
        | e ->
            ((let uu____25575 =
                let uu____25580 =
                  let uu____25581 = FStar_Util.message_of_exn e  in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____25581
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____25580)  in
              FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____25575);
             t)
         in
      FStar_Syntax_Print.term_to_string' env.FStar_TypeChecker_Env.dsenv t1
  
let (comp_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string) =
  fun env  ->
    fun c  ->
      let c1 =
        try
          let uu____25596 = config [AllowUnboundUniverses] env  in
          norm_comp uu____25596 [] c
        with
        | e ->
            ((let uu____25609 =
                let uu____25614 =
                  let uu____25615 = FStar_Util.message_of_exn e  in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____25615
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____25614)  in
              FStar_Errors.log_issue c.FStar_Syntax_Syntax.pos uu____25609);
             c)
         in
      FStar_Syntax_Print.comp_to_string' env.FStar_TypeChecker_Env.dsenv c1
  
let (normalize_refinement :
  steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ)
  =
  fun steps  ->
    fun env  ->
      fun t0  ->
        let t = normalize (FStar_List.append steps [Beta]) env t0  in
        let rec aux t1 =
          let t2 = FStar_Syntax_Subst.compress t1  in
          match t2.FStar_Syntax_Syntax.n with
          | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
              let t01 = aux x.FStar_Syntax_Syntax.sort  in
              (match t01.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_refine (y,phi1) ->
                   let uu____25660 =
                     let uu____25661 =
                       let uu____25668 = FStar_Syntax_Util.mk_conj phi1 phi
                          in
                       (y, uu____25668)  in
                     FStar_Syntax_Syntax.Tm_refine uu____25661  in
                   mk uu____25660 t01.FStar_Syntax_Syntax.pos
               | uu____25673 -> t2)
          | uu____25674 -> t2  in
        aux t
  
let (unfold_whnf :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      normalize
        [Primops;
        Weak;
        HNF;
        UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
        Beta] env t
  
let (reduce_or_remove_uvar_solutions :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun remove  ->
    fun env  ->
      fun t  ->
        normalize
          (FStar_List.append (if remove then [CheckNoUvars] else [])
             [Beta;
             DoNotUnfoldPureLets;
             CompressUvars;
             Exclude Zeta;
             Exclude Iota;
             NoFullNorm]) env t
  
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
        let uu____25738 = FStar_Syntax_Util.arrow_formals_comp t_e  in
        match uu____25738 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____25767 ->
                 let uu____25774 = FStar_Syntax_Util.abs_formals e  in
                 (match uu____25774 with
                  | (actuals,uu____25784,uu____25785) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____25799 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders
                            in
                         match uu____25799 with
                         | (binders,args) ->
                             let uu____25810 =
                               FStar_Syntax_Syntax.mk_Tm_app e args
                                 FStar_Pervasives_Native.None
                                 e.FStar_Syntax_Syntax.pos
                                in
                             FStar_Syntax_Util.abs binders uu____25810
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
      | uu____25824 ->
          let uu____25825 = FStar_Syntax_Util.head_and_args t  in
          (match uu____25825 with
           | (head1,args) ->
               let uu____25856 =
                 let uu____25857 = FStar_Syntax_Subst.compress head1  in
                 uu____25857.FStar_Syntax_Syntax.n  in
               (match uu____25856 with
                | FStar_Syntax_Syntax.Tm_uvar u ->
                    let uu____25861 =
                      FStar_Syntax_Util.arrow_formals
                        u.FStar_Syntax_Syntax.ctx_uvar_typ
                       in
                    (match uu____25861 with
                     | (formals,tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____25903 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___204_25911 = env  in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___204_25911.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___204_25911.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___204_25911.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___204_25911.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_sig =
                                     (uu___204_25911.FStar_TypeChecker_Env.gamma_sig);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___204_25911.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___204_25911.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___204_25911.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___204_25911.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___204_25911.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___204_25911.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___204_25911.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___204_25911.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___204_25911.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___204_25911.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___204_25911.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___204_25911.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___204_25911.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___204_25911.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___204_25911.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___204_25911.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___204_25911.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___204_25911.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___204_25911.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___204_25911.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                     =
                                     (uu___204_25911.FStar_TypeChecker_Env.qtbl_name_and_index);
                                   FStar_TypeChecker_Env.normalized_eff_names
                                     =
                                     (uu___204_25911.FStar_TypeChecker_Env.normalized_eff_names);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___204_25911.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth_hook =
                                     (uu___204_25911.FStar_TypeChecker_Env.synth_hook);
                                   FStar_TypeChecker_Env.splice =
                                     (uu___204_25911.FStar_TypeChecker_Env.splice);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___204_25911.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___204_25911.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___204_25911.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___204_25911.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.dep_graph =
                                     (uu___204_25911.FStar_TypeChecker_Env.dep_graph)
                                 }) t
                               in
                            match uu____25903 with
                            | (uu____25912,ty,uu____25914) ->
                                eta_expand_with_type env t ty))
                | uu____25915 ->
                    let uu____25916 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___205_25924 = env  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___205_25924.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___205_25924.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___205_25924.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___205_25924.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_sig =
                             (uu___205_25924.FStar_TypeChecker_Env.gamma_sig);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___205_25924.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___205_25924.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___205_25924.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___205_25924.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___205_25924.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___205_25924.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___205_25924.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___205_25924.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___205_25924.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___205_25924.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___205_25924.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___205_25924.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___205_25924.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___205_25924.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.failhard =
                             (uu___205_25924.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___205_25924.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___205_25924.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___205_25924.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___205_25924.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___205_25924.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qtbl_name_and_index =
                             (uu___205_25924.FStar_TypeChecker_Env.qtbl_name_and_index);
                           FStar_TypeChecker_Env.normalized_eff_names =
                             (uu___205_25924.FStar_TypeChecker_Env.normalized_eff_names);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___205_25924.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth_hook =
                             (uu___205_25924.FStar_TypeChecker_Env.synth_hook);
                           FStar_TypeChecker_Env.splice =
                             (uu___205_25924.FStar_TypeChecker_Env.splice);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___205_25924.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___205_25924.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___205_25924.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___205_25924.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.dep_graph =
                             (uu___205_25924.FStar_TypeChecker_Env.dep_graph)
                         }) t
                       in
                    (match uu____25916 with
                     | (uu____25925,ty,uu____25927) ->
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
      let uu___206_26000 = x  in
      let uu____26001 = elim_delayed_subst_term x.FStar_Syntax_Syntax.sort
         in
      {
        FStar_Syntax_Syntax.ppname =
          (uu___206_26000.FStar_Syntax_Syntax.ppname);
        FStar_Syntax_Syntax.index =
          (uu___206_26000.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = uu____26001
      }  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____26004 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_bvar uu____26029 -> t1
    | FStar_Syntax_Syntax.Tm_name uu____26030 -> t1
    | FStar_Syntax_Syntax.Tm_fvar uu____26031 -> t1
    | FStar_Syntax_Syntax.Tm_uinst uu____26032 -> t1
    | FStar_Syntax_Syntax.Tm_constant uu____26039 -> t1
    | FStar_Syntax_Syntax.Tm_type uu____26040 -> t1
    | FStar_Syntax_Syntax.Tm_lazy uu____26041 -> t1
    | FStar_Syntax_Syntax.Tm_unknown  -> t1
    | FStar_Syntax_Syntax.Tm_abs (bs,t2,rc_opt) ->
        let elim_rc rc =
          let uu___207_26071 = rc  in
          let uu____26072 =
            FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
              elim_delayed_subst_term
             in
          let uu____26081 =
            elim_delayed_subst_cflags rc.FStar_Syntax_Syntax.residual_flags
             in
          {
            FStar_Syntax_Syntax.residual_effect =
              (uu___207_26071.FStar_Syntax_Syntax.residual_effect);
            FStar_Syntax_Syntax.residual_typ = uu____26072;
            FStar_Syntax_Syntax.residual_flags = uu____26081
          }  in
        let uu____26084 =
          let uu____26085 =
            let uu____26102 = elim_delayed_subst_binders bs  in
            let uu____26109 = elim_delayed_subst_term t2  in
            let uu____26112 = FStar_Util.map_opt rc_opt elim_rc  in
            (uu____26102, uu____26109, uu____26112)  in
          FStar_Syntax_Syntax.Tm_abs uu____26085  in
        mk1 uu____26084
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____26143 =
          let uu____26144 =
            let uu____26157 = elim_delayed_subst_binders bs  in
            let uu____26164 = elim_delayed_subst_comp c  in
            (uu____26157, uu____26164)  in
          FStar_Syntax_Syntax.Tm_arrow uu____26144  in
        mk1 uu____26143
    | FStar_Syntax_Syntax.Tm_refine (bv,phi) ->
        let uu____26181 =
          let uu____26182 =
            let uu____26189 = elim_bv bv  in
            let uu____26190 = elim_delayed_subst_term phi  in
            (uu____26189, uu____26190)  in
          FStar_Syntax_Syntax.Tm_refine uu____26182  in
        mk1 uu____26181
    | FStar_Syntax_Syntax.Tm_app (t2,args) ->
        let uu____26217 =
          let uu____26218 =
            let uu____26233 = elim_delayed_subst_term t2  in
            let uu____26236 = elim_delayed_subst_args args  in
            (uu____26233, uu____26236)  in
          FStar_Syntax_Syntax.Tm_app uu____26218  in
        mk1 uu____26217
    | FStar_Syntax_Syntax.Tm_match (t2,branches) ->
        let rec elim_pat p =
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_var x ->
              let uu___208_26304 = p  in
              let uu____26305 =
                let uu____26306 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_var uu____26306  in
              {
                FStar_Syntax_Syntax.v = uu____26305;
                FStar_Syntax_Syntax.p =
                  (uu___208_26304.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_wild x ->
              let uu___209_26308 = p  in
              let uu____26309 =
                let uu____26310 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_wild uu____26310  in
              {
                FStar_Syntax_Syntax.v = uu____26309;
                FStar_Syntax_Syntax.p =
                  (uu___209_26308.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
              let uu___210_26317 = p  in
              let uu____26318 =
                let uu____26319 =
                  let uu____26326 = elim_bv x  in
                  let uu____26327 = elim_delayed_subst_term t0  in
                  (uu____26326, uu____26327)  in
                FStar_Syntax_Syntax.Pat_dot_term uu____26319  in
              {
                FStar_Syntax_Syntax.v = uu____26318;
                FStar_Syntax_Syntax.p =
                  (uu___210_26317.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
              let uu___211_26350 = p  in
              let uu____26351 =
                let uu____26352 =
                  let uu____26365 =
                    FStar_List.map
                      (fun uu____26388  ->
                         match uu____26388 with
                         | (x,b) ->
                             let uu____26401 = elim_pat x  in
                             (uu____26401, b)) pats
                     in
                  (fv, uu____26365)  in
                FStar_Syntax_Syntax.Pat_cons uu____26352  in
              {
                FStar_Syntax_Syntax.v = uu____26351;
                FStar_Syntax_Syntax.p =
                  (uu___211_26350.FStar_Syntax_Syntax.p)
              }
          | uu____26414 -> p  in
        let elim_branch uu____26438 =
          match uu____26438 with
          | (pat,wopt,t3) ->
              let uu____26464 = elim_pat pat  in
              let uu____26467 =
                FStar_Util.map_opt wopt elim_delayed_subst_term  in
              let uu____26470 = elim_delayed_subst_term t3  in
              (uu____26464, uu____26467, uu____26470)
           in
        let uu____26475 =
          let uu____26476 =
            let uu____26499 = elim_delayed_subst_term t2  in
            let uu____26502 = FStar_List.map elim_branch branches  in
            (uu____26499, uu____26502)  in
          FStar_Syntax_Syntax.Tm_match uu____26476  in
        mk1 uu____26475
    | FStar_Syntax_Syntax.Tm_ascribed (t2,a,lopt) ->
        let elim_ascription uu____26633 =
          match uu____26633 with
          | (tc,topt) ->
              let uu____26668 =
                match tc with
                | FStar_Util.Inl t3 ->
                    let uu____26678 = elim_delayed_subst_term t3  in
                    FStar_Util.Inl uu____26678
                | FStar_Util.Inr c ->
                    let uu____26680 = elim_delayed_subst_comp c  in
                    FStar_Util.Inr uu____26680
                 in
              let uu____26681 =
                FStar_Util.map_opt topt elim_delayed_subst_term  in
              (uu____26668, uu____26681)
           in
        let uu____26690 =
          let uu____26691 =
            let uu____26718 = elim_delayed_subst_term t2  in
            let uu____26721 = elim_ascription a  in
            (uu____26718, uu____26721, lopt)  in
          FStar_Syntax_Syntax.Tm_ascribed uu____26691  in
        mk1 uu____26690
    | FStar_Syntax_Syntax.Tm_let (lbs,t2) ->
        let elim_lb lb =
          let uu___212_26782 = lb  in
          let uu____26783 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbtyp  in
          let uu____26786 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbdef  in
          {
            FStar_Syntax_Syntax.lbname =
              (uu___212_26782.FStar_Syntax_Syntax.lbname);
            FStar_Syntax_Syntax.lbunivs =
              (uu___212_26782.FStar_Syntax_Syntax.lbunivs);
            FStar_Syntax_Syntax.lbtyp = uu____26783;
            FStar_Syntax_Syntax.lbeff =
              (uu___212_26782.FStar_Syntax_Syntax.lbeff);
            FStar_Syntax_Syntax.lbdef = uu____26786;
            FStar_Syntax_Syntax.lbattrs =
              (uu___212_26782.FStar_Syntax_Syntax.lbattrs);
            FStar_Syntax_Syntax.lbpos =
              (uu___212_26782.FStar_Syntax_Syntax.lbpos)
          }  in
        let uu____26789 =
          let uu____26790 =
            let uu____26803 =
              let uu____26810 =
                FStar_List.map elim_lb (FStar_Pervasives_Native.snd lbs)  in
              ((FStar_Pervasives_Native.fst lbs), uu____26810)  in
            let uu____26819 = elim_delayed_subst_term t2  in
            (uu____26803, uu____26819)  in
          FStar_Syntax_Syntax.Tm_let uu____26790  in
        mk1 uu____26789
    | FStar_Syntax_Syntax.Tm_uvar u -> mk1 (FStar_Syntax_Syntax.Tm_uvar u)
    | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
        let qi1 =
          FStar_Syntax_Syntax.on_antiquoted elim_delayed_subst_term qi  in
        let uu____26838 =
          let uu____26839 =
            let uu____26846 = elim_delayed_subst_term tm  in
            (uu____26846, qi1)  in
          FStar_Syntax_Syntax.Tm_quoted uu____26839  in
        mk1 uu____26838
    | FStar_Syntax_Syntax.Tm_meta (t2,md) ->
        let uu____26857 =
          let uu____26858 =
            let uu____26865 = elim_delayed_subst_term t2  in
            let uu____26868 = elim_delayed_subst_meta md  in
            (uu____26865, uu____26868)  in
          FStar_Syntax_Syntax.Tm_meta uu____26858  in
        mk1 uu____26857

and (elim_delayed_subst_cflags :
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun flags1  ->
    FStar_List.map
      (fun uu___95_26877  ->
         match uu___95_26877 with
         | FStar_Syntax_Syntax.DECREASES t ->
             let uu____26881 = elim_delayed_subst_term t  in
             FStar_Syntax_Syntax.DECREASES uu____26881
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
        let uu____26904 =
          let uu____26905 =
            let uu____26914 = elim_delayed_subst_term t  in
            (uu____26914, uopt)  in
          FStar_Syntax_Syntax.Total uu____26905  in
        mk1 uu____26904
    | FStar_Syntax_Syntax.GTotal (t,uopt) ->
        let uu____26931 =
          let uu____26932 =
            let uu____26941 = elim_delayed_subst_term t  in
            (uu____26941, uopt)  in
          FStar_Syntax_Syntax.GTotal uu____26932  in
        mk1 uu____26931
    | FStar_Syntax_Syntax.Comp ct ->
        let ct1 =
          let uu___213_26950 = ct  in
          let uu____26951 =
            elim_delayed_subst_term ct.FStar_Syntax_Syntax.result_typ  in
          let uu____26954 =
            elim_delayed_subst_args ct.FStar_Syntax_Syntax.effect_args  in
          let uu____26963 =
            elim_delayed_subst_cflags ct.FStar_Syntax_Syntax.flags  in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___213_26950.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___213_26950.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ = uu____26951;
            FStar_Syntax_Syntax.effect_args = uu____26954;
            FStar_Syntax_Syntax.flags = uu____26963
          }  in
        mk1 (FStar_Syntax_Syntax.Comp ct1)

and (elim_delayed_subst_meta :
  FStar_Syntax_Syntax.metadata -> FStar_Syntax_Syntax.metadata) =
  fun uu___96_26966  ->
    match uu___96_26966 with
    | FStar_Syntax_Syntax.Meta_pattern args ->
        let uu____26978 = FStar_List.map elim_delayed_subst_args args  in
        FStar_Syntax_Syntax.Meta_pattern uu____26978
    | FStar_Syntax_Syntax.Meta_monadic (m,t) ->
        let uu____27011 =
          let uu____27018 = elim_delayed_subst_term t  in (m, uu____27018)
           in
        FStar_Syntax_Syntax.Meta_monadic uu____27011
    | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,t) ->
        let uu____27030 =
          let uu____27039 = elim_delayed_subst_term t  in
          (m1, m2, uu____27039)  in
        FStar_Syntax_Syntax.Meta_monadic_lift uu____27030
    | m -> m

and (elim_delayed_subst_args :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun args  ->
    FStar_List.map
      (fun uu____27066  ->
         match uu____27066 with
         | (t,q) ->
             let uu____27077 = elim_delayed_subst_term t  in (uu____27077, q))
      args

and (elim_delayed_subst_binders :
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun bs  ->
    FStar_List.map
      (fun uu____27097  ->
         match uu____27097 with
         | (x,q) ->
             let uu____27108 =
               let uu___214_27109 = x  in
               let uu____27110 =
                 elim_delayed_subst_term x.FStar_Syntax_Syntax.sort  in
               {
                 FStar_Syntax_Syntax.ppname =
                   (uu___214_27109.FStar_Syntax_Syntax.ppname);
                 FStar_Syntax_Syntax.index =
                   (uu___214_27109.FStar_Syntax_Syntax.index);
                 FStar_Syntax_Syntax.sort = uu____27110
               }  in
             (uu____27108, q)) bs

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
            | (uu____27202,FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c))
                  FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
            | (uu____27228,FStar_Util.Inl t) ->
                let uu____27246 =
                  let uu____27253 =
                    let uu____27254 =
                      let uu____27267 = FStar_Syntax_Syntax.mk_Total t  in
                      (binders, uu____27267)  in
                    FStar_Syntax_Syntax.Tm_arrow uu____27254  in
                  FStar_Syntax_Syntax.mk uu____27253  in
                uu____27246 FStar_Pervasives_Native.None
                  t.FStar_Syntax_Syntax.pos
             in
          let uu____27281 = FStar_Syntax_Subst.open_univ_vars univ_names t
             in
          match uu____27281 with
          | (univ_names1,t1) ->
              let t2 = remove_uvar_solutions env t1  in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2  in
              let t4 = elim_delayed_subst_term t3  in
              let uu____27311 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t4))
                | uu____27374 ->
                    let uu____27375 =
                      let uu____27384 =
                        let uu____27385 = FStar_Syntax_Subst.compress t4  in
                        uu____27385.FStar_Syntax_Syntax.n  in
                      (uu____27384, tc)  in
                    (match uu____27375 with
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inr uu____27412) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inl uu____27453) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____27492,FStar_Util.Inl uu____27493) ->
                         ([], (FStar_Util.Inl t4))
                     | uu____27516 -> failwith "Impossible")
                 in
              (match uu____27311 with
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
          let uu____27641 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl t)  in
          match uu____27641 with
          | (univ_names1,binders1,tc) ->
              let uu____27707 = FStar_Util.left tc  in
              (univ_names1, binders1, uu____27707)
  
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
          let uu____27756 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr c)  in
          match uu____27756 with
          | (univ_names1,binders1,tc) ->
              let uu____27822 = FStar_Util.right tc  in
              (univ_names1, binders1, uu____27822)
  
let rec (elim_uvars :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt)
  =
  fun env  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univ_names,binders,typ,lids,lids') ->
          let uu____27861 = elim_uvars_aux_t env univ_names binders typ  in
          (match uu____27861 with
           | (univ_names1,binders1,typ1) ->
               let uu___215_27895 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___215_27895.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___215_27895.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___215_27895.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___215_27895.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
          let uu___216_27910 = s  in
          let uu____27911 =
            let uu____27912 =
              let uu____27921 = FStar_List.map (elim_uvars env) sigs  in
              (uu____27921, lids)  in
            FStar_Syntax_Syntax.Sig_bundle uu____27912  in
          {
            FStar_Syntax_Syntax.sigel = uu____27911;
            FStar_Syntax_Syntax.sigrng =
              (uu___216_27910.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___216_27910.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___216_27910.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___216_27910.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_datacon (lid,univ_names,typ,lident,i,lids) ->
          let uu____27938 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____27938 with
           | (univ_names1,uu____27958,typ1) ->
               let uu___217_27976 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___217_27976.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___217_27976.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___217_27976.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___217_27976.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univ_names,typ) ->
          let uu____27982 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____27982 with
           | (univ_names1,uu____28002,typ1) ->
               let uu___218_28020 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___218_28020.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___218_28020.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___218_28020.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___218_28020.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____28048 =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs
                       in
                    match uu____28048 with
                    | (opening,lbunivs) ->
                        let elim t =
                          let uu____28073 =
                            let uu____28074 =
                              let uu____28075 =
                                FStar_Syntax_Subst.subst opening t  in
                              remove_uvar_solutions env uu____28075  in
                            FStar_Syntax_Subst.close_univ_vars lbunivs
                              uu____28074
                             in
                          elim_delayed_subst_term uu____28073  in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp  in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef  in
                        let uu___219_28078 = lb  in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___219_28078.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___219_28078.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___219_28078.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___219_28078.FStar_Syntax_Syntax.lbpos)
                        }))
             in
          let uu___220_28079 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids));
            FStar_Syntax_Syntax.sigrng =
              (uu___220_28079.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___220_28079.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___220_28079.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___220_28079.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_main t ->
          let uu___221_28085 = s  in
          let uu____28086 =
            let uu____28087 = remove_uvar_solutions env t  in
            FStar_Syntax_Syntax.Sig_main uu____28087  in
          {
            FStar_Syntax_Syntax.sigel = uu____28086;
            FStar_Syntax_Syntax.sigrng =
              (uu___221_28085.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___221_28085.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___221_28085.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___221_28085.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_assume (l,us,t) ->
          let uu____28091 = elim_uvars_aux_t env us [] t  in
          (match uu____28091 with
           | (us1,uu____28111,t1) ->
               let uu___222_28129 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___222_28129.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___222_28129.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___222_28129.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___222_28129.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____28130 ->
          failwith "Impossible: should have been desugared already"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____28132 =
            elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature
             in
          (match uu____28132 with
           | (univs1,binders,signature) ->
               let uu____28166 =
                 let uu____28175 = FStar_Syntax_Subst.univ_var_opening univs1
                    in
                 match uu____28175 with
                 | (univs_opening,univs2) ->
                     let uu____28202 =
                       FStar_Syntax_Subst.univ_var_closing univs2  in
                     (univs_opening, uu____28202)
                  in
               (match uu____28166 with
                | (univs_opening,univs_closing) ->
                    let uu____28219 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders
                         in
                      let uu____28225 =
                        FStar_Syntax_Subst.opening_of_binders binders1  in
                      let uu____28226 =
                        FStar_Syntax_Subst.closing_of_binders binders1  in
                      (uu____28225, uu____28226)  in
                    (match uu____28219 with
                     | (b_opening,b_closing) ->
                         let n1 = FStar_List.length univs1  in
                         let n_binders = FStar_List.length binders  in
                         let elim_tscheme uu____28250 =
                           match uu____28250 with
                           | (us,t) ->
                               let n_us = FStar_List.length us  in
                               let uu____28268 =
                                 FStar_Syntax_Subst.open_univ_vars us t  in
                               (match uu____28268 with
                                | (us1,t1) ->
                                    let uu____28279 =
                                      let uu____28288 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      let uu____28299 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      (uu____28288, uu____28299)  in
                                    (match uu____28279 with
                                     | (b_opening1,b_closing1) ->
                                         let uu____28328 =
                                           let uu____28337 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us)
                                              in
                                           let uu____28348 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us)
                                              in
                                           (uu____28337, uu____28348)  in
                                         (match uu____28328 with
                                          | (univs_opening1,univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____28378 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1
                                                   in
                                                FStar_Syntax_Subst.subst
                                                  univs_opening1 uu____28378
                                                 in
                                              let uu____28379 =
                                                elim_uvars_aux_t env [] [] t2
                                                 in
                                              (match uu____28379 with
                                               | (uu____28402,uu____28403,t3)
                                                   ->
                                                   let t4 =
                                                     let uu____28422 =
                                                       let uu____28423 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3
                                                          in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
                                                         uu____28423
                                                        in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____28422
                                                      in
                                                   (us1, t4)))))
                            in
                         let elim_term t =
                           let uu____28432 =
                             elim_uvars_aux_t env univs1 binders t  in
                           match uu____28432 with
                           | (uu____28449,uu____28450,t1) -> t1  in
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
                             | uu____28524 ->
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_abs
                                      ((a.FStar_Syntax_Syntax.action_params),
                                        body, FStar_Pervasives_Native.None))
                                   FStar_Pervasives_Native.None
                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                              in
                           let destruct_action_body body =
                             let uu____28549 =
                               let uu____28550 =
                                 FStar_Syntax_Subst.compress body  in
                               uu____28550.FStar_Syntax_Syntax.n  in
                             match uu____28549 with
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,(FStar_Util.Inl
                                        typ,FStar_Pervasives_Native.None ),FStar_Pervasives_Native.None
                                  )
                                 -> (defn, typ)
                             | uu____28609 -> failwith "Impossible"  in
                           let destruct_action_typ_templ t =
                             let uu____28640 =
                               let uu____28641 =
                                 FStar_Syntax_Subst.compress t  in
                               uu____28641.FStar_Syntax_Syntax.n  in
                             match uu____28640 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (pars,body,uu____28662) ->
                                 let uu____28683 = destruct_action_body body
                                    in
                                 (match uu____28683 with
                                  | (defn,typ) -> (pars, defn, typ))
                             | uu____28728 ->
                                 let uu____28729 = destruct_action_body t  in
                                 (match uu____28729 with
                                  | (defn,typ) -> ([], defn, typ))
                              in
                           let uu____28778 =
                             elim_tscheme
                               ((a.FStar_Syntax_Syntax.action_univs),
                                 action_typ_templ)
                              in
                           match uu____28778 with
                           | (action_univs,t) ->
                               let uu____28787 = destruct_action_typ_templ t
                                  in
                               (match uu____28787 with
                                | (action_params,action_defn,action_typ) ->
                                    let a' =
                                      let uu___223_28828 = a  in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___223_28828.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___223_28828.FStar_Syntax_Syntax.action_unqualified_name);
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
                           let uu___224_28830 = ed  in
                           let uu____28831 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ret_wp  in
                           let uu____28832 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_wp  in
                           let uu____28833 =
                             elim_tscheme ed.FStar_Syntax_Syntax.if_then_else
                              in
                           let uu____28834 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ite_wp  in
                           let uu____28835 =
                             elim_tscheme ed.FStar_Syntax_Syntax.stronger  in
                           let uu____28836 =
                             elim_tscheme ed.FStar_Syntax_Syntax.close_wp  in
                           let uu____28837 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assert_p  in
                           let uu____28838 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assume_p  in
                           let uu____28839 =
                             elim_tscheme ed.FStar_Syntax_Syntax.null_wp  in
                           let uu____28840 =
                             elim_tscheme ed.FStar_Syntax_Syntax.trivial  in
                           let uu____28841 =
                             elim_term ed.FStar_Syntax_Syntax.repr  in
                           let uu____28842 =
                             elim_tscheme ed.FStar_Syntax_Syntax.return_repr
                              in
                           let uu____28843 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_repr
                              in
                           let uu____28844 =
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions
                              in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___224_28830.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___224_28830.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs = univs1;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp = uu____28831;
                             FStar_Syntax_Syntax.bind_wp = uu____28832;
                             FStar_Syntax_Syntax.if_then_else = uu____28833;
                             FStar_Syntax_Syntax.ite_wp = uu____28834;
                             FStar_Syntax_Syntax.stronger = uu____28835;
                             FStar_Syntax_Syntax.close_wp = uu____28836;
                             FStar_Syntax_Syntax.assert_p = uu____28837;
                             FStar_Syntax_Syntax.assume_p = uu____28838;
                             FStar_Syntax_Syntax.null_wp = uu____28839;
                             FStar_Syntax_Syntax.trivial = uu____28840;
                             FStar_Syntax_Syntax.repr = uu____28841;
                             FStar_Syntax_Syntax.return_repr = uu____28842;
                             FStar_Syntax_Syntax.bind_repr = uu____28843;
                             FStar_Syntax_Syntax.actions = uu____28844;
                             FStar_Syntax_Syntax.eff_attrs =
                               (uu___224_28830.FStar_Syntax_Syntax.eff_attrs)
                           }  in
                         let uu___225_28847 = s  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___225_28847.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___225_28847.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___225_28847.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___225_28847.FStar_Syntax_Syntax.sigattrs)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___97_28868 =
            match uu___97_28868 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (us,t) ->
                let uu____28899 = elim_uvars_aux_t env us [] t  in
                (match uu____28899 with
                 | (us1,uu____28927,t1) ->
                     FStar_Pervasives_Native.Some (us1, t1))
             in
          let sub_eff1 =
            let uu___226_28954 = sub_eff  in
            let uu____28955 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp  in
            let uu____28958 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift  in
            {
              FStar_Syntax_Syntax.source =
                (uu___226_28954.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___226_28954.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____28955;
              FStar_Syntax_Syntax.lift = uu____28958
            }  in
          let uu___227_28961 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___227_28961.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___227_28961.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___227_28961.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___227_28961.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,univ_names,binders,comp,flags1) ->
          let uu____28971 = elim_uvars_aux_c env univ_names binders comp  in
          (match uu____28971 with
           | (univ_names1,binders1,comp1) ->
               let uu___228_29005 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___228_29005.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___228_29005.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___228_29005.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___228_29005.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____29008 -> s
      | FStar_Syntax_Syntax.Sig_splice uu____29009 -> s
  
let (erase_universes :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  -> normalize [EraseUniverses; AllowUnboundUniverses] env t
  