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
      fun uu___106_269  ->
        match uu___106_269 with
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
      let add_opt x uu___107_1503 =
        match uu___107_1503 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.Some [x]
        | FStar_Pervasives_Native.Some xs ->
            FStar_Pervasives_Native.Some (x :: xs)
         in
      match s with
      | Beta  ->
          let uu___126_1523 = fs  in
          {
            beta = true;
            iota = (uu___126_1523.iota);
            zeta = (uu___126_1523.zeta);
            weak = (uu___126_1523.weak);
            hnf = (uu___126_1523.hnf);
            primops = (uu___126_1523.primops);
            do_not_unfold_pure_lets = (uu___126_1523.do_not_unfold_pure_lets);
            unfold_until = (uu___126_1523.unfold_until);
            unfold_only = (uu___126_1523.unfold_only);
            unfold_fully = (uu___126_1523.unfold_fully);
            unfold_attr = (uu___126_1523.unfold_attr);
            unfold_tac = (uu___126_1523.unfold_tac);
            pure_subterms_within_computations =
              (uu___126_1523.pure_subterms_within_computations);
            simplify = (uu___126_1523.simplify);
            erase_universes = (uu___126_1523.erase_universes);
            allow_unbound_universes = (uu___126_1523.allow_unbound_universes);
            reify_ = (uu___126_1523.reify_);
            compress_uvars = (uu___126_1523.compress_uvars);
            no_full_norm = (uu___126_1523.no_full_norm);
            check_no_uvars = (uu___126_1523.check_no_uvars);
            unmeta = (uu___126_1523.unmeta);
            unascribe = (uu___126_1523.unascribe);
            in_full_norm_request = (uu___126_1523.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___126_1523.weakly_reduce_scrutinee)
          }
      | Iota  ->
          let uu___127_1524 = fs  in
          {
            beta = (uu___127_1524.beta);
            iota = true;
            zeta = (uu___127_1524.zeta);
            weak = (uu___127_1524.weak);
            hnf = (uu___127_1524.hnf);
            primops = (uu___127_1524.primops);
            do_not_unfold_pure_lets = (uu___127_1524.do_not_unfold_pure_lets);
            unfold_until = (uu___127_1524.unfold_until);
            unfold_only = (uu___127_1524.unfold_only);
            unfold_fully = (uu___127_1524.unfold_fully);
            unfold_attr = (uu___127_1524.unfold_attr);
            unfold_tac = (uu___127_1524.unfold_tac);
            pure_subterms_within_computations =
              (uu___127_1524.pure_subterms_within_computations);
            simplify = (uu___127_1524.simplify);
            erase_universes = (uu___127_1524.erase_universes);
            allow_unbound_universes = (uu___127_1524.allow_unbound_universes);
            reify_ = (uu___127_1524.reify_);
            compress_uvars = (uu___127_1524.compress_uvars);
            no_full_norm = (uu___127_1524.no_full_norm);
            check_no_uvars = (uu___127_1524.check_no_uvars);
            unmeta = (uu___127_1524.unmeta);
            unascribe = (uu___127_1524.unascribe);
            in_full_norm_request = (uu___127_1524.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___127_1524.weakly_reduce_scrutinee)
          }
      | Zeta  ->
          let uu___128_1525 = fs  in
          {
            beta = (uu___128_1525.beta);
            iota = (uu___128_1525.iota);
            zeta = true;
            weak = (uu___128_1525.weak);
            hnf = (uu___128_1525.hnf);
            primops = (uu___128_1525.primops);
            do_not_unfold_pure_lets = (uu___128_1525.do_not_unfold_pure_lets);
            unfold_until = (uu___128_1525.unfold_until);
            unfold_only = (uu___128_1525.unfold_only);
            unfold_fully = (uu___128_1525.unfold_fully);
            unfold_attr = (uu___128_1525.unfold_attr);
            unfold_tac = (uu___128_1525.unfold_tac);
            pure_subterms_within_computations =
              (uu___128_1525.pure_subterms_within_computations);
            simplify = (uu___128_1525.simplify);
            erase_universes = (uu___128_1525.erase_universes);
            allow_unbound_universes = (uu___128_1525.allow_unbound_universes);
            reify_ = (uu___128_1525.reify_);
            compress_uvars = (uu___128_1525.compress_uvars);
            no_full_norm = (uu___128_1525.no_full_norm);
            check_no_uvars = (uu___128_1525.check_no_uvars);
            unmeta = (uu___128_1525.unmeta);
            unascribe = (uu___128_1525.unascribe);
            in_full_norm_request = (uu___128_1525.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___128_1525.weakly_reduce_scrutinee)
          }
      | Exclude (Beta ) ->
          let uu___129_1526 = fs  in
          {
            beta = false;
            iota = (uu___129_1526.iota);
            zeta = (uu___129_1526.zeta);
            weak = (uu___129_1526.weak);
            hnf = (uu___129_1526.hnf);
            primops = (uu___129_1526.primops);
            do_not_unfold_pure_lets = (uu___129_1526.do_not_unfold_pure_lets);
            unfold_until = (uu___129_1526.unfold_until);
            unfold_only = (uu___129_1526.unfold_only);
            unfold_fully = (uu___129_1526.unfold_fully);
            unfold_attr = (uu___129_1526.unfold_attr);
            unfold_tac = (uu___129_1526.unfold_tac);
            pure_subterms_within_computations =
              (uu___129_1526.pure_subterms_within_computations);
            simplify = (uu___129_1526.simplify);
            erase_universes = (uu___129_1526.erase_universes);
            allow_unbound_universes = (uu___129_1526.allow_unbound_universes);
            reify_ = (uu___129_1526.reify_);
            compress_uvars = (uu___129_1526.compress_uvars);
            no_full_norm = (uu___129_1526.no_full_norm);
            check_no_uvars = (uu___129_1526.check_no_uvars);
            unmeta = (uu___129_1526.unmeta);
            unascribe = (uu___129_1526.unascribe);
            in_full_norm_request = (uu___129_1526.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___129_1526.weakly_reduce_scrutinee)
          }
      | Exclude (Iota ) ->
          let uu___130_1527 = fs  in
          {
            beta = (uu___130_1527.beta);
            iota = false;
            zeta = (uu___130_1527.zeta);
            weak = (uu___130_1527.weak);
            hnf = (uu___130_1527.hnf);
            primops = (uu___130_1527.primops);
            do_not_unfold_pure_lets = (uu___130_1527.do_not_unfold_pure_lets);
            unfold_until = (uu___130_1527.unfold_until);
            unfold_only = (uu___130_1527.unfold_only);
            unfold_fully = (uu___130_1527.unfold_fully);
            unfold_attr = (uu___130_1527.unfold_attr);
            unfold_tac = (uu___130_1527.unfold_tac);
            pure_subterms_within_computations =
              (uu___130_1527.pure_subterms_within_computations);
            simplify = (uu___130_1527.simplify);
            erase_universes = (uu___130_1527.erase_universes);
            allow_unbound_universes = (uu___130_1527.allow_unbound_universes);
            reify_ = (uu___130_1527.reify_);
            compress_uvars = (uu___130_1527.compress_uvars);
            no_full_norm = (uu___130_1527.no_full_norm);
            check_no_uvars = (uu___130_1527.check_no_uvars);
            unmeta = (uu___130_1527.unmeta);
            unascribe = (uu___130_1527.unascribe);
            in_full_norm_request = (uu___130_1527.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___130_1527.weakly_reduce_scrutinee)
          }
      | Exclude (Zeta ) ->
          let uu___131_1528 = fs  in
          {
            beta = (uu___131_1528.beta);
            iota = (uu___131_1528.iota);
            zeta = false;
            weak = (uu___131_1528.weak);
            hnf = (uu___131_1528.hnf);
            primops = (uu___131_1528.primops);
            do_not_unfold_pure_lets = (uu___131_1528.do_not_unfold_pure_lets);
            unfold_until = (uu___131_1528.unfold_until);
            unfold_only = (uu___131_1528.unfold_only);
            unfold_fully = (uu___131_1528.unfold_fully);
            unfold_attr = (uu___131_1528.unfold_attr);
            unfold_tac = (uu___131_1528.unfold_tac);
            pure_subterms_within_computations =
              (uu___131_1528.pure_subterms_within_computations);
            simplify = (uu___131_1528.simplify);
            erase_universes = (uu___131_1528.erase_universes);
            allow_unbound_universes = (uu___131_1528.allow_unbound_universes);
            reify_ = (uu___131_1528.reify_);
            compress_uvars = (uu___131_1528.compress_uvars);
            no_full_norm = (uu___131_1528.no_full_norm);
            check_no_uvars = (uu___131_1528.check_no_uvars);
            unmeta = (uu___131_1528.unmeta);
            unascribe = (uu___131_1528.unascribe);
            in_full_norm_request = (uu___131_1528.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___131_1528.weakly_reduce_scrutinee)
          }
      | Exclude uu____1529 -> failwith "Bad exclude"
      | Weak  ->
          let uu___132_1530 = fs  in
          {
            beta = (uu___132_1530.beta);
            iota = (uu___132_1530.iota);
            zeta = (uu___132_1530.zeta);
            weak = true;
            hnf = (uu___132_1530.hnf);
            primops = (uu___132_1530.primops);
            do_not_unfold_pure_lets = (uu___132_1530.do_not_unfold_pure_lets);
            unfold_until = (uu___132_1530.unfold_until);
            unfold_only = (uu___132_1530.unfold_only);
            unfold_fully = (uu___132_1530.unfold_fully);
            unfold_attr = (uu___132_1530.unfold_attr);
            unfold_tac = (uu___132_1530.unfold_tac);
            pure_subterms_within_computations =
              (uu___132_1530.pure_subterms_within_computations);
            simplify = (uu___132_1530.simplify);
            erase_universes = (uu___132_1530.erase_universes);
            allow_unbound_universes = (uu___132_1530.allow_unbound_universes);
            reify_ = (uu___132_1530.reify_);
            compress_uvars = (uu___132_1530.compress_uvars);
            no_full_norm = (uu___132_1530.no_full_norm);
            check_no_uvars = (uu___132_1530.check_no_uvars);
            unmeta = (uu___132_1530.unmeta);
            unascribe = (uu___132_1530.unascribe);
            in_full_norm_request = (uu___132_1530.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___132_1530.weakly_reduce_scrutinee)
          }
      | HNF  ->
          let uu___133_1531 = fs  in
          {
            beta = (uu___133_1531.beta);
            iota = (uu___133_1531.iota);
            zeta = (uu___133_1531.zeta);
            weak = (uu___133_1531.weak);
            hnf = true;
            primops = (uu___133_1531.primops);
            do_not_unfold_pure_lets = (uu___133_1531.do_not_unfold_pure_lets);
            unfold_until = (uu___133_1531.unfold_until);
            unfold_only = (uu___133_1531.unfold_only);
            unfold_fully = (uu___133_1531.unfold_fully);
            unfold_attr = (uu___133_1531.unfold_attr);
            unfold_tac = (uu___133_1531.unfold_tac);
            pure_subterms_within_computations =
              (uu___133_1531.pure_subterms_within_computations);
            simplify = (uu___133_1531.simplify);
            erase_universes = (uu___133_1531.erase_universes);
            allow_unbound_universes = (uu___133_1531.allow_unbound_universes);
            reify_ = (uu___133_1531.reify_);
            compress_uvars = (uu___133_1531.compress_uvars);
            no_full_norm = (uu___133_1531.no_full_norm);
            check_no_uvars = (uu___133_1531.check_no_uvars);
            unmeta = (uu___133_1531.unmeta);
            unascribe = (uu___133_1531.unascribe);
            in_full_norm_request = (uu___133_1531.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___133_1531.weakly_reduce_scrutinee)
          }
      | Primops  ->
          let uu___134_1532 = fs  in
          {
            beta = (uu___134_1532.beta);
            iota = (uu___134_1532.iota);
            zeta = (uu___134_1532.zeta);
            weak = (uu___134_1532.weak);
            hnf = (uu___134_1532.hnf);
            primops = true;
            do_not_unfold_pure_lets = (uu___134_1532.do_not_unfold_pure_lets);
            unfold_until = (uu___134_1532.unfold_until);
            unfold_only = (uu___134_1532.unfold_only);
            unfold_fully = (uu___134_1532.unfold_fully);
            unfold_attr = (uu___134_1532.unfold_attr);
            unfold_tac = (uu___134_1532.unfold_tac);
            pure_subterms_within_computations =
              (uu___134_1532.pure_subterms_within_computations);
            simplify = (uu___134_1532.simplify);
            erase_universes = (uu___134_1532.erase_universes);
            allow_unbound_universes = (uu___134_1532.allow_unbound_universes);
            reify_ = (uu___134_1532.reify_);
            compress_uvars = (uu___134_1532.compress_uvars);
            no_full_norm = (uu___134_1532.no_full_norm);
            check_no_uvars = (uu___134_1532.check_no_uvars);
            unmeta = (uu___134_1532.unmeta);
            unascribe = (uu___134_1532.unascribe);
            in_full_norm_request = (uu___134_1532.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___134_1532.weakly_reduce_scrutinee)
          }
      | Eager_unfolding  -> fs
      | Inlining  -> fs
      | DoNotUnfoldPureLets  ->
          let uu___135_1533 = fs  in
          {
            beta = (uu___135_1533.beta);
            iota = (uu___135_1533.iota);
            zeta = (uu___135_1533.zeta);
            weak = (uu___135_1533.weak);
            hnf = (uu___135_1533.hnf);
            primops = (uu___135_1533.primops);
            do_not_unfold_pure_lets = true;
            unfold_until = (uu___135_1533.unfold_until);
            unfold_only = (uu___135_1533.unfold_only);
            unfold_fully = (uu___135_1533.unfold_fully);
            unfold_attr = (uu___135_1533.unfold_attr);
            unfold_tac = (uu___135_1533.unfold_tac);
            pure_subterms_within_computations =
              (uu___135_1533.pure_subterms_within_computations);
            simplify = (uu___135_1533.simplify);
            erase_universes = (uu___135_1533.erase_universes);
            allow_unbound_universes = (uu___135_1533.allow_unbound_universes);
            reify_ = (uu___135_1533.reify_);
            compress_uvars = (uu___135_1533.compress_uvars);
            no_full_norm = (uu___135_1533.no_full_norm);
            check_no_uvars = (uu___135_1533.check_no_uvars);
            unmeta = (uu___135_1533.unmeta);
            unascribe = (uu___135_1533.unascribe);
            in_full_norm_request = (uu___135_1533.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___135_1533.weakly_reduce_scrutinee)
          }
      | UnfoldUntil d ->
          let uu___136_1535 = fs  in
          {
            beta = (uu___136_1535.beta);
            iota = (uu___136_1535.iota);
            zeta = (uu___136_1535.zeta);
            weak = (uu___136_1535.weak);
            hnf = (uu___136_1535.hnf);
            primops = (uu___136_1535.primops);
            do_not_unfold_pure_lets = (uu___136_1535.do_not_unfold_pure_lets);
            unfold_until = (FStar_Pervasives_Native.Some d);
            unfold_only = (uu___136_1535.unfold_only);
            unfold_fully = (uu___136_1535.unfold_fully);
            unfold_attr = (uu___136_1535.unfold_attr);
            unfold_tac = (uu___136_1535.unfold_tac);
            pure_subterms_within_computations =
              (uu___136_1535.pure_subterms_within_computations);
            simplify = (uu___136_1535.simplify);
            erase_universes = (uu___136_1535.erase_universes);
            allow_unbound_universes = (uu___136_1535.allow_unbound_universes);
            reify_ = (uu___136_1535.reify_);
            compress_uvars = (uu___136_1535.compress_uvars);
            no_full_norm = (uu___136_1535.no_full_norm);
            check_no_uvars = (uu___136_1535.check_no_uvars);
            unmeta = (uu___136_1535.unmeta);
            unascribe = (uu___136_1535.unascribe);
            in_full_norm_request = (uu___136_1535.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___136_1535.weakly_reduce_scrutinee)
          }
      | UnfoldOnly lids ->
          let uu___137_1539 = fs  in
          {
            beta = (uu___137_1539.beta);
            iota = (uu___137_1539.iota);
            zeta = (uu___137_1539.zeta);
            weak = (uu___137_1539.weak);
            hnf = (uu___137_1539.hnf);
            primops = (uu___137_1539.primops);
            do_not_unfold_pure_lets = (uu___137_1539.do_not_unfold_pure_lets);
            unfold_until = (uu___137_1539.unfold_until);
            unfold_only = (FStar_Pervasives_Native.Some lids);
            unfold_fully = (uu___137_1539.unfold_fully);
            unfold_attr = (uu___137_1539.unfold_attr);
            unfold_tac = (uu___137_1539.unfold_tac);
            pure_subterms_within_computations =
              (uu___137_1539.pure_subterms_within_computations);
            simplify = (uu___137_1539.simplify);
            erase_universes = (uu___137_1539.erase_universes);
            allow_unbound_universes = (uu___137_1539.allow_unbound_universes);
            reify_ = (uu___137_1539.reify_);
            compress_uvars = (uu___137_1539.compress_uvars);
            no_full_norm = (uu___137_1539.no_full_norm);
            check_no_uvars = (uu___137_1539.check_no_uvars);
            unmeta = (uu___137_1539.unmeta);
            unascribe = (uu___137_1539.unascribe);
            in_full_norm_request = (uu___137_1539.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___137_1539.weakly_reduce_scrutinee)
          }
      | UnfoldFully lids ->
          let uu___138_1545 = fs  in
          {
            beta = (uu___138_1545.beta);
            iota = (uu___138_1545.iota);
            zeta = (uu___138_1545.zeta);
            weak = (uu___138_1545.weak);
            hnf = (uu___138_1545.hnf);
            primops = (uu___138_1545.primops);
            do_not_unfold_pure_lets = (uu___138_1545.do_not_unfold_pure_lets);
            unfold_until = (uu___138_1545.unfold_until);
            unfold_only = (uu___138_1545.unfold_only);
            unfold_fully = (FStar_Pervasives_Native.Some lids);
            unfold_attr = (uu___138_1545.unfold_attr);
            unfold_tac = (uu___138_1545.unfold_tac);
            pure_subterms_within_computations =
              (uu___138_1545.pure_subterms_within_computations);
            simplify = (uu___138_1545.simplify);
            erase_universes = (uu___138_1545.erase_universes);
            allow_unbound_universes = (uu___138_1545.allow_unbound_universes);
            reify_ = (uu___138_1545.reify_);
            compress_uvars = (uu___138_1545.compress_uvars);
            no_full_norm = (uu___138_1545.no_full_norm);
            check_no_uvars = (uu___138_1545.check_no_uvars);
            unmeta = (uu___138_1545.unmeta);
            unascribe = (uu___138_1545.unascribe);
            in_full_norm_request = (uu___138_1545.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___138_1545.weakly_reduce_scrutinee)
          }
      | UnfoldAttr attr ->
          let uu___139_1549 = fs  in
          {
            beta = (uu___139_1549.beta);
            iota = (uu___139_1549.iota);
            zeta = (uu___139_1549.zeta);
            weak = (uu___139_1549.weak);
            hnf = (uu___139_1549.hnf);
            primops = (uu___139_1549.primops);
            do_not_unfold_pure_lets = (uu___139_1549.do_not_unfold_pure_lets);
            unfold_until = (uu___139_1549.unfold_until);
            unfold_only = (uu___139_1549.unfold_only);
            unfold_fully = (uu___139_1549.unfold_fully);
            unfold_attr = (add_opt attr fs.unfold_attr);
            unfold_tac = (uu___139_1549.unfold_tac);
            pure_subterms_within_computations =
              (uu___139_1549.pure_subterms_within_computations);
            simplify = (uu___139_1549.simplify);
            erase_universes = (uu___139_1549.erase_universes);
            allow_unbound_universes = (uu___139_1549.allow_unbound_universes);
            reify_ = (uu___139_1549.reify_);
            compress_uvars = (uu___139_1549.compress_uvars);
            no_full_norm = (uu___139_1549.no_full_norm);
            check_no_uvars = (uu___139_1549.check_no_uvars);
            unmeta = (uu___139_1549.unmeta);
            unascribe = (uu___139_1549.unascribe);
            in_full_norm_request = (uu___139_1549.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___139_1549.weakly_reduce_scrutinee)
          }
      | UnfoldTac  ->
          let uu___140_1550 = fs  in
          {
            beta = (uu___140_1550.beta);
            iota = (uu___140_1550.iota);
            zeta = (uu___140_1550.zeta);
            weak = (uu___140_1550.weak);
            hnf = (uu___140_1550.hnf);
            primops = (uu___140_1550.primops);
            do_not_unfold_pure_lets = (uu___140_1550.do_not_unfold_pure_lets);
            unfold_until = (uu___140_1550.unfold_until);
            unfold_only = (uu___140_1550.unfold_only);
            unfold_fully = (uu___140_1550.unfold_fully);
            unfold_attr = (uu___140_1550.unfold_attr);
            unfold_tac = true;
            pure_subterms_within_computations =
              (uu___140_1550.pure_subterms_within_computations);
            simplify = (uu___140_1550.simplify);
            erase_universes = (uu___140_1550.erase_universes);
            allow_unbound_universes = (uu___140_1550.allow_unbound_universes);
            reify_ = (uu___140_1550.reify_);
            compress_uvars = (uu___140_1550.compress_uvars);
            no_full_norm = (uu___140_1550.no_full_norm);
            check_no_uvars = (uu___140_1550.check_no_uvars);
            unmeta = (uu___140_1550.unmeta);
            unascribe = (uu___140_1550.unascribe);
            in_full_norm_request = (uu___140_1550.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___140_1550.weakly_reduce_scrutinee)
          }
      | PureSubtermsWithinComputations  ->
          let uu___141_1551 = fs  in
          {
            beta = (uu___141_1551.beta);
            iota = (uu___141_1551.iota);
            zeta = (uu___141_1551.zeta);
            weak = (uu___141_1551.weak);
            hnf = (uu___141_1551.hnf);
            primops = (uu___141_1551.primops);
            do_not_unfold_pure_lets = (uu___141_1551.do_not_unfold_pure_lets);
            unfold_until = (uu___141_1551.unfold_until);
            unfold_only = (uu___141_1551.unfold_only);
            unfold_fully = (uu___141_1551.unfold_fully);
            unfold_attr = (uu___141_1551.unfold_attr);
            unfold_tac = (uu___141_1551.unfold_tac);
            pure_subterms_within_computations = true;
            simplify = (uu___141_1551.simplify);
            erase_universes = (uu___141_1551.erase_universes);
            allow_unbound_universes = (uu___141_1551.allow_unbound_universes);
            reify_ = (uu___141_1551.reify_);
            compress_uvars = (uu___141_1551.compress_uvars);
            no_full_norm = (uu___141_1551.no_full_norm);
            check_no_uvars = (uu___141_1551.check_no_uvars);
            unmeta = (uu___141_1551.unmeta);
            unascribe = (uu___141_1551.unascribe);
            in_full_norm_request = (uu___141_1551.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___141_1551.weakly_reduce_scrutinee)
          }
      | Simplify  ->
          let uu___142_1552 = fs  in
          {
            beta = (uu___142_1552.beta);
            iota = (uu___142_1552.iota);
            zeta = (uu___142_1552.zeta);
            weak = (uu___142_1552.weak);
            hnf = (uu___142_1552.hnf);
            primops = (uu___142_1552.primops);
            do_not_unfold_pure_lets = (uu___142_1552.do_not_unfold_pure_lets);
            unfold_until = (uu___142_1552.unfold_until);
            unfold_only = (uu___142_1552.unfold_only);
            unfold_fully = (uu___142_1552.unfold_fully);
            unfold_attr = (uu___142_1552.unfold_attr);
            unfold_tac = (uu___142_1552.unfold_tac);
            pure_subterms_within_computations =
              (uu___142_1552.pure_subterms_within_computations);
            simplify = true;
            erase_universes = (uu___142_1552.erase_universes);
            allow_unbound_universes = (uu___142_1552.allow_unbound_universes);
            reify_ = (uu___142_1552.reify_);
            compress_uvars = (uu___142_1552.compress_uvars);
            no_full_norm = (uu___142_1552.no_full_norm);
            check_no_uvars = (uu___142_1552.check_no_uvars);
            unmeta = (uu___142_1552.unmeta);
            unascribe = (uu___142_1552.unascribe);
            in_full_norm_request = (uu___142_1552.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___142_1552.weakly_reduce_scrutinee)
          }
      | EraseUniverses  ->
          let uu___143_1553 = fs  in
          {
            beta = (uu___143_1553.beta);
            iota = (uu___143_1553.iota);
            zeta = (uu___143_1553.zeta);
            weak = (uu___143_1553.weak);
            hnf = (uu___143_1553.hnf);
            primops = (uu___143_1553.primops);
            do_not_unfold_pure_lets = (uu___143_1553.do_not_unfold_pure_lets);
            unfold_until = (uu___143_1553.unfold_until);
            unfold_only = (uu___143_1553.unfold_only);
            unfold_fully = (uu___143_1553.unfold_fully);
            unfold_attr = (uu___143_1553.unfold_attr);
            unfold_tac = (uu___143_1553.unfold_tac);
            pure_subterms_within_computations =
              (uu___143_1553.pure_subterms_within_computations);
            simplify = (uu___143_1553.simplify);
            erase_universes = true;
            allow_unbound_universes = (uu___143_1553.allow_unbound_universes);
            reify_ = (uu___143_1553.reify_);
            compress_uvars = (uu___143_1553.compress_uvars);
            no_full_norm = (uu___143_1553.no_full_norm);
            check_no_uvars = (uu___143_1553.check_no_uvars);
            unmeta = (uu___143_1553.unmeta);
            unascribe = (uu___143_1553.unascribe);
            in_full_norm_request = (uu___143_1553.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___143_1553.weakly_reduce_scrutinee)
          }
      | AllowUnboundUniverses  ->
          let uu___144_1554 = fs  in
          {
            beta = (uu___144_1554.beta);
            iota = (uu___144_1554.iota);
            zeta = (uu___144_1554.zeta);
            weak = (uu___144_1554.weak);
            hnf = (uu___144_1554.hnf);
            primops = (uu___144_1554.primops);
            do_not_unfold_pure_lets = (uu___144_1554.do_not_unfold_pure_lets);
            unfold_until = (uu___144_1554.unfold_until);
            unfold_only = (uu___144_1554.unfold_only);
            unfold_fully = (uu___144_1554.unfold_fully);
            unfold_attr = (uu___144_1554.unfold_attr);
            unfold_tac = (uu___144_1554.unfold_tac);
            pure_subterms_within_computations =
              (uu___144_1554.pure_subterms_within_computations);
            simplify = (uu___144_1554.simplify);
            erase_universes = (uu___144_1554.erase_universes);
            allow_unbound_universes = true;
            reify_ = (uu___144_1554.reify_);
            compress_uvars = (uu___144_1554.compress_uvars);
            no_full_norm = (uu___144_1554.no_full_norm);
            check_no_uvars = (uu___144_1554.check_no_uvars);
            unmeta = (uu___144_1554.unmeta);
            unascribe = (uu___144_1554.unascribe);
            in_full_norm_request = (uu___144_1554.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___144_1554.weakly_reduce_scrutinee)
          }
      | Reify  ->
          let uu___145_1555 = fs  in
          {
            beta = (uu___145_1555.beta);
            iota = (uu___145_1555.iota);
            zeta = (uu___145_1555.zeta);
            weak = (uu___145_1555.weak);
            hnf = (uu___145_1555.hnf);
            primops = (uu___145_1555.primops);
            do_not_unfold_pure_lets = (uu___145_1555.do_not_unfold_pure_lets);
            unfold_until = (uu___145_1555.unfold_until);
            unfold_only = (uu___145_1555.unfold_only);
            unfold_fully = (uu___145_1555.unfold_fully);
            unfold_attr = (uu___145_1555.unfold_attr);
            unfold_tac = (uu___145_1555.unfold_tac);
            pure_subterms_within_computations =
              (uu___145_1555.pure_subterms_within_computations);
            simplify = (uu___145_1555.simplify);
            erase_universes = (uu___145_1555.erase_universes);
            allow_unbound_universes = (uu___145_1555.allow_unbound_universes);
            reify_ = true;
            compress_uvars = (uu___145_1555.compress_uvars);
            no_full_norm = (uu___145_1555.no_full_norm);
            check_no_uvars = (uu___145_1555.check_no_uvars);
            unmeta = (uu___145_1555.unmeta);
            unascribe = (uu___145_1555.unascribe);
            in_full_norm_request = (uu___145_1555.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___145_1555.weakly_reduce_scrutinee)
          }
      | CompressUvars  ->
          let uu___146_1556 = fs  in
          {
            beta = (uu___146_1556.beta);
            iota = (uu___146_1556.iota);
            zeta = (uu___146_1556.zeta);
            weak = (uu___146_1556.weak);
            hnf = (uu___146_1556.hnf);
            primops = (uu___146_1556.primops);
            do_not_unfold_pure_lets = (uu___146_1556.do_not_unfold_pure_lets);
            unfold_until = (uu___146_1556.unfold_until);
            unfold_only = (uu___146_1556.unfold_only);
            unfold_fully = (uu___146_1556.unfold_fully);
            unfold_attr = (uu___146_1556.unfold_attr);
            unfold_tac = (uu___146_1556.unfold_tac);
            pure_subterms_within_computations =
              (uu___146_1556.pure_subterms_within_computations);
            simplify = (uu___146_1556.simplify);
            erase_universes = (uu___146_1556.erase_universes);
            allow_unbound_universes = (uu___146_1556.allow_unbound_universes);
            reify_ = (uu___146_1556.reify_);
            compress_uvars = true;
            no_full_norm = (uu___146_1556.no_full_norm);
            check_no_uvars = (uu___146_1556.check_no_uvars);
            unmeta = (uu___146_1556.unmeta);
            unascribe = (uu___146_1556.unascribe);
            in_full_norm_request = (uu___146_1556.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___146_1556.weakly_reduce_scrutinee)
          }
      | NoFullNorm  ->
          let uu___147_1557 = fs  in
          {
            beta = (uu___147_1557.beta);
            iota = (uu___147_1557.iota);
            zeta = (uu___147_1557.zeta);
            weak = (uu___147_1557.weak);
            hnf = (uu___147_1557.hnf);
            primops = (uu___147_1557.primops);
            do_not_unfold_pure_lets = (uu___147_1557.do_not_unfold_pure_lets);
            unfold_until = (uu___147_1557.unfold_until);
            unfold_only = (uu___147_1557.unfold_only);
            unfold_fully = (uu___147_1557.unfold_fully);
            unfold_attr = (uu___147_1557.unfold_attr);
            unfold_tac = (uu___147_1557.unfold_tac);
            pure_subterms_within_computations =
              (uu___147_1557.pure_subterms_within_computations);
            simplify = (uu___147_1557.simplify);
            erase_universes = (uu___147_1557.erase_universes);
            allow_unbound_universes = (uu___147_1557.allow_unbound_universes);
            reify_ = (uu___147_1557.reify_);
            compress_uvars = (uu___147_1557.compress_uvars);
            no_full_norm = true;
            check_no_uvars = (uu___147_1557.check_no_uvars);
            unmeta = (uu___147_1557.unmeta);
            unascribe = (uu___147_1557.unascribe);
            in_full_norm_request = (uu___147_1557.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___147_1557.weakly_reduce_scrutinee)
          }
      | CheckNoUvars  ->
          let uu___148_1558 = fs  in
          {
            beta = (uu___148_1558.beta);
            iota = (uu___148_1558.iota);
            zeta = (uu___148_1558.zeta);
            weak = (uu___148_1558.weak);
            hnf = (uu___148_1558.hnf);
            primops = (uu___148_1558.primops);
            do_not_unfold_pure_lets = (uu___148_1558.do_not_unfold_pure_lets);
            unfold_until = (uu___148_1558.unfold_until);
            unfold_only = (uu___148_1558.unfold_only);
            unfold_fully = (uu___148_1558.unfold_fully);
            unfold_attr = (uu___148_1558.unfold_attr);
            unfold_tac = (uu___148_1558.unfold_tac);
            pure_subterms_within_computations =
              (uu___148_1558.pure_subterms_within_computations);
            simplify = (uu___148_1558.simplify);
            erase_universes = (uu___148_1558.erase_universes);
            allow_unbound_universes = (uu___148_1558.allow_unbound_universes);
            reify_ = (uu___148_1558.reify_);
            compress_uvars = (uu___148_1558.compress_uvars);
            no_full_norm = (uu___148_1558.no_full_norm);
            check_no_uvars = true;
            unmeta = (uu___148_1558.unmeta);
            unascribe = (uu___148_1558.unascribe);
            in_full_norm_request = (uu___148_1558.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___148_1558.weakly_reduce_scrutinee)
          }
      | Unmeta  ->
          let uu___149_1559 = fs  in
          {
            beta = (uu___149_1559.beta);
            iota = (uu___149_1559.iota);
            zeta = (uu___149_1559.zeta);
            weak = (uu___149_1559.weak);
            hnf = (uu___149_1559.hnf);
            primops = (uu___149_1559.primops);
            do_not_unfold_pure_lets = (uu___149_1559.do_not_unfold_pure_lets);
            unfold_until = (uu___149_1559.unfold_until);
            unfold_only = (uu___149_1559.unfold_only);
            unfold_fully = (uu___149_1559.unfold_fully);
            unfold_attr = (uu___149_1559.unfold_attr);
            unfold_tac = (uu___149_1559.unfold_tac);
            pure_subterms_within_computations =
              (uu___149_1559.pure_subterms_within_computations);
            simplify = (uu___149_1559.simplify);
            erase_universes = (uu___149_1559.erase_universes);
            allow_unbound_universes = (uu___149_1559.allow_unbound_universes);
            reify_ = (uu___149_1559.reify_);
            compress_uvars = (uu___149_1559.compress_uvars);
            no_full_norm = (uu___149_1559.no_full_norm);
            check_no_uvars = (uu___149_1559.check_no_uvars);
            unmeta = true;
            unascribe = (uu___149_1559.unascribe);
            in_full_norm_request = (uu___149_1559.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___149_1559.weakly_reduce_scrutinee)
          }
      | Unascribe  ->
          let uu___150_1560 = fs  in
          {
            beta = (uu___150_1560.beta);
            iota = (uu___150_1560.iota);
            zeta = (uu___150_1560.zeta);
            weak = (uu___150_1560.weak);
            hnf = (uu___150_1560.hnf);
            primops = (uu___150_1560.primops);
            do_not_unfold_pure_lets = (uu___150_1560.do_not_unfold_pure_lets);
            unfold_until = (uu___150_1560.unfold_until);
            unfold_only = (uu___150_1560.unfold_only);
            unfold_fully = (uu___150_1560.unfold_fully);
            unfold_attr = (uu___150_1560.unfold_attr);
            unfold_tac = (uu___150_1560.unfold_tac);
            pure_subterms_within_computations =
              (uu___150_1560.pure_subterms_within_computations);
            simplify = (uu___150_1560.simplify);
            erase_universes = (uu___150_1560.erase_universes);
            allow_unbound_universes = (uu___150_1560.allow_unbound_universes);
            reify_ = (uu___150_1560.reify_);
            compress_uvars = (uu___150_1560.compress_uvars);
            no_full_norm = (uu___150_1560.no_full_norm);
            check_no_uvars = (uu___150_1560.check_no_uvars);
            unmeta = (uu___150_1560.unmeta);
            unascribe = true;
            in_full_norm_request = (uu___150_1560.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___150_1560.weakly_reduce_scrutinee)
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
  wpe: Prims.bool ;
  norm_delayed: Prims.bool ;
  print_normalized: Prims.bool }[@@deriving show]
let (__proj__Mkdebug_switches__item__gen : debug_switches -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { gen = __fname__gen; primop = __fname__primop; b380 = __fname__b380;
        wpe = __fname__wpe; norm_delayed = __fname__norm_delayed;
        print_normalized = __fname__print_normalized;_} -> __fname__gen
  
let (__proj__Mkdebug_switches__item__primop : debug_switches -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { gen = __fname__gen; primop = __fname__primop; b380 = __fname__b380;
        wpe = __fname__wpe; norm_delayed = __fname__norm_delayed;
        print_normalized = __fname__print_normalized;_} -> __fname__primop
  
let (__proj__Mkdebug_switches__item__b380 : debug_switches -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { gen = __fname__gen; primop = __fname__primop; b380 = __fname__b380;
        wpe = __fname__wpe; norm_delayed = __fname__norm_delayed;
        print_normalized = __fname__print_normalized;_} -> __fname__b380
  
let (__proj__Mkdebug_switches__item__wpe : debug_switches -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { gen = __fname__gen; primop = __fname__primop; b380 = __fname__b380;
        wpe = __fname__wpe; norm_delayed = __fname__norm_delayed;
        print_normalized = __fname__print_normalized;_} -> __fname__wpe
  
let (__proj__Mkdebug_switches__item__norm_delayed :
  debug_switches -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { gen = __fname__gen; primop = __fname__primop; b380 = __fname__b380;
        wpe = __fname__wpe; norm_delayed = __fname__norm_delayed;
        print_normalized = __fname__print_normalized;_} ->
        __fname__norm_delayed
  
let (__proj__Mkdebug_switches__item__print_normalized :
  debug_switches -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { gen = __fname__gen; primop = __fname__primop; b380 = __fname__b380;
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
             let uu____2351 = FStar_Ident.text_of_lid p.name  in
             FStar_Util.psmap_add m1 uu____2351 p) l m
  
let (prim_from_list :
  primitive_step Prims.list -> primitive_step FStar_Util.psmap) =
  fun l  ->
    let uu____2365 = FStar_Util.psmap_empty ()  in add_steps uu____2365 l
  
let (find_prim_step :
  cfg ->
    FStar_Syntax_Syntax.fv -> primitive_step FStar_Pervasives_Native.option)
  =
  fun cfg  ->
    fun fv  ->
      let uu____2380 =
        FStar_Ident.text_of_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
         in
      FStar_Util.psmap_try_find cfg.primitive_steps uu____2380
  
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
    match projectee with | Arg _0 -> true | uu____2538 -> false
  
let (__proj__Arg__item___0 :
  stack_elt ->
    (closure,FStar_Syntax_Syntax.aqual,FStar_Range.range)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | Arg _0 -> _0 
let (uu___is_UnivArgs : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnivArgs _0 -> true | uu____2576 -> false
  
let (__proj__UnivArgs__item___0 :
  stack_elt ->
    (FStar_Syntax_Syntax.universe Prims.list,FStar_Range.range)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | UnivArgs _0 -> _0 
let (uu___is_MemoLazy : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | MemoLazy _0 -> true | uu____2614 -> false
  
let (__proj__MemoLazy__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.term) FStar_Pervasives_Native.tuple2
      FStar_Syntax_Syntax.memo)
  = fun projectee  -> match projectee with | MemoLazy _0 -> _0 
let (uu___is_Match : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____2687 -> false
  
let (__proj__Match__item___0 :
  stack_elt ->
    (env,branches,cfg,FStar_Range.range) FStar_Pervasives_Native.tuple4)
  = fun projectee  -> match projectee with | Match _0 -> _0 
let (uu___is_Abs : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Abs _0 -> true | uu____2737 -> false
  
let (__proj__Abs__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.binders,env,FStar_Syntax_Syntax.residual_comp
                                           FStar_Pervasives_Native.option,
      FStar_Range.range) FStar_Pervasives_Native.tuple5)
  = fun projectee  -> match projectee with | Abs _0 -> _0 
let (uu___is_App : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____2795 -> false
  
let (__proj__App__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual,FStar_Range.range)
      FStar_Pervasives_Native.tuple4)
  = fun projectee  -> match projectee with | App _0 -> _0 
let (uu___is_Meta : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Meta _0 -> true | uu____2839 -> false
  
let (__proj__Meta__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.metadata,FStar_Range.range)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | Meta _0 -> _0 
let (uu___is_Let : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Let _0 -> true | uu____2879 -> false
  
let (__proj__Let__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.letbinding,FStar_Range.range)
      FStar_Pervasives_Native.tuple4)
  = fun projectee  -> match projectee with | Let _0 -> _0 
let (uu___is_Cfg : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Cfg _0 -> true | uu____2917 -> false
  
let (__proj__Cfg__item___0 : stack_elt -> cfg) =
  fun projectee  -> match projectee with | Cfg _0 -> _0 
let (uu___is_Debug : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Debug _0 -> true | uu____2935 -> false
  
let (__proj__Debug__item___0 :
  stack_elt ->
    (FStar_Syntax_Syntax.term,FStar_Util.time) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Debug _0 -> _0 
type stack = stack_elt Prims.list[@@deriving show]
let (head_of : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____2962 = FStar_Syntax_Util.head_and_args' t  in
    match uu____2962 with | (hd1,uu____2976) -> hd1
  
let mk :
  'Auu____2999 .
    'Auu____2999 ->
      FStar_Range.range -> 'Auu____2999 FStar_Syntax_Syntax.syntax
  =
  fun t  -> fun r  -> FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None r 
let set_memo : 'a . cfg -> 'a FStar_Syntax_Syntax.memo -> 'a -> unit =
  fun cfg  ->
    fun r  ->
      fun t  ->
        if cfg.memoize_lazy
        then
          let uu____3062 = FStar_ST.op_Bang r  in
          match uu____3062 with
          | FStar_Pervasives_Native.Some uu____3114 ->
              failwith "Unexpected set_memo: thunk already evaluated"
          | FStar_Pervasives_Native.None  ->
              FStar_ST.op_Colon_Equals r (FStar_Pervasives_Native.Some t)
        else ()
  
let rec (env_to_string :
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
    FStar_Pervasives_Native.tuple2 Prims.list -> Prims.string)
  =
  fun env  ->
    let uu____3190 =
      FStar_List.map
        (fun uu____3204  ->
           match uu____3204 with
           | (bopt,c) ->
               let uu____3217 =
                 match bopt with
                 | FStar_Pervasives_Native.None  -> "."
                 | FStar_Pervasives_Native.Some x ->
                     FStar_Syntax_Print.binder_to_string x
                  in
               let uu____3219 = closure_to_string c  in
               FStar_Util.format2 "(%s, %s)" uu____3217 uu____3219) env
       in
    FStar_All.pipe_right uu____3190 (FStar_String.concat "; ")

and (closure_to_string : closure -> Prims.string) =
  fun uu___108_3222  ->
    match uu___108_3222 with
    | Clos (env,t,uu____3225,uu____3226) ->
        let uu____3271 =
          FStar_All.pipe_right (FStar_List.length env)
            FStar_Util.string_of_int
           in
        let uu____3278 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format2 "(env=%s elts; %s)" uu____3271 uu____3278
    | Univ uu____3279 -> "Univ"
    | Dummy  -> "dummy"

let (stack_elt_to_string : stack_elt -> Prims.string) =
  fun uu___109_3284  ->
    match uu___109_3284 with
    | Arg (c,uu____3286,uu____3287) ->
        let uu____3288 = closure_to_string c  in
        FStar_Util.format1 "Closure %s" uu____3288
    | MemoLazy uu____3289 -> "MemoLazy"
    | Abs (uu____3296,bs,uu____3298,uu____3299,uu____3300) ->
        let uu____3305 =
          FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs)
           in
        FStar_Util.format1 "Abs %s" uu____3305
    | UnivArgs uu____3310 -> "UnivArgs"
    | Match uu____3317 -> "Match"
    | App (uu____3326,t,uu____3328,uu____3329) ->
        let uu____3330 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "App %s" uu____3330
    | Meta (uu____3331,m,uu____3333) -> "Meta"
    | Let uu____3334 -> "Let"
    | Cfg uu____3343 -> "Cfg"
    | Debug (t,uu____3345) ->
        let uu____3346 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "Debug %s" uu____3346
  
let (stack_to_string : stack_elt Prims.list -> Prims.string) =
  fun s  ->
    let uu____3356 = FStar_List.map stack_elt_to_string s  in
    FStar_All.pipe_right uu____3356 (FStar_String.concat "; ")
  
let (log : cfg -> (unit -> unit) -> unit) =
  fun cfg  -> fun f  -> if (cfg.debug).gen then f () else () 
let (log_primops : cfg -> (unit -> unit) -> unit) =
  fun cfg  -> fun f  -> if (cfg.debug).primop then f () else () 
let is_empty : 'Auu____3397 . 'Auu____3397 Prims.list -> Prims.bool =
  fun uu___110_3404  ->
    match uu___110_3404 with | [] -> true | uu____3407 -> false
  
let (lookup_bvar :
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    FStar_Syntax_Syntax.bv -> closure)
  =
  fun env  ->
    fun x  ->
      try
        let uu____3439 = FStar_List.nth env x.FStar_Syntax_Syntax.index  in
        FStar_Pervasives_Native.snd uu____3439
      with
      | uu____3458 ->
          let uu____3459 =
            let uu____3460 = FStar_Syntax_Print.db_to_string x  in
            let uu____3461 = env_to_string env  in
            FStar_Util.format2 "Failed to find %s\nEnv is %s\n" uu____3460
              uu____3461
             in
          failwith uu____3459
  
let (downgrade_ghost_effect_name :
  FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option) =
  fun l  ->
    let uu____3469 =
      FStar_Ident.lid_equals l FStar_Parser_Const.effect_Ghost_lid  in
    if uu____3469
    then FStar_Pervasives_Native.Some FStar_Parser_Const.effect_Pure_lid
    else
      (let uu____3473 =
         FStar_Ident.lid_equals l FStar_Parser_Const.effect_GTot_lid  in
       if uu____3473
       then FStar_Pervasives_Native.Some FStar_Parser_Const.effect_Tot_lid
       else
         (let uu____3477 =
            FStar_Ident.lid_equals l FStar_Parser_Const.effect_GHOST_lid  in
          if uu____3477
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
          let uu____3511 =
            FStar_List.fold_left
              (fun uu____3537  ->
                 fun u1  ->
                   match uu____3537 with
                   | (cur_kernel,cur_max,out) ->
                       let uu____3562 = FStar_Syntax_Util.univ_kernel u1  in
                       (match uu____3562 with
                        | (k_u,n1) ->
                            let uu____3577 =
                              FStar_Syntax_Util.eq_univs cur_kernel k_u  in
                            if uu____3577
                            then (cur_kernel, u1, out)
                            else (k_u, u1, (cur_max :: out))))
              (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero, [])
              us1
             in
          match uu____3511 with
          | (uu____3595,u1,out) -> FStar_List.rev (u1 :: out)  in
        let rec aux u1 =
          let u2 = FStar_Syntax_Subst.compress_univ u1  in
          match u2 with
          | FStar_Syntax_Syntax.U_bvar x ->
              (try
                 let uu____3622 =
                   let uu____3623 = FStar_List.nth env x  in
                   FStar_Pervasives_Native.snd uu____3623  in
                 match uu____3622 with
                 | Univ u3 -> aux u3
                 | Dummy  -> [u2]
                 | uu____3641 ->
                     failwith "Impossible: universe variable bound to a term"
               with
               | uu____3649 ->
                   if (cfg.steps).allow_unbound_universes
                   then [FStar_Syntax_Syntax.U_unknown]
                   else failwith "Universe variable not found")
          | FStar_Syntax_Syntax.U_unif uu____3655 when
              (cfg.steps).check_no_uvars -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_zero  -> [u2]
          | FStar_Syntax_Syntax.U_unif uu____3664 -> [u2]
          | FStar_Syntax_Syntax.U_name uu____3673 -> [u2]
          | FStar_Syntax_Syntax.U_unknown  -> [u2]
          | FStar_Syntax_Syntax.U_max [] -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_max us ->
              let us1 =
                let uu____3680 = FStar_List.collect aux us  in
                FStar_All.pipe_right uu____3680 norm_univs  in
              (match us1 with
               | u_k::hd1::rest ->
                   let rest1 = hd1 :: rest  in
                   let uu____3697 = FStar_Syntax_Util.univ_kernel u_k  in
                   (match uu____3697 with
                    | (FStar_Syntax_Syntax.U_zero ,n1) ->
                        let uu____3705 =
                          FStar_All.pipe_right rest1
                            (FStar_List.for_all
                               (fun u3  ->
                                  let uu____3713 =
                                    FStar_Syntax_Util.univ_kernel u3  in
                                  match uu____3713 with
                                  | (uu____3718,m) -> n1 <= m))
                           in
                        if uu____3705 then rest1 else us1
                    | uu____3723 -> us1)
               | uu____3728 -> us1)
          | FStar_Syntax_Syntax.U_succ u3 ->
              let uu____3732 = aux u3  in
              FStar_List.map (fun _0_17  -> FStar_Syntax_Syntax.U_succ _0_17)
                uu____3732
           in
        if (cfg.steps).erase_universes
        then FStar_Syntax_Syntax.U_unknown
        else
          (let uu____3736 = aux u  in
           match uu____3736 with
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
            (fun uu____3884  ->
               let uu____3885 = FStar_Syntax_Print.tag_of_term t  in
               let uu____3886 = env_to_string env  in
               let uu____3887 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print3 "\n>>> %s (env=%s) Closure_as_term %s\n"
                 uu____3885 uu____3886 uu____3887);
          (match env with
           | [] when
               FStar_All.pipe_left Prims.op_Negation
                 (cfg.steps).compress_uvars
               -> rebuild_closure cfg env stack t
           | uu____3896 ->
               (match t.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_delayed uu____3899 ->
                    let uu____3924 = FStar_Syntax_Subst.compress t  in
                    inline_closure_env cfg env stack uu____3924
                | FStar_Syntax_Syntax.Tm_unknown  ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_constant uu____3925 ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_name uu____3926 ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_lazy uu____3927 ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_fvar uu____3928 ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_uvar (uv,s) ->
                    if (cfg.steps).check_no_uvars
                    then
                      let t1 = FStar_Syntax_Subst.compress t  in
                      (match t1.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_uvar uu____3940 ->
                           let uu____3947 =
                             let uu____3948 =
                               FStar_Range.string_of_range
                                 t1.FStar_Syntax_Syntax.pos
                                in
                             let uu____3949 =
                               FStar_Syntax_Print.term_to_string t1  in
                             FStar_Util.format2
                               "(%s): CheckNoUvars: Unexpected unification variable remains: %s"
                               uu____3948 uu____3949
                              in
                           failwith uu____3947
                       | uu____3952 -> inline_closure_env cfg env stack t1)
                    else
                      (let s1 =
                         FStar_All.pipe_right s
                           (FStar_List.map
                              (fun uu___111_3965  ->
                                 match uu___111_3965 with
                                 | FStar_Syntax_Syntax.NT (x,t1) ->
                                     let uu____3972 =
                                       let uu____3979 =
                                         inline_closure_env cfg env [] t1  in
                                       (x, uu____3979)  in
                                     FStar_Syntax_Syntax.NT uu____3972
                                 | FStar_Syntax_Syntax.NM (x,i) ->
                                     let t1 =
                                       FStar_Syntax_Syntax.bv_to_tm
                                         (let uu___155_3989 = x  in
                                          {
                                            FStar_Syntax_Syntax.ppname =
                                              (uu___155_3989.FStar_Syntax_Syntax.ppname);
                                            FStar_Syntax_Syntax.index = i;
                                            FStar_Syntax_Syntax.sort =
                                              (uu___155_3989.FStar_Syntax_Syntax.sort)
                                          })
                                        in
                                     let uu____3990 =
                                       let uu____3997 =
                                         inline_closure_env cfg env [] t1  in
                                       (x, uu____3997)  in
                                     FStar_Syntax_Syntax.NT uu____3990
                                 | uu____4002 ->
                                     failwith
                                       "Impossible: subst invariant of uvar nodes"))
                          in
                       let t1 =
                         let uu___156_4006 = t  in
                         {
                           FStar_Syntax_Syntax.n =
                             (FStar_Syntax_Syntax.Tm_uvar (uv, s1));
                           FStar_Syntax_Syntax.pos =
                             (uu___156_4006.FStar_Syntax_Syntax.pos);
                           FStar_Syntax_Syntax.vars =
                             (uu___156_4006.FStar_Syntax_Syntax.vars)
                         }  in
                       rebuild_closure cfg env stack t1)
                | FStar_Syntax_Syntax.Tm_type u ->
                    let t1 =
                      let uu____4013 =
                        let uu____4014 = norm_universe cfg env u  in
                        FStar_Syntax_Syntax.Tm_type uu____4014  in
                      mk uu____4013 t.FStar_Syntax_Syntax.pos  in
                    rebuild_closure cfg env stack t1
                | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
                    let t1 =
                      let uu____4022 =
                        FStar_List.map (norm_universe cfg env) us  in
                      FStar_Syntax_Syntax.mk_Tm_uinst t' uu____4022  in
                    rebuild_closure cfg env stack t1
                | FStar_Syntax_Syntax.Tm_bvar x ->
                    let uu____4024 = lookup_bvar env x  in
                    (match uu____4024 with
                     | Univ uu____4027 ->
                         failwith
                           "Impossible: term variable is bound to a universe"
                     | Dummy  ->
                         let x1 =
                           let uu___157_4031 = x  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___157_4031.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___157_4031.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort =
                               FStar_Syntax_Syntax.tun
                           }  in
                         let t1 =
                           mk (FStar_Syntax_Syntax.Tm_bvar x1)
                             t.FStar_Syntax_Syntax.pos
                            in
                         rebuild_closure cfg env stack t1
                     | Clos (env1,t0,uu____4037,uu____4038) ->
                         inline_closure_env cfg env1 stack t0)
                | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                    let stack1 =
                      FStar_All.pipe_right stack
                        (FStar_List.fold_right
                           (fun uu____4123  ->
                              fun stack1  ->
                                match uu____4123 with
                                | (a,aq) ->
                                    let uu____4135 =
                                      let uu____4136 =
                                        let uu____4143 =
                                          let uu____4144 =
                                            let uu____4175 =
                                              FStar_Util.mk_ref
                                                FStar_Pervasives_Native.None
                                               in
                                            (env, a, uu____4175, false)  in
                                          Clos uu____4144  in
                                        (uu____4143, aq,
                                          (t.FStar_Syntax_Syntax.pos))
                                         in
                                      Arg uu____4136  in
                                    uu____4135 :: stack1) args)
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
                    let uu____4351 = close_binders cfg env bs  in
                    (match uu____4351 with
                     | (bs1,env') ->
                         let c1 = close_comp cfg env' c  in
                         let t1 =
                           mk (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
                             t.FStar_Syntax_Syntax.pos
                            in
                         rebuild_closure cfg env stack t1)
                | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
                    let uu____4398 =
                      let uu____4409 =
                        let uu____4416 = FStar_Syntax_Syntax.mk_binder x  in
                        [uu____4416]  in
                      close_binders cfg env uu____4409  in
                    (match uu____4398 with
                     | (x1,env1) ->
                         let phi1 = non_tail_inline_closure_env cfg env1 phi
                            in
                         let t1 =
                           let uu____4439 =
                             let uu____4440 =
                               let uu____4447 =
                                 let uu____4448 = FStar_List.hd x1  in
                                 FStar_All.pipe_right uu____4448
                                   FStar_Pervasives_Native.fst
                                  in
                               (uu____4447, phi1)  in
                             FStar_Syntax_Syntax.Tm_refine uu____4440  in
                           mk uu____4439 t.FStar_Syntax_Syntax.pos  in
                         rebuild_closure cfg env1 stack t1)
                | FStar_Syntax_Syntax.Tm_ascribed (t1,(annot,tacopt),lopt) ->
                    let annot1 =
                      match annot with
                      | FStar_Util.Inl t2 ->
                          let uu____4539 =
                            non_tail_inline_closure_env cfg env t2  in
                          FStar_Util.Inl uu____4539
                      | FStar_Util.Inr c ->
                          let uu____4553 = close_comp cfg env c  in
                          FStar_Util.Inr uu____4553
                       in
                    let tacopt1 =
                      FStar_Util.map_opt tacopt
                        (non_tail_inline_closure_env cfg env)
                       in
                    let t2 =
                      let uu____4572 =
                        let uu____4573 =
                          let uu____4600 =
                            non_tail_inline_closure_env cfg env t1  in
                          (uu____4600, (annot1, tacopt1), lopt)  in
                        FStar_Syntax_Syntax.Tm_ascribed uu____4573  in
                      mk uu____4572 t.FStar_Syntax_Syntax.pos  in
                    rebuild_closure cfg env stack t2
                | FStar_Syntax_Syntax.Tm_quoted (t',qi) ->
                    let t1 =
                      match qi.FStar_Syntax_Syntax.qkind with
                      | FStar_Syntax_Syntax.Quote_dynamic  ->
                          let uu____4646 =
                            let uu____4647 =
                              let uu____4654 =
                                non_tail_inline_closure_env cfg env t'  in
                              (uu____4654, qi)  in
                            FStar_Syntax_Syntax.Tm_quoted uu____4647  in
                          mk uu____4646 t.FStar_Syntax_Syntax.pos
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
                        (fun env1  -> fun uu____4706  -> dummy :: env1) env
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
                    let uu____4727 =
                      let uu____4738 = FStar_Syntax_Syntax.is_top_level [lb]
                         in
                      if uu____4738
                      then ((lb.FStar_Syntax_Syntax.lbname), body)
                      else
                        (let x =
                           FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                         let uu____4757 =
                           non_tail_inline_closure_env cfg (dummy :: env0)
                             body
                            in
                         ((FStar_Util.Inl
                             (let uu___158_4773 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___158_4773.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___158_4773.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = typ
                              })), uu____4757))
                       in
                    (match uu____4727 with
                     | (nm,body1) ->
                         let lb1 =
                           let uu___159_4791 = lb  in
                           {
                             FStar_Syntax_Syntax.lbname = nm;
                             FStar_Syntax_Syntax.lbunivs =
                               (uu___159_4791.FStar_Syntax_Syntax.lbunivs);
                             FStar_Syntax_Syntax.lbtyp = typ;
                             FStar_Syntax_Syntax.lbeff =
                               (uu___159_4791.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = def;
                             FStar_Syntax_Syntax.lbattrs =
                               (uu___159_4791.FStar_Syntax_Syntax.lbattrs);
                             FStar_Syntax_Syntax.lbpos =
                               (uu___159_4791.FStar_Syntax_Syntax.lbpos)
                           }  in
                         let t1 =
                           mk
                             (FStar_Syntax_Syntax.Tm_let
                                ((false, [lb1]), body1))
                             t.FStar_Syntax_Syntax.pos
                            in
                         rebuild_closure cfg env0 stack t1)
                | FStar_Syntax_Syntax.Tm_let ((uu____4805,lbs),body) ->
                    let norm_one_lb env1 lb =
                      let env_univs =
                        FStar_List.fold_right
                          (fun uu____4868  -> fun env2  -> dummy :: env2)
                          lb.FStar_Syntax_Syntax.lbunivs env1
                         in
                      let env2 =
                        let uu____4885 = FStar_Syntax_Syntax.is_top_level lbs
                           in
                        if uu____4885
                        then env_univs
                        else
                          FStar_List.fold_right
                            (fun uu____4897  -> fun env2  -> dummy :: env2)
                            lbs env_univs
                         in
                      let ty =
                        non_tail_inline_closure_env cfg env_univs
                          lb.FStar_Syntax_Syntax.lbtyp
                         in
                      let nm =
                        let uu____4921 = FStar_Syntax_Syntax.is_top_level lbs
                           in
                        if uu____4921
                        then lb.FStar_Syntax_Syntax.lbname
                        else
                          (let x =
                             FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                              in
                           FStar_Util.Inl
                             (let uu___160_4929 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___160_4929.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___160_4929.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = ty
                              }))
                         in
                      let uu___161_4930 = lb  in
                      let uu____4931 =
                        non_tail_inline_closure_env cfg env2
                          lb.FStar_Syntax_Syntax.lbdef
                         in
                      {
                        FStar_Syntax_Syntax.lbname = nm;
                        FStar_Syntax_Syntax.lbunivs =
                          (uu___161_4930.FStar_Syntax_Syntax.lbunivs);
                        FStar_Syntax_Syntax.lbtyp = ty;
                        FStar_Syntax_Syntax.lbeff =
                          (uu___161_4930.FStar_Syntax_Syntax.lbeff);
                        FStar_Syntax_Syntax.lbdef = uu____4931;
                        FStar_Syntax_Syntax.lbattrs =
                          (uu___161_4930.FStar_Syntax_Syntax.lbattrs);
                        FStar_Syntax_Syntax.lbpos =
                          (uu___161_4930.FStar_Syntax_Syntax.lbpos)
                      }  in
                    let lbs1 =
                      FStar_All.pipe_right lbs
                        (FStar_List.map (norm_one_lb env))
                       in
                    let body1 =
                      let body_env =
                        FStar_List.fold_right
                          (fun uu____4963  -> fun env1  -> dummy :: env1)
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
            (fun uu____5052  ->
               let uu____5053 = FStar_Syntax_Print.tag_of_term t  in
               let uu____5054 = env_to_string env  in
               let uu____5055 = stack_to_string stack  in
               let uu____5056 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print4
                 "\n>>> %s (env=%s, stack=%s) Rebuild closure_as_term %s\n"
                 uu____5053 uu____5054 uu____5055 uu____5056);
          (match stack with
           | [] -> t
           | (Arg (Clos (env_arg,tm,uu____5061,uu____5062),aq,r))::stack1 ->
               let stack2 = (App (env, t, aq, r)) :: stack1  in
               inline_closure_env cfg env_arg stack2 tm
           | (App (env1,head1,aq,r))::stack1 ->
               let t1 =
                 FStar_Syntax_Syntax.extend_app head1 (t, aq)
                   FStar_Pervasives_Native.None r
                  in
               rebuild_closure cfg env1 stack1 t1
           | (Abs (env',bs,env'',lopt,r))::stack1 ->
               let uu____5139 = close_binders cfg env' bs  in
               (match uu____5139 with
                | (bs1,uu____5153) ->
                    let lopt1 = close_lcomp_opt cfg env'' lopt  in
                    let uu____5169 =
                      let uu___162_5172 = FStar_Syntax_Util.abs bs1 t lopt1
                         in
                      {
                        FStar_Syntax_Syntax.n =
                          (uu___162_5172.FStar_Syntax_Syntax.n);
                        FStar_Syntax_Syntax.pos = r;
                        FStar_Syntax_Syntax.vars =
                          (uu___162_5172.FStar_Syntax_Syntax.vars)
                      }  in
                    rebuild_closure cfg env stack1 uu____5169)
           | (Match (env1,branches,cfg1,r))::stack1 ->
               let close_one_branch env2 uu____5228 =
                 match uu____5228 with
                 | (pat,w_opt,tm) ->
                     let rec norm_pat env3 p =
                       match p.FStar_Syntax_Syntax.v with
                       | FStar_Syntax_Syntax.Pat_constant uu____5343 ->
                           (p, env3)
                       | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                           let uu____5372 =
                             FStar_All.pipe_right pats
                               (FStar_List.fold_left
                                  (fun uu____5456  ->
                                     fun uu____5457  ->
                                       match (uu____5456, uu____5457) with
                                       | ((pats1,env4),(p1,b)) ->
                                           let uu____5596 = norm_pat env4 p1
                                              in
                                           (match uu____5596 with
                                            | (p2,env5) ->
                                                (((p2, b) :: pats1), env5)))
                                  ([], env3))
                              in
                           (match uu____5372 with
                            | (pats1,env4) ->
                                ((let uu___163_5758 = p  in
                                  {
                                    FStar_Syntax_Syntax.v =
                                      (FStar_Syntax_Syntax.Pat_cons
                                         (fv, (FStar_List.rev pats1)));
                                    FStar_Syntax_Syntax.p =
                                      (uu___163_5758.FStar_Syntax_Syntax.p)
                                  }), env4))
                       | FStar_Syntax_Syntax.Pat_var x ->
                           let x1 =
                             let uu___164_5777 = x  in
                             let uu____5778 =
                               non_tail_inline_closure_env cfg1 env3
                                 x.FStar_Syntax_Syntax.sort
                                in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___164_5777.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___164_5777.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____5778
                             }  in
                           ((let uu___165_5792 = p  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_var x1);
                               FStar_Syntax_Syntax.p =
                                 (uu___165_5792.FStar_Syntax_Syntax.p)
                             }), (dummy :: env3))
                       | FStar_Syntax_Syntax.Pat_wild x ->
                           let x1 =
                             let uu___166_5803 = x  in
                             let uu____5804 =
                               non_tail_inline_closure_env cfg1 env3
                                 x.FStar_Syntax_Syntax.sort
                                in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___166_5803.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___166_5803.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____5804
                             }  in
                           ((let uu___167_5818 = p  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_wild x1);
                               FStar_Syntax_Syntax.p =
                                 (uu___167_5818.FStar_Syntax_Syntax.p)
                             }), (dummy :: env3))
                       | FStar_Syntax_Syntax.Pat_dot_term (x,t1) ->
                           let x1 =
                             let uu___168_5834 = x  in
                             let uu____5835 =
                               non_tail_inline_closure_env cfg1 env3
                                 x.FStar_Syntax_Syntax.sort
                                in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___168_5834.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___168_5834.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____5835
                             }  in
                           let t2 = non_tail_inline_closure_env cfg1 env3 t1
                              in
                           ((let uu___169_5852 = p  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_dot_term (x1, t2));
                               FStar_Syntax_Syntax.p =
                                 (uu___169_5852.FStar_Syntax_Syntax.p)
                             }), env3)
                        in
                     let uu____5857 = norm_pat env2 pat  in
                     (match uu____5857 with
                      | (pat1,env3) ->
                          let w_opt1 =
                            match w_opt with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Pervasives_Native.None
                            | FStar_Pervasives_Native.Some w ->
                                let uu____5926 =
                                  non_tail_inline_closure_env cfg1 env3 w  in
                                FStar_Pervasives_Native.Some uu____5926
                             in
                          let tm1 = non_tail_inline_closure_env cfg1 env3 tm
                             in
                          (pat1, w_opt1, tm1))
                  in
               let t1 =
                 let uu____5945 =
                   let uu____5946 =
                     let uu____5969 =
                       FStar_All.pipe_right branches
                         (FStar_List.map (close_one_branch env1))
                        in
                     (t, uu____5969)  in
                   FStar_Syntax_Syntax.Tm_match uu____5946  in
                 mk uu____5945 t.FStar_Syntax_Syntax.pos  in
               rebuild_closure cfg1 env1 stack1 t1
           | (Meta (env_m,m,r))::stack1 ->
               let m1 =
                 match m with
                 | FStar_Syntax_Syntax.Meta_pattern args ->
                     let uu____6082 =
                       FStar_All.pipe_right args
                         (FStar_List.map
                            (fun args1  ->
                               FStar_All.pipe_right args1
                                 (FStar_List.map
                                    (fun uu____6171  ->
                                       match uu____6171 with
                                       | (a,q) ->
                                           let uu____6190 =
                                             non_tail_inline_closure_env cfg
                                               env_m a
                                              in
                                           (uu____6190, q)))))
                        in
                     FStar_Syntax_Syntax.Meta_pattern uu____6082
                 | FStar_Syntax_Syntax.Meta_monadic (m1,tbody) ->
                     let uu____6201 =
                       let uu____6208 =
                         non_tail_inline_closure_env cfg env_m tbody  in
                       (m1, uu____6208)  in
                     FStar_Syntax_Syntax.Meta_monadic uu____6201
                 | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,tbody) ->
                     let uu____6220 =
                       let uu____6229 =
                         non_tail_inline_closure_env cfg env_m tbody  in
                       (m1, m2, uu____6229)  in
                     FStar_Syntax_Syntax.Meta_monadic_lift uu____6220
                 | uu____6234 -> m  in
               let t1 = mk (FStar_Syntax_Syntax.Tm_meta (t, m1)) r  in
               rebuild_closure cfg env stack1 t1
           | uu____6240 -> failwith "Impossible: unexpected stack element")

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
        let uu____6254 =
          FStar_All.pipe_right bs
            (FStar_List.fold_left
               (fun uu____6327  ->
                  fun uu____6328  ->
                    match (uu____6327, uu____6328) with
                    | ((env1,out),(b,imp)) ->
                        let b1 =
                          let uu___170_6446 = b  in
                          let uu____6447 =
                            inline_closure_env cfg env1 []
                              b.FStar_Syntax_Syntax.sort
                             in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___170_6446.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___170_6446.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = uu____6447
                          }  in
                        let env2 = dummy :: env1  in
                        (env2, ((b1, imp) :: out))) (env, []))
           in
        match uu____6254 with | (env1,bs1) -> ((FStar_List.rev bs1), env1)

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
        | uu____6564 ->
            (match c.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Total (t,uopt) ->
                 let uu____6577 = inline_closure_env cfg env [] t  in
                 let uu____6578 =
                   FStar_Option.map (norm_universe cfg env) uopt  in
                 FStar_Syntax_Syntax.mk_Total' uu____6577 uu____6578
             | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                 let uu____6591 = inline_closure_env cfg env [] t  in
                 let uu____6592 =
                   FStar_Option.map (norm_universe cfg env) uopt  in
                 FStar_Syntax_Syntax.mk_GTotal' uu____6591 uu____6592
             | FStar_Syntax_Syntax.Comp c1 ->
                 let rt =
                   inline_closure_env cfg env []
                     c1.FStar_Syntax_Syntax.result_typ
                    in
                 let args =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args
                     (FStar_List.map
                        (fun uu____6636  ->
                           match uu____6636 with
                           | (a,q) ->
                               let uu____6649 =
                                 inline_closure_env cfg env [] a  in
                               (uu____6649, q)))
                    in
                 let flags1 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_List.map
                        (fun uu___112_6664  ->
                           match uu___112_6664 with
                           | FStar_Syntax_Syntax.DECREASES t ->
                               let uu____6668 =
                                 inline_closure_env cfg env [] t  in
                               FStar_Syntax_Syntax.DECREASES uu____6668
                           | f -> f))
                    in
                 let uu____6672 =
                   let uu___171_6673 = c1  in
                   let uu____6674 =
                     FStar_List.map (norm_universe cfg env)
                       c1.FStar_Syntax_Syntax.comp_univs
                      in
                   {
                     FStar_Syntax_Syntax.comp_univs = uu____6674;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___171_6673.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ = rt;
                     FStar_Syntax_Syntax.effect_args = args;
                     FStar_Syntax_Syntax.flags = flags1
                   }  in
                 FStar_Syntax_Syntax.mk_Comp uu____6672)

and (filter_out_lcomp_cflags :
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun flags1  ->
    FStar_All.pipe_right flags1
      (FStar_List.filter
         (fun uu___113_6684  ->
            match uu___113_6684 with
            | FStar_Syntax_Syntax.DECREASES uu____6685 -> false
            | uu____6688 -> true))

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
                   (fun uu___114_6706  ->
                      match uu___114_6706 with
                      | FStar_Syntax_Syntax.DECREASES uu____6707 -> false
                      | uu____6710 -> true))
               in
            let rc1 =
              let uu___172_6712 = rc  in
              let uu____6713 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (inline_closure_env cfg env [])
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___172_6712.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____6713;
                FStar_Syntax_Syntax.residual_flags = flags1
              }  in
            FStar_Pervasives_Native.Some rc1
        | uu____6722 -> lopt

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
    let uu____6827 =
      let uu____6836 = FStar_Syntax_Embeddings.e_list e  in
      FStar_Syntax_Embeddings.try_unembed uu____6836  in
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a) uu____6827  in
  let arg_as_bounded_int uu____6862 =
    match uu____6862 with
    | (a,uu____6874) ->
        let uu____6881 =
          let uu____6882 = FStar_Syntax_Subst.compress a  in
          uu____6882.FStar_Syntax_Syntax.n  in
        (match uu____6881 with
         | FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv1;
                FStar_Syntax_Syntax.pos = uu____6892;
                FStar_Syntax_Syntax.vars = uu____6893;_},({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_constant
                                                              (FStar_Const.Const_int
                                                              (i,FStar_Pervasives_Native.None
                                                               ));
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____6895;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____6896;_},uu____6897)::[])
             when
             let uu____6936 =
               FStar_Ident.text_of_lid
                 (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                in
             FStar_Util.ends_with uu____6936 "int_to_t" ->
             let uu____6937 =
               let uu____6942 = FStar_BigInt.big_int_of_string i  in
               (fv1, uu____6942)  in
             FStar_Pervasives_Native.Some uu____6937
         | uu____6947 -> FStar_Pervasives_Native.None)
     in
  let lift_unary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a)::[] ->
        let uu____6995 = f a  in FStar_Pervasives_Native.Some uu____6995
    | uu____6996 -> FStar_Pervasives_Native.None  in
  let lift_binary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a0)::(FStar_Pervasives_Native.Some
        a1)::[] ->
        let uu____7052 = f a0 a1  in FStar_Pervasives_Native.Some uu____7052
    | uu____7053 -> FStar_Pervasives_Native.None  in
  let unary_op as_a f res args =
    let uu____7111 = FStar_List.map as_a args  in
    lift_unary (f res.psc_range) uu____7111  in
  let binary_op as_a f res args =
    let uu____7182 = FStar_List.map as_a args  in
    lift_binary (f res.psc_range) uu____7182  in
  let as_primitive_step is_strong uu____7219 =
    match uu____7219 with
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
           let uu____7279 = f x  in
           FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_int r
             uu____7279)
     in
  let binary_int_op f =
    binary_op arg_as_int
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____7315 = f x y  in
             FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_int r
               uu____7315)
     in
  let unary_bool_op f =
    unary_op arg_as_bool
      (fun r  ->
         fun x  ->
           let uu____7344 = f x  in
           FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_bool r
             uu____7344)
     in
  let binary_bool_op f =
    binary_op arg_as_bool
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____7380 = f x y  in
             FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_bool r
               uu____7380)
     in
  let binary_string_op f =
    binary_op arg_as_string
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____7416 = f x y  in
             FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_string r
               uu____7416)
     in
  let mixed_binary_op as_a as_b embed_c f res args =
    match args with
    | a::b::[] ->
        let uu____7548 =
          let uu____7557 = as_a a  in
          let uu____7560 = as_b b  in (uu____7557, uu____7560)  in
        (match uu____7548 with
         | (FStar_Pervasives_Native.Some a1,FStar_Pervasives_Native.Some b1)
             ->
             let uu____7575 =
               let uu____7576 = f res.psc_range a1 b1  in
               embed_c res.psc_range uu____7576  in
             FStar_Pervasives_Native.Some uu____7575
         | uu____7577 -> FStar_Pervasives_Native.None)
    | uu____7586 -> FStar_Pervasives_Native.None  in
  let list_of_string' rng s =
    let name l =
      let uu____7606 =
        let uu____7607 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
            FStar_Pervasives_Native.None
           in
        FStar_Syntax_Syntax.Tm_fvar uu____7607  in
      mk uu____7606 rng  in
    let char_t = name FStar_Parser_Const.char_lid  in
    let charterm c =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c)) rng  in
    let uu____7619 =
      let uu____7622 = FStar_String.list_of_string s  in
      FStar_List.map charterm uu____7622  in
    FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu____7619  in
  let string_of_list' rng l =
    let s = FStar_String.string_of_list l  in FStar_Syntax_Util.exp_string s
     in
  let string_compare' rng s1 s2 =
    let r = FStar_String.compare s1 s2  in
    let uu____7664 =
      let uu____7665 = FStar_Util.string_of_int r  in
      FStar_BigInt.big_int_of_string uu____7665  in
    FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_int rng
      uu____7664
     in
  let string_concat' psc args =
    match args with
    | a1::a2::[] ->
        let uu____7729 = arg_as_string a1  in
        (match uu____7729 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____7735 = arg_as_list FStar_Syntax_Embeddings.e_string a2
                in
             (match uu____7735 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2  in
                  let uu____7748 =
                    FStar_Syntax_Embeddings.embed
                      FStar_Syntax_Embeddings.e_string psc.psc_range r
                     in
                  FStar_Pervasives_Native.Some uu____7748
              | uu____7749 -> FStar_Pervasives_Native.None)
         | uu____7754 -> FStar_Pervasives_Native.None)
    | uu____7757 -> FStar_Pervasives_Native.None  in
  let string_of_int1 rng i =
    let uu____7777 = FStar_BigInt.string_of_big_int i  in
    FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_string rng
      uu____7777
     in
  let string_of_bool1 rng b =
    FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_string rng
      (if b then "true" else "false")
     in
  let mk_range1 psc args =
    match args with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____7814 =
          let uu____7835 = arg_as_string fn  in
          let uu____7838 = arg_as_int from_line  in
          let uu____7841 = arg_as_int from_col  in
          let uu____7844 = arg_as_int to_line  in
          let uu____7847 = arg_as_int to_col  in
          (uu____7835, uu____7838, uu____7841, uu____7844, uu____7847)  in
        (match uu____7814 with
         | (FStar_Pervasives_Native.Some fn1,FStar_Pervasives_Native.Some
            from_l,FStar_Pervasives_Native.Some
            from_c,FStar_Pervasives_Native.Some
            to_l,FStar_Pervasives_Native.Some to_c) ->
             let r =
               let uu____7878 =
                 let uu____7879 = FStar_BigInt.to_int_fs from_l  in
                 let uu____7880 = FStar_BigInt.to_int_fs from_c  in
                 FStar_Range.mk_pos uu____7879 uu____7880  in
               let uu____7881 =
                 let uu____7882 = FStar_BigInt.to_int_fs to_l  in
                 let uu____7883 = FStar_BigInt.to_int_fs to_c  in
                 FStar_Range.mk_pos uu____7882 uu____7883  in
               FStar_Range.mk_range fn1 uu____7878 uu____7881  in
             let uu____7884 =
               FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_range
                 psc.psc_range r
                in
             FStar_Pervasives_Native.Some uu____7884
         | uu____7885 -> FStar_Pervasives_Native.None)
    | uu____7906 -> FStar_Pervasives_Native.None  in
  let decidable_eq neg psc args =
    let r = psc.psc_range  in
    let tru =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool true)) r
       in
    let fal =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool false)) r
       in
    match args with
    | (_typ,uu____7939)::(a1,uu____7941)::(a2,uu____7943)::[] ->
        let uu____7980 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____7980 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some (if neg then fal else tru)
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some (if neg then tru else fal)
         | uu____7985 -> FStar_Pervasives_Native.None)
    | uu____7986 -> failwith "Unexpected number of arguments"  in
  let prims_to_fstar_range_step psc args =
    match args with
    | (a1,uu____8017)::[] ->
        let uu____8026 =
          FStar_Syntax_Embeddings.try_unembed FStar_Syntax_Embeddings.e_range
            a1
           in
        (match uu____8026 with
         | FStar_Pervasives_Native.Some r ->
             let uu____8032 =
               FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_range
                 psc.psc_range r
                in
             FStar_Pervasives_Native.Some uu____8032
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
    | uu____8033 -> failwith "Unexpected number of arguments"  in
  let basic_ops =
    let uu____8059 =
      let uu____8076 =
        let uu____8093 =
          let uu____8110 =
            let uu____8127 =
              let uu____8144 =
                let uu____8161 =
                  let uu____8178 =
                    let uu____8195 =
                      let uu____8212 =
                        let uu____8229 =
                          let uu____8246 =
                            let uu____8263 =
                              let uu____8280 =
                                let uu____8297 =
                                  let uu____8314 =
                                    let uu____8331 =
                                      let uu____8348 =
                                        let uu____8365 =
                                          let uu____8382 =
                                            let uu____8399 =
                                              let uu____8416 =
                                                let uu____8431 =
                                                  FStar_Parser_Const.p2l
                                                    ["FStar";
                                                    "String";
                                                    "list_of_string"]
                                                   in
                                                (uu____8431,
                                                  (Prims.parse_int "1"),
                                                  (unary_op arg_as_string
                                                     list_of_string'))
                                                 in
                                              let uu____8440 =
                                                let uu____8457 =
                                                  let uu____8472 =
                                                    FStar_Parser_Const.p2l
                                                      ["FStar";
                                                      "String";
                                                      "string_of_list"]
                                                     in
                                                  (uu____8472,
                                                    (Prims.parse_int "1"),
                                                    (unary_op
                                                       (arg_as_list
                                                          FStar_Syntax_Embeddings.e_char)
                                                       string_of_list'))
                                                   in
                                                let uu____8485 =
                                                  let uu____8502 =
                                                    let uu____8517 =
                                                      FStar_Parser_Const.p2l
                                                        ["FStar";
                                                        "String";
                                                        "concat"]
                                                       in
                                                    (uu____8517,
                                                      (Prims.parse_int "2"),
                                                      string_concat')
                                                     in
                                                  let uu____8526 =
                                                    let uu____8543 =
                                                      let uu____8558 =
                                                        FStar_Parser_Const.p2l
                                                          ["Prims";
                                                          "mk_range"]
                                                         in
                                                      (uu____8558,
                                                        (Prims.parse_int "5"),
                                                        mk_range1)
                                                       in
                                                    [uu____8543]  in
                                                  uu____8502 :: uu____8526
                                                   in
                                                uu____8457 :: uu____8485  in
                                              uu____8416 :: uu____8440  in
                                            (FStar_Parser_Const.op_notEq,
                                              (Prims.parse_int "3"),
                                              (decidable_eq true)) ::
                                              uu____8399
                                             in
                                          (FStar_Parser_Const.op_Eq,
                                            (Prims.parse_int "3"),
                                            (decidable_eq false)) ::
                                            uu____8382
                                           in
                                        (FStar_Parser_Const.string_compare,
                                          (Prims.parse_int "2"),
                                          (binary_op arg_as_string
                                             string_compare'))
                                          :: uu____8365
                                         in
                                      (FStar_Parser_Const.string_of_bool_lid,
                                        (Prims.parse_int "1"),
                                        (unary_op arg_as_bool string_of_bool1))
                                        :: uu____8348
                                       in
                                    (FStar_Parser_Const.string_of_int_lid,
                                      (Prims.parse_int "1"),
                                      (unary_op arg_as_int string_of_int1))
                                      :: uu____8331
                                     in
                                  (FStar_Parser_Const.str_make_lid,
                                    (Prims.parse_int "2"),
                                    (mixed_binary_op arg_as_int arg_as_char
                                       (FStar_Syntax_Embeddings.embed
                                          FStar_Syntax_Embeddings.e_string)
                                       (fun r  ->
                                          fun x  ->
                                            fun y  ->
                                              let uu____8778 =
                                                FStar_BigInt.to_int_fs x  in
                                              FStar_String.make uu____8778 y)))
                                    :: uu____8314
                                   in
                                (FStar_Parser_Const.strcat_lid',
                                  (Prims.parse_int "2"),
                                  (binary_string_op
                                     (fun x  -> fun y  -> Prims.strcat x y)))
                                  :: uu____8297
                                 in
                              (FStar_Parser_Const.strcat_lid,
                                (Prims.parse_int "2"),
                                (binary_string_op
                                   (fun x  -> fun y  -> Prims.strcat x y)))
                                :: uu____8280
                               in
                            (FStar_Parser_Const.op_Or, (Prims.parse_int "2"),
                              (binary_bool_op (fun x  -> fun y  -> x || y)))
                              :: uu____8263
                             in
                          (FStar_Parser_Const.op_And, (Prims.parse_int "2"),
                            (binary_bool_op (fun x  -> fun y  -> x && y))) ::
                            uu____8246
                           in
                        (FStar_Parser_Const.op_Negation,
                          (Prims.parse_int "1"),
                          (unary_bool_op (fun x  -> Prims.op_Negation x))) ::
                          uu____8229
                         in
                      (FStar_Parser_Const.op_Modulus, (Prims.parse_int "2"),
                        (binary_int_op
                           (fun x  -> fun y  -> FStar_BigInt.mod_big_int x y)))
                        :: uu____8212
                       in
                    (FStar_Parser_Const.op_GTE, (Prims.parse_int "2"),
                      (binary_op arg_as_int
                         (fun r  ->
                            fun x  ->
                              fun y  ->
                                let uu____8973 = FStar_BigInt.ge_big_int x y
                                   in
                                FStar_Syntax_Embeddings.embed
                                  FStar_Syntax_Embeddings.e_bool r uu____8973)))
                      :: uu____8195
                     in
                  (FStar_Parser_Const.op_GT, (Prims.parse_int "2"),
                    (binary_op arg_as_int
                       (fun r  ->
                          fun x  ->
                            fun y  ->
                              let uu____9003 = FStar_BigInt.gt_big_int x y
                                 in
                              FStar_Syntax_Embeddings.embed
                                FStar_Syntax_Embeddings.e_bool r uu____9003)))
                    :: uu____8178
                   in
                (FStar_Parser_Const.op_LTE, (Prims.parse_int "2"),
                  (binary_op arg_as_int
                     (fun r  ->
                        fun x  ->
                          fun y  ->
                            let uu____9033 = FStar_BigInt.le_big_int x y  in
                            FStar_Syntax_Embeddings.embed
                              FStar_Syntax_Embeddings.e_bool r uu____9033)))
                  :: uu____8161
                 in
              (FStar_Parser_Const.op_LT, (Prims.parse_int "2"),
                (binary_op arg_as_int
                   (fun r  ->
                      fun x  ->
                        fun y  ->
                          let uu____9063 = FStar_BigInt.lt_big_int x y  in
                          FStar_Syntax_Embeddings.embed
                            FStar_Syntax_Embeddings.e_bool r uu____9063)))
                :: uu____8144
               in
            (FStar_Parser_Const.op_Division, (Prims.parse_int "2"),
              (binary_int_op
                 (fun x  -> fun y  -> FStar_BigInt.div_big_int x y)))
              :: uu____8127
             in
          (FStar_Parser_Const.op_Multiply, (Prims.parse_int "2"),
            (binary_int_op
               (fun x  -> fun y  -> FStar_BigInt.mult_big_int x y)))
            :: uu____8110
           in
        (FStar_Parser_Const.op_Subtraction, (Prims.parse_int "2"),
          (binary_int_op (fun x  -> fun y  -> FStar_BigInt.sub_big_int x y)))
          :: uu____8093
         in
      (FStar_Parser_Const.op_Addition, (Prims.parse_int "2"),
        (binary_int_op (fun x  -> fun y  -> FStar_BigInt.add_big_int x y)))
        :: uu____8076
       in
    (FStar_Parser_Const.op_Minus, (Prims.parse_int "1"),
      (unary_int_op (fun x  -> FStar_BigInt.minus_big_int x))) :: uu____8059
     in
  let weak_ops =
    let uu____9218 =
      let uu____9233 =
        FStar_Parser_Const.p2l ["FStar"; "Range"; "prims_to_fstar_range"]  in
      (uu____9233, (Prims.parse_int "1"), prims_to_fstar_range_step)  in
    [uu____9218]  in
  let bounded_arith_ops =
    let bounded_signed_int_types = ["Int8"; "Int16"; "Int32"; "Int64"]  in
    let bounded_unsigned_int_types =
      ["UInt8"; "UInt16"; "UInt32"; "UInt64"; "UInt128"]  in
    let int_as_bounded r int_to_t1 n1 =
      let c =
        FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_int r n1  in
      let int_to_t2 = FStar_Syntax_Syntax.fv_to_tm int_to_t1  in
      let uu____9313 =
        let uu____9318 =
          let uu____9319 = FStar_Syntax_Syntax.as_arg c  in [uu____9319]  in
        FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____9318  in
      uu____9313 FStar_Pervasives_Native.None r  in
    let add_sub_mul_v =
      FStar_All.pipe_right
        (FStar_List.append bounded_signed_int_types
           bounded_unsigned_int_types)
        (FStar_List.collect
           (fun m  ->
              let uu____9393 =
                let uu____9408 = FStar_Parser_Const.p2l ["FStar"; m; "add"]
                   in
                (uu____9408, (Prims.parse_int "2"),
                  (binary_op arg_as_bounded_int
                     (fun r  ->
                        fun uu____9430  ->
                          fun uu____9431  ->
                            match (uu____9430, uu____9431) with
                            | ((int_to_t1,x),(uu____9450,y)) ->
                                let uu____9460 = FStar_BigInt.add_big_int x y
                                   in
                                int_as_bounded r int_to_t1 uu____9460)))
                 in
              let uu____9461 =
                let uu____9478 =
                  let uu____9493 = FStar_Parser_Const.p2l ["FStar"; m; "sub"]
                     in
                  (uu____9493, (Prims.parse_int "2"),
                    (binary_op arg_as_bounded_int
                       (fun r  ->
                          fun uu____9515  ->
                            fun uu____9516  ->
                              match (uu____9515, uu____9516) with
                              | ((int_to_t1,x),(uu____9535,y)) ->
                                  let uu____9545 =
                                    FStar_BigInt.sub_big_int x y  in
                                  int_as_bounded r int_to_t1 uu____9545)))
                   in
                let uu____9546 =
                  let uu____9563 =
                    let uu____9578 =
                      FStar_Parser_Const.p2l ["FStar"; m; "mul"]  in
                    (uu____9578, (Prims.parse_int "2"),
                      (binary_op arg_as_bounded_int
                         (fun r  ->
                            fun uu____9600  ->
                              fun uu____9601  ->
                                match (uu____9600, uu____9601) with
                                | ((int_to_t1,x),(uu____9620,y)) ->
                                    let uu____9630 =
                                      FStar_BigInt.mult_big_int x y  in
                                    int_as_bounded r int_to_t1 uu____9630)))
                     in
                  let uu____9631 =
                    let uu____9648 =
                      let uu____9663 =
                        FStar_Parser_Const.p2l ["FStar"; m; "v"]  in
                      (uu____9663, (Prims.parse_int "1"),
                        (unary_op arg_as_bounded_int
                           (fun r  ->
                              fun uu____9681  ->
                                match uu____9681 with
                                | (int_to_t1,x) ->
                                    FStar_Syntax_Embeddings.embed
                                      FStar_Syntax_Embeddings.e_int r x)))
                       in
                    [uu____9648]  in
                  uu____9563 :: uu____9631  in
                uu____9478 :: uu____9546  in
              uu____9393 :: uu____9461))
       in
    let div_mod_unsigned =
      FStar_All.pipe_right bounded_unsigned_int_types
        (FStar_List.collect
           (fun m  ->
              let uu____9811 =
                let uu____9826 = FStar_Parser_Const.p2l ["FStar"; m; "div"]
                   in
                (uu____9826, (Prims.parse_int "2"),
                  (binary_op arg_as_bounded_int
                     (fun r  ->
                        fun uu____9848  ->
                          fun uu____9849  ->
                            match (uu____9848, uu____9849) with
                            | ((int_to_t1,x),(uu____9868,y)) ->
                                let uu____9878 = FStar_BigInt.div_big_int x y
                                   in
                                int_as_bounded r int_to_t1 uu____9878)))
                 in
              let uu____9879 =
                let uu____9896 =
                  let uu____9911 = FStar_Parser_Const.p2l ["FStar"; m; "rem"]
                     in
                  (uu____9911, (Prims.parse_int "2"),
                    (binary_op arg_as_bounded_int
                       (fun r  ->
                          fun uu____9933  ->
                            fun uu____9934  ->
                              match (uu____9933, uu____9934) with
                              | ((int_to_t1,x),(uu____9953,y)) ->
                                  let uu____9963 =
                                    FStar_BigInt.mod_big_int x y  in
                                  int_as_bounded r int_to_t1 uu____9963)))
                   in
                [uu____9896]  in
              uu____9811 :: uu____9879))
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
    | (_typ,uu____10093)::(a1,uu____10095)::(a2,uu____10097)::[] ->
        let uu____10134 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____10134 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___173_10138 = FStar_Syntax_Util.t_true  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___173_10138.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___173_10138.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___174_10140 = FStar_Syntax_Util.t_false  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___174_10140.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___174_10140.FStar_Syntax_Syntax.vars)
                })
         | uu____10141 -> FStar_Pervasives_Native.None)
    | (_typ,uu____10143)::uu____10144::(a1,uu____10146)::(a2,uu____10148)::[]
        ->
        let uu____10197 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____10197 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___173_10201 = FStar_Syntax_Util.t_true  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___173_10201.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___173_10201.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___174_10203 = FStar_Syntax_Util.t_false  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___174_10203.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___174_10203.FStar_Syntax_Syntax.vars)
                })
         | uu____10204 -> FStar_Pervasives_Native.None)
    | uu____10205 -> failwith "Unexpected number of arguments"  in
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
    let uu____10259 = FStar_ST.op_Bang unembed_binder_knot  in
    match uu____10259 with
    | FStar_Pervasives_Native.Some e -> FStar_Syntax_Embeddings.unembed e t
    | FStar_Pervasives_Native.None  ->
        (FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos
           (FStar_Errors.Warning_UnembedBinderKnot,
             "unembed_binder_knot is unset!");
         FStar_Pervasives_Native.None)
  
let mk_psc_subst :
  'Auu____10311 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____10311) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_Syntax_Syntax.subst_elt Prims.list
  =
  fun cfg  ->
    fun env  ->
      FStar_List.fold_right
        (fun uu____10373  ->
           fun subst1  ->
             match uu____10373 with
             | (binder_opt,closure) ->
                 (match (binder_opt, closure) with
                  | (FStar_Pervasives_Native.Some b,Clos
                     (env1,term,uu____10414,uu____10415)) ->
                      let uu____10474 = b  in
                      (match uu____10474 with
                       | (bv,uu____10482) ->
                           let uu____10483 =
                             let uu____10484 =
                               FStar_Syntax_Util.is_constructed_typ
                                 bv.FStar_Syntax_Syntax.sort
                                 FStar_Parser_Const.binder_lid
                                in
                             Prims.op_Negation uu____10484  in
                           if uu____10483
                           then subst1
                           else
                             (let term1 = closure_as_term cfg env1 term  in
                              let uu____10489 = unembed_binder term1  in
                              match uu____10489 with
                              | FStar_Pervasives_Native.None  -> subst1
                              | FStar_Pervasives_Native.Some x ->
                                  let b1 =
                                    let uu____10496 =
                                      let uu___175_10497 = bv  in
                                      let uu____10498 =
                                        FStar_Syntax_Subst.subst subst1
                                          (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort
                                         in
                                      {
                                        FStar_Syntax_Syntax.ppname =
                                          (uu___175_10497.FStar_Syntax_Syntax.ppname);
                                        FStar_Syntax_Syntax.index =
                                          (uu___175_10497.FStar_Syntax_Syntax.index);
                                        FStar_Syntax_Syntax.sort =
                                          uu____10498
                                      }  in
                                    FStar_Syntax_Syntax.freshen_bv
                                      uu____10496
                                     in
                                  let b_for_x =
                                    let uu____10502 =
                                      let uu____10509 =
                                        FStar_Syntax_Syntax.bv_to_name b1  in
                                      ((FStar_Pervasives_Native.fst x),
                                        uu____10509)
                                       in
                                    FStar_Syntax_Syntax.NT uu____10502  in
                                  let subst2 =
                                    FStar_List.filter
                                      (fun uu___115_10523  ->
                                         match uu___115_10523 with
                                         | FStar_Syntax_Syntax.NT
                                             (uu____10524,{
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_name
                                                              b';
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____10526;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____10527;_})
                                             ->
                                             let uu____10532 =
                                               FStar_Ident.ident_equals
                                                 b1.FStar_Syntax_Syntax.ppname
                                                 b'.FStar_Syntax_Syntax.ppname
                                                in
                                             Prims.op_Negation uu____10532
                                         | uu____10533 -> true) subst1
                                     in
                                  b_for_x :: subst2))
                  | uu____10534 -> subst1)) env []
  
let reduce_primops :
  'Auu____10557 'Auu____10558 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____10557) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____10558 ->
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
            (let uu____10606 = FStar_Syntax_Util.head_and_args tm  in
             match uu____10606 with
             | (head1,args) ->
                 let uu____10645 =
                   let uu____10646 = FStar_Syntax_Util.un_uinst head1  in
                   uu____10646.FStar_Syntax_Syntax.n  in
                 (match uu____10645 with
                  | FStar_Syntax_Syntax.Tm_fvar fv ->
                      let uu____10652 = find_prim_step cfg fv  in
                      (match uu____10652 with
                       | FStar_Pervasives_Native.Some prim_step when
                           prim_step.strong_reduction_ok ||
                             (Prims.op_Negation cfg.strong)
                           ->
                           let l = FStar_List.length args  in
                           if l < prim_step.arity
                           then
                             (log_primops cfg
                                (fun uu____10678  ->
                                   let uu____10679 =
                                     FStar_Syntax_Print.lid_to_string
                                       prim_step.name
                                      in
                                   let uu____10680 =
                                     FStar_Util.string_of_int l  in
                                   let uu____10687 =
                                     FStar_Util.string_of_int prim_step.arity
                                      in
                                   FStar_Util.print3
                                     "primop: found partially applied %s (%s/%s args)\n"
                                     uu____10679 uu____10680 uu____10687);
                              tm)
                           else
                             (let uu____10689 =
                                if l = prim_step.arity
                                then (args, [])
                                else FStar_List.splitAt prim_step.arity args
                                 in
                              match uu____10689 with
                              | (args_1,args_2) ->
                                  (log_primops cfg
                                     (fun uu____10803  ->
                                        let uu____10804 =
                                          FStar_Syntax_Print.term_to_string
                                            tm
                                           in
                                        FStar_Util.print1
                                          "primop: trying to reduce <%s>\n"
                                          uu____10804);
                                   (let psc =
                                      {
                                        psc_range =
                                          (head1.FStar_Syntax_Syntax.pos);
                                        psc_subst =
                                          (fun uu____10807  ->
                                             if
                                               prim_step.requires_binder_substitution
                                             then mk_psc_subst cfg env
                                             else [])
                                      }  in
                                    let uu____10809 =
                                      prim_step.interpretation psc args_1  in
                                    match uu____10809 with
                                    | FStar_Pervasives_Native.None  ->
                                        (log_primops cfg
                                           (fun uu____10817  ->
                                              let uu____10818 =
                                                FStar_Syntax_Print.term_to_string
                                                  tm
                                                 in
                                              FStar_Util.print1
                                                "primop: <%s> did not reduce\n"
                                                uu____10818);
                                         tm)
                                    | FStar_Pervasives_Native.Some reduced ->
                                        (log_primops cfg
                                           (fun uu____10824  ->
                                              let uu____10825 =
                                                FStar_Syntax_Print.term_to_string
                                                  tm
                                                 in
                                              let uu____10826 =
                                                FStar_Syntax_Print.term_to_string
                                                  reduced
                                                 in
                                              FStar_Util.print2
                                                "primop: <%s> reduced to <%s>\n"
                                                uu____10825 uu____10826);
                                         FStar_Syntax_Util.mk_app reduced
                                           args_2))))
                       | FStar_Pervasives_Native.Some uu____10827 ->
                           (log_primops cfg
                              (fun uu____10831  ->
                                 let uu____10832 =
                                   FStar_Syntax_Print.term_to_string tm  in
                                 FStar_Util.print1
                                   "primop: not reducing <%s> since we're doing strong reduction\n"
                                   uu____10832);
                            tm)
                       | FStar_Pervasives_Native.None  -> tm)
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_range_of ) when
                      Prims.op_Negation cfg.strong ->
                      (log_primops cfg
                         (fun uu____10836  ->
                            let uu____10837 =
                              FStar_Syntax_Print.term_to_string tm  in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____10837);
                       (match args with
                        | (a1,uu____10841)::[] ->
                            FStar_Syntax_Embeddings.embed
                              FStar_Syntax_Embeddings.e_range
                              tm.FStar_Syntax_Syntax.pos
                              a1.FStar_Syntax_Syntax.pos
                        | uu____10858 -> tm))
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_set_range_of ) when
                      Prims.op_Negation cfg.strong ->
                      (log_primops cfg
                         (fun uu____10870  ->
                            let uu____10871 =
                              FStar_Syntax_Print.term_to_string tm  in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____10871);
                       (match args with
                        | (t,uu____10875)::(r,uu____10877)::[] ->
                            let uu____10904 =
                              FStar_Syntax_Embeddings.unembed
                                FStar_Syntax_Embeddings.e_range r
                               in
                            (match uu____10904 with
                             | FStar_Pervasives_Native.Some rng ->
                                 let uu___176_10910 = t  in
                                 {
                                   FStar_Syntax_Syntax.n =
                                     (uu___176_10910.FStar_Syntax_Syntax.n);
                                   FStar_Syntax_Syntax.pos = rng;
                                   FStar_Syntax_Syntax.vars =
                                     (uu___176_10910.FStar_Syntax_Syntax.vars)
                                 }
                             | FStar_Pervasives_Native.None  -> tm)
                        | uu____10913 -> tm))
                  | uu____10922 -> tm))
  
let reduce_equality :
  'Auu____10933 'Auu____10934 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____10933) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____10934 ->
          FStar_Syntax_Syntax.term ->
            FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun cfg  ->
    fun tm  ->
      reduce_primops
        (let uu___177_10980 = cfg  in
         {
           steps =
             (let uu___178_10983 = default_steps  in
              {
                beta = (uu___178_10983.beta);
                iota = (uu___178_10983.iota);
                zeta = (uu___178_10983.zeta);
                weak = (uu___178_10983.weak);
                hnf = (uu___178_10983.hnf);
                primops = true;
                do_not_unfold_pure_lets =
                  (uu___178_10983.do_not_unfold_pure_lets);
                unfold_until = (uu___178_10983.unfold_until);
                unfold_only = (uu___178_10983.unfold_only);
                unfold_fully = (uu___178_10983.unfold_fully);
                unfold_attr = (uu___178_10983.unfold_attr);
                unfold_tac = (uu___178_10983.unfold_tac);
                pure_subterms_within_computations =
                  (uu___178_10983.pure_subterms_within_computations);
                simplify = (uu___178_10983.simplify);
                erase_universes = (uu___178_10983.erase_universes);
                allow_unbound_universes =
                  (uu___178_10983.allow_unbound_universes);
                reify_ = (uu___178_10983.reify_);
                compress_uvars = (uu___178_10983.compress_uvars);
                no_full_norm = (uu___178_10983.no_full_norm);
                check_no_uvars = (uu___178_10983.check_no_uvars);
                unmeta = (uu___178_10983.unmeta);
                unascribe = (uu___178_10983.unascribe);
                in_full_norm_request = (uu___178_10983.in_full_norm_request);
                weakly_reduce_scrutinee =
                  (uu___178_10983.weakly_reduce_scrutinee)
              });
           tcenv = (uu___177_10980.tcenv);
           debug = (uu___177_10980.debug);
           delta_level = (uu___177_10980.delta_level);
           primitive_steps = equality_ops;
           strong = (uu___177_10980.strong);
           memoize_lazy = (uu___177_10980.memoize_lazy);
           normalize_pure_lets = (uu___177_10980.normalize_pure_lets)
         }) tm
  
let is_norm_request :
  'Auu____10990 .
    FStar_Syntax_Syntax.term -> 'Auu____10990 Prims.list -> Prims.bool
  =
  fun hd1  ->
    fun args  ->
      let uu____11005 =
        let uu____11012 =
          let uu____11013 = FStar_Syntax_Util.un_uinst hd1  in
          uu____11013.FStar_Syntax_Syntax.n  in
        (uu____11012, args)  in
      match uu____11005 with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____11019::uu____11020::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____11024::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize
      | (FStar_Syntax_Syntax.Tm_fvar fv,steps::uu____11029::uu____11030::[])
          -> FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm
      | uu____11033 -> false
  
let (tr_norm_step : FStar_Syntax_Embeddings.norm_step -> step Prims.list) =
  fun uu___116_11046  ->
    match uu___116_11046 with
    | FStar_Syntax_Embeddings.Zeta  -> [Zeta]
    | FStar_Syntax_Embeddings.Iota  -> [Iota]
    | FStar_Syntax_Embeddings.Delta  ->
        [UnfoldUntil FStar_Syntax_Syntax.delta_constant]
    | FStar_Syntax_Embeddings.Simpl  -> [Simplify]
    | FStar_Syntax_Embeddings.Weak  -> [Weak]
    | FStar_Syntax_Embeddings.HNF  -> [HNF]
    | FStar_Syntax_Embeddings.Primops  -> [Primops]
    | FStar_Syntax_Embeddings.UnfoldOnly names1 ->
        let uu____11052 =
          let uu____11055 =
            let uu____11056 = FStar_List.map FStar_Ident.lid_of_str names1
               in
            UnfoldOnly uu____11056  in
          [uu____11055]  in
        (UnfoldUntil FStar_Syntax_Syntax.delta_constant) :: uu____11052
    | FStar_Syntax_Embeddings.UnfoldFully names1 ->
        let uu____11062 =
          let uu____11065 =
            let uu____11066 = FStar_List.map FStar_Ident.lid_of_str names1
               in
            UnfoldFully uu____11066  in
          [uu____11065]  in
        (UnfoldUntil FStar_Syntax_Syntax.delta_constant) :: uu____11062
    | FStar_Syntax_Embeddings.UnfoldAttr t ->
        [UnfoldUntil FStar_Syntax_Syntax.delta_constant; UnfoldAttr t]
  
let (tr_norm_steps :
  FStar_Syntax_Embeddings.norm_step Prims.list -> step Prims.list) =
  fun s  -> FStar_List.concatMap tr_norm_step s 
let get_norm_request :
  'Auu____11087 .
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
      (FStar_Syntax_Syntax.term,'Auu____11087) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (step Prims.list,FStar_Syntax_Syntax.term)
          FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun full_norm  ->
    fun args  ->
      let parse_steps s =
        let uu____11133 =
          let uu____11138 =
            FStar_Syntax_Embeddings.e_list
              FStar_Syntax_Embeddings.e_norm_step
             in
          FStar_Syntax_Embeddings.try_unembed uu____11138 s  in
        match uu____11133 with
        | FStar_Pervasives_Native.Some steps ->
            let uu____11154 = tr_norm_steps steps  in
            FStar_Pervasives_Native.Some uu____11154
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None  in
      match args with
      | uu____11171::(tm,uu____11173)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.delta_constant;
            Reify]  in
          FStar_Pervasives_Native.Some (s, tm)
      | (tm,uu____11202)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.delta_constant;
            Reify]  in
          FStar_Pervasives_Native.Some (s, tm)
      | (steps,uu____11223)::uu____11224::(tm,uu____11226)::[] ->
          let add_exclude s z =
            if FStar_List.contains z s then s else (Exclude z) :: s  in
          let uu____11267 =
            let uu____11272 = full_norm steps  in parse_steps uu____11272  in
          (match uu____11267 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some s ->
               let s1 = Beta :: s  in
               let s2 = add_exclude s1 Zeta  in
               let s3 = add_exclude s2 Iota  in
               FStar_Pervasives_Native.Some (s3, tm))
      | uu____11311 -> FStar_Pervasives_Native.None
  
let (is_reify_head : stack_elt Prims.list -> Prims.bool) =
  fun uu___117_11330  ->
    match uu___117_11330 with
    | (App
        (uu____11333,{
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reify );
                       FStar_Syntax_Syntax.pos = uu____11334;
                       FStar_Syntax_Syntax.vars = uu____11335;_},uu____11336,uu____11337))::uu____11338
        -> true
    | uu____11343 -> false
  
let firstn :
  'Auu____11352 .
    Prims.int ->
      'Auu____11352 Prims.list ->
        ('Auu____11352 Prims.list,'Auu____11352 Prims.list)
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
          (uu____11394,{
                         FStar_Syntax_Syntax.n =
                           FStar_Syntax_Syntax.Tm_constant
                           (FStar_Const.Const_reify );
                         FStar_Syntax_Syntax.pos = uu____11395;
                         FStar_Syntax_Syntax.vars = uu____11396;_},uu____11397,uu____11398))::uu____11399
          -> (cfg.steps).reify_
      | uu____11404 -> false
  
let rec (maybe_weakly_reduced :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun tm  ->
    let aux_comp c =
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.GTotal (t,uu____11427) -> maybe_weakly_reduced t
      | FStar_Syntax_Syntax.Total (t,uu____11437) -> maybe_weakly_reduced t
      | FStar_Syntax_Syntax.Comp ct ->
          (maybe_weakly_reduced ct.FStar_Syntax_Syntax.result_typ) ||
            (FStar_Util.for_some
               (fun uu____11456  ->
                  match uu____11456 with
                  | (a,uu____11464) -> maybe_weakly_reduced a)
               ct.FStar_Syntax_Syntax.effect_args)
       in
    let t = FStar_Syntax_Subst.compress tm  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____11470 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_name uu____11495 -> false
    | FStar_Syntax_Syntax.Tm_uvar uu____11496 -> false
    | FStar_Syntax_Syntax.Tm_type uu____11503 -> false
    | FStar_Syntax_Syntax.Tm_bvar uu____11504 -> false
    | FStar_Syntax_Syntax.Tm_fvar uu____11505 -> false
    | FStar_Syntax_Syntax.Tm_constant uu____11506 -> false
    | FStar_Syntax_Syntax.Tm_lazy uu____11507 -> false
    | FStar_Syntax_Syntax.Tm_unknown  -> false
    | FStar_Syntax_Syntax.Tm_uinst uu____11508 -> false
    | FStar_Syntax_Syntax.Tm_quoted uu____11515 -> false
    | FStar_Syntax_Syntax.Tm_let uu____11522 -> true
    | FStar_Syntax_Syntax.Tm_abs uu____11535 -> true
    | FStar_Syntax_Syntax.Tm_arrow uu____11552 -> true
    | FStar_Syntax_Syntax.Tm_refine uu____11565 -> true
    | FStar_Syntax_Syntax.Tm_match uu____11572 -> true
    | FStar_Syntax_Syntax.Tm_app (t1,args) ->
        (maybe_weakly_reduced t1) ||
          (FStar_All.pipe_right args
             (FStar_Util.for_some
                (fun uu____11634  ->
                   match uu____11634 with
                   | (a,uu____11642) -> maybe_weakly_reduced a)))
    | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,uu____11649) ->
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
                     (fun uu____11771  ->
                        match uu____11771 with
                        | (a,uu____11779) -> maybe_weakly_reduced a)) args
            | FStar_Syntax_Syntax.Meta_monadic_lift
                (uu____11784,uu____11785,t') -> maybe_weakly_reduced t'
            | FStar_Syntax_Syntax.Meta_monadic (uu____11791,t') ->
                maybe_weakly_reduced t'
            | FStar_Syntax_Syntax.Meta_labeled uu____11797 -> false
            | FStar_Syntax_Syntax.Meta_desugared uu____11804 -> false
            | FStar_Syntax_Syntax.Meta_named uu____11805 -> false))
  
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
               | FStar_Syntax_Syntax.Tm_delayed uu____12097 ->
                   let uu____12122 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print1 "NORM delayed: %s\n" uu____12122
               | uu____12123 -> ())
            else ();
            FStar_Syntax_Subst.compress t  in
          log cfg
            (fun uu____12131  ->
               let uu____12132 = FStar_Syntax_Print.tag_of_term t1  in
               let uu____12133 = FStar_Syntax_Print.term_to_string t1  in
               let uu____12134 =
                 FStar_Util.string_of_int (FStar_List.length env)  in
               let uu____12141 =
                 let uu____12142 =
                   let uu____12145 = firstn (Prims.parse_int "4") stack  in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____12145
                    in
                 stack_to_string uu____12142  in
               FStar_Util.print4
                 ">>> %s\nNorm %s with with %s env elements top of the stack %s \n"
                 uu____12132 uu____12133 uu____12134 uu____12141);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_constant uu____12168 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_name uu____12169 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_lazy uu____12170 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____12171;
                 FStar_Syntax_Syntax.fv_delta =
                   FStar_Syntax_Syntax.Delta_constant_at_level _0_18;
                 FStar_Syntax_Syntax.fv_qual = uu____12172;_}
               when _0_18 = (Prims.parse_int "0") -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____12175;
                 FStar_Syntax_Syntax.fv_delta = uu____12176;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Data_ctor );_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____12177;
                 FStar_Syntax_Syntax.fv_delta = uu____12178;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor uu____12179);_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_quoted uu____12186 ->
               let uu____12193 = closure_as_term cfg env t1  in
               rebuild cfg env stack uu____12193
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               ((Prims.op_Negation (cfg.steps).no_full_norm) &&
                  (is_norm_request hd1 args))
                 &&
                 (let uu____12223 =
                    FStar_Ident.lid_equals
                      (cfg.tcenv).FStar_TypeChecker_Env.curmodule
                      FStar_Parser_Const.prims_lid
                     in
                  Prims.op_Negation uu____12223)
               ->
               let cfg' =
                 let uu___179_12225 = cfg  in
                 {
                   steps =
                     (let uu___180_12228 = cfg.steps  in
                      {
                        beta = (uu___180_12228.beta);
                        iota = (uu___180_12228.iota);
                        zeta = (uu___180_12228.zeta);
                        weak = (uu___180_12228.weak);
                        hnf = (uu___180_12228.hnf);
                        primops = (uu___180_12228.primops);
                        do_not_unfold_pure_lets = false;
                        unfold_until = (uu___180_12228.unfold_until);
                        unfold_only = FStar_Pervasives_Native.None;
                        unfold_fully = FStar_Pervasives_Native.None;
                        unfold_attr = (uu___180_12228.unfold_attr);
                        unfold_tac = (uu___180_12228.unfold_tac);
                        pure_subterms_within_computations =
                          (uu___180_12228.pure_subterms_within_computations);
                        simplify = (uu___180_12228.simplify);
                        erase_universes = (uu___180_12228.erase_universes);
                        allow_unbound_universes =
                          (uu___180_12228.allow_unbound_universes);
                        reify_ = (uu___180_12228.reify_);
                        compress_uvars = (uu___180_12228.compress_uvars);
                        no_full_norm = (uu___180_12228.no_full_norm);
                        check_no_uvars = (uu___180_12228.check_no_uvars);
                        unmeta = (uu___180_12228.unmeta);
                        unascribe = (uu___180_12228.unascribe);
                        in_full_norm_request =
                          (uu___180_12228.in_full_norm_request);
                        weakly_reduce_scrutinee =
                          (uu___180_12228.weakly_reduce_scrutinee)
                      });
                   tcenv = (uu___179_12225.tcenv);
                   debug = (uu___179_12225.debug);
                   delta_level =
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.delta_constant];
                   primitive_steps = (uu___179_12225.primitive_steps);
                   strong = (uu___179_12225.strong);
                   memoize_lazy = (uu___179_12225.memoize_lazy);
                   normalize_pure_lets = true
                 }  in
               let uu____12233 = get_norm_request (norm cfg' env []) args  in
               (match uu____12233 with
                | FStar_Pervasives_Native.None  ->
                    let stack1 =
                      FStar_All.pipe_right stack
                        (FStar_List.fold_right
                           (fun uu____12262  ->
                              fun stack1  ->
                                match uu____12262 with
                                | (a,aq) ->
                                    let uu____12274 =
                                      let uu____12275 =
                                        let uu____12282 =
                                          let uu____12283 =
                                            let uu____12314 =
                                              FStar_Util.mk_ref
                                                FStar_Pervasives_Native.None
                                               in
                                            (env, a, uu____12314, false)  in
                                          Clos uu____12283  in
                                        (uu____12282, aq,
                                          (t1.FStar_Syntax_Syntax.pos))
                                         in
                                      Arg uu____12275  in
                                    uu____12274 :: stack1) args)
                       in
                    (log cfg
                       (fun uu____12402  ->
                          let uu____12403 =
                            FStar_All.pipe_left FStar_Util.string_of_int
                              (FStar_List.length args)
                             in
                          FStar_Util.print1 "\tPushed %s arguments\n"
                            uu____12403);
                     norm cfg env stack1 hd1)
                | FStar_Pervasives_Native.Some (s,tm) ->
                    let delta_level =
                      let uu____12425 =
                        FStar_All.pipe_right s
                          (FStar_Util.for_some
                             (fun uu___118_12430  ->
                                match uu___118_12430 with
                                | UnfoldUntil uu____12431 -> true
                                | UnfoldOnly uu____12432 -> true
                                | UnfoldFully uu____12435 -> true
                                | uu____12438 -> false))
                         in
                      if uu____12425
                      then
                        [FStar_TypeChecker_Env.Unfold
                           FStar_Syntax_Syntax.delta_constant]
                      else [FStar_TypeChecker_Env.NoDelta]  in
                    let cfg'1 =
                      let uu___181_12443 = cfg  in
                      let uu____12444 =
                        let uu___182_12445 = to_fsteps s  in
                        {
                          beta = (uu___182_12445.beta);
                          iota = (uu___182_12445.iota);
                          zeta = (uu___182_12445.zeta);
                          weak = (uu___182_12445.weak);
                          hnf = (uu___182_12445.hnf);
                          primops = (uu___182_12445.primops);
                          do_not_unfold_pure_lets =
                            (uu___182_12445.do_not_unfold_pure_lets);
                          unfold_until = (uu___182_12445.unfold_until);
                          unfold_only = (uu___182_12445.unfold_only);
                          unfold_fully = (uu___182_12445.unfold_fully);
                          unfold_attr = (uu___182_12445.unfold_attr);
                          unfold_tac = (uu___182_12445.unfold_tac);
                          pure_subterms_within_computations =
                            (uu___182_12445.pure_subterms_within_computations);
                          simplify = (uu___182_12445.simplify);
                          erase_universes = (uu___182_12445.erase_universes);
                          allow_unbound_universes =
                            (uu___182_12445.allow_unbound_universes);
                          reify_ = (uu___182_12445.reify_);
                          compress_uvars = (uu___182_12445.compress_uvars);
                          no_full_norm = (uu___182_12445.no_full_norm);
                          check_no_uvars = (uu___182_12445.check_no_uvars);
                          unmeta = (uu___182_12445.unmeta);
                          unascribe = (uu___182_12445.unascribe);
                          in_full_norm_request = true;
                          weakly_reduce_scrutinee =
                            (uu___182_12445.weakly_reduce_scrutinee)
                        }  in
                      {
                        steps = uu____12444;
                        tcenv = (uu___181_12443.tcenv);
                        debug = (uu___181_12443.debug);
                        delta_level;
                        primitive_steps = (uu___181_12443.primitive_steps);
                        strong = (uu___181_12443.strong);
                        memoize_lazy = (uu___181_12443.memoize_lazy);
                        normalize_pure_lets = true
                      }  in
                    let stack' =
                      let tail1 = (Cfg cfg) :: stack  in
                      if (cfg.debug).print_normalized
                      then
                        let uu____12454 =
                          let uu____12455 =
                            let uu____12460 = FStar_Util.now ()  in
                            (t1, uu____12460)  in
                          Debug uu____12455  in
                        uu____12454 :: tail1
                      else tail1  in
                    norm cfg'1 env stack' tm)
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u  in
               let uu____12464 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack uu____12464
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               if (cfg.steps).erase_universes
               then norm cfg env stack t'
               else
                 (let us1 =
                    let uu____12473 =
                      let uu____12480 =
                        FStar_List.map (norm_universe cfg env) us  in
                      (uu____12480, (t1.FStar_Syntax_Syntax.pos))  in
                    UnivArgs uu____12473  in
                  let stack1 = us1 :: stack  in norm cfg env stack1 t')
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let qninfo =
                 let uu____12490 = FStar_Syntax_Syntax.lid_of_fv fv  in
                 FStar_TypeChecker_Env.lookup_qname cfg.tcenv uu____12490  in
               let uu____12491 =
                 FStar_TypeChecker_Env.qninfo_is_action qninfo  in
               if uu____12491
               then
                 let b = should_reify cfg stack  in
                 (log cfg
                    (fun uu____12497  ->
                       let uu____12498 = FStar_Syntax_Print.term_to_string t1
                          in
                       let uu____12499 = FStar_Util.string_of_bool b  in
                       FStar_Util.print2
                         ">>> For DM4F action %s, should_reify = %s\n"
                         uu____12498 uu____12499);
                  if b
                  then
                    (let uu____12500 = FStar_List.tl stack  in
                     do_unfold_fv cfg env uu____12500 t1 qninfo fv)
                  else rebuild cfg env stack t1)
               else
                 (let should_delta =
                    ((let uu____12508 = find_prim_step cfg fv  in
                      FStar_Option.isNone uu____12508) &&
                       (match qninfo with
                        | FStar_Pervasives_Native.Some
                            (FStar_Util.Inr
                             ({
                                FStar_Syntax_Syntax.sigel =
                                  FStar_Syntax_Syntax.Sig_let
                                  ((is_rec,uu____12521),uu____12522);
                                FStar_Syntax_Syntax.sigrng = uu____12523;
                                FStar_Syntax_Syntax.sigquals = qs;
                                FStar_Syntax_Syntax.sigmeta = uu____12525;
                                FStar_Syntax_Syntax.sigattrs = uu____12526;_},uu____12527),uu____12528)
                            ->
                            (Prims.op_Negation
                               (FStar_List.contains
                                  FStar_Syntax_Syntax.HasMaskedEffect qs))
                              &&
                              ((Prims.op_Negation is_rec) || (cfg.steps).zeta)
                        | uu____12587 -> true))
                      &&
                      (FStar_All.pipe_right cfg.delta_level
                         (FStar_Util.for_some
                            (fun uu___119_12591  ->
                               match uu___119_12591 with
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
                          (let uu____12601 =
                             cases
                               (FStar_Util.for_some
                                  (FStar_Syntax_Util.attr_eq
                                     FStar_Syntax_Util.tac_opaque_attr))
                               false attrs
                              in
                           Prims.op_Negation uu____12601))
                         &&
                         ((match (cfg.steps).unfold_only with
                           | FStar_Pervasives_Native.None  -> true
                           | FStar_Pervasives_Native.Some lids ->
                               FStar_Util.for_some
                                 (FStar_Syntax_Syntax.fv_eq_lid fv) lids)
                            ||
                            (match (attrs, ((cfg.steps).unfold_attr)) with
                             | (FStar_Pervasives_Native.None
                                ,FStar_Pervasives_Native.Some uu____12620) ->
                                 false
                             | (FStar_Pervasives_Native.Some
                                ats,FStar_Pervasives_Native.Some ats') ->
                                 FStar_Util.for_some
                                   (fun at  ->
                                      FStar_Util.for_some
                                        (FStar_Syntax_Util.attr_eq at) ats')
                                   ats
                             | (uu____12655,uu____12656) -> false)))
                     in
                  let uu____12673 =
                    match (cfg.steps).unfold_fully with
                    | FStar_Pervasives_Native.None  -> (should_delta1, false)
                    | FStar_Pervasives_Native.Some lids ->
                        let uu____12689 =
                          FStar_Util.for_some
                            (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                           in
                        if uu____12689 then (true, true) else (false, false)
                     in
                  match uu____12673 with
                  | (should_delta2,fully) ->
                      (log cfg
                         (fun uu____12702  ->
                            let uu____12703 =
                              FStar_Syntax_Print.term_to_string t1  in
                            let uu____12704 =
                              FStar_Range.string_of_range
                                t1.FStar_Syntax_Syntax.pos
                               in
                            let uu____12705 =
                              FStar_Util.string_of_bool should_delta2  in
                            FStar_Util.print3
                              ">>> For %s (%s), should_delta = %s\n"
                              uu____12703 uu____12704 uu____12705);
                       if should_delta2
                       then
                         (let uu____12706 =
                            if fully
                            then
                              (((Cfg cfg) :: stack),
                                (let uu___183_12716 = cfg  in
                                 {
                                   steps =
                                     (let uu___184_12719 = cfg.steps  in
                                      {
                                        beta = (uu___184_12719.beta);
                                        iota = false;
                                        zeta = false;
                                        weak = false;
                                        hnf = false;
                                        primops = false;
                                        do_not_unfold_pure_lets =
                                          (uu___184_12719.do_not_unfold_pure_lets);
                                        unfold_until =
                                          (FStar_Pervasives_Native.Some
                                             FStar_Syntax_Syntax.delta_constant);
                                        unfold_only =
                                          FStar_Pervasives_Native.None;
                                        unfold_fully =
                                          FStar_Pervasives_Native.None;
                                        unfold_attr =
                                          (uu___184_12719.unfold_attr);
                                        unfold_tac =
                                          (uu___184_12719.unfold_tac);
                                        pure_subterms_within_computations =
                                          (uu___184_12719.pure_subterms_within_computations);
                                        simplify = false;
                                        erase_universes =
                                          (uu___184_12719.erase_universes);
                                        allow_unbound_universes =
                                          (uu___184_12719.allow_unbound_universes);
                                        reify_ = (uu___184_12719.reify_);
                                        compress_uvars =
                                          (uu___184_12719.compress_uvars);
                                        no_full_norm =
                                          (uu___184_12719.no_full_norm);
                                        check_no_uvars =
                                          (uu___184_12719.check_no_uvars);
                                        unmeta = (uu___184_12719.unmeta);
                                        unascribe =
                                          (uu___184_12719.unascribe);
                                        in_full_norm_request =
                                          (uu___184_12719.in_full_norm_request);
                                        weakly_reduce_scrutinee =
                                          (uu___184_12719.weakly_reduce_scrutinee)
                                      });
                                   tcenv = (uu___183_12716.tcenv);
                                   debug = (uu___183_12716.debug);
                                   delta_level = (uu___183_12716.delta_level);
                                   primitive_steps =
                                     (uu___183_12716.primitive_steps);
                                   strong = (uu___183_12716.strong);
                                   memoize_lazy =
                                     (uu___183_12716.memoize_lazy);
                                   normalize_pure_lets =
                                     (uu___183_12716.normalize_pure_lets)
                                 }))
                            else (stack, cfg)  in
                          match uu____12706 with
                          | (stack1,cfg1) ->
                              do_unfold_fv cfg1 env stack1 t1 qninfo fv)
                       else rebuild cfg env stack t1))
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____12729 = lookup_bvar env x  in
               (match uu____12729 with
                | Univ uu____12730 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if (Prims.op_Negation fix) || (cfg.steps).zeta
                    then
                      let uu____12779 = FStar_ST.op_Bang r  in
                      (match uu____12779 with
                       | FStar_Pervasives_Native.Some (env2,t') ->
                           (log cfg
                              (fun uu____12901  ->
                                 let uu____12902 =
                                   FStar_Syntax_Print.term_to_string t1  in
                                 let uu____12903 =
                                   FStar_Syntax_Print.term_to_string t'  in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____12902
                                   uu____12903);
                            (let uu____12904 = maybe_weakly_reduced t'  in
                             if uu____12904
                             then
                               match stack with
                               | [] when
                                   (cfg.steps).weak ||
                                     (cfg.steps).compress_uvars
                                   -> rebuild cfg env2 stack t'
                               | uu____12905 -> norm cfg env2 stack t'
                             else rebuild cfg env2 stack t'))
                       | FStar_Pervasives_Native.None  ->
                           norm cfg env1 ((MemoLazy r) :: stack) t0)
                    else norm cfg env1 stack t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack with
                | (UnivArgs uu____12976)::uu____12977 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Match uu____12986)::uu____12987 ->
                    failwith
                      "Ill-typed term: cannot pattern match an abstraction"
                | (Arg (c,uu____12999,uu____13000))::stack_rest ->
                    (match c with
                     | Univ uu____13004 ->
                         norm cfg ((FStar_Pervasives_Native.None, c) :: env)
                           stack_rest t1
                     | uu____13013 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | b::[] ->
                              (log cfg
                                 (fun uu____13034  ->
                                    let uu____13035 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____13035);
                               norm cfg
                                 (((FStar_Pervasives_Native.Some b), c) ::
                                 env) stack_rest body)
                          | b::tl1 ->
                              (log cfg
                                 (fun uu____13063  ->
                                    let uu____13064 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____13064);
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
                       (fun uu____13130  ->
                          let uu____13131 =
                            FStar_Syntax_Print.term_to_string t1  in
                          FStar_Util.print1 "\tSet memo %s\n" uu____13131);
                     norm cfg env stack1 t1)
                | (Debug uu____13132)::uu____13133 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___185_13143 = cfg.steps  in
                             {
                               beta = (uu___185_13143.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___185_13143.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___185_13143.unfold_until);
                               unfold_only = (uu___185_13143.unfold_only);
                               unfold_fully = (uu___185_13143.unfold_fully);
                               unfold_attr = (uu___185_13143.unfold_attr);
                               unfold_tac = (uu___185_13143.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___185_13143.erase_universes);
                               allow_unbound_universes =
                                 (uu___185_13143.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___185_13143.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___185_13143.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___185_13143.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___185_13143.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___186_13145 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___186_13145.tcenv);
                               debug = (uu___186_13145.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___186_13145.primitive_steps);
                               strong = (uu___186_13145.strong);
                               memoize_lazy = (uu___186_13145.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___186_13145.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____13147 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____13147 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____13179  -> dummy :: env1) env)
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
                                          let uu____13220 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____13220)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___187_13225 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___187_13225.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___187_13225.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____13226 -> lopt  in
                           (log cfg
                              (fun uu____13232  ->
                                 let uu____13233 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____13233);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___188_13242 = cfg  in
                               {
                                 steps = (uu___188_13242.steps);
                                 tcenv = (uu___188_13242.tcenv);
                                 debug = (uu___188_13242.debug);
                                 delta_level = (uu___188_13242.delta_level);
                                 primitive_steps =
                                   (uu___188_13242.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___188_13242.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___188_13242.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Meta uu____13245)::uu____13246 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___185_13258 = cfg.steps  in
                             {
                               beta = (uu___185_13258.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___185_13258.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___185_13258.unfold_until);
                               unfold_only = (uu___185_13258.unfold_only);
                               unfold_fully = (uu___185_13258.unfold_fully);
                               unfold_attr = (uu___185_13258.unfold_attr);
                               unfold_tac = (uu___185_13258.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___185_13258.erase_universes);
                               allow_unbound_universes =
                                 (uu___185_13258.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___185_13258.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___185_13258.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___185_13258.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___185_13258.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___186_13260 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___186_13260.tcenv);
                               debug = (uu___186_13260.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___186_13260.primitive_steps);
                               strong = (uu___186_13260.strong);
                               memoize_lazy = (uu___186_13260.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___186_13260.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____13262 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____13262 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____13294  -> dummy :: env1) env)
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
                                          let uu____13335 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____13335)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___187_13340 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___187_13340.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___187_13340.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____13341 -> lopt  in
                           (log cfg
                              (fun uu____13347  ->
                                 let uu____13348 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____13348);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___188_13357 = cfg  in
                               {
                                 steps = (uu___188_13357.steps);
                                 tcenv = (uu___188_13357.tcenv);
                                 debug = (uu___188_13357.debug);
                                 delta_level = (uu___188_13357.delta_level);
                                 primitive_steps =
                                   (uu___188_13357.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___188_13357.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___188_13357.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Let uu____13360)::uu____13361 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___185_13375 = cfg.steps  in
                             {
                               beta = (uu___185_13375.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___185_13375.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___185_13375.unfold_until);
                               unfold_only = (uu___185_13375.unfold_only);
                               unfold_fully = (uu___185_13375.unfold_fully);
                               unfold_attr = (uu___185_13375.unfold_attr);
                               unfold_tac = (uu___185_13375.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___185_13375.erase_universes);
                               allow_unbound_universes =
                                 (uu___185_13375.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___185_13375.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___185_13375.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___185_13375.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___185_13375.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___186_13377 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___186_13377.tcenv);
                               debug = (uu___186_13377.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___186_13377.primitive_steps);
                               strong = (uu___186_13377.strong);
                               memoize_lazy = (uu___186_13377.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___186_13377.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____13379 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____13379 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____13411  -> dummy :: env1) env)
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
                                          let uu____13452 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____13452)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___187_13457 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___187_13457.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___187_13457.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____13458 -> lopt  in
                           (log cfg
                              (fun uu____13464  ->
                                 let uu____13465 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____13465);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___188_13474 = cfg  in
                               {
                                 steps = (uu___188_13474.steps);
                                 tcenv = (uu___188_13474.tcenv);
                                 debug = (uu___188_13474.debug);
                                 delta_level = (uu___188_13474.delta_level);
                                 primitive_steps =
                                   (uu___188_13474.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___188_13474.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___188_13474.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (App uu____13477)::uu____13478 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___185_13492 = cfg.steps  in
                             {
                               beta = (uu___185_13492.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___185_13492.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___185_13492.unfold_until);
                               unfold_only = (uu___185_13492.unfold_only);
                               unfold_fully = (uu___185_13492.unfold_fully);
                               unfold_attr = (uu___185_13492.unfold_attr);
                               unfold_tac = (uu___185_13492.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___185_13492.erase_universes);
                               allow_unbound_universes =
                                 (uu___185_13492.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___185_13492.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___185_13492.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___185_13492.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___185_13492.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___186_13494 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___186_13494.tcenv);
                               debug = (uu___186_13494.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___186_13494.primitive_steps);
                               strong = (uu___186_13494.strong);
                               memoize_lazy = (uu___186_13494.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___186_13494.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____13496 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____13496 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____13528  -> dummy :: env1) env)
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
                                          let uu____13569 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____13569)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___187_13574 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___187_13574.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___187_13574.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____13575 -> lopt  in
                           (log cfg
                              (fun uu____13581  ->
                                 let uu____13582 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____13582);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___188_13591 = cfg  in
                               {
                                 steps = (uu___188_13591.steps);
                                 tcenv = (uu___188_13591.tcenv);
                                 debug = (uu___188_13591.debug);
                                 delta_level = (uu___188_13591.delta_level);
                                 primitive_steps =
                                   (uu___188_13591.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___188_13591.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___188_13591.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Abs uu____13594)::uu____13595 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___185_13613 = cfg.steps  in
                             {
                               beta = (uu___185_13613.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___185_13613.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___185_13613.unfold_until);
                               unfold_only = (uu___185_13613.unfold_only);
                               unfold_fully = (uu___185_13613.unfold_fully);
                               unfold_attr = (uu___185_13613.unfold_attr);
                               unfold_tac = (uu___185_13613.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___185_13613.erase_universes);
                               allow_unbound_universes =
                                 (uu___185_13613.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___185_13613.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___185_13613.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___185_13613.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___185_13613.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___186_13615 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___186_13615.tcenv);
                               debug = (uu___186_13615.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___186_13615.primitive_steps);
                               strong = (uu___186_13615.strong);
                               memoize_lazy = (uu___186_13615.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___186_13615.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____13617 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____13617 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____13649  -> dummy :: env1) env)
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
                                          let uu____13690 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____13690)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___187_13695 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___187_13695.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___187_13695.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____13696 -> lopt  in
                           (log cfg
                              (fun uu____13702  ->
                                 let uu____13703 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____13703);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___188_13712 = cfg  in
                               {
                                 steps = (uu___188_13712.steps);
                                 tcenv = (uu___188_13712.tcenv);
                                 debug = (uu___188_13712.debug);
                                 delta_level = (uu___188_13712.delta_level);
                                 primitive_steps =
                                   (uu___188_13712.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___188_13712.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___188_13712.normalize_pure_lets)
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
                             let uu___185_13718 = cfg.steps  in
                             {
                               beta = (uu___185_13718.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___185_13718.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___185_13718.unfold_until);
                               unfold_only = (uu___185_13718.unfold_only);
                               unfold_fully = (uu___185_13718.unfold_fully);
                               unfold_attr = (uu___185_13718.unfold_attr);
                               unfold_tac = (uu___185_13718.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___185_13718.erase_universes);
                               allow_unbound_universes =
                                 (uu___185_13718.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___185_13718.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___185_13718.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___185_13718.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___185_13718.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___186_13720 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___186_13720.tcenv);
                               debug = (uu___186_13720.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___186_13720.primitive_steps);
                               strong = (uu___186_13720.strong);
                               memoize_lazy = (uu___186_13720.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___186_13720.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____13722 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____13722 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____13754  -> dummy :: env1) env)
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
                                          let uu____13795 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____13795)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___187_13800 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___187_13800.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___187_13800.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____13801 -> lopt  in
                           (log cfg
                              (fun uu____13807  ->
                                 let uu____13808 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____13808);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___188_13817 = cfg  in
                               {
                                 steps = (uu___188_13817.steps);
                                 tcenv = (uu___188_13817.tcenv);
                                 debug = (uu___188_13817.debug);
                                 delta_level = (uu___188_13817.delta_level);
                                 primitive_steps =
                                   (uu___188_13817.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___188_13817.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___188_13817.normalize_pure_lets)
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
                      (fun uu____13856  ->
                         fun stack1  ->
                           match uu____13856 with
                           | (a,aq) ->
                               let uu____13868 =
                                 let uu____13869 =
                                   let uu____13876 =
                                     let uu____13877 =
                                       let uu____13908 =
                                         FStar_Util.mk_ref
                                           FStar_Pervasives_Native.None
                                          in
                                       (env, a, uu____13908, false)  in
                                     Clos uu____13877  in
                                   (uu____13876, aq,
                                     (t1.FStar_Syntax_Syntax.pos))
                                    in
                                 Arg uu____13869  in
                               uu____13868 :: stack1) args)
                  in
               (log cfg
                  (fun uu____13996  ->
                     let uu____13997 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args)
                        in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____13997);
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
                             ((let uu___189_14043 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___189_14043.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___189_14043.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos
                         in
                      rebuild cfg env stack t2
                  | uu____14044 ->
                      let uu____14059 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____14059)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort  in
                  let uu____14062 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] f
                     in
                  match uu____14062 with
                  | (closing,f1) ->
                      let f2 = norm cfg (dummy :: env) [] f1  in
                      let t2 =
                        let uu____14087 =
                          let uu____14088 =
                            let uu____14095 =
                              FStar_Syntax_Subst.close closing f2  in
                            ((let uu___190_14101 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___190_14101.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___190_14101.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____14095)
                             in
                          FStar_Syntax_Syntax.Tm_refine uu____14088  in
                        mk uu____14087 t1.FStar_Syntax_Syntax.pos  in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if (cfg.steps).weak
               then
                 let uu____14120 = closure_as_term cfg env t1  in
                 rebuild cfg env stack uu____14120
               else
                 (let uu____14122 = FStar_Syntax_Subst.open_comp bs c  in
                  match uu____14122 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____14130 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun uu____14152  -> dummy :: env1) env)
                           in
                        norm_comp cfg uu____14130 c1  in
                      let t2 =
                        let uu____14174 = norm_binders cfg env bs1  in
                        FStar_Syntax_Util.arrow uu____14174 c2  in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) when
               (cfg.steps).unascribe -> norm cfg env stack t11
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack with
                | (Match uu____14285)::uu____14286 ->
                    (log cfg
                       (fun uu____14299  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (Arg uu____14300)::uu____14301 ->
                    (log cfg
                       (fun uu____14312  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (App
                    (uu____14313,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_constant
                                     (FStar_Const.Const_reify );
                                   FStar_Syntax_Syntax.pos = uu____14314;
                                   FStar_Syntax_Syntax.vars = uu____14315;_},uu____14316,uu____14317))::uu____14318
                    ->
                    (log cfg
                       (fun uu____14325  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (MemoLazy uu____14326)::uu____14327 ->
                    (log cfg
                       (fun uu____14338  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | uu____14339 ->
                    (log cfg
                       (fun uu____14342  ->
                          FStar_Util.print_string "+++ Keeping ascription \n");
                     (let t12 = norm cfg env [] t11  in
                      log cfg
                        (fun uu____14346  ->
                           FStar_Util.print_string
                             "+++ Normalizing ascription \n");
                      (let tc1 =
                         match tc with
                         | FStar_Util.Inl t2 ->
                             let uu____14371 = norm cfg env [] t2  in
                             FStar_Util.Inl uu____14371
                         | FStar_Util.Inr c ->
                             let uu____14381 = norm_comp cfg env c  in
                             FStar_Util.Inr uu____14381
                          in
                       let tacopt1 =
                         FStar_Util.map_opt tacopt (norm cfg env [])  in
                       match stack with
                       | (Cfg cfg1)::stack1 ->
                           let t2 =
                             let uu____14400 =
                               let uu____14401 =
                                 let uu____14428 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____14428, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____14401
                                in
                             mk uu____14400 t1.FStar_Syntax_Syntax.pos  in
                           norm cfg1 env stack1 t2
                       | uu____14463 ->
                           let uu____14464 =
                             let uu____14465 =
                               let uu____14466 =
                                 let uu____14493 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____14493, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____14466
                                in
                             mk uu____14465 t1.FStar_Syntax_Syntax.pos  in
                           rebuild cfg env stack uu____14464))))
           | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
               let stack1 =
                 (Match (env, branches, cfg, (t1.FStar_Syntax_Syntax.pos)))
                 :: stack  in
               let cfg1 =
                 if
                   ((cfg.steps).iota && (cfg.steps).weakly_reduce_scrutinee)
                     && (Prims.op_Negation (cfg.steps).weak)
                 then
                   let uu___191_14570 = cfg  in
                   {
                     steps =
                       (let uu___192_14573 = cfg.steps  in
                        {
                          beta = (uu___192_14573.beta);
                          iota = (uu___192_14573.iota);
                          zeta = (uu___192_14573.zeta);
                          weak = true;
                          hnf = (uu___192_14573.hnf);
                          primops = (uu___192_14573.primops);
                          do_not_unfold_pure_lets =
                            (uu___192_14573.do_not_unfold_pure_lets);
                          unfold_until = (uu___192_14573.unfold_until);
                          unfold_only = (uu___192_14573.unfold_only);
                          unfold_fully = (uu___192_14573.unfold_fully);
                          unfold_attr = (uu___192_14573.unfold_attr);
                          unfold_tac = (uu___192_14573.unfold_tac);
                          pure_subterms_within_computations =
                            (uu___192_14573.pure_subterms_within_computations);
                          simplify = (uu___192_14573.simplify);
                          erase_universes = (uu___192_14573.erase_universes);
                          allow_unbound_universes =
                            (uu___192_14573.allow_unbound_universes);
                          reify_ = (uu___192_14573.reify_);
                          compress_uvars = (uu___192_14573.compress_uvars);
                          no_full_norm = (uu___192_14573.no_full_norm);
                          check_no_uvars = (uu___192_14573.check_no_uvars);
                          unmeta = (uu___192_14573.unmeta);
                          unascribe = (uu___192_14573.unascribe);
                          in_full_norm_request =
                            (uu___192_14573.in_full_norm_request);
                          weakly_reduce_scrutinee =
                            (uu___192_14573.weakly_reduce_scrutinee)
                        });
                     tcenv = (uu___191_14570.tcenv);
                     debug = (uu___191_14570.debug);
                     delta_level = (uu___191_14570.delta_level);
                     primitive_steps = (uu___191_14570.primitive_steps);
                     strong = (uu___191_14570.strong);
                     memoize_lazy = (uu___191_14570.memoize_lazy);
                     normalize_pure_lets =
                       (uu___191_14570.normalize_pure_lets)
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
                         let uu____14609 =
                           FStar_Syntax_Subst.univ_var_opening
                             lb.FStar_Syntax_Syntax.lbunivs
                            in
                         match uu____14609 with
                         | (openings,lbunivs) ->
                             let cfg1 =
                               let uu___193_14629 = cfg  in
                               let uu____14630 =
                                 FStar_TypeChecker_Env.push_univ_vars
                                   cfg.tcenv lbunivs
                                  in
                               {
                                 steps = (uu___193_14629.steps);
                                 tcenv = uu____14630;
                                 debug = (uu___193_14629.debug);
                                 delta_level = (uu___193_14629.delta_level);
                                 primitive_steps =
                                   (uu___193_14629.primitive_steps);
                                 strong = (uu___193_14629.strong);
                                 memoize_lazy = (uu___193_14629.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___193_14629.normalize_pure_lets)
                               }  in
                             let norm1 t2 =
                               let uu____14637 =
                                 let uu____14638 =
                                   FStar_Syntax_Subst.subst openings t2  in
                                 norm cfg1 env [] uu____14638  in
                               FStar_Syntax_Subst.close_univ_vars lbunivs
                                 uu____14637
                                in
                             let lbtyp = norm1 lb.FStar_Syntax_Syntax.lbtyp
                                in
                             let lbdef = norm1 lb.FStar_Syntax_Syntax.lbdef
                                in
                             let uu___194_14641 = lb  in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___194_14641.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs = lbunivs;
                               FStar_Syntax_Syntax.lbtyp = lbtyp;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___194_14641.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = lbdef;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___194_14641.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___194_14641.FStar_Syntax_Syntax.lbpos)
                             }))
                  in
               let uu____14642 =
                 mk (FStar_Syntax_Syntax.Tm_let ((b, lbs1), lbody))
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack uu____14642
           | FStar_Syntax_Syntax.Tm_let
               ((uu____14653,{
                               FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                 uu____14654;
                               FStar_Syntax_Syntax.lbunivs = uu____14655;
                               FStar_Syntax_Syntax.lbtyp = uu____14656;
                               FStar_Syntax_Syntax.lbeff = uu____14657;
                               FStar_Syntax_Syntax.lbdef = uu____14658;
                               FStar_Syntax_Syntax.lbattrs = uu____14659;
                               FStar_Syntax_Syntax.lbpos = uu____14660;_}::uu____14661),uu____14662)
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff
                  in
               let uu____14702 =
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
               if uu____14702
               then
                 let binder =
                   let uu____14704 =
                     FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                   FStar_Syntax_Syntax.mk_binder uu____14704  in
                 let env1 =
                   let uu____14714 =
                     let uu____14721 =
                       let uu____14722 =
                         let uu____14753 =
                           FStar_Util.mk_ref FStar_Pervasives_Native.None  in
                         (env, (lb.FStar_Syntax_Syntax.lbdef), uu____14753,
                           false)
                          in
                       Clos uu____14722  in
                     ((FStar_Pervasives_Native.Some binder), uu____14721)  in
                   uu____14714 :: env  in
                 (log cfg
                    (fun uu____14848  ->
                       FStar_Util.print_string "+++ Reducing Tm_let\n");
                  norm cfg env1 stack body)
               else
                 if (cfg.steps).weak
                 then
                   (log cfg
                      (fun uu____14852  ->
                         FStar_Util.print_string "+++ Not touching Tm_let\n");
                    (let uu____14853 = closure_as_term cfg env t1  in
                     rebuild cfg env stack uu____14853))
                 else
                   (let uu____14855 =
                      let uu____14860 =
                        let uu____14861 =
                          let uu____14866 =
                            FStar_All.pipe_right
                              lb.FStar_Syntax_Syntax.lbname FStar_Util.left
                             in
                          FStar_All.pipe_right uu____14866
                            FStar_Syntax_Syntax.mk_binder
                           in
                        [uu____14861]  in
                      FStar_Syntax_Subst.open_term uu____14860 body  in
                    match uu____14855 with
                    | (bs,body1) ->
                        (log cfg
                           (fun uu____14887  ->
                              FStar_Util.print_string
                                "+++ Normalizing Tm_let -- type");
                         (let ty =
                            norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                          let lbname =
                            let x =
                              let uu____14895 = FStar_List.hd bs  in
                              FStar_Pervasives_Native.fst uu____14895  in
                            FStar_Util.Inl
                              (let uu___195_14905 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___195_14905.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___195_14905.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               })
                             in
                          log cfg
                            (fun uu____14908  ->
                               FStar_Util.print_string
                                 "+++ Normalizing Tm_let -- definiens\n");
                          (let lb1 =
                             let uu___196_14910 = lb  in
                             let uu____14911 =
                               norm cfg env [] lb.FStar_Syntax_Syntax.lbdef
                                in
                             {
                               FStar_Syntax_Syntax.lbname = lbname;
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___196_14910.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp = ty;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___196_14910.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = uu____14911;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___196_14910.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___196_14910.FStar_Syntax_Syntax.lbpos)
                             }  in
                           let env' =
                             FStar_All.pipe_right bs
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____14936  -> dummy :: env1) env)
                              in
                           let stack1 = (Cfg cfg) :: stack  in
                           let cfg1 =
                             let uu___197_14959 = cfg  in
                             {
                               steps = (uu___197_14959.steps);
                               tcenv = (uu___197_14959.tcenv);
                               debug = (uu___197_14959.debug);
                               delta_level = (uu___197_14959.delta_level);
                               primitive_steps =
                                 (uu___197_14959.primitive_steps);
                               strong = true;
                               memoize_lazy = (uu___197_14959.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___197_14959.normalize_pure_lets)
                             }  in
                           log cfg1
                             (fun uu____14962  ->
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
               let uu____14979 = FStar_Syntax_Subst.open_let_rec lbs body  in
               (match uu____14979 with
                | (lbs1,body1) ->
                    let lbs2 =
                      FStar_List.map
                        (fun lb  ->
                           let ty =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                           let lbname =
                             let uu____15015 =
                               let uu___198_15016 =
                                 FStar_Util.left
                                   lb.FStar_Syntax_Syntax.lbname
                                  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___198_15016.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___198_15016.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               }  in
                             FStar_Util.Inl uu____15015  in
                           let uu____15017 =
                             FStar_Syntax_Util.abs_formals
                               lb.FStar_Syntax_Syntax.lbdef
                              in
                           match uu____15017 with
                           | (xs,def_body,lopt) ->
                               let xs1 = norm_binders cfg env xs  in
                               let env1 =
                                 let uu____15043 =
                                   FStar_List.map (fun uu____15059  -> dummy)
                                     lbs1
                                    in
                                 let uu____15060 =
                                   let uu____15069 =
                                     FStar_List.map
                                       (fun uu____15089  -> dummy) xs1
                                      in
                                   FStar_List.append uu____15069 env  in
                                 FStar_List.append uu____15043 uu____15060
                                  in
                               let def_body1 = norm cfg env1 [] def_body  in
                               let lopt1 =
                                 match lopt with
                                 | FStar_Pervasives_Native.Some rc ->
                                     let uu____15113 =
                                       let uu___199_15114 = rc  in
                                       let uu____15115 =
                                         FStar_Util.map_opt
                                           rc.FStar_Syntax_Syntax.residual_typ
                                           (norm cfg env1 [])
                                          in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___199_15114.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           uu____15115;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___199_15114.FStar_Syntax_Syntax.residual_flags)
                                       }  in
                                     FStar_Pervasives_Native.Some uu____15113
                                 | uu____15124 -> lopt  in
                               let def =
                                 FStar_Syntax_Util.abs xs1 def_body1 lopt1
                                  in
                               let uu___200_15130 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname = lbname;
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___200_15130.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp = ty;
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___200_15130.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___200_15130.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___200_15130.FStar_Syntax_Syntax.lbpos)
                               }) lbs1
                       in
                    let env' =
                      let uu____15140 =
                        FStar_List.map (fun uu____15156  -> dummy) lbs2  in
                      FStar_List.append uu____15140 env  in
                    let body2 = norm cfg env' [] body1  in
                    let uu____15164 =
                      FStar_Syntax_Subst.close_let_rec lbs2 body2  in
                    (match uu____15164 with
                     | (lbs3,body3) ->
                         let t2 =
                           let uu___201_15180 = t1  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_let
                                  ((true, lbs3), body3));
                             FStar_Syntax_Syntax.pos =
                               (uu___201_15180.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___201_15180.FStar_Syntax_Syntax.vars)
                           }  in
                         rebuild cfg env stack t2))
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               Prims.op_Negation (cfg.steps).zeta ->
               let uu____15209 = closure_as_term cfg env t1  in
               rebuild cfg env stack uu____15209
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____15228 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____15304  ->
                        match uu____15304 with
                        | (rec_env,memos,i) ->
                            let bv =
                              let uu___202_15425 =
                                FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                                 in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___202_15425.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index = i;
                                FStar_Syntax_Syntax.sort =
                                  (uu___202_15425.FStar_Syntax_Syntax.sort)
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
               (match uu____15228 with
                | (rec_env,memos,uu____15652) ->
                    let uu____15705 =
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
                             let uu____16028 =
                               let uu____16035 =
                                 let uu____16036 =
                                   let uu____16067 =
                                     FStar_Util.mk_ref
                                       FStar_Pervasives_Native.None
                                      in
                                   (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                     uu____16067, false)
                                    in
                                 Clos uu____16036  in
                               (FStar_Pervasives_Native.None, uu____16035)
                                in
                             uu____16028 :: env1)
                        (FStar_Pervasives_Native.snd lbs) env
                       in
                    norm cfg body_env stack body)
           | FStar_Syntax_Syntax.Tm_meta (head1,m) ->
               (log cfg
                  (fun uu____16171  ->
                     let uu____16172 =
                       FStar_Syntax_Print.metadata_to_string m  in
                     FStar_Util.print1 ">> metadata = %s\n" uu____16172);
                (match m with
                 | FStar_Syntax_Syntax.Meta_monadic (m1,t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inl m1) t2
                 | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inr (m1, m')) t2
                 | uu____16194 ->
                     if (cfg.steps).unmeta
                     then norm cfg env stack head1
                     else
                       (match stack with
                        | uu____16196::uu____16197 ->
                            (match m with
                             | FStar_Syntax_Syntax.Meta_labeled
                                 (l,r,uu____16202) ->
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
                             | uu____16225 -> norm cfg env stack head1)
                        | [] ->
                            let head2 = norm cfg env [] head1  in
                            let m1 =
                              match m with
                              | FStar_Syntax_Syntax.Meta_pattern args ->
                                  let uu____16239 =
                                    norm_pattern_args cfg env args  in
                                  FStar_Syntax_Syntax.Meta_pattern
                                    uu____16239
                              | uu____16250 -> m  in
                            let t2 =
                              mk (FStar_Syntax_Syntax.Tm_meta (head2, m1))
                                t1.FStar_Syntax_Syntax.pos
                               in
                            rebuild cfg env stack t2)))
           | FStar_Syntax_Syntax.Tm_delayed uu____16256 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               norm cfg env stack t2
           | FStar_Syntax_Syntax.Tm_uvar uu____16282 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               (match t2.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_uvar uu____16290 ->
                    if (cfg.steps).check_no_uvars
                    then
                      let uu____16297 =
                        let uu____16298 =
                          FStar_Range.string_of_range
                            t2.FStar_Syntax_Syntax.pos
                           in
                        let uu____16299 =
                          FStar_Syntax_Print.term_to_string t2  in
                        FStar_Util.format2
                          "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                          uu____16298 uu____16299
                         in
                      failwith uu____16297
                    else
                      (let uu____16301 = inline_closure_env cfg env [] t2  in
                       rebuild cfg env stack uu____16301)
                | uu____16302 -> norm cfg env stack t2))

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
                let uu____16312 = FStar_Syntax_Syntax.range_of_fv f  in
                FStar_TypeChecker_Env.set_range cfg.tcenv uu____16312  in
              let uu____16313 =
                FStar_TypeChecker_Env.lookup_definition_qninfo
                  cfg.delta_level
                  (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                  qninfo
                 in
              match uu____16313 with
              | FStar_Pervasives_Native.None  ->
                  (log cfg
                     (fun uu____16326  ->
                        FStar_Util.print "Tm_fvar case 2\n" []);
                   rebuild cfg env stack t0)
              | FStar_Pervasives_Native.Some (us,t) ->
                  (log cfg
                     (fun uu____16337  ->
                        let uu____16338 =
                          FStar_Syntax_Print.term_to_string t0  in
                        let uu____16339 = FStar_Syntax_Print.term_to_string t
                           in
                        FStar_Util.print2 ">>> Unfolded %s to %s\n"
                          uu____16338 uu____16339);
                   (let t1 =
                      if
                        ((cfg.steps).unfold_until =
                           (FStar_Pervasives_Native.Some
                              FStar_Syntax_Syntax.delta_constant))
                          && (Prims.op_Negation (cfg.steps).unfold_tac)
                      then t
                      else
                        (let uu____16344 =
                           FStar_Ident.range_of_lid
                             (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                            in
                         FStar_Syntax_Subst.set_use_range uu____16344 t)
                       in
                    let n1 = FStar_List.length us  in
                    if n1 > (Prims.parse_int "0")
                    then
                      match stack with
                      | (UnivArgs (us',uu____16353))::stack1 ->
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
                      | uu____16392 when
                          (cfg.steps).erase_universes ||
                            (cfg.steps).allow_unbound_universes
                          -> norm cfg env stack t1
                      | uu____16395 ->
                          let uu____16398 =
                            let uu____16399 =
                              FStar_Syntax_Print.lid_to_string
                                (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                               in
                            FStar_Util.format1
                              "Impossible: missing universe instantiation on %s"
                              uu____16399
                             in
                          failwith uu____16398
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
                  let uu___203_16423 = cfg  in
                  let uu____16424 =
                    FStar_List.fold_right fstep_add_one new_steps cfg.steps
                     in
                  {
                    steps = uu____16424;
                    tcenv = (uu___203_16423.tcenv);
                    debug = (uu___203_16423.debug);
                    delta_level =
                      [FStar_TypeChecker_Env.Inlining;
                      FStar_TypeChecker_Env.Eager_unfolding_only];
                    primitive_steps = (uu___203_16423.primitive_steps);
                    strong = (uu___203_16423.strong);
                    memoize_lazy = (uu___203_16423.memoize_lazy);
                    normalize_pure_lets =
                      (uu___203_16423.normalize_pure_lets)
                  }
                else
                  (let uu___204_16426 = cfg  in
                   {
                     steps =
                       (let uu___205_16429 = cfg.steps  in
                        {
                          beta = (uu___205_16429.beta);
                          iota = (uu___205_16429.iota);
                          zeta = false;
                          weak = (uu___205_16429.weak);
                          hnf = (uu___205_16429.hnf);
                          primops = (uu___205_16429.primops);
                          do_not_unfold_pure_lets =
                            (uu___205_16429.do_not_unfold_pure_lets);
                          unfold_until = (uu___205_16429.unfold_until);
                          unfold_only = (uu___205_16429.unfold_only);
                          unfold_fully = (uu___205_16429.unfold_fully);
                          unfold_attr = (uu___205_16429.unfold_attr);
                          unfold_tac = (uu___205_16429.unfold_tac);
                          pure_subterms_within_computations =
                            (uu___205_16429.pure_subterms_within_computations);
                          simplify = (uu___205_16429.simplify);
                          erase_universes = (uu___205_16429.erase_universes);
                          allow_unbound_universes =
                            (uu___205_16429.allow_unbound_universes);
                          reify_ = (uu___205_16429.reify_);
                          compress_uvars = (uu___205_16429.compress_uvars);
                          no_full_norm = (uu___205_16429.no_full_norm);
                          check_no_uvars = (uu___205_16429.check_no_uvars);
                          unmeta = (uu___205_16429.unmeta);
                          unascribe = (uu___205_16429.unascribe);
                          in_full_norm_request =
                            (uu___205_16429.in_full_norm_request);
                          weakly_reduce_scrutinee =
                            (uu___205_16429.weakly_reduce_scrutinee)
                        });
                     tcenv = (uu___204_16426.tcenv);
                     debug = (uu___204_16426.debug);
                     delta_level = (uu___204_16426.delta_level);
                     primitive_steps = (uu___204_16426.primitive_steps);
                     strong = (uu___204_16426.strong);
                     memoize_lazy = (uu___204_16426.memoize_lazy);
                     normalize_pure_lets =
                       (uu___204_16426.normalize_pure_lets)
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
                  (fun uu____16463  ->
                     let uu____16464 = FStar_Syntax_Print.tag_of_term head2
                        in
                     let uu____16465 =
                       FStar_Syntax_Print.term_to_string head2  in
                     FStar_Util.print2 "Reifying: (%s) %s\n" uu____16464
                       uu____16465);
                (let head3 = FStar_Syntax_Util.unmeta_safe head2  in
                 let uu____16467 =
                   let uu____16468 = FStar_Syntax_Subst.compress head3  in
                   uu____16468.FStar_Syntax_Syntax.n  in
                 match uu____16467 with
                 | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                     let ed =
                       let uu____16486 =
                         FStar_TypeChecker_Env.norm_eff_name cfg.tcenv m  in
                       FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                         uu____16486
                        in
                     let uu____16487 = ed.FStar_Syntax_Syntax.bind_repr  in
                     (match uu____16487 with
                      | (uu____16488,bind_repr) ->
                          (match lb.FStar_Syntax_Syntax.lbname with
                           | FStar_Util.Inr uu____16498 ->
                               failwith
                                 "Cannot reify a top-level let binding"
                           | FStar_Util.Inl x ->
                               let is_return e =
                                 let uu____16508 =
                                   let uu____16509 =
                                     FStar_Syntax_Subst.compress e  in
                                   uu____16509.FStar_Syntax_Syntax.n  in
                                 match uu____16508 with
                                 | FStar_Syntax_Syntax.Tm_meta
                                     (e1,FStar_Syntax_Syntax.Meta_monadic
                                      (uu____16515,uu____16516))
                                     ->
                                     let uu____16525 =
                                       let uu____16526 =
                                         FStar_Syntax_Subst.compress e1  in
                                       uu____16526.FStar_Syntax_Syntax.n  in
                                     (match uu____16525 with
                                      | FStar_Syntax_Syntax.Tm_meta
                                          (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                           (uu____16532,msrc,uu____16534))
                                          when
                                          FStar_Syntax_Util.is_pure_effect
                                            msrc
                                          ->
                                          let uu____16543 =
                                            FStar_Syntax_Subst.compress e2
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____16543
                                      | uu____16544 ->
                                          FStar_Pervasives_Native.None)
                                 | uu____16545 ->
                                     FStar_Pervasives_Native.None
                                  in
                               let uu____16546 =
                                 is_return lb.FStar_Syntax_Syntax.lbdef  in
                               (match uu____16546 with
                                | FStar_Pervasives_Native.Some e ->
                                    let lb1 =
                                      let uu___206_16551 = lb  in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          (uu___206_16551.FStar_Syntax_Syntax.lbname);
                                        FStar_Syntax_Syntax.lbunivs =
                                          (uu___206_16551.FStar_Syntax_Syntax.lbunivs);
                                        FStar_Syntax_Syntax.lbtyp =
                                          (uu___206_16551.FStar_Syntax_Syntax.lbtyp);
                                        FStar_Syntax_Syntax.lbeff =
                                          FStar_Parser_Const.effect_PURE_lid;
                                        FStar_Syntax_Syntax.lbdef = e;
                                        FStar_Syntax_Syntax.lbattrs =
                                          (uu___206_16551.FStar_Syntax_Syntax.lbattrs);
                                        FStar_Syntax_Syntax.lbpos =
                                          (uu___206_16551.FStar_Syntax_Syntax.lbpos)
                                      }  in
                                    let uu____16552 = FStar_List.tl stack  in
                                    let uu____16553 =
                                      let uu____16554 =
                                        let uu____16561 =
                                          let uu____16562 =
                                            let uu____16575 =
                                              FStar_Syntax_Util.mk_reify body
                                               in
                                            ((false, [lb1]), uu____16575)  in
                                          FStar_Syntax_Syntax.Tm_let
                                            uu____16562
                                           in
                                        FStar_Syntax_Syntax.mk uu____16561
                                         in
                                      uu____16554
                                        FStar_Pervasives_Native.None
                                        head3.FStar_Syntax_Syntax.pos
                                       in
                                    norm cfg env uu____16552 uu____16553
                                | FStar_Pervasives_Native.None  ->
                                    let uu____16591 =
                                      let uu____16592 = is_return body  in
                                      match uu____16592 with
                                      | FStar_Pervasives_Native.Some
                                          {
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_bvar y;
                                            FStar_Syntax_Syntax.pos =
                                              uu____16596;
                                            FStar_Syntax_Syntax.vars =
                                              uu____16597;_}
                                          -> FStar_Syntax_Syntax.bv_eq x y
                                      | uu____16600 -> false  in
                                    if uu____16591
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
                                         let uu____16621 =
                                           let uu____16628 =
                                             let uu____16629 =
                                               let uu____16646 =
                                                 let uu____16653 =
                                                   FStar_Syntax_Syntax.mk_binder
                                                     x
                                                    in
                                                 [uu____16653]  in
                                               (uu____16646, body1,
                                                 (FStar_Pervasives_Native.Some
                                                    body_rc))
                                                in
                                             FStar_Syntax_Syntax.Tm_abs
                                               uu____16629
                                              in
                                           FStar_Syntax_Syntax.mk uu____16628
                                            in
                                         uu____16621
                                           FStar_Pervasives_Native.None
                                           body1.FStar_Syntax_Syntax.pos
                                          in
                                       let close1 = closure_as_term cfg env
                                          in
                                       let bind_inst =
                                         let uu____16687 =
                                           let uu____16688 =
                                             FStar_Syntax_Subst.compress
                                               bind_repr
                                              in
                                           uu____16688.FStar_Syntax_Syntax.n
                                            in
                                         match uu____16687 with
                                         | FStar_Syntax_Syntax.Tm_uinst
                                             (bind1,uu____16694::uu____16695::[])
                                             ->
                                             let uu____16700 =
                                               let uu____16707 =
                                                 let uu____16708 =
                                                   let uu____16715 =
                                                     let uu____16716 =
                                                       let uu____16717 =
                                                         close1
                                                           lb.FStar_Syntax_Syntax.lbtyp
                                                          in
                                                       (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                         cfg.tcenv
                                                         uu____16717
                                                        in
                                                     let uu____16718 =
                                                       let uu____16721 =
                                                         let uu____16722 =
                                                           close1 t  in
                                                         (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                           cfg.tcenv
                                                           uu____16722
                                                          in
                                                       [uu____16721]  in
                                                     uu____16716 ::
                                                       uu____16718
                                                      in
                                                   (bind1, uu____16715)  in
                                                 FStar_Syntax_Syntax.Tm_uinst
                                                   uu____16708
                                                  in
                                               FStar_Syntax_Syntax.mk
                                                 uu____16707
                                                in
                                             uu____16700
                                               FStar_Pervasives_Native.None
                                               rng
                                         | uu____16728 ->
                                             failwith
                                               "NIY : Reification of indexed effects"
                                          in
                                       let maybe_range_arg =
                                         let uu____16740 =
                                           FStar_Util.for_some
                                             (FStar_Syntax_Util.attr_eq
                                                FStar_Syntax_Util.dm4f_bind_range_attr)
                                             ed.FStar_Syntax_Syntax.eff_attrs
                                            in
                                         if uu____16740
                                         then
                                           let uu____16749 =
                                             let uu____16756 =
                                               FStar_Syntax_Embeddings.embed
                                                 FStar_Syntax_Embeddings.e_range
                                                 lb.FStar_Syntax_Syntax.lbpos
                                                 lb.FStar_Syntax_Syntax.lbpos
                                                in
                                             FStar_Syntax_Syntax.as_arg
                                               uu____16756
                                              in
                                           let uu____16757 =
                                             let uu____16766 =
                                               let uu____16773 =
                                                 FStar_Syntax_Embeddings.embed
                                                   FStar_Syntax_Embeddings.e_range
                                                   body2.FStar_Syntax_Syntax.pos
                                                   body2.FStar_Syntax_Syntax.pos
                                                  in
                                               FStar_Syntax_Syntax.as_arg
                                                 uu____16773
                                                in
                                             [uu____16766]  in
                                           uu____16749 :: uu____16757
                                         else []  in
                                       let reified =
                                         let uu____16802 =
                                           let uu____16809 =
                                             let uu____16810 =
                                               let uu____16825 =
                                                 let uu____16834 =
                                                   let uu____16843 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       lb.FStar_Syntax_Syntax.lbtyp
                                                      in
                                                   let uu____16850 =
                                                     let uu____16859 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         t
                                                        in
                                                     [uu____16859]  in
                                                   uu____16843 :: uu____16850
                                                    in
                                                 let uu____16884 =
                                                   let uu____16893 =
                                                     let uu____16902 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         FStar_Syntax_Syntax.tun
                                                        in
                                                     let uu____16909 =
                                                       let uu____16918 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           head4
                                                          in
                                                       let uu____16925 =
                                                         let uu____16934 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             FStar_Syntax_Syntax.tun
                                                            in
                                                         let uu____16941 =
                                                           let uu____16950 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               body2
                                                              in
                                                           [uu____16950]  in
                                                         uu____16934 ::
                                                           uu____16941
                                                          in
                                                       uu____16918 ::
                                                         uu____16925
                                                        in
                                                     uu____16902 ::
                                                       uu____16909
                                                      in
                                                   FStar_List.append
                                                     maybe_range_arg
                                                     uu____16893
                                                    in
                                                 FStar_List.append
                                                   uu____16834 uu____16884
                                                  in
                                               (bind_inst, uu____16825)  in
                                             FStar_Syntax_Syntax.Tm_app
                                               uu____16810
                                              in
                                           FStar_Syntax_Syntax.mk uu____16809
                                            in
                                         uu____16802
                                           FStar_Pervasives_Native.None rng
                                          in
                                       log cfg
                                         (fun uu____17016  ->
                                            let uu____17017 =
                                              FStar_Syntax_Print.term_to_string
                                                head0
                                               in
                                            let uu____17018 =
                                              FStar_Syntax_Print.term_to_string
                                                reified
                                               in
                                            FStar_Util.print2
                                              "Reified (1) <%s> to %s\n"
                                              uu____17017 uu____17018);
                                       (let uu____17019 = FStar_List.tl stack
                                           in
                                        norm cfg env uu____17019 reified)))))
                 | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                     let ed =
                       let uu____17043 =
                         FStar_TypeChecker_Env.norm_eff_name cfg.tcenv m  in
                       FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                         uu____17043
                        in
                     let uu____17044 = ed.FStar_Syntax_Syntax.bind_repr  in
                     (match uu____17044 with
                      | (uu____17045,bind_repr) ->
                          let maybe_unfold_action head4 =
                            let maybe_extract_fv t1 =
                              let t2 =
                                let uu____17082 =
                                  let uu____17083 =
                                    FStar_Syntax_Subst.compress t1  in
                                  uu____17083.FStar_Syntax_Syntax.n  in
                                match uu____17082 with
                                | FStar_Syntax_Syntax.Tm_uinst
                                    (t2,uu____17087) -> t2
                                | uu____17092 -> head4  in
                              let uu____17093 =
                                let uu____17094 =
                                  FStar_Syntax_Subst.compress t2  in
                                uu____17094.FStar_Syntax_Syntax.n  in
                              match uu____17093 with
                              | FStar_Syntax_Syntax.Tm_fvar x ->
                                  FStar_Pervasives_Native.Some x
                              | uu____17100 -> FStar_Pervasives_Native.None
                               in
                            let uu____17101 = maybe_extract_fv head4  in
                            match uu____17101 with
                            | FStar_Pervasives_Native.Some x when
                                let uu____17111 =
                                  FStar_Syntax_Syntax.lid_of_fv x  in
                                FStar_TypeChecker_Env.is_action cfg.tcenv
                                  uu____17111
                                ->
                                let head5 = norm cfg env [] head4  in
                                let action_unfolded =
                                  let uu____17116 = maybe_extract_fv head5
                                     in
                                  match uu____17116 with
                                  | FStar_Pervasives_Native.Some uu____17121
                                      -> FStar_Pervasives_Native.Some true
                                  | uu____17122 ->
                                      FStar_Pervasives_Native.Some false
                                   in
                                (head5, action_unfolded)
                            | uu____17127 ->
                                (head4, FStar_Pervasives_Native.None)
                             in
                          ((let is_arg_impure uu____17142 =
                              match uu____17142 with
                              | (e,q) ->
                                  let uu____17149 =
                                    let uu____17150 =
                                      FStar_Syntax_Subst.compress e  in
                                    uu____17150.FStar_Syntax_Syntax.n  in
                                  (match uu____17149 with
                                   | FStar_Syntax_Syntax.Tm_meta
                                       (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                        (m1,m2,t'))
                                       ->
                                       let uu____17165 =
                                         FStar_Syntax_Util.is_pure_effect m1
                                          in
                                       Prims.op_Negation uu____17165
                                   | uu____17166 -> false)
                               in
                            let uu____17167 =
                              let uu____17168 =
                                let uu____17177 =
                                  FStar_Syntax_Syntax.as_arg head_app  in
                                uu____17177 :: args  in
                              FStar_Util.for_some is_arg_impure uu____17168
                               in
                            if uu____17167
                            then
                              let uu____17196 =
                                let uu____17197 =
                                  FStar_Syntax_Print.term_to_string head3  in
                                FStar_Util.format1
                                  "Incompatibility between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                  uu____17197
                                 in
                              failwith uu____17196
                            else ());
                           (let uu____17199 = maybe_unfold_action head_app
                               in
                            match uu____17199 with
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
                                   (fun uu____17242  ->
                                      let uu____17243 =
                                        FStar_Syntax_Print.term_to_string
                                          head0
                                         in
                                      let uu____17244 =
                                        FStar_Syntax_Print.term_to_string
                                          body1
                                         in
                                      FStar_Util.print2
                                        "Reified (2) <%s> to %s\n"
                                        uu____17243 uu____17244);
                                 (let uu____17245 = FStar_List.tl stack  in
                                  norm cfg env uu____17245 body1)))))
                 | FStar_Syntax_Syntax.Tm_meta
                     (e,FStar_Syntax_Syntax.Meta_monadic uu____17247) ->
                     do_reify_monadic fallback cfg env stack e m t
                 | FStar_Syntax_Syntax.Tm_meta
                     (e,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,t'))
                     ->
                     let lifted =
                       let uu____17271 = closure_as_term cfg env t'  in
                       reify_lift cfg e msrc mtgt uu____17271  in
                     (log cfg
                        (fun uu____17275  ->
                           let uu____17276 =
                             FStar_Syntax_Print.term_to_string lifted  in
                           FStar_Util.print1 "Reified lift to (2): %s\n"
                             uu____17276);
                      (let uu____17277 = FStar_List.tl stack  in
                       norm cfg env uu____17277 lifted))
                 | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                     let branches1 =
                       FStar_All.pipe_right branches
                         (FStar_List.map
                            (fun uu____17398  ->
                               match uu____17398 with
                               | (pat,wopt,tm) ->
                                   let uu____17446 =
                                     FStar_Syntax_Util.mk_reify tm  in
                                   (pat, wopt, uu____17446)))
                        in
                     let tm =
                       mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                         head3.FStar_Syntax_Syntax.pos
                        in
                     let uu____17478 = FStar_List.tl stack  in
                     norm cfg env uu____17478 tm
                 | uu____17479 -> fallback ())

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
              (fun uu____17493  ->
                 let uu____17494 = FStar_Ident.string_of_lid msrc  in
                 let uu____17495 = FStar_Ident.string_of_lid mtgt  in
                 let uu____17496 = FStar_Syntax_Print.term_to_string e  in
                 FStar_Util.print3 "Reifying lift %s -> %s: %s\n" uu____17494
                   uu____17495 uu____17496);
            (let uu____17497 =
               (FStar_Syntax_Util.is_pure_effect msrc) ||
                 (FStar_Syntax_Util.is_div_effect msrc)
                in
             if uu____17497
             then
               let ed =
                 let uu____17499 =
                   FStar_TypeChecker_Env.norm_eff_name cfg.tcenv mtgt  in
                 FStar_TypeChecker_Env.get_effect_decl env uu____17499  in
               let uu____17500 = ed.FStar_Syntax_Syntax.return_repr  in
               match uu____17500 with
               | (uu____17501,return_repr) ->
                   let return_inst =
                     let uu____17514 =
                       let uu____17515 =
                         FStar_Syntax_Subst.compress return_repr  in
                       uu____17515.FStar_Syntax_Syntax.n  in
                     match uu____17514 with
                     | FStar_Syntax_Syntax.Tm_uinst
                         (return_tm,uu____17521::[]) ->
                         let uu____17526 =
                           let uu____17533 =
                             let uu____17534 =
                               let uu____17541 =
                                 let uu____17542 =
                                   env.FStar_TypeChecker_Env.universe_of env
                                     t
                                    in
                                 [uu____17542]  in
                               (return_tm, uu____17541)  in
                             FStar_Syntax_Syntax.Tm_uinst uu____17534  in
                           FStar_Syntax_Syntax.mk uu____17533  in
                         uu____17526 FStar_Pervasives_Native.None
                           e.FStar_Syntax_Syntax.pos
                     | uu____17548 ->
                         failwith "NIY : Reification of indexed effects"
                      in
                   let uu____17551 =
                     let uu____17558 =
                       let uu____17559 =
                         let uu____17574 =
                           let uu____17583 = FStar_Syntax_Syntax.as_arg t  in
                           let uu____17590 =
                             let uu____17599 = FStar_Syntax_Syntax.as_arg e
                                in
                             [uu____17599]  in
                           uu____17583 :: uu____17590  in
                         (return_inst, uu____17574)  in
                       FStar_Syntax_Syntax.Tm_app uu____17559  in
                     FStar_Syntax_Syntax.mk uu____17558  in
                   uu____17551 FStar_Pervasives_Native.None
                     e.FStar_Syntax_Syntax.pos
             else
               (let uu____17638 =
                  FStar_TypeChecker_Env.monad_leq env msrc mtgt  in
                match uu____17638 with
                | FStar_Pervasives_Native.None  ->
                    let uu____17641 =
                      let uu____17642 = FStar_Ident.text_of_lid msrc  in
                      let uu____17643 = FStar_Ident.text_of_lid mtgt  in
                      FStar_Util.format2
                        "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                        uu____17642 uu____17643
                       in
                    failwith uu____17641
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____17644;
                      FStar_TypeChecker_Env.mtarget = uu____17645;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____17646;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.None ;_};_}
                    ->
                    let uu____17668 =
                      let uu____17669 = FStar_Ident.text_of_lid msrc  in
                      let uu____17670 = FStar_Ident.text_of_lid mtgt  in
                      FStar_Util.format2
                        "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
                        uu____17669 uu____17670
                       in
                    failwith uu____17668
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____17671;
                      FStar_TypeChecker_Env.mtarget = uu____17672;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____17673;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.Some lift;_};_}
                    ->
                    let uu____17708 =
                      env.FStar_TypeChecker_Env.universe_of env t  in
                    let uu____17709 = FStar_Syntax_Util.mk_reify e  in
                    lift uu____17708 t FStar_Syntax_Syntax.tun uu____17709))

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
                (fun uu____17765  ->
                   match uu____17765 with
                   | (a,imp) ->
                       let uu____17776 = norm cfg env [] a  in
                       (uu____17776, imp))))

and (norm_comp :
  cfg -> env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp) =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        log cfg
          (fun uu____17784  ->
             let uu____17785 = FStar_Syntax_Print.comp_to_string comp  in
             let uu____17786 =
               FStar_Util.string_of_int (FStar_List.length env)  in
             FStar_Util.print2 ">>> %s\nNormComp with with %s env elements"
               uu____17785 uu____17786);
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Total (t,uopt) ->
             let t1 = norm cfg env [] t  in
             let uopt1 =
               match uopt with
               | FStar_Pervasives_Native.Some u ->
                   let uu____17810 = norm_universe cfg env u  in
                   FStar_All.pipe_left
                     (fun _0_19  -> FStar_Pervasives_Native.Some _0_19)
                     uu____17810
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
                in
             let uu___207_17813 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Total (t1, uopt1));
               FStar_Syntax_Syntax.pos =
                 (uu___207_17813.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___207_17813.FStar_Syntax_Syntax.vars)
             }
         | FStar_Syntax_Syntax.GTotal (t,uopt) ->
             let t1 = norm cfg env [] t  in
             let uopt1 =
               match uopt with
               | FStar_Pervasives_Native.Some u ->
                   let uu____17835 = norm_universe cfg env u  in
                   FStar_All.pipe_left
                     (fun _0_20  -> FStar_Pervasives_Native.Some _0_20)
                     uu____17835
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
                in
             let uu___208_17838 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.GTotal (t1, uopt1));
               FStar_Syntax_Syntax.pos =
                 (uu___208_17838.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___208_17838.FStar_Syntax_Syntax.vars)
             }
         | FStar_Syntax_Syntax.Comp ct ->
             let norm_args =
               FStar_List.mapi
                 (fun idx  ->
                    fun uu____17875  ->
                      match uu____17875 with
                      | (a,i) ->
                          let uu____17886 = norm cfg env [] a  in
                          (uu____17886, i))
                in
             let effect_args = norm_args ct.FStar_Syntax_Syntax.effect_args
                in
             let flags1 =
               FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                 (FStar_List.map
                    (fun uu___120_17904  ->
                       match uu___120_17904 with
                       | FStar_Syntax_Syntax.DECREASES t ->
                           let uu____17908 = norm cfg env [] t  in
                           FStar_Syntax_Syntax.DECREASES uu____17908
                       | f -> f))
                in
             let comp_univs =
               FStar_List.map (norm_universe cfg env)
                 ct.FStar_Syntax_Syntax.comp_univs
                in
             let result_typ =
               norm cfg env [] ct.FStar_Syntax_Syntax.result_typ  in
             let uu___209_17916 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Comp
                    (let uu___210_17919 = ct  in
                     {
                       FStar_Syntax_Syntax.comp_univs = comp_univs;
                       FStar_Syntax_Syntax.effect_name =
                         (uu___210_17919.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ = result_typ;
                       FStar_Syntax_Syntax.effect_args = effect_args;
                       FStar_Syntax_Syntax.flags = flags1
                     }));
               FStar_Syntax_Syntax.pos =
                 (uu___209_17916.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___209_17916.FStar_Syntax_Syntax.vars)
             })

and (norm_binder :
  cfg -> env -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder) =
  fun cfg  ->
    fun env  ->
      fun uu____17922  ->
        match uu____17922 with
        | (x,imp) ->
            let uu____17925 =
              let uu___211_17926 = x  in
              let uu____17927 = norm cfg env [] x.FStar_Syntax_Syntax.sort
                 in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___211_17926.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___211_17926.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____17927
              }  in
            (uu____17925, imp)

and (norm_binders :
  cfg -> env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders) =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____17933 =
          FStar_List.fold_left
            (fun uu____17967  ->
               fun b  ->
                 match uu____17967 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b  in
                     ((b1 :: nbs'), (dummy :: env1))) ([], env) bs
           in
        match uu____17933 with | (nbs,uu____18047) -> FStar_List.rev nbs

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
            let uu____18079 =
              let uu___212_18080 = rc  in
              let uu____18081 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (norm cfg env [])
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___212_18080.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____18081;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___212_18080.FStar_Syntax_Syntax.residual_flags)
              }  in
            FStar_Pervasives_Native.Some uu____18079
        | uu____18090 -> lopt

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
            (let uu____18111 = FStar_Syntax_Print.term_to_string tm  in
             let uu____18112 = FStar_Syntax_Print.term_to_string tm'  in
             FStar_Util.print3 "%sSimplified\n\t%s to\n\t%s\n"
               (if (cfg.steps).simplify then "" else "NOT ") uu____18111
               uu____18112)
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
          let uu____18134 =
            FStar_All.pipe_left Prims.op_Negation (cfg.steps).simplify  in
          if uu____18134
          then tm1
          else
            (let w t =
               let uu___213_18148 = t  in
               {
                 FStar_Syntax_Syntax.n =
                   (uu___213_18148.FStar_Syntax_Syntax.n);
                 FStar_Syntax_Syntax.pos = (tm1.FStar_Syntax_Syntax.pos);
                 FStar_Syntax_Syntax.vars =
                   (uu___213_18148.FStar_Syntax_Syntax.vars)
               }  in
             let simp_t t =
               let uu____18159 =
                 let uu____18160 = FStar_Syntax_Util.unmeta t  in
                 uu____18160.FStar_Syntax_Syntax.n  in
               match uu____18159 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_Pervasives_Native.Some true
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.false_lid
                   -> FStar_Pervasives_Native.Some false
               | uu____18167 -> FStar_Pervasives_Native.None  in
             let rec args_are_binders args bs =
               match (args, bs) with
               | ((t,uu____18216)::args1,(bv,uu____18219)::bs1) ->
                   let uu____18253 =
                     let uu____18254 = FStar_Syntax_Subst.compress t  in
                     uu____18254.FStar_Syntax_Syntax.n  in
                   (match uu____18253 with
                    | FStar_Syntax_Syntax.Tm_name bv' ->
                        (FStar_Syntax_Syntax.bv_eq bv bv') &&
                          (args_are_binders args1 bs1)
                    | uu____18258 -> false)
               | ([],[]) -> true
               | (uu____18279,uu____18280) -> false  in
             let is_applied bs t =
               if (cfg.debug).wpe
               then
                 (let uu____18321 = FStar_Syntax_Print.term_to_string t  in
                  let uu____18322 = FStar_Syntax_Print.tag_of_term t  in
                  FStar_Util.print2 "WPE> is_applied %s -- %s\n" uu____18321
                    uu____18322)
               else ();
               (let uu____18324 = FStar_Syntax_Util.head_and_args' t  in
                match uu____18324 with
                | (hd1,args) ->
                    let uu____18357 =
                      let uu____18358 = FStar_Syntax_Subst.compress hd1  in
                      uu____18358.FStar_Syntax_Syntax.n  in
                    (match uu____18357 with
                     | FStar_Syntax_Syntax.Tm_name bv when
                         args_are_binders args bs ->
                         (if (cfg.debug).wpe
                          then
                            (let uu____18365 =
                               FStar_Syntax_Print.term_to_string t  in
                             let uu____18366 =
                               FStar_Syntax_Print.bv_to_string bv  in
                             let uu____18367 =
                               FStar_Syntax_Print.term_to_string hd1  in
                             FStar_Util.print3
                               "WPE> got it\n>>>>top = %s\n>>>>b = %s\n>>>>hd = %s\n"
                               uu____18365 uu____18366 uu____18367)
                          else ();
                          FStar_Pervasives_Native.Some bv)
                     | uu____18369 -> FStar_Pervasives_Native.None))
                in
             let is_applied_maybe_squashed bs t =
               if (cfg.debug).wpe
               then
                 (let uu____18386 = FStar_Syntax_Print.term_to_string t  in
                  let uu____18387 = FStar_Syntax_Print.tag_of_term t  in
                  FStar_Util.print2
                    "WPE> is_applied_maybe_squashed %s -- %s\n" uu____18386
                    uu____18387)
               else ();
               (let uu____18389 = FStar_Syntax_Util.is_squash t  in
                match uu____18389 with
                | FStar_Pervasives_Native.Some (uu____18400,t') ->
                    is_applied bs t'
                | uu____18412 ->
                    let uu____18421 = FStar_Syntax_Util.is_auto_squash t  in
                    (match uu____18421 with
                     | FStar_Pervasives_Native.Some (uu____18432,t') ->
                         is_applied bs t'
                     | uu____18444 -> is_applied bs t))
                in
             let is_quantified_const bv phi =
               let uu____18468 =
                 FStar_Syntax_Util.destruct_typ_as_formula phi  in
               match uu____18468 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
                   (lid,(p,uu____18475)::(q,uu____18477)::[])) when
                   FStar_Ident.lid_equals lid FStar_Parser_Const.imp_lid ->
                   (if (cfg.debug).wpe
                    then
                      (let uu____18505 = FStar_Syntax_Print.term_to_string p
                          in
                       let uu____18506 = FStar_Syntax_Print.term_to_string q
                          in
                       FStar_Util.print2 "WPE> p = (%s); q = (%s)\n"
                         uu____18505 uu____18506)
                    else ();
                    (let uu____18508 =
                       FStar_Syntax_Util.destruct_typ_as_formula p  in
                     match uu____18508 with
                     | FStar_Pervasives_Native.None  ->
                         let uu____18513 =
                           let uu____18514 = FStar_Syntax_Subst.compress p
                              in
                           uu____18514.FStar_Syntax_Syntax.n  in
                         (match uu____18513 with
                          | FStar_Syntax_Syntax.Tm_bvar bv' when
                              FStar_Syntax_Syntax.bv_eq bv bv' ->
                              (if (cfg.debug).wpe
                               then FStar_Util.print_string "WPE> Case 1\n"
                               else ();
                               (let uu____18522 =
                                  FStar_Syntax_Subst.subst
                                    [FStar_Syntax_Syntax.NT
                                       (bv, FStar_Syntax_Util.t_true)] q
                                   in
                                FStar_Pervasives_Native.Some uu____18522))
                          | uu____18525 -> FStar_Pervasives_Native.None)
                     | FStar_Pervasives_Native.Some
                         (FStar_Syntax_Util.BaseConn
                         (lid1,(p1,uu____18528)::[])) when
                         FStar_Ident.lid_equals lid1
                           FStar_Parser_Const.not_lid
                         ->
                         let uu____18545 =
                           let uu____18546 = FStar_Syntax_Subst.compress p1
                              in
                           uu____18546.FStar_Syntax_Syntax.n  in
                         (match uu____18545 with
                          | FStar_Syntax_Syntax.Tm_bvar bv' when
                              FStar_Syntax_Syntax.bv_eq bv bv' ->
                              (if (cfg.debug).wpe
                               then FStar_Util.print_string "WPE> Case 2\n"
                               else ();
                               (let uu____18554 =
                                  FStar_Syntax_Subst.subst
                                    [FStar_Syntax_Syntax.NT
                                       (bv, FStar_Syntax_Util.t_false)] q
                                   in
                                FStar_Pervasives_Native.Some uu____18554))
                          | uu____18557 -> FStar_Pervasives_Native.None)
                     | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
                         (bs,pats,phi1)) ->
                         let uu____18561 =
                           FStar_Syntax_Util.destruct_typ_as_formula phi1  in
                         (match uu____18561 with
                          | FStar_Pervasives_Native.None  ->
                              let uu____18566 =
                                is_applied_maybe_squashed bs phi1  in
                              (match uu____18566 with
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
                                     let uu____18577 =
                                       FStar_Syntax_Subst.subst
                                         [FStar_Syntax_Syntax.NT (bv, ftrue)]
                                         q
                                        in
                                     FStar_Pervasives_Native.Some uu____18577))
                               | uu____18580 -> FStar_Pervasives_Native.None)
                          | FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.BaseConn
                              (lid1,(p1,uu____18585)::[])) when
                              FStar_Ident.lid_equals lid1
                                FStar_Parser_Const.not_lid
                              ->
                              let uu____18602 =
                                is_applied_maybe_squashed bs p1  in
                              (match uu____18602 with
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
                                     let uu____18613 =
                                       FStar_Syntax_Subst.subst
                                         [FStar_Syntax_Syntax.NT (bv, ffalse)]
                                         q
                                        in
                                     FStar_Pervasives_Native.Some uu____18613))
                               | uu____18616 -> FStar_Pervasives_Native.None)
                          | uu____18619 -> FStar_Pervasives_Native.None)
                     | uu____18622 -> FStar_Pervasives_Native.None))
               | uu____18625 -> FStar_Pervasives_Native.None  in
             let is_forall_const phi =
               let uu____18638 =
                 FStar_Syntax_Util.destruct_typ_as_formula phi  in
               match uu____18638 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
                   ((bv,uu____18644)::[],uu____18645,phi')) ->
                   (if (cfg.debug).wpe
                    then
                      (let uu____18656 = FStar_Syntax_Print.bv_to_string bv
                          in
                       let uu____18657 =
                         FStar_Syntax_Print.term_to_string phi'  in
                       FStar_Util.print2 "WPE> QAll [%s] %s\n" uu____18656
                         uu____18657)
                    else ();
                    is_quantified_const bv phi')
               | uu____18659 -> FStar_Pervasives_Native.None  in
             let is_const_match phi =
               let uu____18672 =
                 let uu____18673 = FStar_Syntax_Subst.compress phi  in
                 uu____18673.FStar_Syntax_Syntax.n  in
               match uu____18672 with
               | FStar_Syntax_Syntax.Tm_match (uu____18678,br::brs) ->
                   let uu____18745 = br  in
                   (match uu____18745 with
                    | (uu____18762,uu____18763,e) ->
                        let r =
                          let uu____18784 = simp_t e  in
                          match uu____18784 with
                          | FStar_Pervasives_Native.None  ->
                              FStar_Pervasives_Native.None
                          | FStar_Pervasives_Native.Some b ->
                              let uu____18790 =
                                FStar_List.for_all
                                  (fun uu____18808  ->
                                     match uu____18808 with
                                     | (uu____18821,uu____18822,e') ->
                                         let uu____18836 = simp_t e'  in
                                         uu____18836 =
                                           (FStar_Pervasives_Native.Some b))
                                  brs
                                 in
                              if uu____18790
                              then FStar_Pervasives_Native.Some b
                              else FStar_Pervasives_Native.None
                           in
                        r)
               | uu____18844 -> FStar_Pervasives_Native.None  in
             let maybe_auto_squash t =
               let uu____18853 = FStar_Syntax_Util.is_sub_singleton t  in
               if uu____18853
               then t
               else
                 FStar_Syntax_Util.mk_auto_squash FStar_Syntax_Syntax.U_zero
                   t
                in
             let squashed_head_un_auto_squash_args t =
               let maybe_un_auto_squash_arg uu____18884 =
                 match uu____18884 with
                 | (t1,q) ->
                     let uu____18897 = FStar_Syntax_Util.is_auto_squash t1
                        in
                     (match uu____18897 with
                      | FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.U_zero ,t2) -> (t2, q)
                      | uu____18925 -> (t1, q))
                  in
               let uu____18936 = FStar_Syntax_Util.head_and_args t  in
               match uu____18936 with
               | (head1,args) ->
                   let args1 = FStar_List.map maybe_un_auto_squash_arg args
                      in
                   FStar_Syntax_Syntax.mk_Tm_app head1 args1
                     FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
                in
             let rec clearly_inhabited ty =
               let uu____19002 =
                 let uu____19003 = FStar_Syntax_Util.unmeta ty  in
                 uu____19003.FStar_Syntax_Syntax.n  in
               match uu____19002 with
               | FStar_Syntax_Syntax.Tm_uinst (t,uu____19007) ->
                   clearly_inhabited t
               | FStar_Syntax_Syntax.Tm_arrow (uu____19012,c) ->
                   clearly_inhabited (FStar_Syntax_Util.comp_result c)
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   let l = FStar_Syntax_Syntax.lid_of_fv fv  in
                   (((FStar_Ident.lid_equals l FStar_Parser_Const.int_lid) ||
                       (FStar_Ident.lid_equals l FStar_Parser_Const.bool_lid))
                      ||
                      (FStar_Ident.lid_equals l FStar_Parser_Const.string_lid))
                     || (FStar_Ident.lid_equals l FStar_Parser_Const.exn_lid)
               | uu____19032 -> false  in
             let simplify1 arg =
               let uu____19057 = simp_t (FStar_Pervasives_Native.fst arg)  in
               (uu____19057, arg)  in
             let uu____19066 = is_forall_const tm1  in
             match uu____19066 with
             | FStar_Pervasives_Native.Some tm' ->
                 (if (cfg.debug).wpe
                  then
                    (let uu____19071 = FStar_Syntax_Print.term_to_string tm1
                        in
                     let uu____19072 = FStar_Syntax_Print.term_to_string tm'
                        in
                     FStar_Util.print2 "WPE> %s ~> %s\n" uu____19071
                       uu____19072)
                  else ();
                  (let uu____19074 = norm cfg env [] tm'  in
                   maybe_simplify_aux cfg env stack uu____19074))
             | FStar_Pervasives_Native.None  ->
                 let uu____19075 =
                   let uu____19076 = FStar_Syntax_Subst.compress tm1  in
                   uu____19076.FStar_Syntax_Syntax.n  in
                 (match uu____19075 with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                           ({
                              FStar_Syntax_Syntax.n =
                                FStar_Syntax_Syntax.Tm_fvar fv;
                              FStar_Syntax_Syntax.pos = uu____19080;
                              FStar_Syntax_Syntax.vars = uu____19081;_},uu____19082);
                         FStar_Syntax_Syntax.pos = uu____19083;
                         FStar_Syntax_Syntax.vars = uu____19084;_},args)
                      ->
                      let uu____19110 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid
                         in
                      if uu____19110
                      then
                        let uu____19111 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        (match uu____19111 with
                         | (FStar_Pervasives_Native.Some (true ),uu____19156)::
                             (uu____19157,(arg,uu____19159))::[] ->
                             maybe_auto_squash arg
                         | (uu____19208,(arg,uu____19210))::(FStar_Pervasives_Native.Some
                                                             (true
                                                             ),uu____19211)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____19260)::uu____19261::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____19312::(FStar_Pervasives_Native.Some (false
                                         ),uu____19313)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____19364 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____19378 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid
                            in
                         if uu____19378
                         then
                           let uu____19379 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify1)
                              in
                           match uu____19379 with
                           | (FStar_Pervasives_Native.Some (true
                              ),uu____19424)::uu____19425::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____19476::(FStar_Pervasives_Native.Some (true
                                           ),uu____19477)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false
                              ),uu____19528)::(uu____19529,(arg,uu____19531))::[]
                               -> maybe_auto_squash arg
                           | (uu____19580,(arg,uu____19582))::(FStar_Pervasives_Native.Some
                                                               (false
                                                               ),uu____19583)::[]
                               -> maybe_auto_squash arg
                           | uu____19632 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____19646 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid
                               in
                            if uu____19646
                            then
                              let uu____19647 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify1)
                                 in
                              match uu____19647 with
                              | uu____19692::(FStar_Pervasives_Native.Some
                                              (true ),uu____19693)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false
                                 ),uu____19744)::uu____19745::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true
                                 ),uu____19796)::(uu____19797,(arg,uu____19799))::[]
                                  -> maybe_auto_squash arg
                              | (uu____19848,(p,uu____19850))::(uu____19851,
                                                                (q,uu____19853))::[]
                                  ->
                                  let uu____19900 =
                                    FStar_Syntax_Util.term_eq p q  in
                                  (if uu____19900
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____19902 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____19916 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid
                                  in
                               if uu____19916
                               then
                                 let uu____19917 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify1)
                                    in
                                 match uu____19917 with
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____19962)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____19963)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____20014)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____20015)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____20066)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____20067)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____20118)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____20119)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____20170,(arg,uu____20172))::(FStar_Pervasives_Native.Some
                                                                    (true
                                                                    ),uu____20173)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____20222)::(uu____20223,(arg,uu____20225))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____20274,(arg,uu____20276))::(FStar_Pervasives_Native.Some
                                                                    (false
                                                                    ),uu____20277)::[]
                                     ->
                                     let uu____20326 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____20326
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____20327)::(uu____20328,(arg,uu____20330))::[]
                                     ->
                                     let uu____20379 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____20379
                                 | (uu____20380,(p,uu____20382))::(uu____20383,
                                                                   (q,uu____20385))::[]
                                     ->
                                     let uu____20432 =
                                       FStar_Syntax_Util.term_eq p q  in
                                     (if uu____20432
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____20434 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____20448 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid
                                     in
                                  if uu____20448
                                  then
                                    let uu____20449 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify1)
                                       in
                                    match uu____20449 with
                                    | (FStar_Pervasives_Native.Some (true
                                       ),uu____20494)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false
                                       ),uu____20525)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____20556 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____20570 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid
                                        in
                                     if uu____20570
                                     then
                                       match args with
                                       | (t,uu____20572)::[] ->
                                           let uu____20589 =
                                             let uu____20590 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____20590.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____20589 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____20593::[],body,uu____20595)
                                                ->
                                                let uu____20622 = simp_t body
                                                   in
                                                (match uu____20622 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____20625 -> tm1)
                                            | uu____20628 -> tm1)
                                       | (ty,FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____20630))::(t,uu____20632)::[]
                                           ->
                                           let uu____20659 =
                                             let uu____20660 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____20660.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____20659 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____20663::[],body,uu____20665)
                                                ->
                                                let uu____20692 = simp_t body
                                                   in
                                                (match uu____20692 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false ) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____20695 -> tm1)
                                            | uu____20698 -> tm1)
                                       | uu____20699 -> tm1
                                     else
                                       (let uu____20709 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid
                                           in
                                        if uu____20709
                                        then
                                          match args with
                                          | (t,uu____20711)::[] ->
                                              let uu____20728 =
                                                let uu____20729 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____20729.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____20728 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____20732::[],body,uu____20734)
                                                   ->
                                                   let uu____20761 =
                                                     simp_t body  in
                                                   (match uu____20761 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____20764 -> tm1)
                                               | uu____20767 -> tm1)
                                          | (ty,FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____20769))::(t,uu____20771)::[]
                                              ->
                                              let uu____20798 =
                                                let uu____20799 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____20799.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____20798 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____20802::[],body,uu____20804)
                                                   ->
                                                   let uu____20831 =
                                                     simp_t body  in
                                                   (match uu____20831 with
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
                                                    | uu____20834 -> tm1)
                                               | uu____20837 -> tm1)
                                          | uu____20838 -> tm1
                                        else
                                          (let uu____20848 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid
                                              in
                                           if uu____20848
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____20849;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____20850;_},uu____20851)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____20868;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____20869;_},uu____20870)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____20887 -> tm1
                                           else
                                             (let uu____20897 =
                                                FStar_Syntax_Util.is_auto_squash
                                                  tm1
                                                 in
                                              match uu____20897 with
                                              | FStar_Pervasives_Native.Some
                                                  (FStar_Syntax_Syntax.U_zero
                                                   ,t)
                                                  when
                                                  FStar_Syntax_Util.is_sub_singleton
                                                    t
                                                  -> t
                                              | uu____20917 ->
                                                  reduce_equality cfg env
                                                    stack tm1))))))))
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____20927;
                         FStar_Syntax_Syntax.vars = uu____20928;_},args)
                      ->
                      let uu____20950 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid
                         in
                      if uu____20950
                      then
                        let uu____20951 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        (match uu____20951 with
                         | (FStar_Pervasives_Native.Some (true ),uu____20996)::
                             (uu____20997,(arg,uu____20999))::[] ->
                             maybe_auto_squash arg
                         | (uu____21048,(arg,uu____21050))::(FStar_Pervasives_Native.Some
                                                             (true
                                                             ),uu____21051)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____21100)::uu____21101::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____21152::(FStar_Pervasives_Native.Some (false
                                         ),uu____21153)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____21204 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____21218 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid
                            in
                         if uu____21218
                         then
                           let uu____21219 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify1)
                              in
                           match uu____21219 with
                           | (FStar_Pervasives_Native.Some (true
                              ),uu____21264)::uu____21265::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____21316::(FStar_Pervasives_Native.Some (true
                                           ),uu____21317)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false
                              ),uu____21368)::(uu____21369,(arg,uu____21371))::[]
                               -> maybe_auto_squash arg
                           | (uu____21420,(arg,uu____21422))::(FStar_Pervasives_Native.Some
                                                               (false
                                                               ),uu____21423)::[]
                               -> maybe_auto_squash arg
                           | uu____21472 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____21486 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid
                               in
                            if uu____21486
                            then
                              let uu____21487 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify1)
                                 in
                              match uu____21487 with
                              | uu____21532::(FStar_Pervasives_Native.Some
                                              (true ),uu____21533)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false
                                 ),uu____21584)::uu____21585::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true
                                 ),uu____21636)::(uu____21637,(arg,uu____21639))::[]
                                  -> maybe_auto_squash arg
                              | (uu____21688,(p,uu____21690))::(uu____21691,
                                                                (q,uu____21693))::[]
                                  ->
                                  let uu____21740 =
                                    FStar_Syntax_Util.term_eq p q  in
                                  (if uu____21740
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____21742 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____21756 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid
                                  in
                               if uu____21756
                               then
                                 let uu____21757 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify1)
                                    in
                                 match uu____21757 with
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____21802)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____21803)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____21854)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____21855)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____21906)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____21907)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____21958)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____21959)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____22010,(arg,uu____22012))::(FStar_Pervasives_Native.Some
                                                                    (true
                                                                    ),uu____22013)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____22062)::(uu____22063,(arg,uu____22065))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____22114,(arg,uu____22116))::(FStar_Pervasives_Native.Some
                                                                    (false
                                                                    ),uu____22117)::[]
                                     ->
                                     let uu____22166 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____22166
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____22167)::(uu____22168,(arg,uu____22170))::[]
                                     ->
                                     let uu____22219 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____22219
                                 | (uu____22220,(p,uu____22222))::(uu____22223,
                                                                   (q,uu____22225))::[]
                                     ->
                                     let uu____22272 =
                                       FStar_Syntax_Util.term_eq p q  in
                                     (if uu____22272
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____22274 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____22288 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid
                                     in
                                  if uu____22288
                                  then
                                    let uu____22289 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify1)
                                       in
                                    match uu____22289 with
                                    | (FStar_Pervasives_Native.Some (true
                                       ),uu____22334)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false
                                       ),uu____22365)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____22396 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____22410 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid
                                        in
                                     if uu____22410
                                     then
                                       match args with
                                       | (t,uu____22412)::[] ->
                                           let uu____22429 =
                                             let uu____22430 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____22430.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____22429 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____22433::[],body,uu____22435)
                                                ->
                                                let uu____22462 = simp_t body
                                                   in
                                                (match uu____22462 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____22465 -> tm1)
                                            | uu____22468 -> tm1)
                                       | (ty,FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____22470))::(t,uu____22472)::[]
                                           ->
                                           let uu____22499 =
                                             let uu____22500 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____22500.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____22499 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____22503::[],body,uu____22505)
                                                ->
                                                let uu____22532 = simp_t body
                                                   in
                                                (match uu____22532 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false ) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____22535 -> tm1)
                                            | uu____22538 -> tm1)
                                       | uu____22539 -> tm1
                                     else
                                       (let uu____22549 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid
                                           in
                                        if uu____22549
                                        then
                                          match args with
                                          | (t,uu____22551)::[] ->
                                              let uu____22568 =
                                                let uu____22569 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____22569.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____22568 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____22572::[],body,uu____22574)
                                                   ->
                                                   let uu____22601 =
                                                     simp_t body  in
                                                   (match uu____22601 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____22604 -> tm1)
                                               | uu____22607 -> tm1)
                                          | (ty,FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____22609))::(t,uu____22611)::[]
                                              ->
                                              let uu____22638 =
                                                let uu____22639 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____22639.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____22638 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____22642::[],body,uu____22644)
                                                   ->
                                                   let uu____22671 =
                                                     simp_t body  in
                                                   (match uu____22671 with
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
                                                    | uu____22674 -> tm1)
                                               | uu____22677 -> tm1)
                                          | uu____22678 -> tm1
                                        else
                                          (let uu____22688 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid
                                              in
                                           if uu____22688
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____22689;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____22690;_},uu____22691)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____22708;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____22709;_},uu____22710)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____22727 -> tm1
                                           else
                                             (let uu____22737 =
                                                FStar_Syntax_Util.is_auto_squash
                                                  tm1
                                                 in
                                              match uu____22737 with
                                              | FStar_Pervasives_Native.Some
                                                  (FStar_Syntax_Syntax.U_zero
                                                   ,t)
                                                  when
                                                  FStar_Syntax_Util.is_sub_singleton
                                                    t
                                                  -> t
                                              | uu____22757 ->
                                                  reduce_equality cfg env
                                                    stack tm1))))))))
                  | FStar_Syntax_Syntax.Tm_refine (bv,t) ->
                      let uu____22772 = simp_t t  in
                      (match uu____22772 with
                       | FStar_Pervasives_Native.Some (true ) ->
                           bv.FStar_Syntax_Syntax.sort
                       | FStar_Pervasives_Native.Some (false ) -> tm1
                       | FStar_Pervasives_Native.None  -> tm1)
                  | FStar_Syntax_Syntax.Tm_match uu____22775 ->
                      let uu____22798 = is_const_match tm1  in
                      (match uu____22798 with
                       | FStar_Pervasives_Native.Some (true ) ->
                           w FStar_Syntax_Util.t_true
                       | FStar_Pervasives_Native.Some (false ) ->
                           w FStar_Syntax_Util.t_false
                       | FStar_Pervasives_Native.None  -> tm1)
                  | uu____22801 -> tm1))

and (rebuild :
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          log cfg
            (fun uu____22811  ->
               (let uu____22813 = FStar_Syntax_Print.tag_of_term t  in
                let uu____22814 = FStar_Syntax_Print.term_to_string t  in
                let uu____22815 =
                  FStar_Util.string_of_int (FStar_List.length env)  in
                let uu____22822 =
                  let uu____22823 =
                    let uu____22826 = firstn (Prims.parse_int "4") stack  in
                    FStar_All.pipe_left FStar_Pervasives_Native.fst
                      uu____22826
                     in
                  stack_to_string uu____22823  in
                FStar_Util.print4
                  ">>> %s\nRebuild %s with %s env elements and top of the stack %s \n"
                  uu____22813 uu____22814 uu____22815 uu____22822);
               (let uu____22849 =
                  FStar_TypeChecker_Env.debug cfg.tcenv
                    (FStar_Options.Other "NormRebuild")
                   in
                if uu____22849
                then
                  let uu____22850 = FStar_Syntax_Util.unbound_variables t  in
                  match uu____22850 with
                  | [] -> ()
                  | bvs ->
                      ((let uu____22857 = FStar_Syntax_Print.tag_of_term t
                           in
                        let uu____22858 = FStar_Syntax_Print.term_to_string t
                           in
                        let uu____22859 =
                          let uu____22860 =
                            FStar_All.pipe_right bvs
                              (FStar_List.map FStar_Syntax_Print.bv_to_string)
                             in
                          FStar_All.pipe_right uu____22860
                            (FStar_String.concat ", ")
                           in
                        FStar_Util.print3
                          "!!! Rebuild (%s) %s, free vars=%s\n" uu____22857
                          uu____22858 uu____22859);
                       failwith "DIE!")
                else ()));
          (let t1 = maybe_simplify cfg env stack t  in
           match stack with
           | [] -> t1
           | (Debug (tm,time_then))::stack1 ->
               (if (cfg.debug).print_normalized
                then
                  (let time_now = FStar_Util.now ()  in
                   let uu____22878 =
                     let uu____22879 =
                       let uu____22880 =
                         FStar_Util.time_diff time_then time_now  in
                       FStar_Pervasives_Native.snd uu____22880  in
                     FStar_Util.string_of_int uu____22879  in
                   let uu____22885 = FStar_Syntax_Print.term_to_string tm  in
                   let uu____22886 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.print3 "Normalized (%s ms) %s\n\tto %s\n"
                     uu____22878 uu____22885 uu____22886)
                else ();
                rebuild cfg env stack1 t1)
           | (Cfg cfg1)::stack1 -> rebuild cfg1 env stack1 t1
           | (Meta (uu____22892,m,r))::stack1 ->
               let t2 = mk (FStar_Syntax_Syntax.Tm_meta (t1, m)) r  in
               rebuild cfg env stack1 t2
           | (MemoLazy r)::stack1 ->
               (set_memo cfg r (env, t1);
                log cfg
                  (fun uu____22943  ->
                     let uu____22944 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 "\tSet memo %s\n" uu____22944);
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
               let uu____22982 =
                 let uu___214_22983 = FStar_Syntax_Util.abs bs1 t1 lopt1  in
                 {
                   FStar_Syntax_Syntax.n =
                     (uu___214_22983.FStar_Syntax_Syntax.n);
                   FStar_Syntax_Syntax.pos = r;
                   FStar_Syntax_Syntax.vars =
                     (uu___214_22983.FStar_Syntax_Syntax.vars)
                 }  in
               rebuild cfg env stack1 uu____22982
           | (Arg (Univ uu____22986,uu____22987,uu____22988))::uu____22989 ->
               failwith "Impossible"
           | (Arg (Dummy ,uu____22992,uu____22993))::uu____22994 ->
               failwith "Impossible"
           | (UnivArgs (us,r))::stack1 ->
               let t2 = FStar_Syntax_Syntax.mk_Tm_uinst t1 us  in
               rebuild cfg env stack1 t2
           | (Arg (Clos (env_arg,tm,uu____23009,uu____23010),aq,r))::stack1
               when
               let uu____23060 = head_of t1  in
               FStar_Syntax_Util.is_fstar_tactics_by_tactic uu____23060 ->
               let t2 =
                 let uu____23064 =
                   let uu____23069 =
                     let uu____23070 = closure_as_term cfg env_arg tm  in
                     (uu____23070, aq)  in
                   FStar_Syntax_Syntax.extend_app t1 uu____23069  in
                 uu____23064 FStar_Pervasives_Native.None r  in
               rebuild cfg env stack1 t2
           | (Arg (Clos (env_arg,tm,m,uu____23080),aq,r))::stack1 ->
               (log cfg
                  (fun uu____23133  ->
                     let uu____23134 = FStar_Syntax_Print.term_to_string tm
                        in
                     FStar_Util.print1 "Rebuilding with arg %s\n" uu____23134);
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
                  (let uu____23146 = FStar_ST.op_Bang m  in
                   match uu____23146 with
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
                   | FStar_Pervasives_Native.Some (uu____23289,a) ->
                       let t2 =
                         FStar_Syntax_Syntax.extend_app t1 (a, aq)
                           FStar_Pervasives_Native.None r
                          in
                       rebuild cfg env_arg stack1 t2))
           | (App (env1,head1,aq,r))::stack' when should_reify cfg stack ->
               let t0 = t1  in
               let fallback msg uu____23342 =
                 log cfg
                   (fun uu____23346  ->
                      let uu____23347 = FStar_Syntax_Print.term_to_string t1
                         in
                      FStar_Util.print2 "Not reifying%s: %s\n" msg
                        uu____23347);
                 (let t2 =
                    FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                      FStar_Pervasives_Native.None r
                     in
                  rebuild cfg env1 stack' t2)
                  in
               let uu____23353 =
                 let uu____23354 = FStar_Syntax_Subst.compress t1  in
                 uu____23354.FStar_Syntax_Syntax.n  in
               (match uu____23353 with
                | FStar_Syntax_Syntax.Tm_meta
                    (t2,FStar_Syntax_Syntax.Meta_monadic (m,ty)) ->
                    do_reify_monadic (fallback " (1)") cfg env1 stack t2 m ty
                | FStar_Syntax_Syntax.Tm_meta
                    (t2,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,ty))
                    ->
                    let lifted =
                      let uu____23381 = closure_as_term cfg env1 ty  in
                      reify_lift cfg t2 msrc mtgt uu____23381  in
                    (log cfg
                       (fun uu____23385  ->
                          let uu____23386 =
                            FStar_Syntax_Print.term_to_string lifted  in
                          FStar_Util.print1 "Reified lift to (1): %s\n"
                            uu____23386);
                     (let uu____23387 = FStar_List.tl stack  in
                      norm cfg env1 uu____23387 lifted))
                | FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reflect uu____23388);
                       FStar_Syntax_Syntax.pos = uu____23389;
                       FStar_Syntax_Syntax.vars = uu____23390;_},(e,uu____23392)::[])
                    -> norm cfg env1 stack' e
                | FStar_Syntax_Syntax.Tm_app uu____23421 when
                    (cfg.steps).primops ->
                    let uu____23436 = FStar_Syntax_Util.head_and_args t1  in
                    (match uu____23436 with
                     | (hd1,args) ->
                         let uu____23473 =
                           let uu____23474 = FStar_Syntax_Util.un_uinst hd1
                              in
                           uu____23474.FStar_Syntax_Syntax.n  in
                         (match uu____23473 with
                          | FStar_Syntax_Syntax.Tm_fvar fv ->
                              let uu____23478 = find_prim_step cfg fv  in
                              (match uu____23478 with
                               | FStar_Pervasives_Native.Some
                                   { name = uu____23481; arity = uu____23482;
                                     auto_reflect =
                                       FStar_Pervasives_Native.Some n1;
                                     strong_reduction_ok = uu____23484;
                                     requires_binder_substitution =
                                       uu____23485;
                                     interpretation = uu____23486;_}
                                   when (FStar_List.length args) = n1 ->
                                   norm cfg env1 stack' t1
                               | uu____23502 -> fallback " (3)" ())
                          | uu____23505 -> fallback " (4)" ()))
                | uu____23506 -> fallback " (2)" ())
           | (App (env1,head1,aq,r))::stack1 ->
               let t2 =
                 FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                   FStar_Pervasives_Native.None r
                  in
               rebuild cfg env1 stack1 t2
           | (Match (env',branches,cfg1,r))::stack1 ->
               (log cfg1
                  (fun uu____23529  ->
                     let uu____23530 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1
                       "Rebuilding with match, scrutinee is %s ...\n"
                       uu____23530);
                (let scrutinee_env = env  in
                 let env1 = env'  in
                 let scrutinee = t1  in
                 let norm_and_rebuild_match uu____23539 =
                   log cfg1
                     (fun uu____23544  ->
                        let uu____23545 =
                          FStar_Syntax_Print.term_to_string scrutinee  in
                        let uu____23546 =
                          let uu____23547 =
                            FStar_All.pipe_right branches
                              (FStar_List.map
                                 (fun uu____23574  ->
                                    match uu____23574 with
                                    | (p,uu____23584,uu____23585) ->
                                        FStar_Syntax_Print.pat_to_string p))
                             in
                          FStar_All.pipe_right uu____23547
                            (FStar_String.concat "\n\t")
                           in
                        FStar_Util.print2
                          "match is irreducible: scrutinee=%s\nbranches=%s\n"
                          uu____23545 uu____23546);
                   (let whnf = (cfg1.steps).weak || (cfg1.steps).hnf  in
                    let cfg_exclude_zeta =
                      let new_delta =
                        FStar_All.pipe_right cfg1.delta_level
                          (FStar_List.filter
                             (fun uu___121_23602  ->
                                match uu___121_23602 with
                                | FStar_TypeChecker_Env.Inlining  -> true
                                | FStar_TypeChecker_Env.Eager_unfolding_only 
                                    -> true
                                | uu____23603 -> false))
                         in
                      let steps =
                        let uu___215_23605 = cfg1.steps  in
                        {
                          beta = (uu___215_23605.beta);
                          iota = (uu___215_23605.iota);
                          zeta = false;
                          weak = (uu___215_23605.weak);
                          hnf = (uu___215_23605.hnf);
                          primops = (uu___215_23605.primops);
                          do_not_unfold_pure_lets =
                            (uu___215_23605.do_not_unfold_pure_lets);
                          unfold_until = FStar_Pervasives_Native.None;
                          unfold_only = FStar_Pervasives_Native.None;
                          unfold_fully = (uu___215_23605.unfold_fully);
                          unfold_attr = FStar_Pervasives_Native.None;
                          unfold_tac = false;
                          pure_subterms_within_computations =
                            (uu___215_23605.pure_subterms_within_computations);
                          simplify = (uu___215_23605.simplify);
                          erase_universes = (uu___215_23605.erase_universes);
                          allow_unbound_universes =
                            (uu___215_23605.allow_unbound_universes);
                          reify_ = (uu___215_23605.reify_);
                          compress_uvars = (uu___215_23605.compress_uvars);
                          no_full_norm = (uu___215_23605.no_full_norm);
                          check_no_uvars = (uu___215_23605.check_no_uvars);
                          unmeta = (uu___215_23605.unmeta);
                          unascribe = (uu___215_23605.unascribe);
                          in_full_norm_request =
                            (uu___215_23605.in_full_norm_request);
                          weakly_reduce_scrutinee =
                            (uu___215_23605.weakly_reduce_scrutinee)
                        }  in
                      let uu___216_23610 = cfg1  in
                      {
                        steps;
                        tcenv = (uu___216_23610.tcenv);
                        debug = (uu___216_23610.debug);
                        delta_level = new_delta;
                        primitive_steps = (uu___216_23610.primitive_steps);
                        strong = true;
                        memoize_lazy = (uu___216_23610.memoize_lazy);
                        normalize_pure_lets =
                          (uu___216_23610.normalize_pure_lets)
                      }  in
                    let norm_or_whnf env2 t2 =
                      if whnf
                      then closure_as_term cfg_exclude_zeta env2 t2
                      else norm cfg_exclude_zeta env2 [] t2  in
                    let rec norm_pat env2 p =
                      match p.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_constant uu____23682 ->
                          (p, env2)
                      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                          let uu____23711 =
                            FStar_All.pipe_right pats
                              (FStar_List.fold_left
                                 (fun uu____23795  ->
                                    fun uu____23796  ->
                                      match (uu____23795, uu____23796) with
                                      | ((pats1,env3),(p1,b)) ->
                                          let uu____23935 = norm_pat env3 p1
                                             in
                                          (match uu____23935 with
                                           | (p2,env4) ->
                                               (((p2, b) :: pats1), env4)))
                                 ([], env2))
                             in
                          (match uu____23711 with
                           | (pats1,env3) ->
                               ((let uu___217_24097 = p  in
                                 {
                                   FStar_Syntax_Syntax.v =
                                     (FStar_Syntax_Syntax.Pat_cons
                                        (fv, (FStar_List.rev pats1)));
                                   FStar_Syntax_Syntax.p =
                                     (uu___217_24097.FStar_Syntax_Syntax.p)
                                 }), env3))
                      | FStar_Syntax_Syntax.Pat_var x ->
                          let x1 =
                            let uu___218_24116 = x  in
                            let uu____24117 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___218_24116.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___218_24116.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____24117
                            }  in
                          ((let uu___219_24131 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_var x1);
                              FStar_Syntax_Syntax.p =
                                (uu___219_24131.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_wild x ->
                          let x1 =
                            let uu___220_24142 = x  in
                            let uu____24143 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___220_24142.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___220_24142.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____24143
                            }  in
                          ((let uu___221_24157 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_wild x1);
                              FStar_Syntax_Syntax.p =
                                (uu___221_24157.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                          let x1 =
                            let uu___222_24173 = x  in
                            let uu____24174 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___222_24173.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___222_24173.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____24174
                            }  in
                          let t3 = norm_or_whnf env2 t2  in
                          ((let uu___223_24189 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_dot_term (x1, t3));
                              FStar_Syntax_Syntax.p =
                                (uu___223_24189.FStar_Syntax_Syntax.p)
                            }), env2)
                       in
                    let branches1 =
                      match env1 with
                      | [] when whnf -> branches
                      | uu____24233 ->
                          FStar_All.pipe_right branches
                            (FStar_List.map
                               (fun branch1  ->
                                  let uu____24249 =
                                    FStar_Syntax_Subst.open_branch branch1
                                     in
                                  match uu____24249 with
                                  | (p,wopt,e) ->
                                      let uu____24269 = norm_pat env1 p  in
                                      (match uu____24269 with
                                       | (p1,env2) ->
                                           let wopt1 =
                                             match wopt with
                                             | FStar_Pervasives_Native.None 
                                                 ->
                                                 FStar_Pervasives_Native.None
                                             | FStar_Pervasives_Native.Some w
                                                 ->
                                                 let uu____24324 =
                                                   norm_or_whnf env2 w  in
                                                 FStar_Pervasives_Native.Some
                                                   uu____24324
                                              in
                                           let e1 = norm_or_whnf env2 e  in
                                           FStar_Syntax_Util.branch
                                             (p1, wopt1, e1))))
                       in
                    let scrutinee1 =
                      let uu____24337 =
                        ((((cfg1.steps).iota &&
                             (Prims.op_Negation (cfg1.steps).weak))
                            &&
                            (Prims.op_Negation (cfg1.steps).compress_uvars))
                           && (cfg1.steps).weakly_reduce_scrutinee)
                          && (maybe_weakly_reduced scrutinee)
                         in
                      if uu____24337
                      then
                        norm
                          (let uu___224_24342 = cfg1  in
                           {
                             steps =
                               (let uu___225_24345 = cfg1.steps  in
                                {
                                  beta = (uu___225_24345.beta);
                                  iota = (uu___225_24345.iota);
                                  zeta = (uu___225_24345.zeta);
                                  weak = (uu___225_24345.weak);
                                  hnf = (uu___225_24345.hnf);
                                  primops = (uu___225_24345.primops);
                                  do_not_unfold_pure_lets =
                                    (uu___225_24345.do_not_unfold_pure_lets);
                                  unfold_until =
                                    (uu___225_24345.unfold_until);
                                  unfold_only = (uu___225_24345.unfold_only);
                                  unfold_fully =
                                    (uu___225_24345.unfold_fully);
                                  unfold_attr = (uu___225_24345.unfold_attr);
                                  unfold_tac = (uu___225_24345.unfold_tac);
                                  pure_subterms_within_computations =
                                    (uu___225_24345.pure_subterms_within_computations);
                                  simplify = (uu___225_24345.simplify);
                                  erase_universes =
                                    (uu___225_24345.erase_universes);
                                  allow_unbound_universes =
                                    (uu___225_24345.allow_unbound_universes);
                                  reify_ = (uu___225_24345.reify_);
                                  compress_uvars =
                                    (uu___225_24345.compress_uvars);
                                  no_full_norm =
                                    (uu___225_24345.no_full_norm);
                                  check_no_uvars =
                                    (uu___225_24345.check_no_uvars);
                                  unmeta = (uu___225_24345.unmeta);
                                  unascribe = (uu___225_24345.unascribe);
                                  in_full_norm_request =
                                    (uu___225_24345.in_full_norm_request);
                                  weakly_reduce_scrutinee = false
                                });
                             tcenv = (uu___224_24342.tcenv);
                             debug = (uu___224_24342.debug);
                             delta_level = (uu___224_24342.delta_level);
                             primitive_steps =
                               (uu___224_24342.primitive_steps);
                             strong = (uu___224_24342.strong);
                             memoize_lazy = (uu___224_24342.memoize_lazy);
                             normalize_pure_lets =
                               (uu___224_24342.normalize_pure_lets)
                           }) scrutinee_env [] scrutinee
                      else scrutinee  in
                    let uu____24347 =
                      mk
                        (FStar_Syntax_Syntax.Tm_match (scrutinee1, branches1))
                        r
                       in
                    rebuild cfg1 env1 stack1 uu____24347)
                    in
                 let rec is_cons head1 =
                   let uu____24372 =
                     let uu____24373 = FStar_Syntax_Subst.compress head1  in
                     uu____24373.FStar_Syntax_Syntax.n  in
                   match uu____24372 with
                   | FStar_Syntax_Syntax.Tm_uinst (h,uu____24377) ->
                       is_cons h
                   | FStar_Syntax_Syntax.Tm_constant uu____24382 -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____24383;
                         FStar_Syntax_Syntax.fv_delta = uu____24384;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Data_ctor );_}
                       -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____24385;
                         FStar_Syntax_Syntax.fv_delta = uu____24386;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Record_ctor uu____24387);_}
                       -> true
                   | uu____24394 -> false  in
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
                   let uu____24557 =
                     FStar_Syntax_Util.head_and_args scrutinee1  in
                   match uu____24557 with
                   | (head1,args) ->
                       (match p.FStar_Syntax_Syntax.v with
                        | FStar_Syntax_Syntax.Pat_var bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_wild bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_dot_term uu____24644 ->
                            FStar_Util.Inl []
                        | FStar_Syntax_Syntax.Pat_constant s ->
                            (match scrutinee1.FStar_Syntax_Syntax.n with
                             | FStar_Syntax_Syntax.Tm_constant s' when
                                 FStar_Const.eq_const s s' ->
                                 FStar_Util.Inl []
                             | uu____24683 ->
                                 let uu____24684 =
                                   let uu____24685 = is_cons head1  in
                                   Prims.op_Negation uu____24685  in
                                 FStar_Util.Inr uu____24684)
                        | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                            let uu____24710 =
                              let uu____24711 =
                                FStar_Syntax_Util.un_uinst head1  in
                              uu____24711.FStar_Syntax_Syntax.n  in
                            (match uu____24710 with
                             | FStar_Syntax_Syntax.Tm_fvar fv' when
                                 FStar_Syntax_Syntax.fv_eq fv fv' ->
                                 matches_args [] args arg_pats
                             | uu____24729 ->
                                 let uu____24730 =
                                   let uu____24731 = is_cons head1  in
                                   Prims.op_Negation uu____24731  in
                                 FStar_Util.Inr uu____24730))
                 
                 and matches_args out a p =
                   match (a, p) with
                   | ([],[]) -> FStar_Util.Inl out
                   | ((t2,uu____24808)::rest_a,(p1,uu____24811)::rest_p) ->
                       let uu____24855 = matches_pat t2 p1  in
                       (match uu____24855 with
                        | FStar_Util.Inl s ->
                            matches_args (FStar_List.append out s) rest_a
                              rest_p
                        | m -> m)
                   | uu____24904 -> FStar_Util.Inr false
                  in
                 let rec matches scrutinee1 p =
                   match p with
                   | [] -> norm_and_rebuild_match ()
                   | (p1,wopt,b)::rest ->
                       let uu____25022 = matches_pat scrutinee1 p1  in
                       (match uu____25022 with
                        | FStar_Util.Inr (false ) -> matches scrutinee1 rest
                        | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                        | FStar_Util.Inl s ->
                            (log cfg1
                               (fun uu____25062  ->
                                  let uu____25063 =
                                    FStar_Syntax_Print.pat_to_string p1  in
                                  let uu____25064 =
                                    let uu____25065 =
                                      FStar_List.map
                                        (fun uu____25075  ->
                                           match uu____25075 with
                                           | (uu____25080,t2) ->
                                               FStar_Syntax_Print.term_to_string
                                                 t2) s
                                       in
                                    FStar_All.pipe_right uu____25065
                                      (FStar_String.concat "; ")
                                     in
                                  FStar_Util.print2
                                    "Matches pattern %s with subst = %s\n"
                                    uu____25063 uu____25064);
                             (let env0 = env1  in
                              let env2 =
                                FStar_List.fold_left
                                  (fun env2  ->
                                     fun uu____25112  ->
                                       match uu____25112 with
                                       | (bv,t2) ->
                                           let uu____25135 =
                                             let uu____25142 =
                                               let uu____25145 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   bv
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 uu____25145
                                                in
                                             let uu____25146 =
                                               let uu____25147 =
                                                 let uu____25178 =
                                                   FStar_Util.mk_ref
                                                     (FStar_Pervasives_Native.Some
                                                        ([], t2))
                                                    in
                                                 ([], t2, uu____25178, false)
                                                  in
                                               Clos uu____25147  in
                                             (uu____25142, uu____25146)  in
                                           uu____25135 :: env2) env1 s
                                 in
                              let uu____25291 = guard_when_clause wopt b rest
                                 in
                              norm cfg1 env2 stack1 uu____25291)))
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
    let uu____25318 =
      let uu____25321 = FStar_ST.op_Bang plugins  in p :: uu____25321  in
    FStar_ST.op_Colon_Equals plugins uu____25318  in
  let retrieve uu____25429 = FStar_ST.op_Bang plugins  in
  (register, retrieve) 
let (register_plugin : primitive_step -> unit) =
  fun p  -> FStar_Pervasives_Native.fst plugins p 
let (retrieve_plugins : unit -> primitive_step Prims.list) =
  fun uu____25506  -> FStar_Pervasives_Native.snd plugins () 
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
               (fun uu___122_25547  ->
                  match uu___122_25547 with
                  | UnfoldUntil k -> [FStar_TypeChecker_Env.Unfold k]
                  | Eager_unfolding  ->
                      [FStar_TypeChecker_Env.Eager_unfolding_only]
                  | Inlining  -> [FStar_TypeChecker_Env.Inlining]
                  | UnfoldTac  -> [FStar_TypeChecker_Env.UnfoldTac]
                  | uu____25551 -> []))
           in
        let d1 =
          match d with
          | [] -> [FStar_TypeChecker_Env.NoDelta]
          | uu____25557 -> d  in
        let uu____25560 = to_fsteps s  in
        let uu____25561 =
          let uu____25562 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Norm")  in
          let uu____25563 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Primops")  in
          let uu____25564 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "380")  in
          let uu____25565 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "WPE")  in
          let uu____25566 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "NormDelayed")
             in
          let uu____25567 =
            FStar_TypeChecker_Env.debug e
              (FStar_Options.Other "print_normalized_terms")
             in
          {
            gen = uu____25562;
            primop = uu____25563;
            b380 = uu____25564;
            wpe = uu____25565;
            norm_delayed = uu____25566;
            print_normalized = uu____25567
          }  in
        let uu____25568 =
          let uu____25571 =
            let uu____25574 = retrieve_plugins ()  in
            FStar_List.append uu____25574 psteps  in
          add_steps built_in_primitive_steps uu____25571  in
        let uu____25577 =
          (FStar_Options.normalize_pure_terms_for_extraction ()) ||
            (let uu____25579 =
               FStar_All.pipe_right s
                 (FStar_List.contains PureSubtermsWithinComputations)
                in
             Prims.op_Negation uu____25579)
           in
        {
          steps = uu____25560;
          tcenv = e;
          debug = uu____25561;
          delta_level = d1;
          primitive_steps = uu____25568;
          strong = false;
          memoize_lazy = true;
          normalize_pure_lets = uu____25577
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
      fun t  -> let uu____25661 = config s e  in norm_comp uu____25661 [] t
  
let (normalize_universe :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun u  ->
      let uu____25678 = config [] env  in norm_universe uu____25678 [] u
  
let (ghost_to_pure :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun env  ->
    fun c  ->
      let cfg =
        config
          [UnfoldUntil FStar_Syntax_Syntax.delta_constant;
          AllowUnboundUniverses;
          EraseUniverses] env
         in
      let non_info t =
        let uu____25702 = norm cfg [] [] t  in
        FStar_Syntax_Util.non_informative uu____25702  in
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____25709 -> c
      | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
          let uu___226_25728 = c  in
          {
            FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
            FStar_Syntax_Syntax.pos =
              (uu___226_25728.FStar_Syntax_Syntax.pos);
            FStar_Syntax_Syntax.vars =
              (uu___226_25728.FStar_Syntax_Syntax.vars)
          }
      | FStar_Syntax_Syntax.Comp ct ->
          let l =
            FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
              ct.FStar_Syntax_Syntax.effect_name
             in
          let uu____25735 =
            (FStar_Syntax_Util.is_ghost_effect l) &&
              (non_info ct.FStar_Syntax_Syntax.result_typ)
             in
          if uu____25735
          then
            let ct1 =
              let uu____25737 =
                downgrade_ghost_effect_name
                  ct.FStar_Syntax_Syntax.effect_name
                 in
              match uu____25737 with
              | FStar_Pervasives_Native.Some pure_eff ->
                  let flags1 =
                    let uu____25744 =
                      FStar_Ident.lid_equals pure_eff
                        FStar_Parser_Const.effect_Tot_lid
                       in
                    if uu____25744
                    then FStar_Syntax_Syntax.TOTAL ::
                      (ct.FStar_Syntax_Syntax.flags)
                    else ct.FStar_Syntax_Syntax.flags  in
                  let uu___227_25748 = ct  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___227_25748.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name = pure_eff;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___227_25748.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___227_25748.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags = flags1
                  }
              | FStar_Pervasives_Native.None  ->
                  let ct1 =
                    FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c
                     in
                  let uu___228_25750 = ct1  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___228_25750.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name =
                      FStar_Parser_Const.effect_PURE_lid;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___228_25750.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___228_25750.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags =
                      (uu___228_25750.FStar_Syntax_Syntax.flags)
                  }
               in
            let uu___229_25751 = c  in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
              FStar_Syntax_Syntax.pos =
                (uu___229_25751.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___229_25751.FStar_Syntax_Syntax.vars)
            }
          else c
      | uu____25753 -> c
  
let (ghost_to_pure_lcomp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.lcomp -> FStar_Syntax_Syntax.lcomp)
  =
  fun env  ->
    fun lc  ->
      let cfg =
        config
          [Eager_unfolding;
          UnfoldUntil FStar_Syntax_Syntax.delta_constant;
          EraseUniverses;
          AllowUnboundUniverses] env
         in
      let non_info t =
        let uu____25771 = norm cfg [] [] t  in
        FStar_Syntax_Util.non_informative uu____25771  in
      let uu____25778 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ)
         in
      if uu____25778
      then
        let uu____25779 =
          downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name  in
        match uu____25779 with
        | FStar_Pervasives_Native.Some pure_eff ->
            FStar_Syntax_Syntax.mk_lcomp pure_eff
              lc.FStar_Syntax_Syntax.res_typ lc.FStar_Syntax_Syntax.cflags
              (fun uu____25785  ->
                 let uu____25786 = FStar_Syntax_Syntax.lcomp_comp lc  in
                 ghost_to_pure env uu____25786)
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
            ((let uu____25807 =
                let uu____25812 =
                  let uu____25813 = FStar_Util.message_of_exn e  in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____25813
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____25812)  in
              FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____25807);
             t)
         in
      FStar_Syntax_Print.term_to_string' env.FStar_TypeChecker_Env.dsenv t1
  
let (comp_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string) =
  fun env  ->
    fun c  ->
      let c1 =
        try
          let uu____25828 = config [AllowUnboundUniverses] env  in
          norm_comp uu____25828 [] c
        with
        | e ->
            ((let uu____25841 =
                let uu____25846 =
                  let uu____25847 = FStar_Util.message_of_exn e  in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____25847
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____25846)  in
              FStar_Errors.log_issue c.FStar_Syntax_Syntax.pos uu____25841);
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
                   let uu____25892 =
                     let uu____25893 =
                       let uu____25900 = FStar_Syntax_Util.mk_conj phi1 phi
                          in
                       (y, uu____25900)  in
                     FStar_Syntax_Syntax.Tm_refine uu____25893  in
                   mk uu____25892 t01.FStar_Syntax_Syntax.pos
               | uu____25905 -> t2)
          | uu____25906 -> t2  in
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
        UnfoldUntil FStar_Syntax_Syntax.delta_constant;
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
        let uu____25970 = FStar_Syntax_Util.arrow_formals_comp t_e  in
        match uu____25970 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____25999 ->
                 let uu____26006 = FStar_Syntax_Util.abs_formals e  in
                 (match uu____26006 with
                  | (actuals,uu____26016,uu____26017) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____26031 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders
                            in
                         match uu____26031 with
                         | (binders,args) ->
                             let uu____26042 =
                               FStar_Syntax_Syntax.mk_Tm_app e args
                                 FStar_Pervasives_Native.None
                                 e.FStar_Syntax_Syntax.pos
                                in
                             FStar_Syntax_Util.abs binders uu____26042
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
      | uu____26056 ->
          let uu____26057 = FStar_Syntax_Util.head_and_args t  in
          (match uu____26057 with
           | (head1,args) ->
               let uu____26094 =
                 let uu____26095 = FStar_Syntax_Subst.compress head1  in
                 uu____26095.FStar_Syntax_Syntax.n  in
               (match uu____26094 with
                | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
                    let uu____26104 =
                      let uu____26117 =
                        FStar_Syntax_Subst.subst s
                          u.FStar_Syntax_Syntax.ctx_uvar_typ
                         in
                      FStar_Syntax_Util.arrow_formals uu____26117  in
                    (match uu____26104 with
                     | (formals,_tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____26147 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___234_26155 = env  in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___234_26155.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___234_26155.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___234_26155.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___234_26155.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_sig =
                                     (uu___234_26155.FStar_TypeChecker_Env.gamma_sig);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___234_26155.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___234_26155.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___234_26155.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___234_26155.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___234_26155.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___234_26155.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___234_26155.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___234_26155.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___234_26155.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___234_26155.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___234_26155.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___234_26155.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___234_26155.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___234_26155.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___234_26155.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___234_26155.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___234_26155.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___234_26155.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___234_26155.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___234_26155.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                     =
                                     (uu___234_26155.FStar_TypeChecker_Env.qtbl_name_and_index);
                                   FStar_TypeChecker_Env.normalized_eff_names
                                     =
                                     (uu___234_26155.FStar_TypeChecker_Env.normalized_eff_names);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___234_26155.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth_hook =
                                     (uu___234_26155.FStar_TypeChecker_Env.synth_hook);
                                   FStar_TypeChecker_Env.splice =
                                     (uu___234_26155.FStar_TypeChecker_Env.splice);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___234_26155.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___234_26155.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___234_26155.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___234_26155.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.dep_graph =
                                     (uu___234_26155.FStar_TypeChecker_Env.dep_graph)
                                 }) t
                               in
                            match uu____26147 with
                            | (uu____26156,ty,uu____26158) ->
                                eta_expand_with_type env t ty))
                | uu____26159 ->
                    let uu____26160 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___235_26168 = env  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___235_26168.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___235_26168.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___235_26168.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___235_26168.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_sig =
                             (uu___235_26168.FStar_TypeChecker_Env.gamma_sig);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___235_26168.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___235_26168.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___235_26168.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___235_26168.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___235_26168.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___235_26168.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___235_26168.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___235_26168.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___235_26168.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___235_26168.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___235_26168.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___235_26168.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___235_26168.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___235_26168.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.failhard =
                             (uu___235_26168.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___235_26168.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___235_26168.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___235_26168.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___235_26168.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___235_26168.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qtbl_name_and_index =
                             (uu___235_26168.FStar_TypeChecker_Env.qtbl_name_and_index);
                           FStar_TypeChecker_Env.normalized_eff_names =
                             (uu___235_26168.FStar_TypeChecker_Env.normalized_eff_names);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___235_26168.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth_hook =
                             (uu___235_26168.FStar_TypeChecker_Env.synth_hook);
                           FStar_TypeChecker_Env.splice =
                             (uu___235_26168.FStar_TypeChecker_Env.splice);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___235_26168.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___235_26168.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___235_26168.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___235_26168.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.dep_graph =
                             (uu___235_26168.FStar_TypeChecker_Env.dep_graph)
                         }) t
                       in
                    (match uu____26160 with
                     | (uu____26169,ty,uu____26171) ->
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
      let uu___236_26244 = x  in
      let uu____26245 = elim_delayed_subst_term x.FStar_Syntax_Syntax.sort
         in
      {
        FStar_Syntax_Syntax.ppname =
          (uu___236_26244.FStar_Syntax_Syntax.ppname);
        FStar_Syntax_Syntax.index =
          (uu___236_26244.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = uu____26245
      }  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____26248 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_bvar uu____26273 -> t1
    | FStar_Syntax_Syntax.Tm_name uu____26274 -> t1
    | FStar_Syntax_Syntax.Tm_fvar uu____26275 -> t1
    | FStar_Syntax_Syntax.Tm_uinst uu____26276 -> t1
    | FStar_Syntax_Syntax.Tm_constant uu____26283 -> t1
    | FStar_Syntax_Syntax.Tm_type uu____26284 -> t1
    | FStar_Syntax_Syntax.Tm_lazy uu____26285 -> t1
    | FStar_Syntax_Syntax.Tm_unknown  -> t1
    | FStar_Syntax_Syntax.Tm_abs (bs,t2,rc_opt) ->
        let elim_rc rc =
          let uu___237_26315 = rc  in
          let uu____26316 =
            FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
              elim_delayed_subst_term
             in
          let uu____26325 =
            elim_delayed_subst_cflags rc.FStar_Syntax_Syntax.residual_flags
             in
          {
            FStar_Syntax_Syntax.residual_effect =
              (uu___237_26315.FStar_Syntax_Syntax.residual_effect);
            FStar_Syntax_Syntax.residual_typ = uu____26316;
            FStar_Syntax_Syntax.residual_flags = uu____26325
          }  in
        let uu____26328 =
          let uu____26329 =
            let uu____26346 = elim_delayed_subst_binders bs  in
            let uu____26353 = elim_delayed_subst_term t2  in
            let uu____26356 = FStar_Util.map_opt rc_opt elim_rc  in
            (uu____26346, uu____26353, uu____26356)  in
          FStar_Syntax_Syntax.Tm_abs uu____26329  in
        mk1 uu____26328
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____26387 =
          let uu____26388 =
            let uu____26401 = elim_delayed_subst_binders bs  in
            let uu____26408 = elim_delayed_subst_comp c  in
            (uu____26401, uu____26408)  in
          FStar_Syntax_Syntax.Tm_arrow uu____26388  in
        mk1 uu____26387
    | FStar_Syntax_Syntax.Tm_refine (bv,phi) ->
        let uu____26425 =
          let uu____26426 =
            let uu____26433 = elim_bv bv  in
            let uu____26434 = elim_delayed_subst_term phi  in
            (uu____26433, uu____26434)  in
          FStar_Syntax_Syntax.Tm_refine uu____26426  in
        mk1 uu____26425
    | FStar_Syntax_Syntax.Tm_app (t2,args) ->
        let uu____26461 =
          let uu____26462 =
            let uu____26477 = elim_delayed_subst_term t2  in
            let uu____26480 = elim_delayed_subst_args args  in
            (uu____26477, uu____26480)  in
          FStar_Syntax_Syntax.Tm_app uu____26462  in
        mk1 uu____26461
    | FStar_Syntax_Syntax.Tm_match (t2,branches) ->
        let rec elim_pat p =
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_var x ->
              let uu___238_26548 = p  in
              let uu____26549 =
                let uu____26550 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_var uu____26550  in
              {
                FStar_Syntax_Syntax.v = uu____26549;
                FStar_Syntax_Syntax.p =
                  (uu___238_26548.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_wild x ->
              let uu___239_26552 = p  in
              let uu____26553 =
                let uu____26554 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_wild uu____26554  in
              {
                FStar_Syntax_Syntax.v = uu____26553;
                FStar_Syntax_Syntax.p =
                  (uu___239_26552.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
              let uu___240_26561 = p  in
              let uu____26562 =
                let uu____26563 =
                  let uu____26570 = elim_bv x  in
                  let uu____26571 = elim_delayed_subst_term t0  in
                  (uu____26570, uu____26571)  in
                FStar_Syntax_Syntax.Pat_dot_term uu____26563  in
              {
                FStar_Syntax_Syntax.v = uu____26562;
                FStar_Syntax_Syntax.p =
                  (uu___240_26561.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
              let uu___241_26594 = p  in
              let uu____26595 =
                let uu____26596 =
                  let uu____26609 =
                    FStar_List.map
                      (fun uu____26632  ->
                         match uu____26632 with
                         | (x,b) ->
                             let uu____26645 = elim_pat x  in
                             (uu____26645, b)) pats
                     in
                  (fv, uu____26609)  in
                FStar_Syntax_Syntax.Pat_cons uu____26596  in
              {
                FStar_Syntax_Syntax.v = uu____26595;
                FStar_Syntax_Syntax.p =
                  (uu___241_26594.FStar_Syntax_Syntax.p)
              }
          | uu____26658 -> p  in
        let elim_branch uu____26682 =
          match uu____26682 with
          | (pat,wopt,t3) ->
              let uu____26708 = elim_pat pat  in
              let uu____26711 =
                FStar_Util.map_opt wopt elim_delayed_subst_term  in
              let uu____26714 = elim_delayed_subst_term t3  in
              (uu____26708, uu____26711, uu____26714)
           in
        let uu____26719 =
          let uu____26720 =
            let uu____26743 = elim_delayed_subst_term t2  in
            let uu____26746 = FStar_List.map elim_branch branches  in
            (uu____26743, uu____26746)  in
          FStar_Syntax_Syntax.Tm_match uu____26720  in
        mk1 uu____26719
    | FStar_Syntax_Syntax.Tm_ascribed (t2,a,lopt) ->
        let elim_ascription uu____26877 =
          match uu____26877 with
          | (tc,topt) ->
              let uu____26912 =
                match tc with
                | FStar_Util.Inl t3 ->
                    let uu____26922 = elim_delayed_subst_term t3  in
                    FStar_Util.Inl uu____26922
                | FStar_Util.Inr c ->
                    let uu____26924 = elim_delayed_subst_comp c  in
                    FStar_Util.Inr uu____26924
                 in
              let uu____26925 =
                FStar_Util.map_opt topt elim_delayed_subst_term  in
              (uu____26912, uu____26925)
           in
        let uu____26934 =
          let uu____26935 =
            let uu____26962 = elim_delayed_subst_term t2  in
            let uu____26965 = elim_ascription a  in
            (uu____26962, uu____26965, lopt)  in
          FStar_Syntax_Syntax.Tm_ascribed uu____26935  in
        mk1 uu____26934
    | FStar_Syntax_Syntax.Tm_let (lbs,t2) ->
        let elim_lb lb =
          let uu___242_27026 = lb  in
          let uu____27027 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbtyp  in
          let uu____27030 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbdef  in
          {
            FStar_Syntax_Syntax.lbname =
              (uu___242_27026.FStar_Syntax_Syntax.lbname);
            FStar_Syntax_Syntax.lbunivs =
              (uu___242_27026.FStar_Syntax_Syntax.lbunivs);
            FStar_Syntax_Syntax.lbtyp = uu____27027;
            FStar_Syntax_Syntax.lbeff =
              (uu___242_27026.FStar_Syntax_Syntax.lbeff);
            FStar_Syntax_Syntax.lbdef = uu____27030;
            FStar_Syntax_Syntax.lbattrs =
              (uu___242_27026.FStar_Syntax_Syntax.lbattrs);
            FStar_Syntax_Syntax.lbpos =
              (uu___242_27026.FStar_Syntax_Syntax.lbpos)
          }  in
        let uu____27033 =
          let uu____27034 =
            let uu____27047 =
              let uu____27054 =
                FStar_List.map elim_lb (FStar_Pervasives_Native.snd lbs)  in
              ((FStar_Pervasives_Native.fst lbs), uu____27054)  in
            let uu____27063 = elim_delayed_subst_term t2  in
            (uu____27047, uu____27063)  in
          FStar_Syntax_Syntax.Tm_let uu____27034  in
        mk1 uu____27033
    | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
        mk1 (FStar_Syntax_Syntax.Tm_uvar (u, s))
    | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
        let qi1 =
          FStar_Syntax_Syntax.on_antiquoted elim_delayed_subst_term qi  in
        let uu____27089 =
          let uu____27090 =
            let uu____27097 = elim_delayed_subst_term tm  in
            (uu____27097, qi1)  in
          FStar_Syntax_Syntax.Tm_quoted uu____27090  in
        mk1 uu____27089
    | FStar_Syntax_Syntax.Tm_meta (t2,md) ->
        let uu____27108 =
          let uu____27109 =
            let uu____27116 = elim_delayed_subst_term t2  in
            let uu____27119 = elim_delayed_subst_meta md  in
            (uu____27116, uu____27119)  in
          FStar_Syntax_Syntax.Tm_meta uu____27109  in
        mk1 uu____27108

and (elim_delayed_subst_cflags :
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun flags1  ->
    FStar_List.map
      (fun uu___123_27128  ->
         match uu___123_27128 with
         | FStar_Syntax_Syntax.DECREASES t ->
             let uu____27132 = elim_delayed_subst_term t  in
             FStar_Syntax_Syntax.DECREASES uu____27132
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
        let uu____27155 =
          let uu____27156 =
            let uu____27165 = elim_delayed_subst_term t  in
            (uu____27165, uopt)  in
          FStar_Syntax_Syntax.Total uu____27156  in
        mk1 uu____27155
    | FStar_Syntax_Syntax.GTotal (t,uopt) ->
        let uu____27182 =
          let uu____27183 =
            let uu____27192 = elim_delayed_subst_term t  in
            (uu____27192, uopt)  in
          FStar_Syntax_Syntax.GTotal uu____27183  in
        mk1 uu____27182
    | FStar_Syntax_Syntax.Comp ct ->
        let ct1 =
          let uu___243_27201 = ct  in
          let uu____27202 =
            elim_delayed_subst_term ct.FStar_Syntax_Syntax.result_typ  in
          let uu____27205 =
            elim_delayed_subst_args ct.FStar_Syntax_Syntax.effect_args  in
          let uu____27214 =
            elim_delayed_subst_cflags ct.FStar_Syntax_Syntax.flags  in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___243_27201.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___243_27201.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ = uu____27202;
            FStar_Syntax_Syntax.effect_args = uu____27205;
            FStar_Syntax_Syntax.flags = uu____27214
          }  in
        mk1 (FStar_Syntax_Syntax.Comp ct1)

and (elim_delayed_subst_meta :
  FStar_Syntax_Syntax.metadata -> FStar_Syntax_Syntax.metadata) =
  fun uu___124_27217  ->
    match uu___124_27217 with
    | FStar_Syntax_Syntax.Meta_pattern args ->
        let uu____27229 = FStar_List.map elim_delayed_subst_args args  in
        FStar_Syntax_Syntax.Meta_pattern uu____27229
    | FStar_Syntax_Syntax.Meta_monadic (m,t) ->
        let uu____27262 =
          let uu____27269 = elim_delayed_subst_term t  in (m, uu____27269)
           in
        FStar_Syntax_Syntax.Meta_monadic uu____27262
    | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,t) ->
        let uu____27281 =
          let uu____27290 = elim_delayed_subst_term t  in
          (m1, m2, uu____27290)  in
        FStar_Syntax_Syntax.Meta_monadic_lift uu____27281
    | m -> m

and (elim_delayed_subst_args :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun args  ->
    FStar_List.map
      (fun uu____27317  ->
         match uu____27317 with
         | (t,q) ->
             let uu____27328 = elim_delayed_subst_term t  in (uu____27328, q))
      args

and (elim_delayed_subst_binders :
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun bs  ->
    FStar_List.map
      (fun uu____27348  ->
         match uu____27348 with
         | (x,q) ->
             let uu____27359 =
               let uu___244_27360 = x  in
               let uu____27361 =
                 elim_delayed_subst_term x.FStar_Syntax_Syntax.sort  in
               {
                 FStar_Syntax_Syntax.ppname =
                   (uu___244_27360.FStar_Syntax_Syntax.ppname);
                 FStar_Syntax_Syntax.index =
                   (uu___244_27360.FStar_Syntax_Syntax.index);
                 FStar_Syntax_Syntax.sort = uu____27361
               }  in
             (uu____27359, q)) bs

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
            | (uu____27453,FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c))
                  FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
            | (uu____27479,FStar_Util.Inl t) ->
                let uu____27497 =
                  let uu____27504 =
                    let uu____27505 =
                      let uu____27518 = FStar_Syntax_Syntax.mk_Total t  in
                      (binders, uu____27518)  in
                    FStar_Syntax_Syntax.Tm_arrow uu____27505  in
                  FStar_Syntax_Syntax.mk uu____27504  in
                uu____27497 FStar_Pervasives_Native.None
                  t.FStar_Syntax_Syntax.pos
             in
          let uu____27532 = FStar_Syntax_Subst.open_univ_vars univ_names t
             in
          match uu____27532 with
          | (univ_names1,t1) ->
              let t2 = remove_uvar_solutions env t1  in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2  in
              let t4 = elim_delayed_subst_term t3  in
              let uu____27562 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t4))
                | uu____27625 ->
                    let uu____27626 =
                      let uu____27635 =
                        let uu____27636 = FStar_Syntax_Subst.compress t4  in
                        uu____27636.FStar_Syntax_Syntax.n  in
                      (uu____27635, tc)  in
                    (match uu____27626 with
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inr uu____27663) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inl uu____27704) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____27743,FStar_Util.Inl uu____27744) ->
                         ([], (FStar_Util.Inl t4))
                     | uu____27767 -> failwith "Impossible")
                 in
              (match uu____27562 with
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
          let uu____27892 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl t)  in
          match uu____27892 with
          | (univ_names1,binders1,tc) ->
              let uu____27958 = FStar_Util.left tc  in
              (univ_names1, binders1, uu____27958)
  
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
          let uu____28007 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr c)  in
          match uu____28007 with
          | (univ_names1,binders1,tc) ->
              let uu____28073 = FStar_Util.right tc  in
              (univ_names1, binders1, uu____28073)
  
let rec (elim_uvars :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt)
  =
  fun env  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univ_names,binders,typ,lids,lids') ->
          let uu____28112 = elim_uvars_aux_t env univ_names binders typ  in
          (match uu____28112 with
           | (univ_names1,binders1,typ1) ->
               let uu___245_28146 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___245_28146.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___245_28146.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___245_28146.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___245_28146.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
          let uu___246_28161 = s  in
          let uu____28162 =
            let uu____28163 =
              let uu____28172 = FStar_List.map (elim_uvars env) sigs  in
              (uu____28172, lids)  in
            FStar_Syntax_Syntax.Sig_bundle uu____28163  in
          {
            FStar_Syntax_Syntax.sigel = uu____28162;
            FStar_Syntax_Syntax.sigrng =
              (uu___246_28161.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___246_28161.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___246_28161.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___246_28161.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_datacon (lid,univ_names,typ,lident,i,lids) ->
          let uu____28189 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____28189 with
           | (univ_names1,uu____28209,typ1) ->
               let uu___247_28227 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___247_28227.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___247_28227.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___247_28227.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___247_28227.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univ_names,typ) ->
          let uu____28233 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____28233 with
           | (univ_names1,uu____28253,typ1) ->
               let uu___248_28271 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___248_28271.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___248_28271.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___248_28271.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___248_28271.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____28299 =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs
                       in
                    match uu____28299 with
                    | (opening,lbunivs) ->
                        let elim t =
                          let uu____28324 =
                            let uu____28325 =
                              let uu____28326 =
                                FStar_Syntax_Subst.subst opening t  in
                              remove_uvar_solutions env uu____28326  in
                            FStar_Syntax_Subst.close_univ_vars lbunivs
                              uu____28325
                             in
                          elim_delayed_subst_term uu____28324  in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp  in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef  in
                        let uu___249_28329 = lb  in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___249_28329.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___249_28329.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___249_28329.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___249_28329.FStar_Syntax_Syntax.lbpos)
                        }))
             in
          let uu___250_28330 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids));
            FStar_Syntax_Syntax.sigrng =
              (uu___250_28330.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___250_28330.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___250_28330.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___250_28330.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_main t ->
          let uu___251_28336 = s  in
          let uu____28337 =
            let uu____28338 = remove_uvar_solutions env t  in
            FStar_Syntax_Syntax.Sig_main uu____28338  in
          {
            FStar_Syntax_Syntax.sigel = uu____28337;
            FStar_Syntax_Syntax.sigrng =
              (uu___251_28336.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___251_28336.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___251_28336.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___251_28336.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_assume (l,us,t) ->
          let uu____28342 = elim_uvars_aux_t env us [] t  in
          (match uu____28342 with
           | (us1,uu____28362,t1) ->
               let uu___252_28380 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___252_28380.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___252_28380.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___252_28380.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___252_28380.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____28381 ->
          failwith "Impossible: should have been desugared already"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____28383 =
            elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature
             in
          (match uu____28383 with
           | (univs1,binders,signature) ->
               let uu____28417 =
                 let uu____28426 = FStar_Syntax_Subst.univ_var_opening univs1
                    in
                 match uu____28426 with
                 | (univs_opening,univs2) ->
                     let uu____28453 =
                       FStar_Syntax_Subst.univ_var_closing univs2  in
                     (univs_opening, uu____28453)
                  in
               (match uu____28417 with
                | (univs_opening,univs_closing) ->
                    let uu____28470 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders
                         in
                      let uu____28476 =
                        FStar_Syntax_Subst.opening_of_binders binders1  in
                      let uu____28477 =
                        FStar_Syntax_Subst.closing_of_binders binders1  in
                      (uu____28476, uu____28477)  in
                    (match uu____28470 with
                     | (b_opening,b_closing) ->
                         let n1 = FStar_List.length univs1  in
                         let n_binders = FStar_List.length binders  in
                         let elim_tscheme uu____28501 =
                           match uu____28501 with
                           | (us,t) ->
                               let n_us = FStar_List.length us  in
                               let uu____28519 =
                                 FStar_Syntax_Subst.open_univ_vars us t  in
                               (match uu____28519 with
                                | (us1,t1) ->
                                    let uu____28530 =
                                      let uu____28539 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      let uu____28548 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      (uu____28539, uu____28548)  in
                                    (match uu____28530 with
                                     | (b_opening1,b_closing1) ->
                                         let uu____28575 =
                                           let uu____28584 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us)
                                              in
                                           let uu____28593 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us)
                                              in
                                           (uu____28584, uu____28593)  in
                                         (match uu____28575 with
                                          | (univs_opening1,univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____28621 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1
                                                   in
                                                FStar_Syntax_Subst.subst
                                                  univs_opening1 uu____28621
                                                 in
                                              let uu____28622 =
                                                elim_uvars_aux_t env [] [] t2
                                                 in
                                              (match uu____28622 with
                                               | (uu____28645,uu____28646,t3)
                                                   ->
                                                   let t4 =
                                                     let uu____28665 =
                                                       let uu____28666 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3
                                                          in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
                                                         uu____28666
                                                        in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____28665
                                                      in
                                                   (us1, t4)))))
                            in
                         let elim_term t =
                           let uu____28675 =
                             elim_uvars_aux_t env univs1 binders t  in
                           match uu____28675 with
                           | (uu____28692,uu____28693,t1) -> t1  in
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
                             | uu____28767 ->
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_abs
                                      ((a.FStar_Syntax_Syntax.action_params),
                                        body, FStar_Pervasives_Native.None))
                                   FStar_Pervasives_Native.None
                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                              in
                           let destruct_action_body body =
                             let uu____28792 =
                               let uu____28793 =
                                 FStar_Syntax_Subst.compress body  in
                               uu____28793.FStar_Syntax_Syntax.n  in
                             match uu____28792 with
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,(FStar_Util.Inl
                                        typ,FStar_Pervasives_Native.None ),FStar_Pervasives_Native.None
                                  )
                                 -> (defn, typ)
                             | uu____28852 -> failwith "Impossible"  in
                           let destruct_action_typ_templ t =
                             let uu____28883 =
                               let uu____28884 =
                                 FStar_Syntax_Subst.compress t  in
                               uu____28884.FStar_Syntax_Syntax.n  in
                             match uu____28883 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (pars,body,uu____28905) ->
                                 let uu____28926 = destruct_action_body body
                                    in
                                 (match uu____28926 with
                                  | (defn,typ) -> (pars, defn, typ))
                             | uu____28971 ->
                                 let uu____28972 = destruct_action_body t  in
                                 (match uu____28972 with
                                  | (defn,typ) -> ([], defn, typ))
                              in
                           let uu____29021 =
                             elim_tscheme
                               ((a.FStar_Syntax_Syntax.action_univs),
                                 action_typ_templ)
                              in
                           match uu____29021 with
                           | (action_univs,t) ->
                               let uu____29030 = destruct_action_typ_templ t
                                  in
                               (match uu____29030 with
                                | (action_params,action_defn,action_typ) ->
                                    let a' =
                                      let uu___253_29071 = a  in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___253_29071.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___253_29071.FStar_Syntax_Syntax.action_unqualified_name);
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
                           let uu___254_29073 = ed  in
                           let uu____29074 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ret_wp  in
                           let uu____29075 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_wp  in
                           let uu____29076 =
                             elim_tscheme ed.FStar_Syntax_Syntax.if_then_else
                              in
                           let uu____29077 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ite_wp  in
                           let uu____29078 =
                             elim_tscheme ed.FStar_Syntax_Syntax.stronger  in
                           let uu____29079 =
                             elim_tscheme ed.FStar_Syntax_Syntax.close_wp  in
                           let uu____29080 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assert_p  in
                           let uu____29081 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assume_p  in
                           let uu____29082 =
                             elim_tscheme ed.FStar_Syntax_Syntax.null_wp  in
                           let uu____29083 =
                             elim_tscheme ed.FStar_Syntax_Syntax.trivial  in
                           let uu____29084 =
                             elim_term ed.FStar_Syntax_Syntax.repr  in
                           let uu____29085 =
                             elim_tscheme ed.FStar_Syntax_Syntax.return_repr
                              in
                           let uu____29086 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_repr
                              in
                           let uu____29087 =
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions
                              in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___254_29073.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___254_29073.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs = univs1;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp = uu____29074;
                             FStar_Syntax_Syntax.bind_wp = uu____29075;
                             FStar_Syntax_Syntax.if_then_else = uu____29076;
                             FStar_Syntax_Syntax.ite_wp = uu____29077;
                             FStar_Syntax_Syntax.stronger = uu____29078;
                             FStar_Syntax_Syntax.close_wp = uu____29079;
                             FStar_Syntax_Syntax.assert_p = uu____29080;
                             FStar_Syntax_Syntax.assume_p = uu____29081;
                             FStar_Syntax_Syntax.null_wp = uu____29082;
                             FStar_Syntax_Syntax.trivial = uu____29083;
                             FStar_Syntax_Syntax.repr = uu____29084;
                             FStar_Syntax_Syntax.return_repr = uu____29085;
                             FStar_Syntax_Syntax.bind_repr = uu____29086;
                             FStar_Syntax_Syntax.actions = uu____29087;
                             FStar_Syntax_Syntax.eff_attrs =
                               (uu___254_29073.FStar_Syntax_Syntax.eff_attrs)
                           }  in
                         let uu___255_29090 = s  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___255_29090.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___255_29090.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___255_29090.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___255_29090.FStar_Syntax_Syntax.sigattrs)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___125_29111 =
            match uu___125_29111 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (us,t) ->
                let uu____29142 = elim_uvars_aux_t env us [] t  in
                (match uu____29142 with
                 | (us1,uu____29170,t1) ->
                     FStar_Pervasives_Native.Some (us1, t1))
             in
          let sub_eff1 =
            let uu___256_29197 = sub_eff  in
            let uu____29198 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp  in
            let uu____29201 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift  in
            {
              FStar_Syntax_Syntax.source =
                (uu___256_29197.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___256_29197.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____29198;
              FStar_Syntax_Syntax.lift = uu____29201
            }  in
          let uu___257_29204 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___257_29204.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___257_29204.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___257_29204.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___257_29204.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,univ_names,binders,comp,flags1) ->
          let uu____29214 = elim_uvars_aux_c env univ_names binders comp  in
          (match uu____29214 with
           | (univ_names1,binders1,comp1) ->
               let uu___258_29248 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___258_29248.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___258_29248.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___258_29248.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___258_29248.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____29251 -> s
      | FStar_Syntax_Syntax.Sig_splice uu____29252 -> s
  
let (erase_universes :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  -> normalize [EraseUniverses; AllowUnboundUniverses] env t
  