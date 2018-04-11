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
      fun uu___77_269  ->
        match uu___77_269 with
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
  in_full_norm_request: Prims.bool }[@@deriving show]
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
        in_full_norm_request = __fname__in_full_norm_request;_} ->
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
        in_full_norm_request = __fname__in_full_norm_request;_} ->
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
        in_full_norm_request = __fname__in_full_norm_request;_} ->
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
        in_full_norm_request = __fname__in_full_norm_request;_} ->
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
        in_full_norm_request = __fname__in_full_norm_request;_} ->
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
        in_full_norm_request = __fname__in_full_norm_request;_} ->
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
        in_full_norm_request = __fname__in_full_norm_request;_} ->
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
        in_full_norm_request = __fname__in_full_norm_request;_} ->
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
        in_full_norm_request = __fname__in_full_norm_request;_} ->
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
        in_full_norm_request = __fname__in_full_norm_request;_} ->
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
        in_full_norm_request = __fname__in_full_norm_request;_} ->
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
        in_full_norm_request = __fname__in_full_norm_request;_} ->
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
        in_full_norm_request = __fname__in_full_norm_request;_} ->
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
        in_full_norm_request = __fname__in_full_norm_request;_} ->
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
        in_full_norm_request = __fname__in_full_norm_request;_} ->
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
        in_full_norm_request = __fname__in_full_norm_request;_} ->
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
        in_full_norm_request = __fname__in_full_norm_request;_} ->
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
        in_full_norm_request = __fname__in_full_norm_request;_} ->
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
        in_full_norm_request = __fname__in_full_norm_request;_} ->
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
        in_full_norm_request = __fname__in_full_norm_request;_} ->
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
        in_full_norm_request = __fname__in_full_norm_request;_} ->
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
        in_full_norm_request = __fname__in_full_norm_request;_} ->
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
        in_full_norm_request = __fname__in_full_norm_request;_} ->
        __fname__in_full_norm_request
  
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
    in_full_norm_request = false
  } 
let (fstep_add_one : step -> fsteps -> fsteps) =
  fun s  ->
    fun fs  ->
      let add_opt x uu___78_1432 =
        match uu___78_1432 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.Some [x]
        | FStar_Pervasives_Native.Some xs ->
            FStar_Pervasives_Native.Some (x :: xs)
         in
      match s with
      | Beta  ->
          let uu___96_1452 = fs  in
          {
            beta = true;
            iota = (uu___96_1452.iota);
            zeta = (uu___96_1452.zeta);
            weak = (uu___96_1452.weak);
            hnf = (uu___96_1452.hnf);
            primops = (uu___96_1452.primops);
            do_not_unfold_pure_lets = (uu___96_1452.do_not_unfold_pure_lets);
            unfold_until = (uu___96_1452.unfold_until);
            unfold_only = (uu___96_1452.unfold_only);
            unfold_fully = (uu___96_1452.unfold_fully);
            unfold_attr = (uu___96_1452.unfold_attr);
            unfold_tac = (uu___96_1452.unfold_tac);
            pure_subterms_within_computations =
              (uu___96_1452.pure_subterms_within_computations);
            simplify = (uu___96_1452.simplify);
            erase_universes = (uu___96_1452.erase_universes);
            allow_unbound_universes = (uu___96_1452.allow_unbound_universes);
            reify_ = (uu___96_1452.reify_);
            compress_uvars = (uu___96_1452.compress_uvars);
            no_full_norm = (uu___96_1452.no_full_norm);
            check_no_uvars = (uu___96_1452.check_no_uvars);
            unmeta = (uu___96_1452.unmeta);
            unascribe = (uu___96_1452.unascribe);
            in_full_norm_request = (uu___96_1452.in_full_norm_request)
          }
      | Iota  ->
          let uu___97_1453 = fs  in
          {
            beta = (uu___97_1453.beta);
            iota = true;
            zeta = (uu___97_1453.zeta);
            weak = (uu___97_1453.weak);
            hnf = (uu___97_1453.hnf);
            primops = (uu___97_1453.primops);
            do_not_unfold_pure_lets = (uu___97_1453.do_not_unfold_pure_lets);
            unfold_until = (uu___97_1453.unfold_until);
            unfold_only = (uu___97_1453.unfold_only);
            unfold_fully = (uu___97_1453.unfold_fully);
            unfold_attr = (uu___97_1453.unfold_attr);
            unfold_tac = (uu___97_1453.unfold_tac);
            pure_subterms_within_computations =
              (uu___97_1453.pure_subterms_within_computations);
            simplify = (uu___97_1453.simplify);
            erase_universes = (uu___97_1453.erase_universes);
            allow_unbound_universes = (uu___97_1453.allow_unbound_universes);
            reify_ = (uu___97_1453.reify_);
            compress_uvars = (uu___97_1453.compress_uvars);
            no_full_norm = (uu___97_1453.no_full_norm);
            check_no_uvars = (uu___97_1453.check_no_uvars);
            unmeta = (uu___97_1453.unmeta);
            unascribe = (uu___97_1453.unascribe);
            in_full_norm_request = (uu___97_1453.in_full_norm_request)
          }
      | Zeta  ->
          let uu___98_1454 = fs  in
          {
            beta = (uu___98_1454.beta);
            iota = (uu___98_1454.iota);
            zeta = true;
            weak = (uu___98_1454.weak);
            hnf = (uu___98_1454.hnf);
            primops = (uu___98_1454.primops);
            do_not_unfold_pure_lets = (uu___98_1454.do_not_unfold_pure_lets);
            unfold_until = (uu___98_1454.unfold_until);
            unfold_only = (uu___98_1454.unfold_only);
            unfold_fully = (uu___98_1454.unfold_fully);
            unfold_attr = (uu___98_1454.unfold_attr);
            unfold_tac = (uu___98_1454.unfold_tac);
            pure_subterms_within_computations =
              (uu___98_1454.pure_subterms_within_computations);
            simplify = (uu___98_1454.simplify);
            erase_universes = (uu___98_1454.erase_universes);
            allow_unbound_universes = (uu___98_1454.allow_unbound_universes);
            reify_ = (uu___98_1454.reify_);
            compress_uvars = (uu___98_1454.compress_uvars);
            no_full_norm = (uu___98_1454.no_full_norm);
            check_no_uvars = (uu___98_1454.check_no_uvars);
            unmeta = (uu___98_1454.unmeta);
            unascribe = (uu___98_1454.unascribe);
            in_full_norm_request = (uu___98_1454.in_full_norm_request)
          }
      | Exclude (Beta ) ->
          let uu___99_1455 = fs  in
          {
            beta = false;
            iota = (uu___99_1455.iota);
            zeta = (uu___99_1455.zeta);
            weak = (uu___99_1455.weak);
            hnf = (uu___99_1455.hnf);
            primops = (uu___99_1455.primops);
            do_not_unfold_pure_lets = (uu___99_1455.do_not_unfold_pure_lets);
            unfold_until = (uu___99_1455.unfold_until);
            unfold_only = (uu___99_1455.unfold_only);
            unfold_fully = (uu___99_1455.unfold_fully);
            unfold_attr = (uu___99_1455.unfold_attr);
            unfold_tac = (uu___99_1455.unfold_tac);
            pure_subterms_within_computations =
              (uu___99_1455.pure_subterms_within_computations);
            simplify = (uu___99_1455.simplify);
            erase_universes = (uu___99_1455.erase_universes);
            allow_unbound_universes = (uu___99_1455.allow_unbound_universes);
            reify_ = (uu___99_1455.reify_);
            compress_uvars = (uu___99_1455.compress_uvars);
            no_full_norm = (uu___99_1455.no_full_norm);
            check_no_uvars = (uu___99_1455.check_no_uvars);
            unmeta = (uu___99_1455.unmeta);
            unascribe = (uu___99_1455.unascribe);
            in_full_norm_request = (uu___99_1455.in_full_norm_request)
          }
      | Exclude (Iota ) ->
          let uu___100_1456 = fs  in
          {
            beta = (uu___100_1456.beta);
            iota = false;
            zeta = (uu___100_1456.zeta);
            weak = (uu___100_1456.weak);
            hnf = (uu___100_1456.hnf);
            primops = (uu___100_1456.primops);
            do_not_unfold_pure_lets = (uu___100_1456.do_not_unfold_pure_lets);
            unfold_until = (uu___100_1456.unfold_until);
            unfold_only = (uu___100_1456.unfold_only);
            unfold_fully = (uu___100_1456.unfold_fully);
            unfold_attr = (uu___100_1456.unfold_attr);
            unfold_tac = (uu___100_1456.unfold_tac);
            pure_subterms_within_computations =
              (uu___100_1456.pure_subterms_within_computations);
            simplify = (uu___100_1456.simplify);
            erase_universes = (uu___100_1456.erase_universes);
            allow_unbound_universes = (uu___100_1456.allow_unbound_universes);
            reify_ = (uu___100_1456.reify_);
            compress_uvars = (uu___100_1456.compress_uvars);
            no_full_norm = (uu___100_1456.no_full_norm);
            check_no_uvars = (uu___100_1456.check_no_uvars);
            unmeta = (uu___100_1456.unmeta);
            unascribe = (uu___100_1456.unascribe);
            in_full_norm_request = (uu___100_1456.in_full_norm_request)
          }
      | Exclude (Zeta ) ->
          let uu___101_1457 = fs  in
          {
            beta = (uu___101_1457.beta);
            iota = (uu___101_1457.iota);
            zeta = false;
            weak = (uu___101_1457.weak);
            hnf = (uu___101_1457.hnf);
            primops = (uu___101_1457.primops);
            do_not_unfold_pure_lets = (uu___101_1457.do_not_unfold_pure_lets);
            unfold_until = (uu___101_1457.unfold_until);
            unfold_only = (uu___101_1457.unfold_only);
            unfold_fully = (uu___101_1457.unfold_fully);
            unfold_attr = (uu___101_1457.unfold_attr);
            unfold_tac = (uu___101_1457.unfold_tac);
            pure_subterms_within_computations =
              (uu___101_1457.pure_subterms_within_computations);
            simplify = (uu___101_1457.simplify);
            erase_universes = (uu___101_1457.erase_universes);
            allow_unbound_universes = (uu___101_1457.allow_unbound_universes);
            reify_ = (uu___101_1457.reify_);
            compress_uvars = (uu___101_1457.compress_uvars);
            no_full_norm = (uu___101_1457.no_full_norm);
            check_no_uvars = (uu___101_1457.check_no_uvars);
            unmeta = (uu___101_1457.unmeta);
            unascribe = (uu___101_1457.unascribe);
            in_full_norm_request = (uu___101_1457.in_full_norm_request)
          }
      | Exclude uu____1458 -> failwith "Bad exclude"
      | Weak  ->
          let uu___102_1459 = fs  in
          {
            beta = (uu___102_1459.beta);
            iota = (uu___102_1459.iota);
            zeta = (uu___102_1459.zeta);
            weak = true;
            hnf = (uu___102_1459.hnf);
            primops = (uu___102_1459.primops);
            do_not_unfold_pure_lets = (uu___102_1459.do_not_unfold_pure_lets);
            unfold_until = (uu___102_1459.unfold_until);
            unfold_only = (uu___102_1459.unfold_only);
            unfold_fully = (uu___102_1459.unfold_fully);
            unfold_attr = (uu___102_1459.unfold_attr);
            unfold_tac = (uu___102_1459.unfold_tac);
            pure_subterms_within_computations =
              (uu___102_1459.pure_subterms_within_computations);
            simplify = (uu___102_1459.simplify);
            erase_universes = (uu___102_1459.erase_universes);
            allow_unbound_universes = (uu___102_1459.allow_unbound_universes);
            reify_ = (uu___102_1459.reify_);
            compress_uvars = (uu___102_1459.compress_uvars);
            no_full_norm = (uu___102_1459.no_full_norm);
            check_no_uvars = (uu___102_1459.check_no_uvars);
            unmeta = (uu___102_1459.unmeta);
            unascribe = (uu___102_1459.unascribe);
            in_full_norm_request = (uu___102_1459.in_full_norm_request)
          }
      | HNF  ->
          let uu___103_1460 = fs  in
          {
            beta = (uu___103_1460.beta);
            iota = (uu___103_1460.iota);
            zeta = (uu___103_1460.zeta);
            weak = (uu___103_1460.weak);
            hnf = true;
            primops = (uu___103_1460.primops);
            do_not_unfold_pure_lets = (uu___103_1460.do_not_unfold_pure_lets);
            unfold_until = (uu___103_1460.unfold_until);
            unfold_only = (uu___103_1460.unfold_only);
            unfold_fully = (uu___103_1460.unfold_fully);
            unfold_attr = (uu___103_1460.unfold_attr);
            unfold_tac = (uu___103_1460.unfold_tac);
            pure_subterms_within_computations =
              (uu___103_1460.pure_subterms_within_computations);
            simplify = (uu___103_1460.simplify);
            erase_universes = (uu___103_1460.erase_universes);
            allow_unbound_universes = (uu___103_1460.allow_unbound_universes);
            reify_ = (uu___103_1460.reify_);
            compress_uvars = (uu___103_1460.compress_uvars);
            no_full_norm = (uu___103_1460.no_full_norm);
            check_no_uvars = (uu___103_1460.check_no_uvars);
            unmeta = (uu___103_1460.unmeta);
            unascribe = (uu___103_1460.unascribe);
            in_full_norm_request = (uu___103_1460.in_full_norm_request)
          }
      | Primops  ->
          let uu___104_1461 = fs  in
          {
            beta = (uu___104_1461.beta);
            iota = (uu___104_1461.iota);
            zeta = (uu___104_1461.zeta);
            weak = (uu___104_1461.weak);
            hnf = (uu___104_1461.hnf);
            primops = true;
            do_not_unfold_pure_lets = (uu___104_1461.do_not_unfold_pure_lets);
            unfold_until = (uu___104_1461.unfold_until);
            unfold_only = (uu___104_1461.unfold_only);
            unfold_fully = (uu___104_1461.unfold_fully);
            unfold_attr = (uu___104_1461.unfold_attr);
            unfold_tac = (uu___104_1461.unfold_tac);
            pure_subterms_within_computations =
              (uu___104_1461.pure_subterms_within_computations);
            simplify = (uu___104_1461.simplify);
            erase_universes = (uu___104_1461.erase_universes);
            allow_unbound_universes = (uu___104_1461.allow_unbound_universes);
            reify_ = (uu___104_1461.reify_);
            compress_uvars = (uu___104_1461.compress_uvars);
            no_full_norm = (uu___104_1461.no_full_norm);
            check_no_uvars = (uu___104_1461.check_no_uvars);
            unmeta = (uu___104_1461.unmeta);
            unascribe = (uu___104_1461.unascribe);
            in_full_norm_request = (uu___104_1461.in_full_norm_request)
          }
      | Eager_unfolding  -> fs
      | Inlining  -> fs
      | DoNotUnfoldPureLets  ->
          let uu___105_1462 = fs  in
          {
            beta = (uu___105_1462.beta);
            iota = (uu___105_1462.iota);
            zeta = (uu___105_1462.zeta);
            weak = (uu___105_1462.weak);
            hnf = (uu___105_1462.hnf);
            primops = (uu___105_1462.primops);
            do_not_unfold_pure_lets = true;
            unfold_until = (uu___105_1462.unfold_until);
            unfold_only = (uu___105_1462.unfold_only);
            unfold_fully = (uu___105_1462.unfold_fully);
            unfold_attr = (uu___105_1462.unfold_attr);
            unfold_tac = (uu___105_1462.unfold_tac);
            pure_subterms_within_computations =
              (uu___105_1462.pure_subterms_within_computations);
            simplify = (uu___105_1462.simplify);
            erase_universes = (uu___105_1462.erase_universes);
            allow_unbound_universes = (uu___105_1462.allow_unbound_universes);
            reify_ = (uu___105_1462.reify_);
            compress_uvars = (uu___105_1462.compress_uvars);
            no_full_norm = (uu___105_1462.no_full_norm);
            check_no_uvars = (uu___105_1462.check_no_uvars);
            unmeta = (uu___105_1462.unmeta);
            unascribe = (uu___105_1462.unascribe);
            in_full_norm_request = (uu___105_1462.in_full_norm_request)
          }
      | UnfoldUntil d ->
          let uu___106_1464 = fs  in
          {
            beta = (uu___106_1464.beta);
            iota = (uu___106_1464.iota);
            zeta = (uu___106_1464.zeta);
            weak = (uu___106_1464.weak);
            hnf = (uu___106_1464.hnf);
            primops = (uu___106_1464.primops);
            do_not_unfold_pure_lets = (uu___106_1464.do_not_unfold_pure_lets);
            unfold_until = (FStar_Pervasives_Native.Some d);
            unfold_only = (uu___106_1464.unfold_only);
            unfold_fully = (uu___106_1464.unfold_fully);
            unfold_attr = (uu___106_1464.unfold_attr);
            unfold_tac = (uu___106_1464.unfold_tac);
            pure_subterms_within_computations =
              (uu___106_1464.pure_subterms_within_computations);
            simplify = (uu___106_1464.simplify);
            erase_universes = (uu___106_1464.erase_universes);
            allow_unbound_universes = (uu___106_1464.allow_unbound_universes);
            reify_ = (uu___106_1464.reify_);
            compress_uvars = (uu___106_1464.compress_uvars);
            no_full_norm = (uu___106_1464.no_full_norm);
            check_no_uvars = (uu___106_1464.check_no_uvars);
            unmeta = (uu___106_1464.unmeta);
            unascribe = (uu___106_1464.unascribe);
            in_full_norm_request = (uu___106_1464.in_full_norm_request)
          }
      | UnfoldOnly lids ->
          let uu___107_1468 = fs  in
          {
            beta = (uu___107_1468.beta);
            iota = (uu___107_1468.iota);
            zeta = (uu___107_1468.zeta);
            weak = (uu___107_1468.weak);
            hnf = (uu___107_1468.hnf);
            primops = (uu___107_1468.primops);
            do_not_unfold_pure_lets = (uu___107_1468.do_not_unfold_pure_lets);
            unfold_until = (uu___107_1468.unfold_until);
            unfold_only = (FStar_Pervasives_Native.Some lids);
            unfold_fully = (uu___107_1468.unfold_fully);
            unfold_attr = (uu___107_1468.unfold_attr);
            unfold_tac = (uu___107_1468.unfold_tac);
            pure_subterms_within_computations =
              (uu___107_1468.pure_subterms_within_computations);
            simplify = (uu___107_1468.simplify);
            erase_universes = (uu___107_1468.erase_universes);
            allow_unbound_universes = (uu___107_1468.allow_unbound_universes);
            reify_ = (uu___107_1468.reify_);
            compress_uvars = (uu___107_1468.compress_uvars);
            no_full_norm = (uu___107_1468.no_full_norm);
            check_no_uvars = (uu___107_1468.check_no_uvars);
            unmeta = (uu___107_1468.unmeta);
            unascribe = (uu___107_1468.unascribe);
            in_full_norm_request = (uu___107_1468.in_full_norm_request)
          }
      | UnfoldFully lids ->
          let uu___108_1474 = fs  in
          {
            beta = (uu___108_1474.beta);
            iota = (uu___108_1474.iota);
            zeta = (uu___108_1474.zeta);
            weak = (uu___108_1474.weak);
            hnf = (uu___108_1474.hnf);
            primops = (uu___108_1474.primops);
            do_not_unfold_pure_lets = (uu___108_1474.do_not_unfold_pure_lets);
            unfold_until = (uu___108_1474.unfold_until);
            unfold_only = (uu___108_1474.unfold_only);
            unfold_fully = (FStar_Pervasives_Native.Some lids);
            unfold_attr = (uu___108_1474.unfold_attr);
            unfold_tac = (uu___108_1474.unfold_tac);
            pure_subterms_within_computations =
              (uu___108_1474.pure_subterms_within_computations);
            simplify = (uu___108_1474.simplify);
            erase_universes = (uu___108_1474.erase_universes);
            allow_unbound_universes = (uu___108_1474.allow_unbound_universes);
            reify_ = (uu___108_1474.reify_);
            compress_uvars = (uu___108_1474.compress_uvars);
            no_full_norm = (uu___108_1474.no_full_norm);
            check_no_uvars = (uu___108_1474.check_no_uvars);
            unmeta = (uu___108_1474.unmeta);
            unascribe = (uu___108_1474.unascribe);
            in_full_norm_request = (uu___108_1474.in_full_norm_request)
          }
      | UnfoldAttr attr ->
          let uu___109_1478 = fs  in
          {
            beta = (uu___109_1478.beta);
            iota = (uu___109_1478.iota);
            zeta = (uu___109_1478.zeta);
            weak = (uu___109_1478.weak);
            hnf = (uu___109_1478.hnf);
            primops = (uu___109_1478.primops);
            do_not_unfold_pure_lets = (uu___109_1478.do_not_unfold_pure_lets);
            unfold_until = (uu___109_1478.unfold_until);
            unfold_only = (uu___109_1478.unfold_only);
            unfold_fully = (uu___109_1478.unfold_fully);
            unfold_attr = (add_opt attr fs.unfold_attr);
            unfold_tac = (uu___109_1478.unfold_tac);
            pure_subterms_within_computations =
              (uu___109_1478.pure_subterms_within_computations);
            simplify = (uu___109_1478.simplify);
            erase_universes = (uu___109_1478.erase_universes);
            allow_unbound_universes = (uu___109_1478.allow_unbound_universes);
            reify_ = (uu___109_1478.reify_);
            compress_uvars = (uu___109_1478.compress_uvars);
            no_full_norm = (uu___109_1478.no_full_norm);
            check_no_uvars = (uu___109_1478.check_no_uvars);
            unmeta = (uu___109_1478.unmeta);
            unascribe = (uu___109_1478.unascribe);
            in_full_norm_request = (uu___109_1478.in_full_norm_request)
          }
      | UnfoldTac  ->
          let uu___110_1479 = fs  in
          {
            beta = (uu___110_1479.beta);
            iota = (uu___110_1479.iota);
            zeta = (uu___110_1479.zeta);
            weak = (uu___110_1479.weak);
            hnf = (uu___110_1479.hnf);
            primops = (uu___110_1479.primops);
            do_not_unfold_pure_lets = (uu___110_1479.do_not_unfold_pure_lets);
            unfold_until = (uu___110_1479.unfold_until);
            unfold_only = (uu___110_1479.unfold_only);
            unfold_fully = (uu___110_1479.unfold_fully);
            unfold_attr = (uu___110_1479.unfold_attr);
            unfold_tac = true;
            pure_subterms_within_computations =
              (uu___110_1479.pure_subterms_within_computations);
            simplify = (uu___110_1479.simplify);
            erase_universes = (uu___110_1479.erase_universes);
            allow_unbound_universes = (uu___110_1479.allow_unbound_universes);
            reify_ = (uu___110_1479.reify_);
            compress_uvars = (uu___110_1479.compress_uvars);
            no_full_norm = (uu___110_1479.no_full_norm);
            check_no_uvars = (uu___110_1479.check_no_uvars);
            unmeta = (uu___110_1479.unmeta);
            unascribe = (uu___110_1479.unascribe);
            in_full_norm_request = (uu___110_1479.in_full_norm_request)
          }
      | PureSubtermsWithinComputations  ->
          let uu___111_1480 = fs  in
          {
            beta = (uu___111_1480.beta);
            iota = (uu___111_1480.iota);
            zeta = (uu___111_1480.zeta);
            weak = (uu___111_1480.weak);
            hnf = (uu___111_1480.hnf);
            primops = (uu___111_1480.primops);
            do_not_unfold_pure_lets = (uu___111_1480.do_not_unfold_pure_lets);
            unfold_until = (uu___111_1480.unfold_until);
            unfold_only = (uu___111_1480.unfold_only);
            unfold_fully = (uu___111_1480.unfold_fully);
            unfold_attr = (uu___111_1480.unfold_attr);
            unfold_tac = (uu___111_1480.unfold_tac);
            pure_subterms_within_computations = true;
            simplify = (uu___111_1480.simplify);
            erase_universes = (uu___111_1480.erase_universes);
            allow_unbound_universes = (uu___111_1480.allow_unbound_universes);
            reify_ = (uu___111_1480.reify_);
            compress_uvars = (uu___111_1480.compress_uvars);
            no_full_norm = (uu___111_1480.no_full_norm);
            check_no_uvars = (uu___111_1480.check_no_uvars);
            unmeta = (uu___111_1480.unmeta);
            unascribe = (uu___111_1480.unascribe);
            in_full_norm_request = (uu___111_1480.in_full_norm_request)
          }
      | Simplify  ->
          let uu___112_1481 = fs  in
          {
            beta = (uu___112_1481.beta);
            iota = (uu___112_1481.iota);
            zeta = (uu___112_1481.zeta);
            weak = (uu___112_1481.weak);
            hnf = (uu___112_1481.hnf);
            primops = (uu___112_1481.primops);
            do_not_unfold_pure_lets = (uu___112_1481.do_not_unfold_pure_lets);
            unfold_until = (uu___112_1481.unfold_until);
            unfold_only = (uu___112_1481.unfold_only);
            unfold_fully = (uu___112_1481.unfold_fully);
            unfold_attr = (uu___112_1481.unfold_attr);
            unfold_tac = (uu___112_1481.unfold_tac);
            pure_subterms_within_computations =
              (uu___112_1481.pure_subterms_within_computations);
            simplify = true;
            erase_universes = (uu___112_1481.erase_universes);
            allow_unbound_universes = (uu___112_1481.allow_unbound_universes);
            reify_ = (uu___112_1481.reify_);
            compress_uvars = (uu___112_1481.compress_uvars);
            no_full_norm = (uu___112_1481.no_full_norm);
            check_no_uvars = (uu___112_1481.check_no_uvars);
            unmeta = (uu___112_1481.unmeta);
            unascribe = (uu___112_1481.unascribe);
            in_full_norm_request = (uu___112_1481.in_full_norm_request)
          }
      | EraseUniverses  ->
          let uu___113_1482 = fs  in
          {
            beta = (uu___113_1482.beta);
            iota = (uu___113_1482.iota);
            zeta = (uu___113_1482.zeta);
            weak = (uu___113_1482.weak);
            hnf = (uu___113_1482.hnf);
            primops = (uu___113_1482.primops);
            do_not_unfold_pure_lets = (uu___113_1482.do_not_unfold_pure_lets);
            unfold_until = (uu___113_1482.unfold_until);
            unfold_only = (uu___113_1482.unfold_only);
            unfold_fully = (uu___113_1482.unfold_fully);
            unfold_attr = (uu___113_1482.unfold_attr);
            unfold_tac = (uu___113_1482.unfold_tac);
            pure_subterms_within_computations =
              (uu___113_1482.pure_subterms_within_computations);
            simplify = (uu___113_1482.simplify);
            erase_universes = true;
            allow_unbound_universes = (uu___113_1482.allow_unbound_universes);
            reify_ = (uu___113_1482.reify_);
            compress_uvars = (uu___113_1482.compress_uvars);
            no_full_norm = (uu___113_1482.no_full_norm);
            check_no_uvars = (uu___113_1482.check_no_uvars);
            unmeta = (uu___113_1482.unmeta);
            unascribe = (uu___113_1482.unascribe);
            in_full_norm_request = (uu___113_1482.in_full_norm_request)
          }
      | AllowUnboundUniverses  ->
          let uu___114_1483 = fs  in
          {
            beta = (uu___114_1483.beta);
            iota = (uu___114_1483.iota);
            zeta = (uu___114_1483.zeta);
            weak = (uu___114_1483.weak);
            hnf = (uu___114_1483.hnf);
            primops = (uu___114_1483.primops);
            do_not_unfold_pure_lets = (uu___114_1483.do_not_unfold_pure_lets);
            unfold_until = (uu___114_1483.unfold_until);
            unfold_only = (uu___114_1483.unfold_only);
            unfold_fully = (uu___114_1483.unfold_fully);
            unfold_attr = (uu___114_1483.unfold_attr);
            unfold_tac = (uu___114_1483.unfold_tac);
            pure_subterms_within_computations =
              (uu___114_1483.pure_subterms_within_computations);
            simplify = (uu___114_1483.simplify);
            erase_universes = (uu___114_1483.erase_universes);
            allow_unbound_universes = true;
            reify_ = (uu___114_1483.reify_);
            compress_uvars = (uu___114_1483.compress_uvars);
            no_full_norm = (uu___114_1483.no_full_norm);
            check_no_uvars = (uu___114_1483.check_no_uvars);
            unmeta = (uu___114_1483.unmeta);
            unascribe = (uu___114_1483.unascribe);
            in_full_norm_request = (uu___114_1483.in_full_norm_request)
          }
      | Reify  ->
          let uu___115_1484 = fs  in
          {
            beta = (uu___115_1484.beta);
            iota = (uu___115_1484.iota);
            zeta = (uu___115_1484.zeta);
            weak = (uu___115_1484.weak);
            hnf = (uu___115_1484.hnf);
            primops = (uu___115_1484.primops);
            do_not_unfold_pure_lets = (uu___115_1484.do_not_unfold_pure_lets);
            unfold_until = (uu___115_1484.unfold_until);
            unfold_only = (uu___115_1484.unfold_only);
            unfold_fully = (uu___115_1484.unfold_fully);
            unfold_attr = (uu___115_1484.unfold_attr);
            unfold_tac = (uu___115_1484.unfold_tac);
            pure_subterms_within_computations =
              (uu___115_1484.pure_subterms_within_computations);
            simplify = (uu___115_1484.simplify);
            erase_universes = (uu___115_1484.erase_universes);
            allow_unbound_universes = (uu___115_1484.allow_unbound_universes);
            reify_ = true;
            compress_uvars = (uu___115_1484.compress_uvars);
            no_full_norm = (uu___115_1484.no_full_norm);
            check_no_uvars = (uu___115_1484.check_no_uvars);
            unmeta = (uu___115_1484.unmeta);
            unascribe = (uu___115_1484.unascribe);
            in_full_norm_request = (uu___115_1484.in_full_norm_request)
          }
      | CompressUvars  ->
          let uu___116_1485 = fs  in
          {
            beta = (uu___116_1485.beta);
            iota = (uu___116_1485.iota);
            zeta = (uu___116_1485.zeta);
            weak = (uu___116_1485.weak);
            hnf = (uu___116_1485.hnf);
            primops = (uu___116_1485.primops);
            do_not_unfold_pure_lets = (uu___116_1485.do_not_unfold_pure_lets);
            unfold_until = (uu___116_1485.unfold_until);
            unfold_only = (uu___116_1485.unfold_only);
            unfold_fully = (uu___116_1485.unfold_fully);
            unfold_attr = (uu___116_1485.unfold_attr);
            unfold_tac = (uu___116_1485.unfold_tac);
            pure_subterms_within_computations =
              (uu___116_1485.pure_subterms_within_computations);
            simplify = (uu___116_1485.simplify);
            erase_universes = (uu___116_1485.erase_universes);
            allow_unbound_universes = (uu___116_1485.allow_unbound_universes);
            reify_ = (uu___116_1485.reify_);
            compress_uvars = true;
            no_full_norm = (uu___116_1485.no_full_norm);
            check_no_uvars = (uu___116_1485.check_no_uvars);
            unmeta = (uu___116_1485.unmeta);
            unascribe = (uu___116_1485.unascribe);
            in_full_norm_request = (uu___116_1485.in_full_norm_request)
          }
      | NoFullNorm  ->
          let uu___117_1486 = fs  in
          {
            beta = (uu___117_1486.beta);
            iota = (uu___117_1486.iota);
            zeta = (uu___117_1486.zeta);
            weak = (uu___117_1486.weak);
            hnf = (uu___117_1486.hnf);
            primops = (uu___117_1486.primops);
            do_not_unfold_pure_lets = (uu___117_1486.do_not_unfold_pure_lets);
            unfold_until = (uu___117_1486.unfold_until);
            unfold_only = (uu___117_1486.unfold_only);
            unfold_fully = (uu___117_1486.unfold_fully);
            unfold_attr = (uu___117_1486.unfold_attr);
            unfold_tac = (uu___117_1486.unfold_tac);
            pure_subterms_within_computations =
              (uu___117_1486.pure_subterms_within_computations);
            simplify = (uu___117_1486.simplify);
            erase_universes = (uu___117_1486.erase_universes);
            allow_unbound_universes = (uu___117_1486.allow_unbound_universes);
            reify_ = (uu___117_1486.reify_);
            compress_uvars = (uu___117_1486.compress_uvars);
            no_full_norm = true;
            check_no_uvars = (uu___117_1486.check_no_uvars);
            unmeta = (uu___117_1486.unmeta);
            unascribe = (uu___117_1486.unascribe);
            in_full_norm_request = (uu___117_1486.in_full_norm_request)
          }
      | CheckNoUvars  ->
          let uu___118_1487 = fs  in
          {
            beta = (uu___118_1487.beta);
            iota = (uu___118_1487.iota);
            zeta = (uu___118_1487.zeta);
            weak = (uu___118_1487.weak);
            hnf = (uu___118_1487.hnf);
            primops = (uu___118_1487.primops);
            do_not_unfold_pure_lets = (uu___118_1487.do_not_unfold_pure_lets);
            unfold_until = (uu___118_1487.unfold_until);
            unfold_only = (uu___118_1487.unfold_only);
            unfold_fully = (uu___118_1487.unfold_fully);
            unfold_attr = (uu___118_1487.unfold_attr);
            unfold_tac = (uu___118_1487.unfold_tac);
            pure_subterms_within_computations =
              (uu___118_1487.pure_subterms_within_computations);
            simplify = (uu___118_1487.simplify);
            erase_universes = (uu___118_1487.erase_universes);
            allow_unbound_universes = (uu___118_1487.allow_unbound_universes);
            reify_ = (uu___118_1487.reify_);
            compress_uvars = (uu___118_1487.compress_uvars);
            no_full_norm = (uu___118_1487.no_full_norm);
            check_no_uvars = true;
            unmeta = (uu___118_1487.unmeta);
            unascribe = (uu___118_1487.unascribe);
            in_full_norm_request = (uu___118_1487.in_full_norm_request)
          }
      | Unmeta  ->
          let uu___119_1488 = fs  in
          {
            beta = (uu___119_1488.beta);
            iota = (uu___119_1488.iota);
            zeta = (uu___119_1488.zeta);
            weak = (uu___119_1488.weak);
            hnf = (uu___119_1488.hnf);
            primops = (uu___119_1488.primops);
            do_not_unfold_pure_lets = (uu___119_1488.do_not_unfold_pure_lets);
            unfold_until = (uu___119_1488.unfold_until);
            unfold_only = (uu___119_1488.unfold_only);
            unfold_fully = (uu___119_1488.unfold_fully);
            unfold_attr = (uu___119_1488.unfold_attr);
            unfold_tac = (uu___119_1488.unfold_tac);
            pure_subterms_within_computations =
              (uu___119_1488.pure_subterms_within_computations);
            simplify = (uu___119_1488.simplify);
            erase_universes = (uu___119_1488.erase_universes);
            allow_unbound_universes = (uu___119_1488.allow_unbound_universes);
            reify_ = (uu___119_1488.reify_);
            compress_uvars = (uu___119_1488.compress_uvars);
            no_full_norm = (uu___119_1488.no_full_norm);
            check_no_uvars = (uu___119_1488.check_no_uvars);
            unmeta = true;
            unascribe = (uu___119_1488.unascribe);
            in_full_norm_request = (uu___119_1488.in_full_norm_request)
          }
      | Unascribe  ->
          let uu___120_1489 = fs  in
          {
            beta = (uu___120_1489.beta);
            iota = (uu___120_1489.iota);
            zeta = (uu___120_1489.zeta);
            weak = (uu___120_1489.weak);
            hnf = (uu___120_1489.hnf);
            primops = (uu___120_1489.primops);
            do_not_unfold_pure_lets = (uu___120_1489.do_not_unfold_pure_lets);
            unfold_until = (uu___120_1489.unfold_until);
            unfold_only = (uu___120_1489.unfold_only);
            unfold_fully = (uu___120_1489.unfold_fully);
            unfold_attr = (uu___120_1489.unfold_attr);
            unfold_tac = (uu___120_1489.unfold_tac);
            pure_subterms_within_computations =
              (uu___120_1489.pure_subterms_within_computations);
            simplify = (uu___120_1489.simplify);
            erase_universes = (uu___120_1489.erase_universes);
            allow_unbound_universes = (uu___120_1489.allow_unbound_universes);
            reify_ = (uu___120_1489.reify_);
            compress_uvars = (uu___120_1489.compress_uvars);
            no_full_norm = (uu___120_1489.no_full_norm);
            check_no_uvars = (uu___120_1489.check_no_uvars);
            unmeta = (uu___120_1489.unmeta);
            unascribe = true;
            in_full_norm_request = (uu___120_1489.in_full_norm_request)
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
  { psc_range = FStar_Range.dummyRange; psc_subst = (fun uu____1542  -> []) } 
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
    match projectee with | Clos _0 -> true | uu____1831 -> false
  
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
    match projectee with | Univ _0 -> true | uu____1935 -> false
  
let (__proj__Univ__item___0 : closure -> FStar_Syntax_Syntax.universe) =
  fun projectee  -> match projectee with | Univ _0 -> _0 
let (uu___is_Dummy : closure -> Prims.bool) =
  fun projectee  ->
    match projectee with | Dummy  -> true | uu____1948 -> false
  
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
             let uu____2259 = FStar_Ident.text_of_lid p.name  in
             FStar_Util.psmap_add m1 uu____2259 p) l m
  
let (prim_from_list :
  primitive_step Prims.list -> primitive_step FStar_Util.psmap) =
  fun l  ->
    let uu____2273 = FStar_Util.psmap_empty ()  in add_steps uu____2273 l
  
let (find_prim_step :
  cfg ->
    FStar_Syntax_Syntax.fv -> primitive_step FStar_Pervasives_Native.option)
  =
  fun cfg  ->
    fun fv  ->
      let uu____2288 =
        FStar_Ident.text_of_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
         in
      FStar_Util.psmap_try_find cfg.primitive_steps uu____2288
  
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
    match projectee with | Arg _0 -> true | uu____2446 -> false
  
let (__proj__Arg__item___0 :
  stack_elt ->
    (closure,FStar_Syntax_Syntax.aqual,FStar_Range.range)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | Arg _0 -> _0 
let (uu___is_UnivArgs : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnivArgs _0 -> true | uu____2484 -> false
  
let (__proj__UnivArgs__item___0 :
  stack_elt ->
    (FStar_Syntax_Syntax.universe Prims.list,FStar_Range.range)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | UnivArgs _0 -> _0 
let (uu___is_MemoLazy : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | MemoLazy _0 -> true | uu____2522 -> false
  
let (__proj__MemoLazy__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.term) FStar_Pervasives_Native.tuple2
      FStar_Syntax_Syntax.memo)
  = fun projectee  -> match projectee with | MemoLazy _0 -> _0 
let (uu___is_Match : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____2595 -> false
  
let (__proj__Match__item___0 :
  stack_elt ->
    (env,branches,cfg,FStar_Range.range) FStar_Pervasives_Native.tuple4)
  = fun projectee  -> match projectee with | Match _0 -> _0 
let (uu___is_Abs : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Abs _0 -> true | uu____2645 -> false
  
let (__proj__Abs__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.binders,env,FStar_Syntax_Syntax.residual_comp
                                           FStar_Pervasives_Native.option,
      FStar_Range.range) FStar_Pervasives_Native.tuple5)
  = fun projectee  -> match projectee with | Abs _0 -> _0 
let (uu___is_App : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____2703 -> false
  
let (__proj__App__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual,FStar_Range.range)
      FStar_Pervasives_Native.tuple4)
  = fun projectee  -> match projectee with | App _0 -> _0 
let (uu___is_Meta : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Meta _0 -> true | uu____2747 -> false
  
let (__proj__Meta__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.metadata,FStar_Range.range)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | Meta _0 -> _0 
let (uu___is_Let : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Let _0 -> true | uu____2787 -> false
  
let (__proj__Let__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.letbinding,FStar_Range.range)
      FStar_Pervasives_Native.tuple4)
  = fun projectee  -> match projectee with | Let _0 -> _0 
let (uu___is_Cfg : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Cfg _0 -> true | uu____2825 -> false
  
let (__proj__Cfg__item___0 : stack_elt -> cfg) =
  fun projectee  -> match projectee with | Cfg _0 -> _0 
let (uu___is_Debug : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Debug _0 -> true | uu____2843 -> false
  
let (__proj__Debug__item___0 :
  stack_elt ->
    (FStar_Syntax_Syntax.term,FStar_Util.time) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Debug _0 -> _0 
type stack = stack_elt Prims.list[@@deriving show]
let (head_of : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____2870 = FStar_Syntax_Util.head_and_args' t  in
    match uu____2870 with | (hd1,uu____2884) -> hd1
  
let mk :
  'Auu____2907 .
    'Auu____2907 ->
      FStar_Range.range -> 'Auu____2907 FStar_Syntax_Syntax.syntax
  =
  fun t  -> fun r  -> FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None r 
let set_memo : 'a . cfg -> 'a FStar_Syntax_Syntax.memo -> 'a -> unit =
  fun cfg  ->
    fun r  ->
      fun t  ->
        if cfg.memoize_lazy
        then
          let uu____2970 = FStar_ST.op_Bang r  in
          match uu____2970 with
          | FStar_Pervasives_Native.Some uu____3022 ->
              failwith "Unexpected set_memo: thunk already evaluated"
          | FStar_Pervasives_Native.None  ->
              FStar_ST.op_Colon_Equals r (FStar_Pervasives_Native.Some t)
        else ()
  
let rec (env_to_string :
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
    FStar_Pervasives_Native.tuple2 Prims.list -> Prims.string)
  =
  fun env  ->
    let uu____3098 =
      FStar_List.map
        (fun uu____3112  ->
           match uu____3112 with
           | (bopt,c) ->
               let uu____3125 =
                 match bopt with
                 | FStar_Pervasives_Native.None  -> "."
                 | FStar_Pervasives_Native.Some x ->
                     FStar_Syntax_Print.binder_to_string x
                  in
               let uu____3127 = closure_to_string c  in
               FStar_Util.format2 "(%s, %s)" uu____3125 uu____3127) env
       in
    FStar_All.pipe_right uu____3098 (FStar_String.concat "; ")

and (closure_to_string : closure -> Prims.string) =
  fun uu___79_3130  ->
    match uu___79_3130 with
    | Clos (env,t,uu____3133,uu____3134) ->
        let uu____3179 =
          FStar_All.pipe_right (FStar_List.length env)
            FStar_Util.string_of_int
           in
        let uu____3186 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format2 "(env=%s elts; %s)" uu____3179 uu____3186
    | Univ uu____3187 -> "Univ"
    | Dummy  -> "dummy"

let (stack_elt_to_string : stack_elt -> Prims.string) =
  fun uu___80_3192  ->
    match uu___80_3192 with
    | Arg (c,uu____3194,uu____3195) ->
        let uu____3196 = closure_to_string c  in
        FStar_Util.format1 "Closure %s" uu____3196
    | MemoLazy uu____3197 -> "MemoLazy"
    | Abs (uu____3204,bs,uu____3206,uu____3207,uu____3208) ->
        let uu____3213 =
          FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs)
           in
        FStar_Util.format1 "Abs %s" uu____3213
    | UnivArgs uu____3218 -> "UnivArgs"
    | Match uu____3225 -> "Match"
    | App (uu____3234,t,uu____3236,uu____3237) ->
        let uu____3238 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "App %s" uu____3238
    | Meta (uu____3239,m,uu____3241) -> "Meta"
    | Let uu____3242 -> "Let"
    | Cfg uu____3251 -> "Cfg"
    | Debug (t,uu____3253) ->
        let uu____3254 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "Debug %s" uu____3254
  
let (stack_to_string : stack_elt Prims.list -> Prims.string) =
  fun s  ->
    let uu____3264 = FStar_List.map stack_elt_to_string s  in
    FStar_All.pipe_right uu____3264 (FStar_String.concat "; ")
  
let (log : cfg -> (unit -> unit) -> unit) =
  fun cfg  -> fun f  -> if (cfg.debug).gen then f () else () 
let (log_primops : cfg -> (unit -> unit) -> unit) =
  fun cfg  -> fun f  -> if (cfg.debug).primop then f () else () 
let is_empty : 'Auu____3305 . 'Auu____3305 Prims.list -> Prims.bool =
  fun uu___81_3312  ->
    match uu___81_3312 with | [] -> true | uu____3315 -> false
  
let (lookup_bvar :
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    FStar_Syntax_Syntax.bv -> closure)
  =
  fun env  ->
    fun x  ->
      try
        let uu____3347 = FStar_List.nth env x.FStar_Syntax_Syntax.index  in
        FStar_Pervasives_Native.snd uu____3347
      with
      | uu____3366 ->
          let uu____3367 =
            let uu____3368 = FStar_Syntax_Print.db_to_string x  in
            let uu____3369 = env_to_string env  in
            FStar_Util.format2 "Failed to find %s\nEnv is %s\n" uu____3368
              uu____3369
             in
          failwith uu____3367
  
let (downgrade_ghost_effect_name :
  FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option) =
  fun l  ->
    let uu____3377 =
      FStar_Ident.lid_equals l FStar_Parser_Const.effect_Ghost_lid  in
    if uu____3377
    then FStar_Pervasives_Native.Some FStar_Parser_Const.effect_Pure_lid
    else
      (let uu____3381 =
         FStar_Ident.lid_equals l FStar_Parser_Const.effect_GTot_lid  in
       if uu____3381
       then FStar_Pervasives_Native.Some FStar_Parser_Const.effect_Tot_lid
       else
         (let uu____3385 =
            FStar_Ident.lid_equals l FStar_Parser_Const.effect_GHOST_lid  in
          if uu____3385
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
          let uu____3419 =
            FStar_List.fold_left
              (fun uu____3445  ->
                 fun u1  ->
                   match uu____3445 with
                   | (cur_kernel,cur_max,out) ->
                       let uu____3470 = FStar_Syntax_Util.univ_kernel u1  in
                       (match uu____3470 with
                        | (k_u,n1) ->
                            let uu____3485 =
                              FStar_Syntax_Util.eq_univs cur_kernel k_u  in
                            if uu____3485
                            then (cur_kernel, u1, out)
                            else (k_u, u1, (cur_max :: out))))
              (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero, [])
              us1
             in
          match uu____3419 with
          | (uu____3503,u1,out) -> FStar_List.rev (u1 :: out)  in
        let rec aux u1 =
          let u2 = FStar_Syntax_Subst.compress_univ u1  in
          match u2 with
          | FStar_Syntax_Syntax.U_bvar x ->
              (try
                 let uu____3530 =
                   let uu____3531 = FStar_List.nth env x  in
                   FStar_Pervasives_Native.snd uu____3531  in
                 match uu____3530 with
                 | Univ u3 -> aux u3
                 | Dummy  -> [u2]
                 | uu____3549 ->
                     failwith "Impossible: universe variable bound to a term"
               with
               | uu____3557 ->
                   if (cfg.steps).allow_unbound_universes
                   then [FStar_Syntax_Syntax.U_unknown]
                   else failwith "Universe variable not found")
          | FStar_Syntax_Syntax.U_unif uu____3563 when
              (cfg.steps).check_no_uvars -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_zero  -> [u2]
          | FStar_Syntax_Syntax.U_unif uu____3572 -> [u2]
          | FStar_Syntax_Syntax.U_name uu____3581 -> [u2]
          | FStar_Syntax_Syntax.U_unknown  -> [u2]
          | FStar_Syntax_Syntax.U_max [] -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_max us ->
              let us1 =
                let uu____3588 = FStar_List.collect aux us  in
                FStar_All.pipe_right uu____3588 norm_univs  in
              (match us1 with
               | u_k::hd1::rest ->
                   let rest1 = hd1 :: rest  in
                   let uu____3605 = FStar_Syntax_Util.univ_kernel u_k  in
                   (match uu____3605 with
                    | (FStar_Syntax_Syntax.U_zero ,n1) ->
                        let uu____3613 =
                          FStar_All.pipe_right rest1
                            (FStar_List.for_all
                               (fun u3  ->
                                  let uu____3621 =
                                    FStar_Syntax_Util.univ_kernel u3  in
                                  match uu____3621 with
                                  | (uu____3626,m) -> n1 <= m))
                           in
                        if uu____3613 then rest1 else us1
                    | uu____3631 -> us1)
               | uu____3636 -> us1)
          | FStar_Syntax_Syntax.U_succ u3 ->
              let uu____3640 = aux u3  in
              FStar_List.map (fun _0_17  -> FStar_Syntax_Syntax.U_succ _0_17)
                uu____3640
           in
        if (cfg.steps).erase_universes
        then FStar_Syntax_Syntax.U_unknown
        else
          (let uu____3644 = aux u  in
           match uu____3644 with
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
            (fun uu____3790  ->
               let uu____3791 = FStar_Syntax_Print.tag_of_term t  in
               let uu____3792 = env_to_string env  in
               let uu____3793 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print3 "\n>>> %s (env=%s) Closure_as_term %s\n"
                 uu____3791 uu____3792 uu____3793);
          (match env with
           | [] when
               FStar_All.pipe_left Prims.op_Negation
                 (cfg.steps).compress_uvars
               -> rebuild_closure cfg env stack t
           | uu____3802 ->
               (match t.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_delayed uu____3805 ->
                    let uu____3830 = FStar_Syntax_Subst.compress t  in
                    inline_closure_env cfg env stack uu____3830
                | FStar_Syntax_Syntax.Tm_unknown  ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_constant uu____3831 ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_name uu____3832 ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_lazy uu____3833 ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_fvar uu____3834 ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_uvar uu____3835 ->
                    if (cfg.steps).check_no_uvars
                    then
                      let t1 = FStar_Syntax_Subst.compress t  in
                      (match t1.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_uvar uu____3857 ->
                           let uu____3874 =
                             let uu____3875 =
                               FStar_Range.string_of_range
                                 t1.FStar_Syntax_Syntax.pos
                                in
                             let uu____3876 =
                               FStar_Syntax_Print.term_to_string t1  in
                             FStar_Util.format2
                               "(%s): CheckNoUvars: Unexpected unification variable remains: %s"
                               uu____3875 uu____3876
                              in
                           failwith uu____3874
                       | uu____3879 -> inline_closure_env cfg env stack t1)
                    else rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_type u ->
                    let t1 =
                      let uu____3885 =
                        let uu____3886 = norm_universe cfg env u  in
                        FStar_Syntax_Syntax.Tm_type uu____3886  in
                      mk uu____3885 t.FStar_Syntax_Syntax.pos  in
                    rebuild_closure cfg env stack t1
                | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
                    let t1 =
                      let uu____3894 =
                        FStar_List.map (norm_universe cfg env) us  in
                      FStar_Syntax_Syntax.mk_Tm_uinst t' uu____3894  in
                    rebuild_closure cfg env stack t1
                | FStar_Syntax_Syntax.Tm_bvar x ->
                    let uu____3896 = lookup_bvar env x  in
                    (match uu____3896 with
                     | Univ uu____3899 ->
                         failwith
                           "Impossible: term variable is bound to a universe"
                     | Dummy  ->
                         let x1 =
                           let uu___125_3903 = x  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___125_3903.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___125_3903.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort =
                               FStar_Syntax_Syntax.tun
                           }  in
                         let t1 =
                           mk (FStar_Syntax_Syntax.Tm_bvar x1)
                             t.FStar_Syntax_Syntax.pos
                            in
                         rebuild_closure cfg env stack t1
                     | Clos (env1,t0,uu____3909,uu____3910) ->
                         inline_closure_env cfg env1 stack t0)
                | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                    let stack1 =
                      FStar_All.pipe_right stack
                        (FStar_List.fold_right
                           (fun uu____3995  ->
                              fun stack1  ->
                                match uu____3995 with
                                | (a,aq) ->
                                    let uu____4007 =
                                      let uu____4008 =
                                        let uu____4015 =
                                          let uu____4016 =
                                            let uu____4047 =
                                              FStar_Util.mk_ref
                                                FStar_Pervasives_Native.None
                                               in
                                            (env, a, uu____4047, false)  in
                                          Clos uu____4016  in
                                        (uu____4015, aq,
                                          (t.FStar_Syntax_Syntax.pos))
                                         in
                                      Arg uu____4008  in
                                    uu____4007 :: stack1) args)
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
                    let uu____4241 = close_binders cfg env bs  in
                    (match uu____4241 with
                     | (bs1,env') ->
                         let c1 = close_comp cfg env' c  in
                         let t1 =
                           mk (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
                             t.FStar_Syntax_Syntax.pos
                            in
                         rebuild_closure cfg env stack t1)
                | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
                    let uu____4288 =
                      let uu____4299 =
                        let uu____4306 = FStar_Syntax_Syntax.mk_binder x  in
                        [uu____4306]  in
                      close_binders cfg env uu____4299  in
                    (match uu____4288 with
                     | (x1,env1) ->
                         let phi1 = non_tail_inline_closure_env cfg env1 phi
                            in
                         let t1 =
                           let uu____4329 =
                             let uu____4330 =
                               let uu____4337 =
                                 let uu____4338 = FStar_List.hd x1  in
                                 FStar_All.pipe_right uu____4338
                                   FStar_Pervasives_Native.fst
                                  in
                               (uu____4337, phi1)  in
                             FStar_Syntax_Syntax.Tm_refine uu____4330  in
                           mk uu____4329 t.FStar_Syntax_Syntax.pos  in
                         rebuild_closure cfg env1 stack t1)
                | FStar_Syntax_Syntax.Tm_ascribed (t1,(annot,tacopt),lopt) ->
                    let annot1 =
                      match annot with
                      | FStar_Util.Inl t2 ->
                          let uu____4429 =
                            non_tail_inline_closure_env cfg env t2  in
                          FStar_Util.Inl uu____4429
                      | FStar_Util.Inr c ->
                          let uu____4443 = close_comp cfg env c  in
                          FStar_Util.Inr uu____4443
                       in
                    let tacopt1 =
                      FStar_Util.map_opt tacopt
                        (non_tail_inline_closure_env cfg env)
                       in
                    let t2 =
                      let uu____4462 =
                        let uu____4463 =
                          let uu____4490 =
                            non_tail_inline_closure_env cfg env t1  in
                          (uu____4490, (annot1, tacopt1), lopt)  in
                        FStar_Syntax_Syntax.Tm_ascribed uu____4463  in
                      mk uu____4462 t.FStar_Syntax_Syntax.pos  in
                    rebuild_closure cfg env stack t2
                | FStar_Syntax_Syntax.Tm_quoted (t',qi) ->
                    let t1 =
                      match qi.FStar_Syntax_Syntax.qkind with
                      | FStar_Syntax_Syntax.Quote_dynamic  ->
                          let uu____4536 =
                            let uu____4537 =
                              let uu____4544 =
                                non_tail_inline_closure_env cfg env t'  in
                              (uu____4544, qi)  in
                            FStar_Syntax_Syntax.Tm_quoted uu____4537  in
                          mk uu____4536 t.FStar_Syntax_Syntax.pos
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
                        (fun env1  -> fun uu____4596  -> dummy :: env1) env
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
                    let uu____4617 =
                      let uu____4628 = FStar_Syntax_Syntax.is_top_level [lb]
                         in
                      if uu____4628
                      then ((lb.FStar_Syntax_Syntax.lbname), body)
                      else
                        (let x =
                           FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                         let uu____4647 =
                           non_tail_inline_closure_env cfg (dummy :: env0)
                             body
                            in
                         ((FStar_Util.Inl
                             (let uu___126_4663 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___126_4663.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___126_4663.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = typ
                              })), uu____4647))
                       in
                    (match uu____4617 with
                     | (nm,body1) ->
                         let lb1 =
                           let uu___127_4681 = lb  in
                           {
                             FStar_Syntax_Syntax.lbname = nm;
                             FStar_Syntax_Syntax.lbunivs =
                               (uu___127_4681.FStar_Syntax_Syntax.lbunivs);
                             FStar_Syntax_Syntax.lbtyp = typ;
                             FStar_Syntax_Syntax.lbeff =
                               (uu___127_4681.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = def;
                             FStar_Syntax_Syntax.lbattrs =
                               (uu___127_4681.FStar_Syntax_Syntax.lbattrs);
                             FStar_Syntax_Syntax.lbpos =
                               (uu___127_4681.FStar_Syntax_Syntax.lbpos)
                           }  in
                         let t1 =
                           mk
                             (FStar_Syntax_Syntax.Tm_let
                                ((false, [lb1]), body1))
                             t.FStar_Syntax_Syntax.pos
                            in
                         rebuild_closure cfg env0 stack t1)
                | FStar_Syntax_Syntax.Tm_let ((uu____4695,lbs),body) ->
                    let norm_one_lb env1 lb =
                      let env_univs =
                        FStar_List.fold_right
                          (fun uu____4758  -> fun env2  -> dummy :: env2)
                          lb.FStar_Syntax_Syntax.lbunivs env1
                         in
                      let env2 =
                        let uu____4783 = FStar_Syntax_Syntax.is_top_level lbs
                           in
                        if uu____4783
                        then env_univs
                        else
                          FStar_List.fold_right
                            (fun uu____4803  -> fun env2  -> dummy :: env2)
                            lbs env_univs
                         in
                      let ty =
                        non_tail_inline_closure_env cfg env_univs
                          lb.FStar_Syntax_Syntax.lbtyp
                         in
                      let nm =
                        let uu____4827 = FStar_Syntax_Syntax.is_top_level lbs
                           in
                        if uu____4827
                        then lb.FStar_Syntax_Syntax.lbname
                        else
                          (let x =
                             FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                              in
                           FStar_Util.Inl
                             (let uu___128_4835 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___128_4835.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___128_4835.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = ty
                              }))
                         in
                      let uu___129_4836 = lb  in
                      let uu____4837 =
                        non_tail_inline_closure_env cfg env2
                          lb.FStar_Syntax_Syntax.lbdef
                         in
                      {
                        FStar_Syntax_Syntax.lbname = nm;
                        FStar_Syntax_Syntax.lbunivs =
                          (uu___129_4836.FStar_Syntax_Syntax.lbunivs);
                        FStar_Syntax_Syntax.lbtyp = ty;
                        FStar_Syntax_Syntax.lbeff =
                          (uu___129_4836.FStar_Syntax_Syntax.lbeff);
                        FStar_Syntax_Syntax.lbdef = uu____4837;
                        FStar_Syntax_Syntax.lbattrs =
                          (uu___129_4836.FStar_Syntax_Syntax.lbattrs);
                        FStar_Syntax_Syntax.lbpos =
                          (uu___129_4836.FStar_Syntax_Syntax.lbpos)
                      }  in
                    let lbs1 =
                      FStar_All.pipe_right lbs
                        (FStar_List.map (norm_one_lb env))
                       in
                    let body1 =
                      let body_env =
                        FStar_List.fold_right
                          (fun uu____4869  -> fun env1  -> dummy :: env1)
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
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          log cfg
            (fun uu____4972  ->
               let uu____4973 = FStar_Syntax_Print.tag_of_term t  in
               let uu____4974 = env_to_string env  in
               let uu____4975 = stack_to_string stack  in
               let uu____4976 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print4
                 "\n>>> %s (env=%s, stack=%s) Rebuild closure_as_term %s\n"
                 uu____4973 uu____4974 uu____4975 uu____4976);
          (match stack with
           | [] -> t
           | (Arg (Clos (env_arg,tm,uu____4981,uu____4982),aq,r))::stack1 ->
               let stack2 = (App (env, t, aq, r)) :: stack1  in
               inline_closure_env cfg env_arg stack2 tm
           | (App (env1,head1,aq,r))::stack1 ->
               let t1 =
                 FStar_Syntax_Syntax.extend_app head1 (t, aq)
                   FStar_Pervasives_Native.None r
                  in
               rebuild_closure cfg env1 stack1 t1
           | (Abs (env',bs,env'',lopt,r))::stack1 ->
               let uu____5057 = close_binders cfg env' bs  in
               (match uu____5057 with
                | (bs1,uu____5071) ->
                    let lopt1 = close_lcomp_opt cfg env'' lopt  in
                    let uu____5087 =
                      let uu___130_5088 = FStar_Syntax_Util.abs bs1 t lopt1
                         in
                      {
                        FStar_Syntax_Syntax.n =
                          (uu___130_5088.FStar_Syntax_Syntax.n);
                        FStar_Syntax_Syntax.pos = r;
                        FStar_Syntax_Syntax.vars =
                          (uu___130_5088.FStar_Syntax_Syntax.vars)
                      }  in
                    rebuild_closure cfg env stack1 uu____5087)
           | (Match (env1,branches,cfg1,r))::stack1 ->
               let close_one_branch env2 uu____5134 =
                 match uu____5134 with
                 | (pat,w_opt,tm) ->
                     let rec norm_pat env3 p =
                       match p.FStar_Syntax_Syntax.v with
                       | FStar_Syntax_Syntax.Pat_constant uu____5209 ->
                           (p, env3)
                       | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                           let uu____5230 =
                             FStar_All.pipe_right pats
                               (FStar_List.fold_left
                                  (fun uu____5290  ->
                                     fun uu____5291  ->
                                       match (uu____5290, uu____5291) with
                                       | ((pats1,env4),(p1,b)) ->
                                           let uu____5382 = norm_pat env4 p1
                                              in
                                           (match uu____5382 with
                                            | (p2,env5) ->
                                                (((p2, b) :: pats1), env5)))
                                  ([], env3))
                              in
                           (match uu____5230 with
                            | (pats1,env4) ->
                                ((let uu___131_5464 = p  in
                                  {
                                    FStar_Syntax_Syntax.v =
                                      (FStar_Syntax_Syntax.Pat_cons
                                         (fv, (FStar_List.rev pats1)));
                                    FStar_Syntax_Syntax.p =
                                      (uu___131_5464.FStar_Syntax_Syntax.p)
                                  }), env4))
                       | FStar_Syntax_Syntax.Pat_var x ->
                           let x1 =
                             let uu___132_5483 = x  in
                             let uu____5484 =
                               non_tail_inline_closure_env cfg1 env3
                                 x.FStar_Syntax_Syntax.sort
                                in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___132_5483.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___132_5483.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____5484
                             }  in
                           ((let uu___133_5498 = p  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_var x1);
                               FStar_Syntax_Syntax.p =
                                 (uu___133_5498.FStar_Syntax_Syntax.p)
                             }), (dummy :: env3))
                       | FStar_Syntax_Syntax.Pat_wild x ->
                           let x1 =
                             let uu___134_5509 = x  in
                             let uu____5510 =
                               non_tail_inline_closure_env cfg1 env3
                                 x.FStar_Syntax_Syntax.sort
                                in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___134_5509.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___134_5509.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____5510
                             }  in
                           ((let uu___135_5524 = p  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_wild x1);
                               FStar_Syntax_Syntax.p =
                                 (uu___135_5524.FStar_Syntax_Syntax.p)
                             }), (dummy :: env3))
                       | FStar_Syntax_Syntax.Pat_dot_term (x,t1) ->
                           let x1 =
                             let uu___136_5540 = x  in
                             let uu____5541 =
                               non_tail_inline_closure_env cfg1 env3
                                 x.FStar_Syntax_Syntax.sort
                                in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___136_5540.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___136_5540.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____5541
                             }  in
                           let t2 = non_tail_inline_closure_env cfg1 env3 t1
                              in
                           ((let uu___137_5550 = p  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_dot_term (x1, t2));
                               FStar_Syntax_Syntax.p =
                                 (uu___137_5550.FStar_Syntax_Syntax.p)
                             }), env3)
                        in
                     let uu____5555 = norm_pat env2 pat  in
                     (match uu____5555 with
                      | (pat1,env3) ->
                          let w_opt1 =
                            match w_opt with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Pervasives_Native.None
                            | FStar_Pervasives_Native.Some w ->
                                let uu____5600 =
                                  non_tail_inline_closure_env cfg1 env3 w  in
                                FStar_Pervasives_Native.Some uu____5600
                             in
                          let tm1 = non_tail_inline_closure_env cfg1 env3 tm
                             in
                          (pat1, w_opt1, tm1))
                  in
               let t1 =
                 let uu____5619 =
                   let uu____5620 =
                     let uu____5643 =
                       FStar_All.pipe_right branches
                         (FStar_List.map (close_one_branch env1))
                        in
                     (t, uu____5643)  in
                   FStar_Syntax_Syntax.Tm_match uu____5620  in
                 mk uu____5619 t.FStar_Syntax_Syntax.pos  in
               rebuild_closure cfg1 env1 stack1 t1
           | (Meta (env_m,m,r))::stack1 ->
               let m1 =
                 match m with
                 | FStar_Syntax_Syntax.Meta_pattern args ->
                     let uu____5738 =
                       FStar_All.pipe_right args
                         (FStar_List.map
                            (fun args1  ->
                               FStar_All.pipe_right args1
                                 (FStar_List.map
                                    (fun uu____5827  ->
                                       match uu____5827 with
                                       | (a,q) ->
                                           let uu____5846 =
                                             non_tail_inline_closure_env cfg
                                               env_m a
                                              in
                                           (uu____5846, q)))))
                        in
                     FStar_Syntax_Syntax.Meta_pattern uu____5738
                 | FStar_Syntax_Syntax.Meta_monadic (m1,tbody) ->
                     let uu____5857 =
                       let uu____5864 =
                         non_tail_inline_closure_env cfg env_m tbody  in
                       (m1, uu____5864)  in
                     FStar_Syntax_Syntax.Meta_monadic uu____5857
                 | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,tbody) ->
                     let uu____5876 =
                       let uu____5885 =
                         non_tail_inline_closure_env cfg env_m tbody  in
                       (m1, m2, uu____5885)  in
                     FStar_Syntax_Syntax.Meta_monadic_lift uu____5876
                 | uu____5890 -> m  in
               let t1 = mk (FStar_Syntax_Syntax.Tm_meta (t, m1)) r  in
               rebuild_closure cfg env stack1 t1
           | uu____5894 -> failwith "Impossible: unexpected stack element")

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
        let uu____5908 =
          FStar_All.pipe_right bs
            (FStar_List.fold_left
               (fun uu____5957  ->
                  fun uu____5958  ->
                    match (uu____5957, uu____5958) with
                    | ((env1,out),(b,imp)) ->
                        let b1 =
                          let uu___138_6028 = b  in
                          let uu____6029 =
                            inline_closure_env cfg env1 []
                              b.FStar_Syntax_Syntax.sort
                             in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___138_6028.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___138_6028.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = uu____6029
                          }  in
                        let env2 = dummy :: env1  in
                        (env2, ((b1, imp) :: out))) (env, []))
           in
        match uu____5908 with | (env1,bs1) -> ((FStar_List.rev bs1), env1)

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
        | uu____6122 ->
            (match c.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Total (t,uopt) ->
                 let uu____6135 = inline_closure_env cfg env [] t  in
                 let uu____6136 =
                   FStar_Option.map (norm_universe cfg env) uopt  in
                 FStar_Syntax_Syntax.mk_Total' uu____6135 uu____6136
             | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                 let uu____6149 = inline_closure_env cfg env [] t  in
                 let uu____6150 =
                   FStar_Option.map (norm_universe cfg env) uopt  in
                 FStar_Syntax_Syntax.mk_GTotal' uu____6149 uu____6150
             | FStar_Syntax_Syntax.Comp c1 ->
                 let rt =
                   inline_closure_env cfg env []
                     c1.FStar_Syntax_Syntax.result_typ
                    in
                 let args =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args
                     (FStar_List.map
                        (fun uu____6196  ->
                           match uu____6196 with
                           | (a,q) ->
                               let uu____6209 =
                                 inline_closure_env cfg env [] a  in
                               (uu____6209, q)))
                    in
                 let flags1 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_List.map
                        (fun uu___82_6224  ->
                           match uu___82_6224 with
                           | FStar_Syntax_Syntax.DECREASES t ->
                               let uu____6228 =
                                 inline_closure_env cfg env [] t  in
                               FStar_Syntax_Syntax.DECREASES uu____6228
                           | f -> f))
                    in
                 let uu____6232 =
                   let uu___139_6233 = c1  in
                   let uu____6234 =
                     FStar_List.map (norm_universe cfg env)
                       c1.FStar_Syntax_Syntax.comp_univs
                      in
                   {
                     FStar_Syntax_Syntax.comp_univs = uu____6234;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___139_6233.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ = rt;
                     FStar_Syntax_Syntax.effect_args = args;
                     FStar_Syntax_Syntax.flags = flags1
                   }  in
                 FStar_Syntax_Syntax.mk_Comp uu____6232)

and (filter_out_lcomp_cflags :
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun flags1  ->
    FStar_All.pipe_right flags1
      (FStar_List.filter
         (fun uu___83_6244  ->
            match uu___83_6244 with
            | FStar_Syntax_Syntax.DECREASES uu____6245 -> false
            | uu____6248 -> true))

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
                   (fun uu___84_6266  ->
                      match uu___84_6266 with
                      | FStar_Syntax_Syntax.DECREASES uu____6267 -> false
                      | uu____6270 -> true))
               in
            let rc1 =
              let uu___140_6272 = rc  in
              let uu____6273 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (inline_closure_env cfg env [])
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___140_6272.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____6273;
                FStar_Syntax_Syntax.residual_flags = flags1
              }  in
            FStar_Pervasives_Native.Some rc1
        | uu____6282 -> lopt

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
    let uu____6395 =
      let uu____6404 = FStar_Syntax_Embeddings.e_list e  in
      FStar_Syntax_Embeddings.try_unembed uu____6404  in
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a) uu____6395  in
  let arg_as_bounded_int uu____6430 =
    match uu____6430 with
    | (a,uu____6442) ->
        let uu____6449 =
          let uu____6450 = FStar_Syntax_Subst.compress a  in
          uu____6450.FStar_Syntax_Syntax.n  in
        (match uu____6449 with
         | FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv1;
                FStar_Syntax_Syntax.pos = uu____6460;
                FStar_Syntax_Syntax.vars = uu____6461;_},({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_constant
                                                              (FStar_Const.Const_int
                                                              (i,FStar_Pervasives_Native.None
                                                               ));
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____6463;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____6464;_},uu____6465)::[])
             when
             let uu____6504 =
               FStar_Ident.text_of_lid
                 (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                in
             FStar_Util.ends_with uu____6504 "int_to_t" ->
             let uu____6505 =
               let uu____6510 = FStar_BigInt.big_int_of_string i  in
               (fv1, uu____6510)  in
             FStar_Pervasives_Native.Some uu____6505
         | uu____6515 -> FStar_Pervasives_Native.None)
     in
  let lift_unary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a)::[] ->
        let uu____6563 = f a  in FStar_Pervasives_Native.Some uu____6563
    | uu____6564 -> FStar_Pervasives_Native.None  in
  let lift_binary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a0)::(FStar_Pervasives_Native.Some
        a1)::[] ->
        let uu____6620 = f a0 a1  in FStar_Pervasives_Native.Some uu____6620
    | uu____6621 -> FStar_Pervasives_Native.None  in
  let unary_op as_a f res args =
    let uu____6679 = FStar_List.map as_a args  in
    lift_unary (f res.psc_range) uu____6679  in
  let binary_op as_a f res args =
    let uu____6744 = FStar_List.map as_a args  in
    lift_binary (f res.psc_range) uu____6744  in
  let as_primitive_step is_strong uu____6775 =
    match uu____6775 with
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
           let uu____6835 = f x  in
           FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_int r
             uu____6835)
     in
  let binary_int_op f =
    binary_op arg_as_int
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____6871 = f x y  in
             FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_int r
               uu____6871)
     in
  let unary_bool_op f =
    unary_op arg_as_bool
      (fun r  ->
         fun x  ->
           let uu____6900 = f x  in
           FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_bool r
             uu____6900)
     in
  let binary_bool_op f =
    binary_op arg_as_bool
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____6936 = f x y  in
             FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_bool r
               uu____6936)
     in
  let binary_string_op f =
    binary_op arg_as_string
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____6972 = f x y  in
             FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_string r
               uu____6972)
     in
  let mixed_binary_op as_a as_b embed_c f res args =
    match args with
    | a::b::[] ->
        let uu____7104 =
          let uu____7113 = as_a a  in
          let uu____7116 = as_b b  in (uu____7113, uu____7116)  in
        (match uu____7104 with
         | (FStar_Pervasives_Native.Some a1,FStar_Pervasives_Native.Some b1)
             ->
             let uu____7131 =
               let uu____7132 = f res.psc_range a1 b1  in
               embed_c res.psc_range uu____7132  in
             FStar_Pervasives_Native.Some uu____7131
         | uu____7133 -> FStar_Pervasives_Native.None)
    | uu____7142 -> FStar_Pervasives_Native.None  in
  let list_of_string' rng s =
    let name l =
      let uu____7162 =
        let uu____7163 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant
            FStar_Pervasives_Native.None
           in
        FStar_Syntax_Syntax.Tm_fvar uu____7163  in
      mk uu____7162 rng  in
    let char_t = name FStar_Parser_Const.char_lid  in
    let charterm c =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c)) rng  in
    let uu____7175 =
      let uu____7178 = FStar_String.list_of_string s  in
      FStar_List.map charterm uu____7178  in
    FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu____7175  in
  let string_of_list' rng l =
    let s = FStar_String.string_of_list l  in FStar_Syntax_Util.exp_string s
     in
  let string_compare' rng s1 s2 =
    let r = FStar_String.compare s1 s2  in
    let uu____7220 =
      let uu____7221 = FStar_Util.string_of_int r  in
      FStar_BigInt.big_int_of_string uu____7221  in
    FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_int rng
      uu____7220
     in
  let string_concat' psc args =
    match args with
    | a1::a2::[] ->
        let uu____7243 = arg_as_string a1  in
        (match uu____7243 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____7249 = arg_as_list FStar_Syntax_Embeddings.e_string a2
                in
             (match uu____7249 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2  in
                  let uu____7262 =
                    FStar_Syntax_Embeddings.embed
                      FStar_Syntax_Embeddings.e_string psc.psc_range r
                     in
                  FStar_Pervasives_Native.Some uu____7262
              | uu____7263 -> FStar_Pervasives_Native.None)
         | uu____7268 -> FStar_Pervasives_Native.None)
    | uu____7271 -> FStar_Pervasives_Native.None  in
  let string_of_int1 rng i =
    let uu____7285 = FStar_BigInt.string_of_big_int i  in
    FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_string rng
      uu____7285
     in
  let string_of_bool1 rng b =
    FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_string rng
      (if b then "true" else "false")
     in
  let mk_range1 psc args =
    match args with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____7322 =
          let uu____7343 = arg_as_string fn  in
          let uu____7346 = arg_as_int from_line  in
          let uu____7349 = arg_as_int from_col  in
          let uu____7352 = arg_as_int to_line  in
          let uu____7355 = arg_as_int to_col  in
          (uu____7343, uu____7346, uu____7349, uu____7352, uu____7355)  in
        (match uu____7322 with
         | (FStar_Pervasives_Native.Some fn1,FStar_Pervasives_Native.Some
            from_l,FStar_Pervasives_Native.Some
            from_c,FStar_Pervasives_Native.Some
            to_l,FStar_Pervasives_Native.Some to_c) ->
             let r =
               let uu____7386 =
                 let uu____7387 = FStar_BigInt.to_int_fs from_l  in
                 let uu____7388 = FStar_BigInt.to_int_fs from_c  in
                 FStar_Range.mk_pos uu____7387 uu____7388  in
               let uu____7389 =
                 let uu____7390 = FStar_BigInt.to_int_fs to_l  in
                 let uu____7391 = FStar_BigInt.to_int_fs to_c  in
                 FStar_Range.mk_pos uu____7390 uu____7391  in
               FStar_Range.mk_range fn1 uu____7386 uu____7389  in
             let uu____7392 =
               FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_range
                 psc.psc_range r
                in
             FStar_Pervasives_Native.Some uu____7392
         | uu____7393 -> FStar_Pervasives_Native.None)
    | uu____7414 -> FStar_Pervasives_Native.None  in
  let decidable_eq neg psc args =
    let r = psc.psc_range  in
    let tru =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool true)) r
       in
    let fal =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool false)) r
       in
    match args with
    | (_typ,uu____7447)::(a1,uu____7449)::(a2,uu____7451)::[] ->
        let uu____7488 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____7488 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some (if neg then fal else tru)
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some (if neg then tru else fal)
         | uu____7501 -> FStar_Pervasives_Native.None)
    | uu____7502 -> failwith "Unexpected number of arguments"  in
  let prims_to_fstar_range_step psc args =
    match args with
    | (a1,uu____7533)::[] ->
        let uu____7542 =
          FStar_Syntax_Embeddings.try_unembed FStar_Syntax_Embeddings.e_range
            a1
           in
        (match uu____7542 with
         | FStar_Pervasives_Native.Some r ->
             let uu____7548 =
               FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_range
                 psc.psc_range r
                in
             FStar_Pervasives_Native.Some uu____7548
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
    | uu____7549 -> failwith "Unexpected number of arguments"  in
  let basic_ops =
    let uu____7575 =
      let uu____7592 =
        let uu____7609 =
          let uu____7626 =
            let uu____7643 =
              let uu____7660 =
                let uu____7677 =
                  let uu____7694 =
                    let uu____7711 =
                      let uu____7728 =
                        let uu____7745 =
                          let uu____7762 =
                            let uu____7779 =
                              let uu____7796 =
                                let uu____7813 =
                                  let uu____7830 =
                                    let uu____7847 =
                                      let uu____7864 =
                                        let uu____7881 =
                                          let uu____7898 =
                                            let uu____7915 =
                                              let uu____7932 =
                                                let uu____7947 =
                                                  FStar_Parser_Const.p2l
                                                    ["FStar";
                                                    "String";
                                                    "list_of_string"]
                                                   in
                                                (uu____7947,
                                                  (Prims.parse_int "1"),
                                                  (unary_op arg_as_string
                                                     list_of_string'))
                                                 in
                                              let uu____7956 =
                                                let uu____7973 =
                                                  let uu____7988 =
                                                    FStar_Parser_Const.p2l
                                                      ["FStar";
                                                      "String";
                                                      "string_of_list"]
                                                     in
                                                  (uu____7988,
                                                    (Prims.parse_int "1"),
                                                    (unary_op
                                                       (arg_as_list
                                                          FStar_Syntax_Embeddings.e_char)
                                                       string_of_list'))
                                                   in
                                                let uu____8001 =
                                                  let uu____8018 =
                                                    let uu____8035 =
                                                      FStar_Parser_Const.p2l
                                                        ["FStar";
                                                        "String";
                                                        "concat"]
                                                       in
                                                    (uu____8035,
                                                      (Prims.parse_int "2"),
                                                      string_concat')
                                                     in
                                                  let uu____8046 =
                                                    let uu____8065 =
                                                      let uu____8082 =
                                                        FStar_Parser_Const.p2l
                                                          ["Prims";
                                                          "mk_range"]
                                                         in
                                                      (uu____8082,
                                                        (Prims.parse_int "5"),
                                                        mk_range1)
                                                       in
                                                    [uu____8065]  in
                                                  uu____8018 :: uu____8046
                                                   in
                                                uu____7973 :: uu____8001  in
                                              uu____7932 :: uu____7956  in
                                            (FStar_Parser_Const.op_notEq,
                                              (Prims.parse_int "3"),
                                              (decidable_eq true)) ::
                                              uu____7915
                                             in
                                          (FStar_Parser_Const.op_Eq,
                                            (Prims.parse_int "3"),
                                            (decidable_eq false)) ::
                                            uu____7898
                                           in
                                        (FStar_Parser_Const.string_compare,
                                          (Prims.parse_int "2"),
                                          (binary_op arg_as_string
                                             string_compare'))
                                          :: uu____7881
                                         in
                                      (FStar_Parser_Const.string_of_bool_lid,
                                        (Prims.parse_int "1"),
                                        (unary_op arg_as_bool string_of_bool1))
                                        :: uu____7864
                                       in
                                    (FStar_Parser_Const.string_of_int_lid,
                                      (Prims.parse_int "1"),
                                      (unary_op arg_as_int string_of_int1))
                                      :: uu____7847
                                     in
                                  (FStar_Parser_Const.str_make_lid,
                                    (Prims.parse_int "2"),
                                    (mixed_binary_op arg_as_int arg_as_char
                                       (FStar_Syntax_Embeddings.embed
                                          FStar_Syntax_Embeddings.e_string)
                                       (fun r  ->
                                          fun x  ->
                                            fun y  ->
                                              let uu____8310 =
                                                FStar_BigInt.to_int_fs x  in
                                              FStar_String.make uu____8310 y)))
                                    :: uu____7830
                                   in
                                (FStar_Parser_Const.strcat_lid',
                                  (Prims.parse_int "2"),
                                  (binary_string_op
                                     (fun x  -> fun y  -> Prims.strcat x y)))
                                  :: uu____7813
                                 in
                              (FStar_Parser_Const.strcat_lid,
                                (Prims.parse_int "2"),
                                (binary_string_op
                                   (fun x  -> fun y  -> Prims.strcat x y)))
                                :: uu____7796
                               in
                            (FStar_Parser_Const.op_Or, (Prims.parse_int "2"),
                              (binary_bool_op (fun x  -> fun y  -> x || y)))
                              :: uu____7779
                             in
                          (FStar_Parser_Const.op_And, (Prims.parse_int "2"),
                            (binary_bool_op (fun x  -> fun y  -> x && y))) ::
                            uu____7762
                           in
                        (FStar_Parser_Const.op_Negation,
                          (Prims.parse_int "1"),
                          (unary_bool_op (fun x  -> Prims.op_Negation x))) ::
                          uu____7745
                         in
                      (FStar_Parser_Const.op_Modulus, (Prims.parse_int "2"),
                        (binary_int_op
                           (fun x  -> fun y  -> FStar_BigInt.mod_big_int x y)))
                        :: uu____7728
                       in
                    (FStar_Parser_Const.op_GTE, (Prims.parse_int "2"),
                      (binary_op arg_as_int
                         (fun r  ->
                            fun x  ->
                              fun y  ->
                                let uu____8505 = FStar_BigInt.ge_big_int x y
                                   in
                                FStar_Syntax_Embeddings.embed
                                  FStar_Syntax_Embeddings.e_bool r uu____8505)))
                      :: uu____7711
                     in
                  (FStar_Parser_Const.op_GT, (Prims.parse_int "2"),
                    (binary_op arg_as_int
                       (fun r  ->
                          fun x  ->
                            fun y  ->
                              let uu____8535 = FStar_BigInt.gt_big_int x y
                                 in
                              FStar_Syntax_Embeddings.embed
                                FStar_Syntax_Embeddings.e_bool r uu____8535)))
                    :: uu____7694
                   in
                (FStar_Parser_Const.op_LTE, (Prims.parse_int "2"),
                  (binary_op arg_as_int
                     (fun r  ->
                        fun x  ->
                          fun y  ->
                            let uu____8565 = FStar_BigInt.le_big_int x y  in
                            FStar_Syntax_Embeddings.embed
                              FStar_Syntax_Embeddings.e_bool r uu____8565)))
                  :: uu____7677
                 in
              (FStar_Parser_Const.op_LT, (Prims.parse_int "2"),
                (binary_op arg_as_int
                   (fun r  ->
                      fun x  ->
                        fun y  ->
                          let uu____8595 = FStar_BigInt.lt_big_int x y  in
                          FStar_Syntax_Embeddings.embed
                            FStar_Syntax_Embeddings.e_bool r uu____8595)))
                :: uu____7660
               in
            (FStar_Parser_Const.op_Division, (Prims.parse_int "2"),
              (binary_int_op
                 (fun x  -> fun y  -> FStar_BigInt.div_big_int x y)))
              :: uu____7643
             in
          (FStar_Parser_Const.op_Multiply, (Prims.parse_int "2"),
            (binary_int_op
               (fun x  -> fun y  -> FStar_BigInt.mult_big_int x y)))
            :: uu____7626
           in
        (FStar_Parser_Const.op_Subtraction, (Prims.parse_int "2"),
          (binary_int_op (fun x  -> fun y  -> FStar_BigInt.sub_big_int x y)))
          :: uu____7609
         in
      (FStar_Parser_Const.op_Addition, (Prims.parse_int "2"),
        (binary_int_op (fun x  -> fun y  -> FStar_BigInt.add_big_int x y)))
        :: uu____7592
       in
    (FStar_Parser_Const.op_Minus, (Prims.parse_int "1"),
      (unary_int_op (fun x  -> FStar_BigInt.minus_big_int x))) :: uu____7575
     in
  let weak_ops =
    let uu____8756 =
      let uu____8777 =
        FStar_Parser_Const.p2l ["FStar"; "Range"; "prims_to_fstar_range"]  in
      (uu____8777, (Prims.parse_int "1"), prims_to_fstar_range_step)  in
    [uu____8756]  in
  let bounded_arith_ops =
    let bounded_signed_int_types = ["Int8"; "Int16"; "Int32"; "Int64"]  in
    let bounded_unsigned_int_types =
      ["UInt8"; "UInt16"; "UInt32"; "UInt64"; "UInt128"]  in
    let int_as_bounded r int_to_t1 n1 =
      let c =
        FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_int r n1  in
      let int_to_t2 = FStar_Syntax_Syntax.fv_to_tm int_to_t1  in
      let uu____8875 =
        let uu____8880 =
          let uu____8881 = FStar_Syntax_Syntax.as_arg c  in [uu____8881]  in
        FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____8880  in
      uu____8875 FStar_Pervasives_Native.None r  in
    let add_sub_mul_v =
      FStar_All.pipe_right
        (FStar_List.append bounded_signed_int_types
           bounded_unsigned_int_types)
        (FStar_List.collect
           (fun m  ->
              let uu____8937 =
                let uu____8952 = FStar_Parser_Const.p2l ["FStar"; m; "add"]
                   in
                (uu____8952, (Prims.parse_int "2"),
                  (binary_op arg_as_bounded_int
                     (fun r  ->
                        fun uu____8974  ->
                          fun uu____8975  ->
                            match (uu____8974, uu____8975) with
                            | ((int_to_t1,x),(uu____8994,y)) ->
                                let uu____9004 = FStar_BigInt.add_big_int x y
                                   in
                                int_as_bounded r int_to_t1 uu____9004)))
                 in
              let uu____9005 =
                let uu____9022 =
                  let uu____9037 = FStar_Parser_Const.p2l ["FStar"; m; "sub"]
                     in
                  (uu____9037, (Prims.parse_int "2"),
                    (binary_op arg_as_bounded_int
                       (fun r  ->
                          fun uu____9059  ->
                            fun uu____9060  ->
                              match (uu____9059, uu____9060) with
                              | ((int_to_t1,x),(uu____9079,y)) ->
                                  let uu____9089 =
                                    FStar_BigInt.sub_big_int x y  in
                                  int_as_bounded r int_to_t1 uu____9089)))
                   in
                let uu____9090 =
                  let uu____9107 =
                    let uu____9122 =
                      FStar_Parser_Const.p2l ["FStar"; m; "mul"]  in
                    (uu____9122, (Prims.parse_int "2"),
                      (binary_op arg_as_bounded_int
                         (fun r  ->
                            fun uu____9144  ->
                              fun uu____9145  ->
                                match (uu____9144, uu____9145) with
                                | ((int_to_t1,x),(uu____9164,y)) ->
                                    let uu____9174 =
                                      FStar_BigInt.mult_big_int x y  in
                                    int_as_bounded r int_to_t1 uu____9174)))
                     in
                  let uu____9175 =
                    let uu____9192 =
                      let uu____9207 =
                        FStar_Parser_Const.p2l ["FStar"; m; "v"]  in
                      (uu____9207, (Prims.parse_int "1"),
                        (unary_op arg_as_bounded_int
                           (fun r  ->
                              fun uu____9225  ->
                                match uu____9225 with
                                | (int_to_t1,x) ->
                                    FStar_Syntax_Embeddings.embed
                                      FStar_Syntax_Embeddings.e_int r x)))
                       in
                    [uu____9192]  in
                  uu____9107 :: uu____9175  in
                uu____9022 :: uu____9090  in
              uu____8937 :: uu____9005))
       in
    let div_mod_unsigned =
      FStar_All.pipe_right bounded_unsigned_int_types
        (FStar_List.collect
           (fun m  ->
              let uu____9355 =
                let uu____9370 = FStar_Parser_Const.p2l ["FStar"; m; "div"]
                   in
                (uu____9370, (Prims.parse_int "2"),
                  (binary_op arg_as_bounded_int
                     (fun r  ->
                        fun uu____9392  ->
                          fun uu____9393  ->
                            match (uu____9392, uu____9393) with
                            | ((int_to_t1,x),(uu____9412,y)) ->
                                let uu____9422 = FStar_BigInt.div_big_int x y
                                   in
                                int_as_bounded r int_to_t1 uu____9422)))
                 in
              let uu____9423 =
                let uu____9440 =
                  let uu____9455 = FStar_Parser_Const.p2l ["FStar"; m; "rem"]
                     in
                  (uu____9455, (Prims.parse_int "2"),
                    (binary_op arg_as_bounded_int
                       (fun r  ->
                          fun uu____9477  ->
                            fun uu____9478  ->
                              match (uu____9477, uu____9478) with
                              | ((int_to_t1,x),(uu____9497,y)) ->
                                  let uu____9507 =
                                    FStar_BigInt.mod_big_int x y  in
                                  int_as_bounded r int_to_t1 uu____9507)))
                   in
                [uu____9440]  in
              uu____9355 :: uu____9423))
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
    | (_typ,uu____9637)::(a1,uu____9639)::(a2,uu____9641)::[] ->
        let uu____9678 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____9678 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___141_9684 = FStar_Syntax_Util.t_true  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___141_9684.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___141_9684.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___142_9688 = FStar_Syntax_Util.t_false  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___142_9688.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___142_9688.FStar_Syntax_Syntax.vars)
                })
         | uu____9689 -> FStar_Pervasives_Native.None)
    | (_typ,uu____9691)::uu____9692::(a1,uu____9694)::(a2,uu____9696)::[] ->
        let uu____9745 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____9745 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___141_9751 = FStar_Syntax_Util.t_true  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___141_9751.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___141_9751.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___142_9755 = FStar_Syntax_Util.t_false  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___142_9755.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___142_9755.FStar_Syntax_Syntax.vars)
                })
         | uu____9756 -> FStar_Pervasives_Native.None)
    | uu____9757 -> failwith "Unexpected number of arguments"  in
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
    let uu____9811 = FStar_ST.op_Bang unembed_binder_knot  in
    match uu____9811 with
    | FStar_Pervasives_Native.Some e -> FStar_Syntax_Embeddings.unembed e t
    | FStar_Pervasives_Native.None  ->
        (FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos
           (FStar_Errors.Warning_UnembedBinderKnot,
             "unembed_binder_knot is unset!");
         FStar_Pervasives_Native.None)
  
let mk_psc_subst :
  'Auu____9863 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____9863) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_Syntax_Syntax.subst_elt Prims.list
  =
  fun cfg  ->
    fun env  ->
      FStar_List.fold_right
        (fun uu____9925  ->
           fun subst1  ->
             match uu____9925 with
             | (binder_opt,closure) ->
                 (match (binder_opt, closure) with
                  | (FStar_Pervasives_Native.Some b,Clos
                     (env1,term,uu____9966,uu____9967)) ->
                      let uu____10026 = b  in
                      (match uu____10026 with
                       | (bv,uu____10034) ->
                           let uu____10035 =
                             let uu____10036 =
                               FStar_Syntax_Util.is_constructed_typ
                                 bv.FStar_Syntax_Syntax.sort
                                 FStar_Parser_Const.binder_lid
                                in
                             Prims.op_Negation uu____10036  in
                           if uu____10035
                           then subst1
                           else
                             (let term1 = closure_as_term cfg env1 term  in
                              let uu____10041 = unembed_binder term1  in
                              match uu____10041 with
                              | FStar_Pervasives_Native.None  -> subst1
                              | FStar_Pervasives_Native.Some x ->
                                  let b1 =
                                    let uu____10048 =
                                      let uu___143_10049 = bv  in
                                      let uu____10050 =
                                        FStar_Syntax_Subst.subst subst1
                                          (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort
                                         in
                                      {
                                        FStar_Syntax_Syntax.ppname =
                                          (uu___143_10049.FStar_Syntax_Syntax.ppname);
                                        FStar_Syntax_Syntax.index =
                                          (uu___143_10049.FStar_Syntax_Syntax.index);
                                        FStar_Syntax_Syntax.sort =
                                          uu____10050
                                      }  in
                                    FStar_Syntax_Syntax.freshen_bv
                                      uu____10048
                                     in
                                  let b_for_x =
                                    let uu____10054 =
                                      let uu____10061 =
                                        FStar_Syntax_Syntax.bv_to_name b1  in
                                      ((FStar_Pervasives_Native.fst x),
                                        uu____10061)
                                       in
                                    FStar_Syntax_Syntax.NT uu____10054  in
                                  let subst2 =
                                    FStar_List.filter
                                      (fun uu___85_10071  ->
                                         match uu___85_10071 with
                                         | FStar_Syntax_Syntax.NT
                                             (uu____10072,{
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_name
                                                              b';
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____10074;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____10075;_})
                                             ->
                                             let uu____10080 =
                                               FStar_Ident.ident_equals
                                                 b1.FStar_Syntax_Syntax.ppname
                                                 b'.FStar_Syntax_Syntax.ppname
                                                in
                                             Prims.op_Negation uu____10080
                                         | uu____10081 -> true) subst1
                                     in
                                  b_for_x :: subst2))
                  | uu____10082 -> subst1)) env []
  
let reduce_primops :
  'Auu____10105 'Auu____10106 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____10105) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____10106 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          if Prims.op_Negation (cfg.steps).primops
          then tm
          else
            (let uu____10152 = FStar_Syntax_Util.head_and_args tm  in
             match uu____10152 with
             | (head1,args) ->
                 let uu____10189 =
                   let uu____10190 = FStar_Syntax_Util.un_uinst head1  in
                   uu____10190.FStar_Syntax_Syntax.n  in
                 (match uu____10189 with
                  | FStar_Syntax_Syntax.Tm_fvar fv ->
                      let uu____10194 = find_prim_step cfg fv  in
                      (match uu____10194 with
                       | FStar_Pervasives_Native.Some prim_step when
                           prim_step.strong_reduction_ok ||
                             (Prims.op_Negation cfg.strong)
                           ->
                           let l = FStar_List.length args  in
                           if l < prim_step.arity
                           then
                             (log_primops cfg
                                (fun uu____10216  ->
                                   let uu____10217 =
                                     FStar_Syntax_Print.lid_to_string
                                       prim_step.name
                                      in
                                   let uu____10218 =
                                     FStar_Util.string_of_int l  in
                                   let uu____10225 =
                                     FStar_Util.string_of_int prim_step.arity
                                      in
                                   FStar_Util.print3
                                     "primop: found partially applied %s (%s/%s args)\n"
                                     uu____10217 uu____10218 uu____10225);
                              tm)
                           else
                             (let uu____10227 =
                                if l = prim_step.arity
                                then (args, [])
                                else FStar_List.splitAt prim_step.arity args
                                 in
                              match uu____10227 with
                              | (args_1,args_2) ->
                                  (log_primops cfg
                                     (fun uu____10338  ->
                                        let uu____10339 =
                                          FStar_Syntax_Print.term_to_string
                                            tm
                                           in
                                        FStar_Util.print1
                                          "primop: trying to reduce <%s>\n"
                                          uu____10339);
                                   (let psc =
                                      {
                                        psc_range =
                                          (head1.FStar_Syntax_Syntax.pos);
                                        psc_subst =
                                          (fun uu____10342  ->
                                             if
                                               prim_step.requires_binder_substitution
                                             then mk_psc_subst cfg env
                                             else [])
                                      }  in
                                    let uu____10344 =
                                      prim_step.interpretation psc args_1  in
                                    match uu____10344 with
                                    | FStar_Pervasives_Native.None  ->
                                        (log_primops cfg
                                           (fun uu____10350  ->
                                              let uu____10351 =
                                                FStar_Syntax_Print.term_to_string
                                                  tm
                                                 in
                                              FStar_Util.print1
                                                "primop: <%s> did not reduce\n"
                                                uu____10351);
                                         tm)
                                    | FStar_Pervasives_Native.Some reduced ->
                                        (log_primops cfg
                                           (fun uu____10357  ->
                                              let uu____10358 =
                                                FStar_Syntax_Print.term_to_string
                                                  tm
                                                 in
                                              let uu____10359 =
                                                FStar_Syntax_Print.term_to_string
                                                  reduced
                                                 in
                                              FStar_Util.print2
                                                "primop: <%s> reduced to <%s>\n"
                                                uu____10358 uu____10359);
                                         FStar_Syntax_Util.mk_app reduced
                                           args_2))))
                       | FStar_Pervasives_Native.Some uu____10360 ->
                           (log_primops cfg
                              (fun uu____10364  ->
                                 let uu____10365 =
                                   FStar_Syntax_Print.term_to_string tm  in
                                 FStar_Util.print1
                                   "primop: not reducing <%s> since we're doing strong reduction\n"
                                   uu____10365);
                            tm)
                       | FStar_Pervasives_Native.None  -> tm)
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_range_of ) when
                      Prims.op_Negation cfg.strong ->
                      (log_primops cfg
                         (fun uu____10369  ->
                            let uu____10370 =
                              FStar_Syntax_Print.term_to_string tm  in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____10370);
                       (match args with
                        | (a1,uu____10372)::[] ->
                            FStar_Syntax_Embeddings.embed
                              FStar_Syntax_Embeddings.e_range
                              tm.FStar_Syntax_Syntax.pos
                              a1.FStar_Syntax_Syntax.pos
                        | uu____10389 -> tm))
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_set_range_of ) when
                      Prims.op_Negation cfg.strong ->
                      (log_primops cfg
                         (fun uu____10401  ->
                            let uu____10402 =
                              FStar_Syntax_Print.term_to_string tm  in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____10402);
                       (match args with
                        | (t,uu____10404)::(r,uu____10406)::[] ->
                            let uu____10433 =
                              FStar_Syntax_Embeddings.unembed
                                FStar_Syntax_Embeddings.e_range r
                               in
                            (match uu____10433 with
                             | FStar_Pervasives_Native.Some rng ->
                                 let uu___144_10437 = t  in
                                 {
                                   FStar_Syntax_Syntax.n =
                                     (uu___144_10437.FStar_Syntax_Syntax.n);
                                   FStar_Syntax_Syntax.pos = rng;
                                   FStar_Syntax_Syntax.vars =
                                     (uu___144_10437.FStar_Syntax_Syntax.vars)
                                 }
                             | FStar_Pervasives_Native.None  -> tm)
                        | uu____10440 -> tm))
                  | uu____10449 -> tm))
  
let reduce_equality :
  'Auu____10460 'Auu____10461 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____10460) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____10461 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun tm  ->
      reduce_primops
        (let uu___145_10505 = cfg  in
         {
           steps =
             (let uu___146_10508 = default_steps  in
              {
                beta = (uu___146_10508.beta);
                iota = (uu___146_10508.iota);
                zeta = (uu___146_10508.zeta);
                weak = (uu___146_10508.weak);
                hnf = (uu___146_10508.hnf);
                primops = true;
                do_not_unfold_pure_lets =
                  (uu___146_10508.do_not_unfold_pure_lets);
                unfold_until = (uu___146_10508.unfold_until);
                unfold_only = (uu___146_10508.unfold_only);
                unfold_fully = (uu___146_10508.unfold_fully);
                unfold_attr = (uu___146_10508.unfold_attr);
                unfold_tac = (uu___146_10508.unfold_tac);
                pure_subterms_within_computations =
                  (uu___146_10508.pure_subterms_within_computations);
                simplify = (uu___146_10508.simplify);
                erase_universes = (uu___146_10508.erase_universes);
                allow_unbound_universes =
                  (uu___146_10508.allow_unbound_universes);
                reify_ = (uu___146_10508.reify_);
                compress_uvars = (uu___146_10508.compress_uvars);
                no_full_norm = (uu___146_10508.no_full_norm);
                check_no_uvars = (uu___146_10508.check_no_uvars);
                unmeta = (uu___146_10508.unmeta);
                unascribe = (uu___146_10508.unascribe);
                in_full_norm_request = (uu___146_10508.in_full_norm_request)
              });
           tcenv = (uu___145_10505.tcenv);
           debug = (uu___145_10505.debug);
           delta_level = (uu___145_10505.delta_level);
           primitive_steps = equality_ops;
           strong = (uu___145_10505.strong);
           memoize_lazy = (uu___145_10505.memoize_lazy);
           normalize_pure_lets = (uu___145_10505.normalize_pure_lets)
         }) tm
  
let is_norm_request :
  'Auu____10515 .
    FStar_Syntax_Syntax.term -> 'Auu____10515 Prims.list -> Prims.bool
  =
  fun hd1  ->
    fun args  ->
      let uu____10530 =
        let uu____10537 =
          let uu____10538 = FStar_Syntax_Util.un_uinst hd1  in
          uu____10538.FStar_Syntax_Syntax.n  in
        (uu____10537, args)  in
      match uu____10530 with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____10544::uu____10545::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____10549::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize
      | (FStar_Syntax_Syntax.Tm_fvar fv,steps::uu____10554::uu____10555::[])
          -> FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm
      | uu____10558 -> false
  
let (tr_norm_step : FStar_Syntax_Embeddings.norm_step -> step Prims.list) =
  fun uu___86_10571  ->
    match uu___86_10571 with
    | FStar_Syntax_Embeddings.Zeta  -> [Zeta]
    | FStar_Syntax_Embeddings.Iota  -> [Iota]
    | FStar_Syntax_Embeddings.Delta  ->
        [UnfoldUntil FStar_Syntax_Syntax.Delta_constant]
    | FStar_Syntax_Embeddings.Simpl  -> [Simplify]
    | FStar_Syntax_Embeddings.Weak  -> [Weak]
    | FStar_Syntax_Embeddings.HNF  -> [HNF]
    | FStar_Syntax_Embeddings.Primops  -> [Primops]
    | FStar_Syntax_Embeddings.UnfoldOnly names1 ->
        let uu____10577 =
          let uu____10580 =
            let uu____10581 = FStar_List.map FStar_Ident.lid_of_str names1
               in
            UnfoldOnly uu____10581  in
          [uu____10580]  in
        (UnfoldUntil FStar_Syntax_Syntax.Delta_constant) :: uu____10577
    | FStar_Syntax_Embeddings.UnfoldFully names1 ->
        let uu____10587 =
          let uu____10590 =
            let uu____10591 = FStar_List.map FStar_Ident.lid_of_str names1
               in
            UnfoldFully uu____10591  in
          [uu____10590]  in
        (UnfoldUntil FStar_Syntax_Syntax.Delta_constant) :: uu____10587
    | FStar_Syntax_Embeddings.UnfoldAttr t ->
        [UnfoldUntil FStar_Syntax_Syntax.Delta_constant; UnfoldAttr t]
  
let (tr_norm_steps :
  FStar_Syntax_Embeddings.norm_step Prims.list -> step Prims.list) =
  fun s  -> FStar_List.concatMap tr_norm_step s 
let get_norm_request :
  'Auu____10612 .
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
      (FStar_Syntax_Syntax.term,'Auu____10612) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (step Prims.list,FStar_Syntax_Syntax.term)
          FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun full_norm  ->
    fun args  ->
      let parse_steps s =
        let uu____10658 =
          let uu____10663 =
            FStar_Syntax_Embeddings.e_list
              FStar_Syntax_Embeddings.e_norm_step
             in
          FStar_Syntax_Embeddings.try_unembed uu____10663 s  in
        match uu____10658 with
        | FStar_Pervasives_Native.Some steps ->
            let uu____10679 = tr_norm_steps steps  in
            FStar_Pervasives_Native.Some uu____10679
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None  in
      match args with
      | uu____10696::(tm,uu____10698)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify]  in
          FStar_Pervasives_Native.Some (s, tm)
      | (tm,uu____10727)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify]  in
          FStar_Pervasives_Native.Some (s, tm)
      | (steps,uu____10748)::uu____10749::(tm,uu____10751)::[] ->
          let add_exclude s z =
            if FStar_List.contains z s then s else (Exclude z) :: s  in
          let uu____10792 =
            let uu____10797 = full_norm steps  in parse_steps uu____10797  in
          (match uu____10792 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some s ->
               let s1 = Beta :: s  in
               let s2 = add_exclude s1 Zeta  in
               let s3 = add_exclude s2 Iota  in
               FStar_Pervasives_Native.Some (s3, tm))
      | uu____10836 -> FStar_Pervasives_Native.None
  
let (is_reify_head : stack_elt Prims.list -> Prims.bool) =
  fun uu___87_10855  ->
    match uu___87_10855 with
    | (App
        (uu____10858,{
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reify );
                       FStar_Syntax_Syntax.pos = uu____10859;
                       FStar_Syntax_Syntax.vars = uu____10860;_},uu____10861,uu____10862))::uu____10863
        -> true
    | uu____10870 -> false
  
let firstn :
  'Auu____10879 .
    Prims.int ->
      'Auu____10879 Prims.list ->
        ('Auu____10879 Prims.list,'Auu____10879 Prims.list)
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
          (uu____10921,{
                         FStar_Syntax_Syntax.n =
                           FStar_Syntax_Syntax.Tm_constant
                           (FStar_Const.Const_reify );
                         FStar_Syntax_Syntax.pos = uu____10922;
                         FStar_Syntax_Syntax.vars = uu____10923;_},uu____10924,uu____10925))::uu____10926
          -> (cfg.steps).reify_
      | uu____10933 -> false
  
let rec (maybe_weakly_reduced :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun tm  ->
    let aux_comp c =
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.GTotal (t,uu____10956) -> maybe_weakly_reduced t
      | FStar_Syntax_Syntax.Total (t,uu____10966) -> maybe_weakly_reduced t
      | FStar_Syntax_Syntax.Comp ct ->
          (maybe_weakly_reduced ct.FStar_Syntax_Syntax.result_typ) ||
            (FStar_Util.for_some
               (fun uu____10985  ->
                  match uu____10985 with
                  | (a,uu____10993) -> maybe_weakly_reduced a)
               ct.FStar_Syntax_Syntax.effect_args)
       in
    let t = FStar_Syntax_Subst.compress tm  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____10999 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_name uu____11024 -> false
    | FStar_Syntax_Syntax.Tm_uvar uu____11025 -> false
    | FStar_Syntax_Syntax.Tm_type uu____11042 -> false
    | FStar_Syntax_Syntax.Tm_bvar uu____11043 -> false
    | FStar_Syntax_Syntax.Tm_fvar uu____11044 -> false
    | FStar_Syntax_Syntax.Tm_constant uu____11045 -> false
    | FStar_Syntax_Syntax.Tm_lazy uu____11046 -> false
    | FStar_Syntax_Syntax.Tm_unknown  -> false
    | FStar_Syntax_Syntax.Tm_uinst uu____11047 -> false
    | FStar_Syntax_Syntax.Tm_quoted uu____11054 -> false
    | FStar_Syntax_Syntax.Tm_let uu____11061 -> true
    | FStar_Syntax_Syntax.Tm_abs uu____11074 -> true
    | FStar_Syntax_Syntax.Tm_arrow uu____11091 -> true
    | FStar_Syntax_Syntax.Tm_refine uu____11104 -> true
    | FStar_Syntax_Syntax.Tm_app (t1,args) ->
        (maybe_weakly_reduced t1) ||
          (FStar_All.pipe_right args
             (FStar_Util.for_some
                (fun uu____11150  ->
                   match uu____11150 with
                   | (a,uu____11158) -> maybe_weakly_reduced a)))
    | FStar_Syntax_Syntax.Tm_match (t1,pats) ->
        (maybe_weakly_reduced t1) ||
          (FStar_All.pipe_right pats
             (FStar_Util.for_some
                (fun uu____11235  ->
                   match uu____11235 with
                   | (uu____11250,wopt,t2) ->
                       (match wopt with
                        | FStar_Pervasives_Native.None  -> false
                        | FStar_Pervasives_Native.Some t3 ->
                            maybe_weakly_reduced t3)
                         || (maybe_weakly_reduced t2))))
    | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,uu____11278) ->
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
                     (fun uu____11400  ->
                        match uu____11400 with
                        | (a,uu____11408) -> maybe_weakly_reduced a)) args
            | FStar_Syntax_Syntax.Meta_monadic_lift
                (uu____11413,uu____11414,t') -> maybe_weakly_reduced t'
            | FStar_Syntax_Syntax.Meta_monadic (uu____11420,t') ->
                maybe_weakly_reduced t'
            | FStar_Syntax_Syntax.Meta_labeled uu____11426 -> false
            | FStar_Syntax_Syntax.Meta_desugared uu____11433 -> false
            | FStar_Syntax_Syntax.Meta_named uu____11434 -> false))
  
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
               | FStar_Syntax_Syntax.Tm_delayed uu____11726 ->
                   let uu____11751 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print1 "NORM delayed: %s\n" uu____11751
               | uu____11752 -> ())
            else ();
            FStar_Syntax_Subst.compress t  in
          log cfg
            (fun uu____11760  ->
               let uu____11761 = FStar_Syntax_Print.tag_of_term t1  in
               let uu____11762 = FStar_Syntax_Print.term_to_string t1  in
               let uu____11763 =
                 FStar_Util.string_of_int (FStar_List.length env)  in
               let uu____11770 =
                 let uu____11771 =
                   let uu____11774 = firstn (Prims.parse_int "4") stack  in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____11774
                    in
                 stack_to_string uu____11771  in
               FStar_Util.print4
                 ">>> %s\nNorm %s with with %s env elements top of the stack %s \n"
                 uu____11761 uu____11762 uu____11763 uu____11770);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_constant uu____11797 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_name uu____11798 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_lazy uu____11799 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____11800;
                 FStar_Syntax_Syntax.fv_delta =
                   FStar_Syntax_Syntax.Delta_constant ;
                 FStar_Syntax_Syntax.fv_qual = uu____11801;_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____11804;
                 FStar_Syntax_Syntax.fv_delta = uu____11805;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Data_ctor );_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____11806;
                 FStar_Syntax_Syntax.fv_delta = uu____11807;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor uu____11808);_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_quoted uu____11815 ->
               let uu____11822 = closure_as_term cfg env t1  in
               rebuild cfg env stack uu____11822
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               ((Prims.op_Negation (cfg.steps).no_full_norm) &&
                  (is_norm_request hd1 args))
                 &&
                 (let uu____11852 =
                    FStar_Ident.lid_equals
                      (cfg.tcenv).FStar_TypeChecker_Env.curmodule
                      FStar_Parser_Const.prims_lid
                     in
                  Prims.op_Negation uu____11852)
               ->
               let cfg' =
                 let uu___147_11854 = cfg  in
                 {
                   steps =
                     (let uu___148_11857 = cfg.steps  in
                      {
                        beta = (uu___148_11857.beta);
                        iota = (uu___148_11857.iota);
                        zeta = (uu___148_11857.zeta);
                        weak = (uu___148_11857.weak);
                        hnf = (uu___148_11857.hnf);
                        primops = (uu___148_11857.primops);
                        do_not_unfold_pure_lets = false;
                        unfold_until = (uu___148_11857.unfold_until);
                        unfold_only = FStar_Pervasives_Native.None;
                        unfold_fully = FStar_Pervasives_Native.None;
                        unfold_attr = (uu___148_11857.unfold_attr);
                        unfold_tac = (uu___148_11857.unfold_tac);
                        pure_subterms_within_computations =
                          (uu___148_11857.pure_subterms_within_computations);
                        simplify = (uu___148_11857.simplify);
                        erase_universes = (uu___148_11857.erase_universes);
                        allow_unbound_universes =
                          (uu___148_11857.allow_unbound_universes);
                        reify_ = (uu___148_11857.reify_);
                        compress_uvars = (uu___148_11857.compress_uvars);
                        no_full_norm = (uu___148_11857.no_full_norm);
                        check_no_uvars = (uu___148_11857.check_no_uvars);
                        unmeta = (uu___148_11857.unmeta);
                        unascribe = (uu___148_11857.unascribe);
                        in_full_norm_request =
                          (uu___148_11857.in_full_norm_request)
                      });
                   tcenv = (uu___147_11854.tcenv);
                   debug = (uu___147_11854.debug);
                   delta_level =
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.Delta_constant];
                   primitive_steps = (uu___147_11854.primitive_steps);
                   strong = (uu___147_11854.strong);
                   memoize_lazy = (uu___147_11854.memoize_lazy);
                   normalize_pure_lets = true
                 }  in
               let uu____11862 = get_norm_request (norm cfg' env []) args  in
               (match uu____11862 with
                | FStar_Pervasives_Native.None  ->
                    let stack1 =
                      FStar_All.pipe_right stack
                        (FStar_List.fold_right
                           (fun uu____11893  ->
                              fun stack1  ->
                                match uu____11893 with
                                | (a,aq) ->
                                    let uu____11905 =
                                      let uu____11906 =
                                        let uu____11913 =
                                          let uu____11914 =
                                            let uu____11945 =
                                              FStar_Util.mk_ref
                                                FStar_Pervasives_Native.None
                                               in
                                            (env, a, uu____11945, false)  in
                                          Clos uu____11914  in
                                        (uu____11913, aq,
                                          (t1.FStar_Syntax_Syntax.pos))
                                         in
                                      Arg uu____11906  in
                                    uu____11905 :: stack1) args)
                       in
                    (log cfg
                       (fun uu____12029  ->
                          let uu____12030 =
                            FStar_All.pipe_left FStar_Util.string_of_int
                              (FStar_List.length args)
                             in
                          FStar_Util.print1 "\tPushed %s arguments\n"
                            uu____12030);
                     norm cfg env stack1 hd1)
                | FStar_Pervasives_Native.Some (s,tm) ->
                    let delta_level =
                      let uu____12052 =
                        FStar_All.pipe_right s
                          (FStar_Util.for_some
                             (fun uu___88_12057  ->
                                match uu___88_12057 with
                                | UnfoldUntil uu____12058 -> true
                                | UnfoldOnly uu____12059 -> true
                                | UnfoldFully uu____12062 -> true
                                | uu____12065 -> false))
                         in
                      if uu____12052
                      then
                        [FStar_TypeChecker_Env.Unfold
                           FStar_Syntax_Syntax.Delta_constant]
                      else [FStar_TypeChecker_Env.NoDelta]  in
                    let cfg'1 =
                      let uu___149_12070 = cfg  in
                      let uu____12071 =
                        let uu___150_12072 = to_fsteps s  in
                        {
                          beta = (uu___150_12072.beta);
                          iota = (uu___150_12072.iota);
                          zeta = (uu___150_12072.zeta);
                          weak = (uu___150_12072.weak);
                          hnf = (uu___150_12072.hnf);
                          primops = (uu___150_12072.primops);
                          do_not_unfold_pure_lets =
                            (uu___150_12072.do_not_unfold_pure_lets);
                          unfold_until = (uu___150_12072.unfold_until);
                          unfold_only = (uu___150_12072.unfold_only);
                          unfold_fully = (uu___150_12072.unfold_fully);
                          unfold_attr = (uu___150_12072.unfold_attr);
                          unfold_tac = (uu___150_12072.unfold_tac);
                          pure_subterms_within_computations =
                            (uu___150_12072.pure_subterms_within_computations);
                          simplify = (uu___150_12072.simplify);
                          erase_universes = (uu___150_12072.erase_universes);
                          allow_unbound_universes =
                            (uu___150_12072.allow_unbound_universes);
                          reify_ = (uu___150_12072.reify_);
                          compress_uvars = (uu___150_12072.compress_uvars);
                          no_full_norm = (uu___150_12072.no_full_norm);
                          check_no_uvars = (uu___150_12072.check_no_uvars);
                          unmeta = (uu___150_12072.unmeta);
                          unascribe = (uu___150_12072.unascribe);
                          in_full_norm_request = true
                        }  in
                      {
                        steps = uu____12071;
                        tcenv = (uu___149_12070.tcenv);
                        debug = (uu___149_12070.debug);
                        delta_level;
                        primitive_steps = (uu___149_12070.primitive_steps);
                        strong = (uu___149_12070.strong);
                        memoize_lazy = (uu___149_12070.memoize_lazy);
                        normalize_pure_lets = true
                      }  in
                    let stack' =
                      let tail1 = (Cfg cfg) :: stack  in
                      if (cfg.debug).print_normalized
                      then
                        let uu____12081 =
                          let uu____12082 =
                            let uu____12087 = FStar_Util.now ()  in
                            (t1, uu____12087)  in
                          Debug uu____12082  in
                        uu____12081 :: tail1
                      else tail1  in
                    norm cfg'1 env stack' tm)
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u  in
               let uu____12091 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack uu____12091
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               if (cfg.steps).erase_universes
               then norm cfg env stack t'
               else
                 (let us1 =
                    let uu____12100 =
                      let uu____12107 =
                        FStar_List.map (norm_universe cfg env) us  in
                      (uu____12107, (t1.FStar_Syntax_Syntax.pos))  in
                    UnivArgs uu____12100  in
                  let stack1 = us1 :: stack  in norm cfg env stack1 t')
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let qninfo =
                 let uu____12117 = FStar_Syntax_Syntax.lid_of_fv fv  in
                 FStar_TypeChecker_Env.lookup_qname cfg.tcenv uu____12117  in
               let uu____12118 =
                 FStar_TypeChecker_Env.qninfo_is_action qninfo  in
               if uu____12118
               then
                 let b = should_reify cfg stack  in
                 (log cfg
                    (fun uu____12124  ->
                       let uu____12125 = FStar_Syntax_Print.term_to_string t1
                          in
                       let uu____12126 = FStar_Util.string_of_bool b  in
                       FStar_Util.print2
                         ">>> For DM4F action %s, should_reify = %s\n"
                         uu____12125 uu____12126);
                  if b
                  then
                    (let uu____12127 = FStar_List.tl stack  in
                     do_unfold_fv cfg env uu____12127 t1 qninfo fv)
                  else rebuild cfg env stack t1)
               else
                 (let should_delta =
                    ((let uu____12135 = find_prim_step cfg fv  in
                      FStar_Option.isNone uu____12135) &&
                       (match qninfo with
                        | FStar_Pervasives_Native.Some
                            (FStar_Util.Inr
                             ({
                                FStar_Syntax_Syntax.sigel =
                                  FStar_Syntax_Syntax.Sig_let
                                  ((is_rec,uu____12148),uu____12149);
                                FStar_Syntax_Syntax.sigrng = uu____12150;
                                FStar_Syntax_Syntax.sigquals = qs;
                                FStar_Syntax_Syntax.sigmeta = uu____12152;
                                FStar_Syntax_Syntax.sigattrs = uu____12153;_},uu____12154),uu____12155)
                            ->
                            (Prims.op_Negation
                               (FStar_List.contains
                                  FStar_Syntax_Syntax.HasMaskedEffect qs))
                              &&
                              ((Prims.op_Negation is_rec) || (cfg.steps).zeta)
                        | uu____12220 -> true))
                      &&
                      (FStar_All.pipe_right cfg.delta_level
                         (FStar_Util.for_some
                            (fun uu___89_12224  ->
                               match uu___89_12224 with
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
                          (let uu____12234 =
                             cases
                               (FStar_Util.for_some
                                  (FStar_Syntax_Util.attr_eq
                                     FStar_Syntax_Util.tac_opaque_attr))
                               false attrs
                              in
                           Prims.op_Negation uu____12234))
                         &&
                         ((match (cfg.steps).unfold_only with
                           | FStar_Pervasives_Native.None  -> true
                           | FStar_Pervasives_Native.Some lids ->
                               FStar_Util.for_some
                                 (FStar_Syntax_Syntax.fv_eq_lid fv) lids)
                            ||
                            (match (attrs, ((cfg.steps).unfold_attr)) with
                             | (FStar_Pervasives_Native.None
                                ,FStar_Pervasives_Native.Some uu____12253) ->
                                 false
                             | (FStar_Pervasives_Native.Some
                                ats,FStar_Pervasives_Native.Some ats') ->
                                 FStar_Util.for_some
                                   (fun at  ->
                                      FStar_Util.for_some
                                        (FStar_Syntax_Util.attr_eq at) ats')
                                   ats
                             | (uu____12288,uu____12289) -> false)))
                     in
                  let uu____12306 =
                    match (cfg.steps).unfold_fully with
                    | FStar_Pervasives_Native.None  -> (should_delta1, false)
                    | FStar_Pervasives_Native.Some lids ->
                        let uu____12322 =
                          FStar_Util.for_some
                            (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                           in
                        if uu____12322 then (true, true) else (false, false)
                     in
                  match uu____12306 with
                  | (should_delta2,fully) ->
                      (log cfg
                         (fun uu____12335  ->
                            let uu____12336 =
                              FStar_Syntax_Print.term_to_string t1  in
                            let uu____12337 =
                              FStar_Range.string_of_range
                                t1.FStar_Syntax_Syntax.pos
                               in
                            let uu____12338 =
                              FStar_Util.string_of_bool should_delta2  in
                            FStar_Util.print3
                              ">>> For %s (%s), should_delta = %s\n"
                              uu____12336 uu____12337 uu____12338);
                       if should_delta2
                       then
                         (let uu____12339 =
                            if fully
                            then
                              (((Cfg cfg) :: stack),
                                (let uu___151_12355 = cfg  in
                                 {
                                   steps =
                                     (let uu___152_12358 = cfg.steps  in
                                      {
                                        beta = (uu___152_12358.beta);
                                        iota = false;
                                        zeta = false;
                                        weak = false;
                                        hnf = false;
                                        primops = false;
                                        do_not_unfold_pure_lets =
                                          (uu___152_12358.do_not_unfold_pure_lets);
                                        unfold_until =
                                          (FStar_Pervasives_Native.Some
                                             FStar_Syntax_Syntax.Delta_constant);
                                        unfold_only =
                                          FStar_Pervasives_Native.None;
                                        unfold_fully =
                                          FStar_Pervasives_Native.None;
                                        unfold_attr =
                                          (uu___152_12358.unfold_attr);
                                        unfold_tac =
                                          (uu___152_12358.unfold_tac);
                                        pure_subterms_within_computations =
                                          (uu___152_12358.pure_subterms_within_computations);
                                        simplify = false;
                                        erase_universes =
                                          (uu___152_12358.erase_universes);
                                        allow_unbound_universes =
                                          (uu___152_12358.allow_unbound_universes);
                                        reify_ = (uu___152_12358.reify_);
                                        compress_uvars =
                                          (uu___152_12358.compress_uvars);
                                        no_full_norm =
                                          (uu___152_12358.no_full_norm);
                                        check_no_uvars =
                                          (uu___152_12358.check_no_uvars);
                                        unmeta = (uu___152_12358.unmeta);
                                        unascribe =
                                          (uu___152_12358.unascribe);
                                        in_full_norm_request =
                                          (uu___152_12358.in_full_norm_request)
                                      });
                                   tcenv = (uu___151_12355.tcenv);
                                   debug = (uu___151_12355.debug);
                                   delta_level = (uu___151_12355.delta_level);
                                   primitive_steps =
                                     (uu___151_12355.primitive_steps);
                                   strong = (uu___151_12355.strong);
                                   memoize_lazy =
                                     (uu___151_12355.memoize_lazy);
                                   normalize_pure_lets =
                                     (uu___151_12355.normalize_pure_lets)
                                 }))
                            else (stack, cfg)  in
                          match uu____12339 with
                          | (stack1,cfg1) ->
                              do_unfold_fv cfg1 env stack1 t1 qninfo fv)
                       else rebuild cfg env stack t1))
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____12372 = lookup_bvar env x  in
               (match uu____12372 with
                | Univ uu____12373 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if (Prims.op_Negation fix) || (cfg.steps).zeta
                    then
                      let uu____12422 = FStar_ST.op_Bang r  in
                      (match uu____12422 with
                       | FStar_Pervasives_Native.Some (env2,t') ->
                           (log cfg
                              (fun uu____12544  ->
                                 let uu____12545 =
                                   FStar_Syntax_Print.term_to_string t1  in
                                 let uu____12546 =
                                   FStar_Syntax_Print.term_to_string t'  in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____12545
                                   uu____12546);
                            (let uu____12547 = maybe_weakly_reduced t'  in
                             if uu____12547
                             then
                               match stack with
                               | [] when
                                   (cfg.steps).weak ||
                                     (cfg.steps).compress_uvars
                                   -> rebuild cfg env2 stack t'
                               | uu____12548 -> norm cfg env2 stack t'
                             else rebuild cfg env2 stack t'))
                       | FStar_Pervasives_Native.None  ->
                           norm cfg env1 ((MemoLazy r) :: stack) t0)
                    else norm cfg env1 stack t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack with
                | (UnivArgs uu____12619)::uu____12620 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Match uu____12629)::uu____12630 ->
                    failwith
                      "Ill-typed term: cannot pattern match an abstraction"
                | (Arg (c,uu____12642,uu____12643))::stack_rest ->
                    (match c with
                     | Univ uu____12647 ->
                         norm cfg ((FStar_Pervasives_Native.None, c) :: env)
                           stack_rest t1
                     | uu____12656 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | b::[] ->
                              (log cfg
                                 (fun uu____12677  ->
                                    let uu____12678 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____12678);
                               norm cfg
                                 (((FStar_Pervasives_Native.Some b), c) ::
                                 env) stack_rest body)
                          | b::tl1 ->
                              (log cfg
                                 (fun uu____12718  ->
                                    let uu____12719 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____12719);
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
                       (fun uu____12797  ->
                          let uu____12798 =
                            FStar_Syntax_Print.term_to_string t1  in
                          FStar_Util.print1 "\tSet memo %s\n" uu____12798);
                     norm cfg env stack1 t1)
                | (Debug uu____12799)::uu____12800 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___153_12810 = cfg.steps  in
                             {
                               beta = (uu___153_12810.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___153_12810.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___153_12810.unfold_until);
                               unfold_only = (uu___153_12810.unfold_only);
                               unfold_fully = (uu___153_12810.unfold_fully);
                               unfold_attr = (uu___153_12810.unfold_attr);
                               unfold_tac = (uu___153_12810.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___153_12810.erase_universes);
                               allow_unbound_universes =
                                 (uu___153_12810.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___153_12810.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___153_12810.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___153_12810.in_full_norm_request)
                             }  in
                           let cfg' =
                             let uu___154_12812 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___154_12812.tcenv);
                               debug = (uu___154_12812.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___154_12812.primitive_steps);
                               strong = (uu___154_12812.strong);
                               memoize_lazy = (uu___154_12812.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___154_12812.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____12814 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____12814 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12856  -> dummy :: env1) env)
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
                                          let uu____12893 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____12893)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___155_12898 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___155_12898.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___155_12898.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12899 -> lopt  in
                           (log cfg
                              (fun uu____12905  ->
                                 let uu____12906 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12906);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___156_12915 = cfg  in
                               {
                                 steps = (uu___156_12915.steps);
                                 tcenv = (uu___156_12915.tcenv);
                                 debug = (uu___156_12915.debug);
                                 delta_level = (uu___156_12915.delta_level);
                                 primitive_steps =
                                   (uu___156_12915.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___156_12915.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___156_12915.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Meta uu____12926)::uu____12927 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___153_12939 = cfg.steps  in
                             {
                               beta = (uu___153_12939.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___153_12939.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___153_12939.unfold_until);
                               unfold_only = (uu___153_12939.unfold_only);
                               unfold_fully = (uu___153_12939.unfold_fully);
                               unfold_attr = (uu___153_12939.unfold_attr);
                               unfold_tac = (uu___153_12939.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___153_12939.erase_universes);
                               allow_unbound_universes =
                                 (uu___153_12939.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___153_12939.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___153_12939.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___153_12939.in_full_norm_request)
                             }  in
                           let cfg' =
                             let uu___154_12941 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___154_12941.tcenv);
                               debug = (uu___154_12941.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___154_12941.primitive_steps);
                               strong = (uu___154_12941.strong);
                               memoize_lazy = (uu___154_12941.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___154_12941.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____12943 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____12943 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12985  -> dummy :: env1) env)
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
                                          let uu____13022 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____13022)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___155_13027 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___155_13027.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___155_13027.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____13028 -> lopt  in
                           (log cfg
                              (fun uu____13034  ->
                                 let uu____13035 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____13035);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___156_13044 = cfg  in
                               {
                                 steps = (uu___156_13044.steps);
                                 tcenv = (uu___156_13044.tcenv);
                                 debug = (uu___156_13044.debug);
                                 delta_level = (uu___156_13044.delta_level);
                                 primitive_steps =
                                   (uu___156_13044.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___156_13044.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___156_13044.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Let uu____13055)::uu____13056 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___153_13070 = cfg.steps  in
                             {
                               beta = (uu___153_13070.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___153_13070.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___153_13070.unfold_until);
                               unfold_only = (uu___153_13070.unfold_only);
                               unfold_fully = (uu___153_13070.unfold_fully);
                               unfold_attr = (uu___153_13070.unfold_attr);
                               unfold_tac = (uu___153_13070.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___153_13070.erase_universes);
                               allow_unbound_universes =
                                 (uu___153_13070.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___153_13070.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___153_13070.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___153_13070.in_full_norm_request)
                             }  in
                           let cfg' =
                             let uu___154_13072 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___154_13072.tcenv);
                               debug = (uu___154_13072.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___154_13072.primitive_steps);
                               strong = (uu___154_13072.strong);
                               memoize_lazy = (uu___154_13072.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___154_13072.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____13074 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____13074 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____13116  -> dummy :: env1) env)
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
                                          let uu____13153 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____13153)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___155_13158 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___155_13158.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___155_13158.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____13159 -> lopt  in
                           (log cfg
                              (fun uu____13165  ->
                                 let uu____13166 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____13166);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___156_13175 = cfg  in
                               {
                                 steps = (uu___156_13175.steps);
                                 tcenv = (uu___156_13175.tcenv);
                                 debug = (uu___156_13175.debug);
                                 delta_level = (uu___156_13175.delta_level);
                                 primitive_steps =
                                   (uu___156_13175.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___156_13175.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___156_13175.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (App uu____13186)::uu____13187 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___153_13201 = cfg.steps  in
                             {
                               beta = (uu___153_13201.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___153_13201.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___153_13201.unfold_until);
                               unfold_only = (uu___153_13201.unfold_only);
                               unfold_fully = (uu___153_13201.unfold_fully);
                               unfold_attr = (uu___153_13201.unfold_attr);
                               unfold_tac = (uu___153_13201.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___153_13201.erase_universes);
                               allow_unbound_universes =
                                 (uu___153_13201.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___153_13201.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___153_13201.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___153_13201.in_full_norm_request)
                             }  in
                           let cfg' =
                             let uu___154_13203 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___154_13203.tcenv);
                               debug = (uu___154_13203.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___154_13203.primitive_steps);
                               strong = (uu___154_13203.strong);
                               memoize_lazy = (uu___154_13203.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___154_13203.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____13205 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____13205 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____13247  -> dummy :: env1) env)
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
                                          let uu____13284 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____13284)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___155_13289 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___155_13289.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___155_13289.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____13290 -> lopt  in
                           (log cfg
                              (fun uu____13296  ->
                                 let uu____13297 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____13297);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___156_13306 = cfg  in
                               {
                                 steps = (uu___156_13306.steps);
                                 tcenv = (uu___156_13306.tcenv);
                                 debug = (uu___156_13306.debug);
                                 delta_level = (uu___156_13306.delta_level);
                                 primitive_steps =
                                   (uu___156_13306.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___156_13306.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___156_13306.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Abs uu____13317)::uu____13318 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___153_13336 = cfg.steps  in
                             {
                               beta = (uu___153_13336.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___153_13336.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___153_13336.unfold_until);
                               unfold_only = (uu___153_13336.unfold_only);
                               unfold_fully = (uu___153_13336.unfold_fully);
                               unfold_attr = (uu___153_13336.unfold_attr);
                               unfold_tac = (uu___153_13336.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___153_13336.erase_universes);
                               allow_unbound_universes =
                                 (uu___153_13336.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___153_13336.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___153_13336.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___153_13336.in_full_norm_request)
                             }  in
                           let cfg' =
                             let uu___154_13338 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___154_13338.tcenv);
                               debug = (uu___154_13338.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___154_13338.primitive_steps);
                               strong = (uu___154_13338.strong);
                               memoize_lazy = (uu___154_13338.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___154_13338.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____13340 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____13340 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____13382  -> dummy :: env1) env)
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
                                          let uu____13419 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____13419)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___155_13424 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___155_13424.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___155_13424.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____13425 -> lopt  in
                           (log cfg
                              (fun uu____13431  ->
                                 let uu____13432 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____13432);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___156_13441 = cfg  in
                               {
                                 steps = (uu___156_13441.steps);
                                 tcenv = (uu___156_13441.tcenv);
                                 debug = (uu___156_13441.debug);
                                 delta_level = (uu___156_13441.delta_level);
                                 primitive_steps =
                                   (uu___156_13441.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___156_13441.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___156_13441.normalize_pure_lets)
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
                             let uu___153_13455 = cfg.steps  in
                             {
                               beta = (uu___153_13455.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___153_13455.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___153_13455.unfold_until);
                               unfold_only = (uu___153_13455.unfold_only);
                               unfold_fully = (uu___153_13455.unfold_fully);
                               unfold_attr = (uu___153_13455.unfold_attr);
                               unfold_tac = (uu___153_13455.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___153_13455.erase_universes);
                               allow_unbound_universes =
                                 (uu___153_13455.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___153_13455.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___153_13455.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___153_13455.in_full_norm_request)
                             }  in
                           let cfg' =
                             let uu___154_13457 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___154_13457.tcenv);
                               debug = (uu___154_13457.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___154_13457.primitive_steps);
                               strong = (uu___154_13457.strong);
                               memoize_lazy = (uu___154_13457.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___154_13457.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____13459 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____13459 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____13501  -> dummy :: env1) env)
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
                                          let uu____13538 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____13538)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___155_13543 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___155_13543.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___155_13543.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____13544 -> lopt  in
                           (log cfg
                              (fun uu____13550  ->
                                 let uu____13551 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____13551);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___156_13560 = cfg  in
                               {
                                 steps = (uu___156_13560.steps);
                                 tcenv = (uu___156_13560.tcenv);
                                 debug = (uu___156_13560.debug);
                                 delta_level = (uu___156_13560.delta_level);
                                 primitive_steps =
                                   (uu___156_13560.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___156_13560.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___156_13560.normalize_pure_lets)
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
                      (fun uu____13609  ->
                         fun stack1  ->
                           match uu____13609 with
                           | (a,aq) ->
                               let uu____13621 =
                                 let uu____13622 =
                                   let uu____13629 =
                                     let uu____13630 =
                                       let uu____13661 =
                                         FStar_Util.mk_ref
                                           FStar_Pervasives_Native.None
                                          in
                                       (env, a, uu____13661, false)  in
                                     Clos uu____13630  in
                                   (uu____13629, aq,
                                     (t1.FStar_Syntax_Syntax.pos))
                                    in
                                 Arg uu____13622  in
                               uu____13621 :: stack1) args)
                  in
               (log cfg
                  (fun uu____13745  ->
                     let uu____13746 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args)
                        in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____13746);
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
                             ((let uu___157_13782 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___157_13782.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___157_13782.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos
                         in
                      rebuild cfg env stack t2
                  | uu____13783 ->
                      let uu____13788 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____13788)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort  in
                  let uu____13791 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] f
                     in
                  match uu____13791 with
                  | (closing,f1) ->
                      let f2 = norm cfg (dummy :: env) [] f1  in
                      let t2 =
                        let uu____13822 =
                          let uu____13823 =
                            let uu____13830 =
                              FStar_Syntax_Subst.close closing f2  in
                            ((let uu___158_13832 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___158_13832.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___158_13832.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____13830)
                             in
                          FStar_Syntax_Syntax.Tm_refine uu____13823  in
                        mk uu____13822 t1.FStar_Syntax_Syntax.pos  in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if (cfg.steps).weak
               then
                 let uu____13851 = closure_as_term cfg env t1  in
                 rebuild cfg env stack uu____13851
               else
                 (let uu____13853 = FStar_Syntax_Subst.open_comp bs c  in
                  match uu____13853 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____13861 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun uu____13885  -> dummy :: env1) env)
                           in
                        norm_comp cfg uu____13861 c1  in
                      let t2 =
                        let uu____13907 = norm_binders cfg env bs1  in
                        FStar_Syntax_Util.arrow uu____13907 c2  in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) when
               (cfg.steps).unascribe -> norm cfg env stack t11
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack with
                | (Match uu____14018)::uu____14019 ->
                    (log cfg
                       (fun uu____14032  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (Arg uu____14033)::uu____14034 ->
                    (log cfg
                       (fun uu____14045  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (App
                    (uu____14046,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_constant
                                     (FStar_Const.Const_reify );
                                   FStar_Syntax_Syntax.pos = uu____14047;
                                   FStar_Syntax_Syntax.vars = uu____14048;_},uu____14049,uu____14050))::uu____14051
                    ->
                    (log cfg
                       (fun uu____14060  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (MemoLazy uu____14061)::uu____14062 ->
                    (log cfg
                       (fun uu____14073  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | uu____14074 ->
                    (log cfg
                       (fun uu____14077  ->
                          FStar_Util.print_string "+++ Keeping ascription \n");
                     (let t12 = norm cfg env [] t11  in
                      log cfg
                        (fun uu____14081  ->
                           FStar_Util.print_string
                             "+++ Normalizing ascription \n");
                      (let tc1 =
                         match tc with
                         | FStar_Util.Inl t2 ->
                             let uu____14098 = norm cfg env [] t2  in
                             FStar_Util.Inl uu____14098
                         | FStar_Util.Inr c ->
                             let uu____14106 = norm_comp cfg env c  in
                             FStar_Util.Inr uu____14106
                          in
                       let tacopt1 =
                         FStar_Util.map_opt tacopt (norm cfg env [])  in
                       match stack with
                       | (Cfg cfg1)::stack1 ->
                           let t2 =
                             let uu____14119 =
                               let uu____14120 =
                                 let uu____14147 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____14147, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____14120
                                in
                             mk uu____14119 t1.FStar_Syntax_Syntax.pos  in
                           norm cfg1 env stack1 t2
                       | uu____14166 ->
                           let uu____14167 =
                             let uu____14168 =
                               let uu____14169 =
                                 let uu____14196 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____14196, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____14169
                                in
                             mk uu____14168 t1.FStar_Syntax_Syntax.pos  in
                           rebuild cfg env stack uu____14167))))
           | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
               let stack1 =
                 (Match (env, branches, cfg, (t1.FStar_Syntax_Syntax.pos)))
                 :: stack  in
               let cfg1 =
                 if (cfg.steps).iota
                 then
                   let uu___159_14273 = cfg  in
                   {
                     steps =
                       (let uu___160_14276 = cfg.steps  in
                        {
                          beta = (uu___160_14276.beta);
                          iota = (uu___160_14276.iota);
                          zeta = (uu___160_14276.zeta);
                          weak = true;
                          hnf = (uu___160_14276.hnf);
                          primops = (uu___160_14276.primops);
                          do_not_unfold_pure_lets =
                            (uu___160_14276.do_not_unfold_pure_lets);
                          unfold_until = (uu___160_14276.unfold_until);
                          unfold_only = (uu___160_14276.unfold_only);
                          unfold_fully = (uu___160_14276.unfold_fully);
                          unfold_attr = (uu___160_14276.unfold_attr);
                          unfold_tac = (uu___160_14276.unfold_tac);
                          pure_subterms_within_computations =
                            (uu___160_14276.pure_subterms_within_computations);
                          simplify = (uu___160_14276.simplify);
                          erase_universes = (uu___160_14276.erase_universes);
                          allow_unbound_universes =
                            (uu___160_14276.allow_unbound_universes);
                          reify_ = (uu___160_14276.reify_);
                          compress_uvars = (uu___160_14276.compress_uvars);
                          no_full_norm = (uu___160_14276.no_full_norm);
                          check_no_uvars = (uu___160_14276.check_no_uvars);
                          unmeta = (uu___160_14276.unmeta);
                          unascribe = (uu___160_14276.unascribe);
                          in_full_norm_request =
                            (uu___160_14276.in_full_norm_request)
                        });
                     tcenv = (uu___159_14273.tcenv);
                     debug = (uu___159_14273.debug);
                     delta_level = (uu___159_14273.delta_level);
                     primitive_steps = (uu___159_14273.primitive_steps);
                     strong = (uu___159_14273.strong);
                     memoize_lazy = (uu___159_14273.memoize_lazy);
                     normalize_pure_lets =
                       (uu___159_14273.normalize_pure_lets)
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
                         let uu____14312 =
                           FStar_Syntax_Subst.univ_var_opening
                             lb.FStar_Syntax_Syntax.lbunivs
                            in
                         match uu____14312 with
                         | (openings,lbunivs) ->
                             let cfg1 =
                               let uu___161_14332 = cfg  in
                               let uu____14333 =
                                 FStar_TypeChecker_Env.push_univ_vars
                                   cfg.tcenv lbunivs
                                  in
                               {
                                 steps = (uu___161_14332.steps);
                                 tcenv = uu____14333;
                                 debug = (uu___161_14332.debug);
                                 delta_level = (uu___161_14332.delta_level);
                                 primitive_steps =
                                   (uu___161_14332.primitive_steps);
                                 strong = (uu___161_14332.strong);
                                 memoize_lazy = (uu___161_14332.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___161_14332.normalize_pure_lets)
                               }  in
                             let norm1 t2 =
                               let uu____14340 =
                                 let uu____14341 =
                                   FStar_Syntax_Subst.subst openings t2  in
                                 norm cfg1 env [] uu____14341  in
                               FStar_Syntax_Subst.close_univ_vars lbunivs
                                 uu____14340
                                in
                             let lbtyp = norm1 lb.FStar_Syntax_Syntax.lbtyp
                                in
                             let lbdef = norm1 lb.FStar_Syntax_Syntax.lbdef
                                in
                             let uu___162_14344 = lb  in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___162_14344.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs = lbunivs;
                               FStar_Syntax_Syntax.lbtyp = lbtyp;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___162_14344.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = lbdef;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___162_14344.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___162_14344.FStar_Syntax_Syntax.lbpos)
                             }))
                  in
               let uu____14345 =
                 mk (FStar_Syntax_Syntax.Tm_let ((b, lbs1), lbody))
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack uu____14345
           | FStar_Syntax_Syntax.Tm_let
               ((uu____14356,{
                               FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                 uu____14357;
                               FStar_Syntax_Syntax.lbunivs = uu____14358;
                               FStar_Syntax_Syntax.lbtyp = uu____14359;
                               FStar_Syntax_Syntax.lbeff = uu____14360;
                               FStar_Syntax_Syntax.lbdef = uu____14361;
                               FStar_Syntax_Syntax.lbattrs = uu____14362;
                               FStar_Syntax_Syntax.lbpos = uu____14363;_}::uu____14364),uu____14365)
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff
                  in
               let uu____14405 =
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
               if uu____14405
               then
                 let binder =
                   let uu____14407 =
                     FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                   FStar_Syntax_Syntax.mk_binder uu____14407  in
                 let env1 =
                   let uu____14417 =
                     let uu____14424 =
                       let uu____14425 =
                         let uu____14456 =
                           FStar_Util.mk_ref FStar_Pervasives_Native.None  in
                         (env, (lb.FStar_Syntax_Syntax.lbdef), uu____14456,
                           false)
                          in
                       Clos uu____14425  in
                     ((FStar_Pervasives_Native.Some binder), uu____14424)  in
                   uu____14417 :: env  in
                 (log cfg
                    (fun uu____14549  ->
                       FStar_Util.print_string "+++ Reducing Tm_let\n");
                  norm cfg env1 stack body)
               else
                 if (cfg.steps).weak
                 then
                   (log cfg
                      (fun uu____14553  ->
                         FStar_Util.print_string "+++ Not touching Tm_let\n");
                    (let uu____14554 = closure_as_term cfg env t1  in
                     rebuild cfg env stack uu____14554))
                 else
                   (let uu____14556 =
                      let uu____14561 =
                        let uu____14562 =
                          let uu____14563 =
                            FStar_All.pipe_right
                              lb.FStar_Syntax_Syntax.lbname FStar_Util.left
                             in
                          FStar_All.pipe_right uu____14563
                            FStar_Syntax_Syntax.mk_binder
                           in
                        [uu____14562]  in
                      FStar_Syntax_Subst.open_term uu____14561 body  in
                    match uu____14556 with
                    | (bs,body1) ->
                        (log cfg
                           (fun uu____14572  ->
                              FStar_Util.print_string
                                "+++ Normalizing Tm_let -- type");
                         (let ty =
                            norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                          let lbname =
                            let x =
                              let uu____14580 = FStar_List.hd bs  in
                              FStar_Pervasives_Native.fst uu____14580  in
                            FStar_Util.Inl
                              (let uu___163_14590 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___163_14590.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___163_14590.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               })
                             in
                          log cfg
                            (fun uu____14593  ->
                               FStar_Util.print_string
                                 "+++ Normalizing Tm_let -- definiens\n");
                          (let lb1 =
                             let uu___164_14595 = lb  in
                             let uu____14596 =
                               norm cfg env [] lb.FStar_Syntax_Syntax.lbdef
                                in
                             {
                               FStar_Syntax_Syntax.lbname = lbname;
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___164_14595.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp = ty;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___164_14595.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = uu____14596;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___164_14595.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___164_14595.FStar_Syntax_Syntax.lbpos)
                             }  in
                           let env' =
                             FStar_All.pipe_right bs
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____14631  -> dummy :: env1) env)
                              in
                           let stack1 = (Cfg cfg) :: stack  in
                           let cfg1 =
                             let uu___165_14654 = cfg  in
                             {
                               steps = (uu___165_14654.steps);
                               tcenv = (uu___165_14654.tcenv);
                               debug = (uu___165_14654.debug);
                               delta_level = (uu___165_14654.delta_level);
                               primitive_steps =
                                 (uu___165_14654.primitive_steps);
                               strong = true;
                               memoize_lazy = (uu___165_14654.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___165_14654.normalize_pure_lets)
                             }  in
                           log cfg1
                             (fun uu____14657  ->
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
               let uu____14674 = FStar_Syntax_Subst.open_let_rec lbs body  in
               (match uu____14674 with
                | (lbs1,body1) ->
                    let lbs2 =
                      FStar_List.map
                        (fun lb  ->
                           let ty =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                           let lbname =
                             let uu____14710 =
                               let uu___166_14711 =
                                 FStar_Util.left
                                   lb.FStar_Syntax_Syntax.lbname
                                  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___166_14711.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___166_14711.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               }  in
                             FStar_Util.Inl uu____14710  in
                           let uu____14712 =
                             FStar_Syntax_Util.abs_formals
                               lb.FStar_Syntax_Syntax.lbdef
                              in
                           match uu____14712 with
                           | (xs,def_body,lopt) ->
                               let xs1 = norm_binders cfg env xs  in
                               let env1 =
                                 let uu____14738 =
                                   FStar_List.map (fun uu____14754  -> dummy)
                                     lbs1
                                    in
                                 let uu____14755 =
                                   let uu____14764 =
                                     FStar_List.map
                                       (fun uu____14784  -> dummy) xs1
                                      in
                                   FStar_List.append uu____14764 env  in
                                 FStar_List.append uu____14738 uu____14755
                                  in
                               let def_body1 = norm cfg env1 [] def_body  in
                               let lopt1 =
                                 match lopt with
                                 | FStar_Pervasives_Native.Some rc ->
                                     let uu____14808 =
                                       let uu___167_14809 = rc  in
                                       let uu____14810 =
                                         FStar_Util.map_opt
                                           rc.FStar_Syntax_Syntax.residual_typ
                                           (norm cfg env1 [])
                                          in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___167_14809.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           uu____14810;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___167_14809.FStar_Syntax_Syntax.residual_flags)
                                       }  in
                                     FStar_Pervasives_Native.Some uu____14808
                                 | uu____14817 -> lopt  in
                               let def =
                                 FStar_Syntax_Util.abs xs1 def_body1 lopt1
                                  in
                               let uu___168_14821 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname = lbname;
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___168_14821.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp = ty;
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___168_14821.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___168_14821.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___168_14821.FStar_Syntax_Syntax.lbpos)
                               }) lbs1
                       in
                    let env' =
                      let uu____14831 =
                        FStar_List.map (fun uu____14847  -> dummy) lbs2  in
                      FStar_List.append uu____14831 env  in
                    let body2 = norm cfg env' [] body1  in
                    let uu____14855 =
                      FStar_Syntax_Subst.close_let_rec lbs2 body2  in
                    (match uu____14855 with
                     | (lbs3,body3) ->
                         let t2 =
                           let uu___169_14871 = t1  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_let
                                  ((true, lbs3), body3));
                             FStar_Syntax_Syntax.pos =
                               (uu___169_14871.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___169_14871.FStar_Syntax_Syntax.vars)
                           }  in
                         rebuild cfg env stack t2))
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               Prims.op_Negation (cfg.steps).zeta ->
               let uu____14898 = closure_as_term cfg env t1  in
               rebuild cfg env stack uu____14898
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____14917 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____14993  ->
                        match uu____14993 with
                        | (rec_env,memos,i) ->
                            let bv =
                              let uu___170_15114 =
                                FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                                 in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___170_15114.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index = i;
                                FStar_Syntax_Syntax.sort =
                                  (uu___170_15114.FStar_Syntax_Syntax.sort)
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
               (match uu____14917 with
                | (rec_env,memos,uu____15327) ->
                    let uu____15380 =
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
                             let uu____15703 =
                               let uu____15710 =
                                 let uu____15711 =
                                   let uu____15742 =
                                     FStar_Util.mk_ref
                                       FStar_Pervasives_Native.None
                                      in
                                   (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                     uu____15742, false)
                                    in
                                 Clos uu____15711  in
                               (FStar_Pervasives_Native.None, uu____15710)
                                in
                             uu____15703 :: env1)
                        (FStar_Pervasives_Native.snd lbs) env
                       in
                    norm cfg body_env stack body)
           | FStar_Syntax_Syntax.Tm_meta (head1,m) ->
               (log cfg
                  (fun uu____15852  ->
                     let uu____15853 =
                       FStar_Syntax_Print.metadata_to_string m  in
                     FStar_Util.print1 ">> metadata = %s\n" uu____15853);
                (match m with
                 | FStar_Syntax_Syntax.Meta_monadic (m1,t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inl m1) t2
                 | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inr (m1, m')) t2
                 | uu____15875 ->
                     if (cfg.steps).unmeta
                     then norm cfg env stack head1
                     else
                       (match stack with
                        | uu____15877::uu____15878 ->
                            (match m with
                             | FStar_Syntax_Syntax.Meta_labeled
                                 (l,r,uu____15883) ->
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
                             | uu____15906 -> norm cfg env stack head1)
                        | [] ->
                            let head2 = norm cfg env [] head1  in
                            let m1 =
                              match m with
                              | FStar_Syntax_Syntax.Meta_pattern args ->
                                  let uu____15920 =
                                    norm_pattern_args cfg env args  in
                                  FStar_Syntax_Syntax.Meta_pattern
                                    uu____15920
                              | uu____15931 -> m  in
                            let t2 =
                              mk (FStar_Syntax_Syntax.Tm_meta (head2, m1))
                                t1.FStar_Syntax_Syntax.pos
                               in
                            rebuild cfg env stack t2)))
           | FStar_Syntax_Syntax.Tm_delayed uu____15935 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               norm cfg env stack t2
           | FStar_Syntax_Syntax.Tm_uvar uu____15961 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               (match t2.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_uvar uu____15979 ->
                    if (cfg.steps).check_no_uvars
                    then
                      let uu____15996 =
                        let uu____15997 =
                          FStar_Range.string_of_range
                            t2.FStar_Syntax_Syntax.pos
                           in
                        let uu____15998 =
                          FStar_Syntax_Print.term_to_string t2  in
                        FStar_Util.format2
                          "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                          uu____15997 uu____15998
                         in
                      failwith uu____15996
                    else rebuild cfg env stack t2
                | uu____16000 -> norm cfg env stack t2))

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
                let uu____16010 = FStar_Syntax_Syntax.range_of_fv f  in
                FStar_TypeChecker_Env.set_range cfg.tcenv uu____16010  in
              let uu____16011 =
                FStar_TypeChecker_Env.lookup_definition_qninfo
                  cfg.delta_level
                  (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                  qninfo
                 in
              match uu____16011 with
              | FStar_Pervasives_Native.None  ->
                  (log cfg
                     (fun uu____16024  ->
                        FStar_Util.print "Tm_fvar case 2\n" []);
                   rebuild cfg env stack t0)
              | FStar_Pervasives_Native.Some (us,t) ->
                  (log cfg
                     (fun uu____16035  ->
                        let uu____16036 =
                          FStar_Syntax_Print.term_to_string t0  in
                        let uu____16037 = FStar_Syntax_Print.term_to_string t
                           in
                        FStar_Util.print2 ">>> Unfolded %s to %s\n"
                          uu____16036 uu____16037);
                   (let t1 =
                      if
                        ((cfg.steps).unfold_until =
                           (FStar_Pervasives_Native.Some
                              FStar_Syntax_Syntax.Delta_constant))
                          && (Prims.op_Negation (cfg.steps).unfold_tac)
                      then t
                      else
                        (let uu____16042 =
                           FStar_Ident.range_of_lid
                             (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                            in
                         FStar_Syntax_Subst.set_use_range uu____16042 t)
                       in
                    let n1 = FStar_List.length us  in
                    if n1 > (Prims.parse_int "0")
                    then
                      match stack with
                      | (UnivArgs (us',uu____16051))::stack1 ->
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
                      | uu____16106 when
                          (cfg.steps).erase_universes ||
                            (cfg.steps).allow_unbound_universes
                          -> norm cfg env stack t1
                      | uu____16109 ->
                          let uu____16112 =
                            let uu____16113 =
                              FStar_Syntax_Print.lid_to_string
                                (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                               in
                            FStar_Util.format1
                              "Impossible: missing universe instantiation on %s"
                              uu____16113
                             in
                          failwith uu____16112
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
                  let uu___171_16137 = cfg  in
                  let uu____16138 =
                    FStar_List.fold_right fstep_add_one new_steps cfg.steps
                     in
                  {
                    steps = uu____16138;
                    tcenv = (uu___171_16137.tcenv);
                    debug = (uu___171_16137.debug);
                    delta_level =
                      [FStar_TypeChecker_Env.Inlining;
                      FStar_TypeChecker_Env.Eager_unfolding_only];
                    primitive_steps = (uu___171_16137.primitive_steps);
                    strong = (uu___171_16137.strong);
                    memoize_lazy = (uu___171_16137.memoize_lazy);
                    normalize_pure_lets =
                      (uu___171_16137.normalize_pure_lets)
                  }
                else
                  (let uu___172_16140 = cfg  in
                   {
                     steps =
                       (let uu___173_16143 = cfg.steps  in
                        {
                          beta = (uu___173_16143.beta);
                          iota = (uu___173_16143.iota);
                          zeta = false;
                          weak = (uu___173_16143.weak);
                          hnf = (uu___173_16143.hnf);
                          primops = (uu___173_16143.primops);
                          do_not_unfold_pure_lets =
                            (uu___173_16143.do_not_unfold_pure_lets);
                          unfold_until = (uu___173_16143.unfold_until);
                          unfold_only = (uu___173_16143.unfold_only);
                          unfold_fully = (uu___173_16143.unfold_fully);
                          unfold_attr = (uu___173_16143.unfold_attr);
                          unfold_tac = (uu___173_16143.unfold_tac);
                          pure_subterms_within_computations =
                            (uu___173_16143.pure_subterms_within_computations);
                          simplify = (uu___173_16143.simplify);
                          erase_universes = (uu___173_16143.erase_universes);
                          allow_unbound_universes =
                            (uu___173_16143.allow_unbound_universes);
                          reify_ = (uu___173_16143.reify_);
                          compress_uvars = (uu___173_16143.compress_uvars);
                          no_full_norm = (uu___173_16143.no_full_norm);
                          check_no_uvars = (uu___173_16143.check_no_uvars);
                          unmeta = (uu___173_16143.unmeta);
                          unascribe = (uu___173_16143.unascribe);
                          in_full_norm_request =
                            (uu___173_16143.in_full_norm_request)
                        });
                     tcenv = (uu___172_16140.tcenv);
                     debug = (uu___172_16140.debug);
                     delta_level = (uu___172_16140.delta_level);
                     primitive_steps = (uu___172_16140.primitive_steps);
                     strong = (uu___172_16140.strong);
                     memoize_lazy = (uu___172_16140.memoize_lazy);
                     normalize_pure_lets =
                       (uu___172_16140.normalize_pure_lets)
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
                  (fun uu____16173  ->
                     let uu____16174 = FStar_Syntax_Print.tag_of_term head2
                        in
                     let uu____16175 =
                       FStar_Syntax_Print.term_to_string head2  in
                     FStar_Util.print2 "Reifying: (%s) %s\n" uu____16174
                       uu____16175);
                (let head3 = FStar_Syntax_Util.unmeta_safe head2  in
                 let uu____16177 =
                   let uu____16178 = FStar_Syntax_Subst.compress head3  in
                   uu____16178.FStar_Syntax_Syntax.n  in
                 match uu____16177 with
                 | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                     let ed =
                       let uu____16196 =
                         FStar_TypeChecker_Env.norm_eff_name cfg.tcenv m  in
                       FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                         uu____16196
                        in
                     let uu____16197 = ed.FStar_Syntax_Syntax.bind_repr  in
                     (match uu____16197 with
                      | (uu____16198,bind_repr) ->
                          (match lb.FStar_Syntax_Syntax.lbname with
                           | FStar_Util.Inr uu____16204 ->
                               failwith
                                 "Cannot reify a top-level let binding"
                           | FStar_Util.Inl x ->
                               let is_return e =
                                 let uu____16214 =
                                   let uu____16215 =
                                     FStar_Syntax_Subst.compress e  in
                                   uu____16215.FStar_Syntax_Syntax.n  in
                                 match uu____16214 with
                                 | FStar_Syntax_Syntax.Tm_meta
                                     (e1,FStar_Syntax_Syntax.Meta_monadic
                                      (uu____16221,uu____16222))
                                     ->
                                     let uu____16231 =
                                       let uu____16232 =
                                         FStar_Syntax_Subst.compress e1  in
                                       uu____16232.FStar_Syntax_Syntax.n  in
                                     (match uu____16231 with
                                      | FStar_Syntax_Syntax.Tm_meta
                                          (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                           (uu____16238,msrc,uu____16240))
                                          when
                                          FStar_Syntax_Util.is_pure_effect
                                            msrc
                                          ->
                                          let uu____16249 =
                                            FStar_Syntax_Subst.compress e2
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____16249
                                      | uu____16250 ->
                                          FStar_Pervasives_Native.None)
                                 | uu____16251 ->
                                     FStar_Pervasives_Native.None
                                  in
                               let uu____16252 =
                                 is_return lb.FStar_Syntax_Syntax.lbdef  in
                               (match uu____16252 with
                                | FStar_Pervasives_Native.Some e ->
                                    let lb1 =
                                      let uu___174_16257 = lb  in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          (uu___174_16257.FStar_Syntax_Syntax.lbname);
                                        FStar_Syntax_Syntax.lbunivs =
                                          (uu___174_16257.FStar_Syntax_Syntax.lbunivs);
                                        FStar_Syntax_Syntax.lbtyp =
                                          (uu___174_16257.FStar_Syntax_Syntax.lbtyp);
                                        FStar_Syntax_Syntax.lbeff =
                                          FStar_Parser_Const.effect_PURE_lid;
                                        FStar_Syntax_Syntax.lbdef = e;
                                        FStar_Syntax_Syntax.lbattrs =
                                          (uu___174_16257.FStar_Syntax_Syntax.lbattrs);
                                        FStar_Syntax_Syntax.lbpos =
                                          (uu___174_16257.FStar_Syntax_Syntax.lbpos)
                                      }  in
                                    let uu____16258 = FStar_List.tl stack  in
                                    let uu____16259 =
                                      let uu____16260 =
                                        let uu____16267 =
                                          let uu____16268 =
                                            let uu____16281 =
                                              FStar_Syntax_Util.mk_reify body
                                               in
                                            ((false, [lb1]), uu____16281)  in
                                          FStar_Syntax_Syntax.Tm_let
                                            uu____16268
                                           in
                                        FStar_Syntax_Syntax.mk uu____16267
                                         in
                                      uu____16260
                                        FStar_Pervasives_Native.None
                                        head3.FStar_Syntax_Syntax.pos
                                       in
                                    norm cfg env uu____16258 uu____16259
                                | FStar_Pervasives_Native.None  ->
                                    let uu____16297 =
                                      let uu____16298 = is_return body  in
                                      match uu____16298 with
                                      | FStar_Pervasives_Native.Some
                                          {
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_bvar y;
                                            FStar_Syntax_Syntax.pos =
                                              uu____16302;
                                            FStar_Syntax_Syntax.vars =
                                              uu____16303;_}
                                          -> FStar_Syntax_Syntax.bv_eq x y
                                      | uu____16308 -> false  in
                                    if uu____16297
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
                                         let uu____16331 =
                                           let uu____16338 =
                                             let uu____16339 =
                                               let uu____16356 =
                                                 let uu____16359 =
                                                   FStar_Syntax_Syntax.mk_binder
                                                     x
                                                    in
                                                 [uu____16359]  in
                                               (uu____16356, body1,
                                                 (FStar_Pervasives_Native.Some
                                                    body_rc))
                                                in
                                             FStar_Syntax_Syntax.Tm_abs
                                               uu____16339
                                              in
                                           FStar_Syntax_Syntax.mk uu____16338
                                            in
                                         uu____16331
                                           FStar_Pervasives_Native.None
                                           body1.FStar_Syntax_Syntax.pos
                                          in
                                       let close1 = closure_as_term cfg env
                                          in
                                       let bind_inst =
                                         let uu____16377 =
                                           let uu____16378 =
                                             FStar_Syntax_Subst.compress
                                               bind_repr
                                              in
                                           uu____16378.FStar_Syntax_Syntax.n
                                            in
                                         match uu____16377 with
                                         | FStar_Syntax_Syntax.Tm_uinst
                                             (bind1,uu____16384::uu____16385::[])
                                             ->
                                             let uu____16392 =
                                               let uu____16399 =
                                                 let uu____16400 =
                                                   let uu____16407 =
                                                     let uu____16410 =
                                                       let uu____16411 =
                                                         close1
                                                           lb.FStar_Syntax_Syntax.lbtyp
                                                          in
                                                       (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                         cfg.tcenv
                                                         uu____16411
                                                        in
                                                     let uu____16412 =
                                                       let uu____16415 =
                                                         let uu____16416 =
                                                           close1 t  in
                                                         (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                           cfg.tcenv
                                                           uu____16416
                                                          in
                                                       [uu____16415]  in
                                                     uu____16410 ::
                                                       uu____16412
                                                      in
                                                   (bind1, uu____16407)  in
                                                 FStar_Syntax_Syntax.Tm_uinst
                                                   uu____16400
                                                  in
                                               FStar_Syntax_Syntax.mk
                                                 uu____16399
                                                in
                                             uu____16392
                                               FStar_Pervasives_Native.None
                                               rng
                                         | uu____16424 ->
                                             failwith
                                               "NIY : Reification of indexed effects"
                                          in
                                       let maybe_range_arg =
                                         let uu____16430 =
                                           FStar_Util.for_some
                                             (FStar_Syntax_Util.attr_eq
                                                FStar_Syntax_Util.dm4f_bind_range_attr)
                                             ed.FStar_Syntax_Syntax.eff_attrs
                                            in
                                         if uu____16430
                                         then
                                           let uu____16433 =
                                             let uu____16434 =
                                               FStar_Syntax_Embeddings.embed
                                                 FStar_Syntax_Embeddings.e_range
                                                 lb.FStar_Syntax_Syntax.lbpos
                                                 lb.FStar_Syntax_Syntax.lbpos
                                                in
                                             FStar_Syntax_Syntax.as_arg
                                               uu____16434
                                              in
                                           let uu____16435 =
                                             let uu____16438 =
                                               let uu____16439 =
                                                 FStar_Syntax_Embeddings.embed
                                                   FStar_Syntax_Embeddings.e_range
                                                   body2.FStar_Syntax_Syntax.pos
                                                   body2.FStar_Syntax_Syntax.pos
                                                  in
                                               FStar_Syntax_Syntax.as_arg
                                                 uu____16439
                                                in
                                             [uu____16438]  in
                                           uu____16433 :: uu____16435
                                         else []  in
                                       let reified =
                                         let uu____16444 =
                                           let uu____16451 =
                                             let uu____16452 =
                                               let uu____16467 =
                                                 let uu____16470 =
                                                   let uu____16473 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       lb.FStar_Syntax_Syntax.lbtyp
                                                      in
                                                   let uu____16474 =
                                                     let uu____16477 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         t
                                                        in
                                                     [uu____16477]  in
                                                   uu____16473 :: uu____16474
                                                    in
                                                 let uu____16478 =
                                                   let uu____16481 =
                                                     let uu____16484 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         FStar_Syntax_Syntax.tun
                                                        in
                                                     let uu____16485 =
                                                       let uu____16488 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           head4
                                                          in
                                                       let uu____16489 =
                                                         let uu____16492 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             FStar_Syntax_Syntax.tun
                                                            in
                                                         let uu____16493 =
                                                           let uu____16496 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               body2
                                                              in
                                                           [uu____16496]  in
                                                         uu____16492 ::
                                                           uu____16493
                                                          in
                                                       uu____16488 ::
                                                         uu____16489
                                                        in
                                                     uu____16484 ::
                                                       uu____16485
                                                      in
                                                   FStar_List.append
                                                     maybe_range_arg
                                                     uu____16481
                                                    in
                                                 FStar_List.append
                                                   uu____16470 uu____16478
                                                  in
                                               (bind_inst, uu____16467)  in
                                             FStar_Syntax_Syntax.Tm_app
                                               uu____16452
                                              in
                                           FStar_Syntax_Syntax.mk uu____16451
                                            in
                                         uu____16444
                                           FStar_Pervasives_Native.None rng
                                          in
                                       log cfg
                                         (fun uu____16508  ->
                                            let uu____16509 =
                                              FStar_Syntax_Print.term_to_string
                                                head0
                                               in
                                            let uu____16510 =
                                              FStar_Syntax_Print.term_to_string
                                                reified
                                               in
                                            FStar_Util.print2
                                              "Reified (1) <%s> to %s\n"
                                              uu____16509 uu____16510);
                                       (let uu____16511 = FStar_List.tl stack
                                           in
                                        norm cfg env uu____16511 reified)))))
                 | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                     let ed =
                       let uu____16535 =
                         FStar_TypeChecker_Env.norm_eff_name cfg.tcenv m  in
                       FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                         uu____16535
                        in
                     let uu____16536 = ed.FStar_Syntax_Syntax.bind_repr  in
                     (match uu____16536 with
                      | (uu____16537,bind_repr) ->
                          let maybe_unfold_action head4 =
                            let maybe_extract_fv t1 =
                              let t2 =
                                let uu____16576 =
                                  let uu____16577 =
                                    FStar_Syntax_Subst.compress t1  in
                                  uu____16577.FStar_Syntax_Syntax.n  in
                                match uu____16576 with
                                | FStar_Syntax_Syntax.Tm_uinst
                                    (t2,uu____16583) -> t2
                                | uu____16588 -> head4  in
                              let uu____16589 =
                                let uu____16590 =
                                  FStar_Syntax_Subst.compress t2  in
                                uu____16590.FStar_Syntax_Syntax.n  in
                              match uu____16589 with
                              | FStar_Syntax_Syntax.Tm_fvar x ->
                                  FStar_Pervasives_Native.Some x
                              | uu____16596 -> FStar_Pervasives_Native.None
                               in
                            let uu____16597 = maybe_extract_fv head4  in
                            match uu____16597 with
                            | FStar_Pervasives_Native.Some x when
                                let uu____16607 =
                                  FStar_Syntax_Syntax.lid_of_fv x  in
                                FStar_TypeChecker_Env.is_action cfg.tcenv
                                  uu____16607
                                ->
                                let head5 = norm cfg env [] head4  in
                                let action_unfolded =
                                  let uu____16612 = maybe_extract_fv head5
                                     in
                                  match uu____16612 with
                                  | FStar_Pervasives_Native.Some uu____16617
                                      -> FStar_Pervasives_Native.Some true
                                  | uu____16618 ->
                                      FStar_Pervasives_Native.Some false
                                   in
                                (head5, action_unfolded)
                            | uu____16623 ->
                                (head4, FStar_Pervasives_Native.None)
                             in
                          ((let is_arg_impure uu____16640 =
                              match uu____16640 with
                              | (e,q) ->
                                  let uu____16647 =
                                    let uu____16648 =
                                      FStar_Syntax_Subst.compress e  in
                                    uu____16648.FStar_Syntax_Syntax.n  in
                                  (match uu____16647 with
                                   | FStar_Syntax_Syntax.Tm_meta
                                       (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                        (m1,m2,t'))
                                       ->
                                       let uu____16663 =
                                         FStar_Syntax_Util.is_pure_effect m1
                                          in
                                       Prims.op_Negation uu____16663
                                   | uu____16664 -> false)
                               in
                            let uu____16665 =
                              let uu____16666 =
                                let uu____16673 =
                                  FStar_Syntax_Syntax.as_arg head_app  in
                                uu____16673 :: args  in
                              FStar_Util.for_some is_arg_impure uu____16666
                               in
                            if uu____16665
                            then
                              let uu____16678 =
                                let uu____16679 =
                                  FStar_Syntax_Print.term_to_string head3  in
                                FStar_Util.format1
                                  "Incompatibility between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                  uu____16679
                                 in
                              failwith uu____16678
                            else ());
                           (let uu____16681 = maybe_unfold_action head_app
                               in
                            match uu____16681 with
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
                                   (fun uu____16724  ->
                                      let uu____16725 =
                                        FStar_Syntax_Print.term_to_string
                                          head0
                                         in
                                      let uu____16726 =
                                        FStar_Syntax_Print.term_to_string
                                          body1
                                         in
                                      FStar_Util.print2
                                        "Reified (2) <%s> to %s\n"
                                        uu____16725 uu____16726);
                                 (let uu____16727 = FStar_List.tl stack  in
                                  norm cfg env uu____16727 body1)))))
                 | FStar_Syntax_Syntax.Tm_meta
                     (e,FStar_Syntax_Syntax.Meta_monadic uu____16729) ->
                     do_reify_monadic fallback cfg env stack e m t
                 | FStar_Syntax_Syntax.Tm_meta
                     (e,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,t'))
                     ->
                     let lifted =
                       let uu____16753 = closure_as_term cfg env t'  in
                       reify_lift cfg e msrc mtgt uu____16753  in
                     (log cfg
                        (fun uu____16757  ->
                           let uu____16758 =
                             FStar_Syntax_Print.term_to_string lifted  in
                           FStar_Util.print1 "Reified lift to (2): %s\n"
                             uu____16758);
                      (let uu____16759 = FStar_List.tl stack  in
                       norm cfg env uu____16759 lifted))
                 | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                     let branches1 =
                       FStar_All.pipe_right branches
                         (FStar_List.map
                            (fun uu____16880  ->
                               match uu____16880 with
                               | (pat,wopt,tm) ->
                                   let uu____16928 =
                                     FStar_Syntax_Util.mk_reify tm  in
                                   (pat, wopt, uu____16928)))
                        in
                     let tm =
                       mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                         head3.FStar_Syntax_Syntax.pos
                        in
                     let uu____16960 = FStar_List.tl stack  in
                     norm cfg env uu____16960 tm
                 | uu____16961 -> fallback ())

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
              (fun uu____16975  ->
                 let uu____16976 = FStar_Ident.string_of_lid msrc  in
                 let uu____16977 = FStar_Ident.string_of_lid mtgt  in
                 let uu____16978 = FStar_Syntax_Print.term_to_string e  in
                 FStar_Util.print3 "Reifying lift %s -> %s: %s\n" uu____16976
                   uu____16977 uu____16978);
            (let uu____16979 =
               (FStar_Syntax_Util.is_pure_effect msrc) ||
                 (FStar_Syntax_Util.is_div_effect msrc)
                in
             if uu____16979
             then
               let ed =
                 let uu____16981 =
                   FStar_TypeChecker_Env.norm_eff_name cfg.tcenv mtgt  in
                 FStar_TypeChecker_Env.get_effect_decl env uu____16981  in
               let uu____16982 = ed.FStar_Syntax_Syntax.return_repr  in
               match uu____16982 with
               | (uu____16983,return_repr) ->
                   let return_inst =
                     let uu____16992 =
                       let uu____16993 =
                         FStar_Syntax_Subst.compress return_repr  in
                       uu____16993.FStar_Syntax_Syntax.n  in
                     match uu____16992 with
                     | FStar_Syntax_Syntax.Tm_uinst
                         (return_tm,uu____16999::[]) ->
                         let uu____17006 =
                           let uu____17013 =
                             let uu____17014 =
                               let uu____17021 =
                                 let uu____17024 =
                                   env.FStar_TypeChecker_Env.universe_of env
                                     t
                                    in
                                 [uu____17024]  in
                               (return_tm, uu____17021)  in
                             FStar_Syntax_Syntax.Tm_uinst uu____17014  in
                           FStar_Syntax_Syntax.mk uu____17013  in
                         uu____17006 FStar_Pervasives_Native.None
                           e.FStar_Syntax_Syntax.pos
                     | uu____17032 ->
                         failwith "NIY : Reification of indexed effects"
                      in
                   let uu____17035 =
                     let uu____17042 =
                       let uu____17043 =
                         let uu____17058 =
                           let uu____17061 = FStar_Syntax_Syntax.as_arg t  in
                           let uu____17062 =
                             let uu____17065 = FStar_Syntax_Syntax.as_arg e
                                in
                             [uu____17065]  in
                           uu____17061 :: uu____17062  in
                         (return_inst, uu____17058)  in
                       FStar_Syntax_Syntax.Tm_app uu____17043  in
                     FStar_Syntax_Syntax.mk uu____17042  in
                   uu____17035 FStar_Pervasives_Native.None
                     e.FStar_Syntax_Syntax.pos
             else
               (let uu____17074 =
                  FStar_TypeChecker_Env.monad_leq env msrc mtgt  in
                match uu____17074 with
                | FStar_Pervasives_Native.None  ->
                    let uu____17077 =
                      let uu____17078 = FStar_Ident.text_of_lid msrc  in
                      let uu____17079 = FStar_Ident.text_of_lid mtgt  in
                      FStar_Util.format2
                        "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                        uu____17078 uu____17079
                       in
                    failwith uu____17077
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____17080;
                      FStar_TypeChecker_Env.mtarget = uu____17081;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____17082;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.None ;_};_}
                    ->
                    let uu____17104 =
                      let uu____17105 = FStar_Ident.text_of_lid msrc  in
                      let uu____17106 = FStar_Ident.text_of_lid mtgt  in
                      FStar_Util.format2
                        "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
                        uu____17105 uu____17106
                       in
                    failwith uu____17104
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____17107;
                      FStar_TypeChecker_Env.mtarget = uu____17108;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____17109;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.Some lift;_};_}
                    ->
                    let uu____17144 =
                      env.FStar_TypeChecker_Env.universe_of env t  in
                    let uu____17145 = FStar_Syntax_Util.mk_reify e  in
                    lift uu____17144 t FStar_Syntax_Syntax.tun uu____17145))

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
                (fun uu____17201  ->
                   match uu____17201 with
                   | (a,imp) ->
                       let uu____17212 = norm cfg env [] a  in
                       (uu____17212, imp))))

and (norm_comp :
  cfg -> env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp) =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        log cfg
          (fun uu____17220  ->
             let uu____17221 = FStar_Syntax_Print.comp_to_string comp  in
             let uu____17222 =
               FStar_Util.string_of_int (FStar_List.length env)  in
             FStar_Util.print2 ">>> %s\nNormComp with with %s env elements"
               uu____17221 uu____17222);
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Total (t,uopt) ->
             let t1 = norm cfg env [] t  in
             let uopt1 =
               match uopt with
               | FStar_Pervasives_Native.Some u ->
                   let uu____17246 = norm_universe cfg env u  in
                   FStar_All.pipe_left
                     (fun _0_18  -> FStar_Pervasives_Native.Some _0_18)
                     uu____17246
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
                in
             let uu___175_17249 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Total (t1, uopt1));
               FStar_Syntax_Syntax.pos =
                 (uu___175_17249.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___175_17249.FStar_Syntax_Syntax.vars)
             }
         | FStar_Syntax_Syntax.GTotal (t,uopt) ->
             let t1 = norm cfg env [] t  in
             let uopt1 =
               match uopt with
               | FStar_Pervasives_Native.Some u ->
                   let uu____17269 = norm_universe cfg env u  in
                   FStar_All.pipe_left
                     (fun _0_19  -> FStar_Pervasives_Native.Some _0_19)
                     uu____17269
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
                in
             let uu___176_17272 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.GTotal (t1, uopt1));
               FStar_Syntax_Syntax.pos =
                 (uu___176_17272.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___176_17272.FStar_Syntax_Syntax.vars)
             }
         | FStar_Syntax_Syntax.Comp ct ->
             let norm_args =
               FStar_List.mapi
                 (fun idx  ->
                    fun uu____17307  ->
                      match uu____17307 with
                      | (a,i) ->
                          let uu____17318 = norm cfg env [] a  in
                          (uu____17318, i))
                in
             let effect_args = norm_args ct.FStar_Syntax_Syntax.effect_args
                in
             let flags1 =
               FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                 (FStar_List.map
                    (fun uu___90_17336  ->
                       match uu___90_17336 with
                       | FStar_Syntax_Syntax.DECREASES t ->
                           let uu____17340 = norm cfg env [] t  in
                           FStar_Syntax_Syntax.DECREASES uu____17340
                       | f -> f))
                in
             let comp_univs =
               FStar_List.map (norm_universe cfg env)
                 ct.FStar_Syntax_Syntax.comp_univs
                in
             let result_typ =
               norm cfg env [] ct.FStar_Syntax_Syntax.result_typ  in
             let uu___177_17348 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Comp
                    (let uu___178_17351 = ct  in
                     {
                       FStar_Syntax_Syntax.comp_univs = comp_univs;
                       FStar_Syntax_Syntax.effect_name =
                         (uu___178_17351.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ = result_typ;
                       FStar_Syntax_Syntax.effect_args = effect_args;
                       FStar_Syntax_Syntax.flags = flags1
                     }));
               FStar_Syntax_Syntax.pos =
                 (uu___177_17348.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___177_17348.FStar_Syntax_Syntax.vars)
             })

and (norm_binder :
  cfg -> env -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder) =
  fun cfg  ->
    fun env  ->
      fun uu____17354  ->
        match uu____17354 with
        | (x,imp) ->
            let uu____17357 =
              let uu___179_17358 = x  in
              let uu____17359 = norm cfg env [] x.FStar_Syntax_Syntax.sort
                 in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___179_17358.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___179_17358.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____17359
              }  in
            (uu____17357, imp)

and (norm_binders :
  cfg -> env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders) =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____17365 =
          FStar_List.fold_left
            (fun uu____17383  ->
               fun b  ->
                 match uu____17383 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b  in
                     ((b1 :: nbs'), (dummy :: env1))) ([], env) bs
           in
        match uu____17365 with | (nbs,uu____17423) -> FStar_List.rev nbs

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
            let uu____17439 =
              let uu___180_17440 = rc  in
              let uu____17441 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (norm cfg env [])
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___180_17440.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____17441;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___180_17440.FStar_Syntax_Syntax.residual_flags)
              }  in
            FStar_Pervasives_Native.Some uu____17439
        | uu____17448 -> lopt

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
            (let uu____17469 = FStar_Syntax_Print.term_to_string tm  in
             let uu____17470 = FStar_Syntax_Print.term_to_string tm'  in
             FStar_Util.print3 "%sSimplified\n\t%s to\n\t%s\n"
               (if (cfg.steps).simplify then "" else "NOT ") uu____17469
               uu____17470)
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
          let uu____17490 =
            FStar_All.pipe_left Prims.op_Negation (cfg.steps).simplify  in
          if uu____17490
          then tm1
          else
            (let w t =
               let uu___181_17504 = t  in
               {
                 FStar_Syntax_Syntax.n =
                   (uu___181_17504.FStar_Syntax_Syntax.n);
                 FStar_Syntax_Syntax.pos = (tm1.FStar_Syntax_Syntax.pos);
                 FStar_Syntax_Syntax.vars =
                   (uu___181_17504.FStar_Syntax_Syntax.vars)
               }  in
             let simp_t t =
               let uu____17515 =
                 let uu____17516 = FStar_Syntax_Util.unmeta t  in
                 uu____17516.FStar_Syntax_Syntax.n  in
               match uu____17515 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_Pervasives_Native.Some true
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.false_lid
                   -> FStar_Pervasives_Native.Some false
               | uu____17523 -> FStar_Pervasives_Native.None  in
             let rec args_are_binders args bs =
               match (args, bs) with
               | ((t,uu____17572)::args1,(bv,uu____17575)::bs1) ->
                   let uu____17609 =
                     let uu____17610 = FStar_Syntax_Subst.compress t  in
                     uu____17610.FStar_Syntax_Syntax.n  in
                   (match uu____17609 with
                    | FStar_Syntax_Syntax.Tm_name bv' ->
                        (FStar_Syntax_Syntax.bv_eq bv bv') &&
                          (args_are_binders args1 bs1)
                    | uu____17614 -> false)
               | ([],[]) -> true
               | (uu____17635,uu____17636) -> false  in
             let is_applied bs t =
               let uu____17676 = FStar_Syntax_Util.head_and_args' t  in
               match uu____17676 with
               | (hd1,args) ->
                   let uu____17709 =
                     let uu____17710 = FStar_Syntax_Subst.compress hd1  in
                     uu____17710.FStar_Syntax_Syntax.n  in
                   (match uu____17709 with
                    | FStar_Syntax_Syntax.Tm_name bv when
                        args_are_binders args bs ->
                        FStar_Pervasives_Native.Some bv
                    | uu____17716 -> FStar_Pervasives_Native.None)
                in
             let is_applied_maybe_squashed bs t =
               let uu____17732 = FStar_Syntax_Util.is_squash t  in
               match uu____17732 with
               | FStar_Pervasives_Native.Some (uu____17743,t') ->
                   is_applied bs t'
               | uu____17755 ->
                   let uu____17764 = FStar_Syntax_Util.is_auto_squash t  in
                   (match uu____17764 with
                    | FStar_Pervasives_Native.Some (uu____17775,t') ->
                        is_applied bs t'
                    | uu____17787 -> is_applied bs t)
                in
             let is_quantified_const phi =
               let uu____17806 =
                 FStar_Syntax_Util.destruct_typ_as_formula phi  in
               match uu____17806 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
                   (lid,(p,uu____17813)::(q,uu____17815)::[])) when
                   FStar_Ident.lid_equals lid FStar_Parser_Const.imp_lid ->
                   let uu____17850 =
                     FStar_Syntax_Util.destruct_typ_as_formula p  in
                   (match uu____17850 with
                    | FStar_Pervasives_Native.None  ->
                        let uu____17855 =
                          let uu____17856 = FStar_Syntax_Subst.compress p  in
                          uu____17856.FStar_Syntax_Syntax.n  in
                        (match uu____17855 with
                         | FStar_Syntax_Syntax.Tm_bvar bv ->
                             let uu____17862 =
                               FStar_Syntax_Subst.subst
                                 [FStar_Syntax_Syntax.NT
                                    (bv, FStar_Syntax_Util.t_true)] q
                                in
                             FStar_Pervasives_Native.Some uu____17862
                         | uu____17863 -> FStar_Pervasives_Native.None)
                    | FStar_Pervasives_Native.Some
                        (FStar_Syntax_Util.BaseConn
                        (lid1,(p1,uu____17866)::[])) when
                        FStar_Ident.lid_equals lid1
                          FStar_Parser_Const.not_lid
                        ->
                        let uu____17891 =
                          let uu____17892 = FStar_Syntax_Subst.compress p1
                             in
                          uu____17892.FStar_Syntax_Syntax.n  in
                        (match uu____17891 with
                         | FStar_Syntax_Syntax.Tm_bvar bv ->
                             let uu____17898 =
                               FStar_Syntax_Subst.subst
                                 [FStar_Syntax_Syntax.NT
                                    (bv, FStar_Syntax_Util.t_false)] q
                                in
                             FStar_Pervasives_Native.Some uu____17898
                         | uu____17899 -> FStar_Pervasives_Native.None)
                    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
                        (bs,pats,phi1)) ->
                        let uu____17903 =
                          FStar_Syntax_Util.destruct_typ_as_formula phi1  in
                        (match uu____17903 with
                         | FStar_Pervasives_Native.None  ->
                             let uu____17908 =
                               is_applied_maybe_squashed bs phi1  in
                             (match uu____17908 with
                              | FStar_Pervasives_Native.Some bv ->
                                  let ftrue =
                                    FStar_Syntax_Util.abs bs
                                      FStar_Syntax_Util.t_true
                                      (FStar_Pervasives_Native.Some
                                         (FStar_Syntax_Util.residual_tot
                                            FStar_Syntax_Util.ktype0))
                                     in
                                  let uu____17915 =
                                    FStar_Syntax_Subst.subst
                                      [FStar_Syntax_Syntax.NT (bv, ftrue)] q
                                     in
                                  FStar_Pervasives_Native.Some uu____17915
                              | FStar_Pervasives_Native.None  ->
                                  FStar_Pervasives_Native.None)
                         | FStar_Pervasives_Native.Some
                             (FStar_Syntax_Util.BaseConn
                             (lid1,(p1,uu____17918)::[])) when
                             FStar_Ident.lid_equals lid1
                               FStar_Parser_Const.not_lid
                             ->
                             let uu____17943 =
                               is_applied_maybe_squashed bs p1  in
                             (match uu____17943 with
                              | FStar_Pervasives_Native.Some bv ->
                                  let ffalse =
                                    FStar_Syntax_Util.abs bs
                                      FStar_Syntax_Util.t_false
                                      (FStar_Pervasives_Native.Some
                                         (FStar_Syntax_Util.residual_tot
                                            FStar_Syntax_Util.ktype0))
                                     in
                                  let uu____17950 =
                                    FStar_Syntax_Subst.subst
                                      [FStar_Syntax_Syntax.NT (bv, ffalse)] q
                                     in
                                  FStar_Pervasives_Native.Some uu____17950
                              | uu____17951 -> FStar_Pervasives_Native.None)
                         | uu____17954 -> FStar_Pervasives_Native.None)
                    | uu____17957 -> FStar_Pervasives_Native.None)
               | uu____17960 -> FStar_Pervasives_Native.None  in
             let is_const_match phi =
               let uu____17973 =
                 let uu____17974 = FStar_Syntax_Subst.compress phi  in
                 uu____17974.FStar_Syntax_Syntax.n  in
               match uu____17973 with
               | FStar_Syntax_Syntax.Tm_match (uu____17979,br::brs) ->
                   let uu____18046 = br  in
                   (match uu____18046 with
                    | (uu____18063,uu____18064,e) ->
                        let r =
                          let uu____18085 = simp_t e  in
                          match uu____18085 with
                          | FStar_Pervasives_Native.None  ->
                              FStar_Pervasives_Native.None
                          | FStar_Pervasives_Native.Some b ->
                              let uu____18091 =
                                FStar_List.for_all
                                  (fun uu____18109  ->
                                     match uu____18109 with
                                     | (uu____18122,uu____18123,e') ->
                                         let uu____18137 = simp_t e'  in
                                         uu____18137 =
                                           (FStar_Pervasives_Native.Some b))
                                  brs
                                 in
                              if uu____18091
                              then FStar_Pervasives_Native.Some b
                              else FStar_Pervasives_Native.None
                           in
                        r)
               | uu____18145 -> FStar_Pervasives_Native.None  in
             let maybe_auto_squash t =
               let uu____18152 = FStar_Syntax_Util.is_sub_singleton t  in
               if uu____18152
               then t
               else
                 FStar_Syntax_Util.mk_auto_squash FStar_Syntax_Syntax.U_zero
                   t
                in
             let squashed_head_un_auto_squash_args t =
               let maybe_un_auto_squash_arg uu____18177 =
                 match uu____18177 with
                 | (t1,q) ->
                     let uu____18190 = FStar_Syntax_Util.is_auto_squash t1
                        in
                     (match uu____18190 with
                      | FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.U_zero ,t2) -> (t2, q)
                      | uu____18218 -> (t1, q))
                  in
               let uu____18227 = FStar_Syntax_Util.head_and_args t  in
               match uu____18227 with
               | (head1,args) ->
                   let args1 = FStar_List.map maybe_un_auto_squash_arg args
                      in
                   FStar_Syntax_Syntax.mk_Tm_app head1 args1
                     FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
                in
             let rec clearly_inhabited ty =
               let uu____18291 =
                 let uu____18292 = FStar_Syntax_Util.unmeta ty  in
                 uu____18292.FStar_Syntax_Syntax.n  in
               match uu____18291 with
               | FStar_Syntax_Syntax.Tm_uinst (t,uu____18296) ->
                   clearly_inhabited t
               | FStar_Syntax_Syntax.Tm_arrow (uu____18301,c) ->
                   clearly_inhabited (FStar_Syntax_Util.comp_result c)
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   let l = FStar_Syntax_Syntax.lid_of_fv fv  in
                   (((FStar_Ident.lid_equals l FStar_Parser_Const.int_lid) ||
                       (FStar_Ident.lid_equals l FStar_Parser_Const.bool_lid))
                      ||
                      (FStar_Ident.lid_equals l FStar_Parser_Const.string_lid))
                     || (FStar_Ident.lid_equals l FStar_Parser_Const.exn_lid)
               | uu____18321 -> false  in
             let simplify1 arg =
               let uu____18346 = simp_t (FStar_Pervasives_Native.fst arg)  in
               (uu____18346, arg)  in
             let uu____18355 = is_quantified_const tm1  in
             match uu____18355 with
             | FStar_Pervasives_Native.Some tm2 ->
                 let uu____18359 = norm cfg env [] tm2  in
                 maybe_simplify_aux cfg env stack uu____18359
             | FStar_Pervasives_Native.None  ->
                 let uu____18360 =
                   let uu____18361 = FStar_Syntax_Subst.compress tm1  in
                   uu____18361.FStar_Syntax_Syntax.n  in
                 (match uu____18360 with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                           ({
                              FStar_Syntax_Syntax.n =
                                FStar_Syntax_Syntax.Tm_fvar fv;
                              FStar_Syntax_Syntax.pos = uu____18365;
                              FStar_Syntax_Syntax.vars = uu____18366;_},uu____18367);
                         FStar_Syntax_Syntax.pos = uu____18368;
                         FStar_Syntax_Syntax.vars = uu____18369;_},args)
                      ->
                      let uu____18395 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid
                         in
                      if uu____18395
                      then
                        let uu____18396 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        (match uu____18396 with
                         | (FStar_Pervasives_Native.Some (true ),uu____18443)::
                             (uu____18444,(arg,uu____18446))::[] ->
                             maybe_auto_squash arg
                         | (uu____18495,(arg,uu____18497))::(FStar_Pervasives_Native.Some
                                                             (true
                                                             ),uu____18498)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____18547)::uu____18548::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____18599::(FStar_Pervasives_Native.Some (false
                                         ),uu____18600)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____18651 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____18665 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid
                            in
                         if uu____18665
                         then
                           let uu____18666 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify1)
                              in
                           match uu____18666 with
                           | (FStar_Pervasives_Native.Some (true
                              ),uu____18713)::uu____18714::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____18765::(FStar_Pervasives_Native.Some (true
                                           ),uu____18766)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false
                              ),uu____18817)::(uu____18818,(arg,uu____18820))::[]
                               -> maybe_auto_squash arg
                           | (uu____18869,(arg,uu____18871))::(FStar_Pervasives_Native.Some
                                                               (false
                                                               ),uu____18872)::[]
                               -> maybe_auto_squash arg
                           | uu____18921 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____18935 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid
                               in
                            if uu____18935
                            then
                              let uu____18936 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify1)
                                 in
                              match uu____18936 with
                              | uu____18983::(FStar_Pervasives_Native.Some
                                              (true ),uu____18984)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false
                                 ),uu____19035)::uu____19036::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true
                                 ),uu____19087)::(uu____19088,(arg,uu____19090))::[]
                                  -> maybe_auto_squash arg
                              | (uu____19139,(p,uu____19141))::(uu____19142,
                                                                (q,uu____19144))::[]
                                  ->
                                  let uu____19191 =
                                    FStar_Syntax_Util.term_eq p q  in
                                  (if uu____19191
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____19193 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____19207 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid
                                  in
                               if uu____19207
                               then
                                 let uu____19208 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify1)
                                    in
                                 match uu____19208 with
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____19255)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____19256)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____19307)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____19308)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____19359)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____19360)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____19411)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____19412)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____19463,(arg,uu____19465))::(FStar_Pervasives_Native.Some
                                                                    (true
                                                                    ),uu____19466)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____19515)::(uu____19516,(arg,uu____19518))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____19567,(arg,uu____19569))::(FStar_Pervasives_Native.Some
                                                                    (false
                                                                    ),uu____19570)::[]
                                     ->
                                     let uu____19619 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____19619
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____19620)::(uu____19621,(arg,uu____19623))::[]
                                     ->
                                     let uu____19672 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____19672
                                 | (uu____19673,(p,uu____19675))::(uu____19676,
                                                                   (q,uu____19678))::[]
                                     ->
                                     let uu____19725 =
                                       FStar_Syntax_Util.term_eq p q  in
                                     (if uu____19725
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____19727 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____19741 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid
                                     in
                                  if uu____19741
                                  then
                                    let uu____19742 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify1)
                                       in
                                    match uu____19742 with
                                    | (FStar_Pervasives_Native.Some (true
                                       ),uu____19789)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false
                                       ),uu____19820)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____19851 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____19865 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid
                                        in
                                     if uu____19865
                                     then
                                       match args with
                                       | (t,uu____19867)::[] ->
                                           let uu____19884 =
                                             let uu____19885 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____19885.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____19884 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____19888::[],body,uu____19890)
                                                ->
                                                let uu____19917 = simp_t body
                                                   in
                                                (match uu____19917 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____19920 -> tm1)
                                            | uu____19923 -> tm1)
                                       | (ty,FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____19925))::(t,uu____19927)::[]
                                           ->
                                           let uu____19966 =
                                             let uu____19967 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____19967.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____19966 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____19970::[],body,uu____19972)
                                                ->
                                                let uu____19999 = simp_t body
                                                   in
                                                (match uu____19999 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false ) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____20002 -> tm1)
                                            | uu____20005 -> tm1)
                                       | uu____20006 -> tm1
                                     else
                                       (let uu____20016 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid
                                           in
                                        if uu____20016
                                        then
                                          match args with
                                          | (t,uu____20018)::[] ->
                                              let uu____20035 =
                                                let uu____20036 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____20036.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____20035 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____20039::[],body,uu____20041)
                                                   ->
                                                   let uu____20068 =
                                                     simp_t body  in
                                                   (match uu____20068 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____20071 -> tm1)
                                               | uu____20074 -> tm1)
                                          | (ty,FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____20076))::(t,uu____20078)::[]
                                              ->
                                              let uu____20117 =
                                                let uu____20118 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____20118.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____20117 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____20121::[],body,uu____20123)
                                                   ->
                                                   let uu____20150 =
                                                     simp_t body  in
                                                   (match uu____20150 with
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
                                                    | uu____20153 -> tm1)
                                               | uu____20156 -> tm1)
                                          | uu____20157 -> tm1
                                        else
                                          (let uu____20167 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid
                                              in
                                           if uu____20167
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____20168;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____20169;_},uu____20170)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____20187;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____20188;_},uu____20189)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____20206 -> tm1
                                           else
                                             (let uu____20216 =
                                                FStar_Syntax_Util.is_auto_squash
                                                  tm1
                                                 in
                                              match uu____20216 with
                                              | FStar_Pervasives_Native.Some
                                                  (FStar_Syntax_Syntax.U_zero
                                                   ,t)
                                                  when
                                                  FStar_Syntax_Util.is_sub_singleton
                                                    t
                                                  -> t
                                              | uu____20236 ->
                                                  reduce_equality cfg env
                                                    stack tm1))))))))
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____20246;
                         FStar_Syntax_Syntax.vars = uu____20247;_},args)
                      ->
                      let uu____20269 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid
                         in
                      if uu____20269
                      then
                        let uu____20270 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        (match uu____20270 with
                         | (FStar_Pervasives_Native.Some (true ),uu____20317)::
                             (uu____20318,(arg,uu____20320))::[] ->
                             maybe_auto_squash arg
                         | (uu____20369,(arg,uu____20371))::(FStar_Pervasives_Native.Some
                                                             (true
                                                             ),uu____20372)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____20421)::uu____20422::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____20473::(FStar_Pervasives_Native.Some (false
                                         ),uu____20474)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____20525 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____20539 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid
                            in
                         if uu____20539
                         then
                           let uu____20540 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify1)
                              in
                           match uu____20540 with
                           | (FStar_Pervasives_Native.Some (true
                              ),uu____20587)::uu____20588::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____20639::(FStar_Pervasives_Native.Some (true
                                           ),uu____20640)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false
                              ),uu____20691)::(uu____20692,(arg,uu____20694))::[]
                               -> maybe_auto_squash arg
                           | (uu____20743,(arg,uu____20745))::(FStar_Pervasives_Native.Some
                                                               (false
                                                               ),uu____20746)::[]
                               -> maybe_auto_squash arg
                           | uu____20795 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____20809 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid
                               in
                            if uu____20809
                            then
                              let uu____20810 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify1)
                                 in
                              match uu____20810 with
                              | uu____20857::(FStar_Pervasives_Native.Some
                                              (true ),uu____20858)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false
                                 ),uu____20909)::uu____20910::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true
                                 ),uu____20961)::(uu____20962,(arg,uu____20964))::[]
                                  -> maybe_auto_squash arg
                              | (uu____21013,(p,uu____21015))::(uu____21016,
                                                                (q,uu____21018))::[]
                                  ->
                                  let uu____21065 =
                                    FStar_Syntax_Util.term_eq p q  in
                                  (if uu____21065
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____21067 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____21081 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid
                                  in
                               if uu____21081
                               then
                                 let uu____21082 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify1)
                                    in
                                 match uu____21082 with
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____21129)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____21130)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____21181)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____21182)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____21233)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____21234)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____21285)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____21286)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____21337,(arg,uu____21339))::(FStar_Pervasives_Native.Some
                                                                    (true
                                                                    ),uu____21340)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____21389)::(uu____21390,(arg,uu____21392))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____21441,(arg,uu____21443))::(FStar_Pervasives_Native.Some
                                                                    (false
                                                                    ),uu____21444)::[]
                                     ->
                                     let uu____21493 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____21493
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____21494)::(uu____21495,(arg,uu____21497))::[]
                                     ->
                                     let uu____21546 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____21546
                                 | (uu____21547,(p,uu____21549))::(uu____21550,
                                                                   (q,uu____21552))::[]
                                     ->
                                     let uu____21599 =
                                       FStar_Syntax_Util.term_eq p q  in
                                     (if uu____21599
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____21601 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____21615 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid
                                     in
                                  if uu____21615
                                  then
                                    let uu____21616 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify1)
                                       in
                                    match uu____21616 with
                                    | (FStar_Pervasives_Native.Some (true
                                       ),uu____21663)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false
                                       ),uu____21694)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____21725 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____21739 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid
                                        in
                                     if uu____21739
                                     then
                                       match args with
                                       | (t,uu____21741)::[] ->
                                           let uu____21758 =
                                             let uu____21759 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____21759.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____21758 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____21762::[],body,uu____21764)
                                                ->
                                                let uu____21791 = simp_t body
                                                   in
                                                (match uu____21791 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____21794 -> tm1)
                                            | uu____21797 -> tm1)
                                       | (ty,FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____21799))::(t,uu____21801)::[]
                                           ->
                                           let uu____21840 =
                                             let uu____21841 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____21841.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____21840 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____21844::[],body,uu____21846)
                                                ->
                                                let uu____21873 = simp_t body
                                                   in
                                                (match uu____21873 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false ) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____21876 -> tm1)
                                            | uu____21879 -> tm1)
                                       | uu____21880 -> tm1
                                     else
                                       (let uu____21890 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid
                                           in
                                        if uu____21890
                                        then
                                          match args with
                                          | (t,uu____21892)::[] ->
                                              let uu____21909 =
                                                let uu____21910 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____21910.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____21909 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____21913::[],body,uu____21915)
                                                   ->
                                                   let uu____21942 =
                                                     simp_t body  in
                                                   (match uu____21942 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____21945 -> tm1)
                                               | uu____21948 -> tm1)
                                          | (ty,FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____21950))::(t,uu____21952)::[]
                                              ->
                                              let uu____21991 =
                                                let uu____21992 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____21992.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____21991 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____21995::[],body,uu____21997)
                                                   ->
                                                   let uu____22024 =
                                                     simp_t body  in
                                                   (match uu____22024 with
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
                                                    | uu____22027 -> tm1)
                                               | uu____22030 -> tm1)
                                          | uu____22031 -> tm1
                                        else
                                          (let uu____22041 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid
                                              in
                                           if uu____22041
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____22042;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____22043;_},uu____22044)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____22061;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____22062;_},uu____22063)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____22080 -> tm1
                                           else
                                             (let uu____22090 =
                                                FStar_Syntax_Util.is_auto_squash
                                                  tm1
                                                 in
                                              match uu____22090 with
                                              | FStar_Pervasives_Native.Some
                                                  (FStar_Syntax_Syntax.U_zero
                                                   ,t)
                                                  when
                                                  FStar_Syntax_Util.is_sub_singleton
                                                    t
                                                  -> t
                                              | uu____22110 ->
                                                  reduce_equality cfg env
                                                    stack tm1))))))))
                  | FStar_Syntax_Syntax.Tm_refine (bv,t) ->
                      let uu____22125 = simp_t t  in
                      (match uu____22125 with
                       | FStar_Pervasives_Native.Some (true ) ->
                           bv.FStar_Syntax_Syntax.sort
                       | FStar_Pervasives_Native.Some (false ) -> tm1
                       | FStar_Pervasives_Native.None  -> tm1)
                  | FStar_Syntax_Syntax.Tm_match uu____22128 ->
                      let uu____22151 = is_const_match tm1  in
                      (match uu____22151 with
                       | FStar_Pervasives_Native.Some (true ) ->
                           w FStar_Syntax_Util.t_true
                       | FStar_Pervasives_Native.Some (false ) ->
                           w FStar_Syntax_Util.t_false
                       | FStar_Pervasives_Native.None  -> tm1)
                  | uu____22154 -> tm1))

and (rebuild :
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          log cfg
            (fun uu____22164  ->
               (let uu____22166 = FStar_Syntax_Print.tag_of_term t  in
                let uu____22167 = FStar_Syntax_Print.term_to_string t  in
                let uu____22168 =
                  FStar_Util.string_of_int (FStar_List.length env)  in
                let uu____22175 =
                  let uu____22176 =
                    let uu____22179 = firstn (Prims.parse_int "4") stack  in
                    FStar_All.pipe_left FStar_Pervasives_Native.fst
                      uu____22179
                     in
                  stack_to_string uu____22176  in
                FStar_Util.print4
                  ">>> %s\nRebuild %s with %s env elements and top of the stack %s \n"
                  uu____22166 uu____22167 uu____22168 uu____22175);
               (let uu____22202 =
                  FStar_TypeChecker_Env.debug cfg.tcenv
                    (FStar_Options.Other "NormRebuild")
                   in
                if uu____22202
                then
                  let uu____22203 = FStar_Syntax_Util.unbound_variables t  in
                  match uu____22203 with
                  | [] -> ()
                  | bvs ->
                      ((let uu____22210 = FStar_Syntax_Print.tag_of_term t
                           in
                        let uu____22211 = FStar_Syntax_Print.term_to_string t
                           in
                        let uu____22212 =
                          let uu____22213 =
                            FStar_All.pipe_right bvs
                              (FStar_List.map FStar_Syntax_Print.bv_to_string)
                             in
                          FStar_All.pipe_right uu____22213
                            (FStar_String.concat ", ")
                           in
                        FStar_Util.print3
                          "!!! Rebuild (%s) %s, free vars=%s\n" uu____22210
                          uu____22211 uu____22212);
                       failwith "DIE!")
                else ()));
          (let t1 = maybe_simplify cfg env stack t  in
           match stack with
           | [] -> t1
           | (Debug (tm,time_then))::stack1 ->
               (if (cfg.debug).print_normalized
                then
                  (let time_now = FStar_Util.now ()  in
                   let uu____22231 =
                     let uu____22232 =
                       let uu____22233 =
                         FStar_Util.time_diff time_then time_now  in
                       FStar_Pervasives_Native.snd uu____22233  in
                     FStar_Util.string_of_int uu____22232  in
                   let uu____22238 = FStar_Syntax_Print.term_to_string tm  in
                   let uu____22239 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.print3 "Normalized (%s ms) %s\n\tto %s\n"
                     uu____22231 uu____22238 uu____22239)
                else ();
                rebuild cfg env stack1 t1)
           | (Cfg cfg1)::stack1 -> rebuild cfg1 env stack1 t1
           | (Meta (uu____22245,m,r))::stack1 ->
               let t2 = mk (FStar_Syntax_Syntax.Tm_meta (t1, m)) r  in
               rebuild cfg env stack1 t2
           | (MemoLazy r)::stack1 ->
               (set_memo cfg r (env, t1);
                log cfg
                  (fun uu____22294  ->
                     let uu____22295 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 "\tSet memo %s\n" uu____22295);
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
               let uu____22331 =
                 let uu___182_22332 = FStar_Syntax_Util.abs bs1 t1 lopt1  in
                 {
                   FStar_Syntax_Syntax.n =
                     (uu___182_22332.FStar_Syntax_Syntax.n);
                   FStar_Syntax_Syntax.pos = r;
                   FStar_Syntax_Syntax.vars =
                     (uu___182_22332.FStar_Syntax_Syntax.vars)
                 }  in
               rebuild cfg env stack1 uu____22331
           | (Arg (Univ uu____22333,uu____22334,uu____22335))::uu____22336 ->
               failwith "Impossible"
           | (Arg (Dummy ,uu____22339,uu____22340))::uu____22341 ->
               failwith "Impossible"
           | (UnivArgs (us,r))::stack1 ->
               let t2 = FStar_Syntax_Syntax.mk_Tm_uinst t1 us  in
               rebuild cfg env stack1 t2
           | (Arg (Clos (env_arg,tm,uu____22356,uu____22357),aq,r))::stack1
               when
               let uu____22407 = head_of t1  in
               FStar_Syntax_Util.is_fstar_tactics_by_tactic uu____22407 ->
               let t2 =
                 let uu____22411 =
                   let uu____22416 =
                     let uu____22417 = closure_as_term cfg env_arg tm  in
                     (uu____22417, aq)  in
                   FStar_Syntax_Syntax.extend_app t1 uu____22416  in
                 uu____22411 FStar_Pervasives_Native.None r  in
               rebuild cfg env stack1 t2
           | (Arg (Clos (env_arg,tm,m,uu____22423),aq,r))::stack1 ->
               (log cfg
                  (fun uu____22476  ->
                     let uu____22477 = FStar_Syntax_Print.term_to_string tm
                        in
                     FStar_Util.print1 "Rebuilding with arg %s\n" uu____22477);
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
                  (let uu____22487 = FStar_ST.op_Bang m  in
                   match uu____22487 with
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
                   | FStar_Pervasives_Native.Some (uu____22628,a) ->
                       let t2 =
                         FStar_Syntax_Syntax.extend_app t1 (a, aq)
                           FStar_Pervasives_Native.None r
                          in
                       rebuild cfg env_arg stack1 t2))
           | (App (env1,head1,aq,r))::stack' when should_reify cfg stack ->
               let t0 = t1  in
               let fallback msg uu____22679 =
                 log cfg
                   (fun uu____22683  ->
                      let uu____22684 = FStar_Syntax_Print.term_to_string t1
                         in
                      FStar_Util.print2 "Not reifying%s: %s\n" msg
                        uu____22684);
                 (let t2 =
                    FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                      FStar_Pervasives_Native.None r
                     in
                  rebuild cfg env1 stack' t2)
                  in
               let uu____22688 =
                 let uu____22689 = FStar_Syntax_Subst.compress t1  in
                 uu____22689.FStar_Syntax_Syntax.n  in
               (match uu____22688 with
                | FStar_Syntax_Syntax.Tm_meta
                    (t2,FStar_Syntax_Syntax.Meta_monadic (m,ty)) ->
                    do_reify_monadic (fallback " (1)") cfg env1 stack t2 m ty
                | FStar_Syntax_Syntax.Tm_meta
                    (t2,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,ty))
                    ->
                    let lifted =
                      let uu____22716 = closure_as_term cfg env1 ty  in
                      reify_lift cfg t2 msrc mtgt uu____22716  in
                    (log cfg
                       (fun uu____22720  ->
                          let uu____22721 =
                            FStar_Syntax_Print.term_to_string lifted  in
                          FStar_Util.print1 "Reified lift to (1): %s\n"
                            uu____22721);
                     (let uu____22722 = FStar_List.tl stack  in
                      norm cfg env1 uu____22722 lifted))
                | FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reflect uu____22723);
                       FStar_Syntax_Syntax.pos = uu____22724;
                       FStar_Syntax_Syntax.vars = uu____22725;_},(e,uu____22727)::[])
                    -> norm cfg env1 stack' e
                | FStar_Syntax_Syntax.Tm_app uu____22756 when
                    (cfg.steps).primops ->
                    let uu____22771 = FStar_Syntax_Util.head_and_args t1  in
                    (match uu____22771 with
                     | (hd1,args) ->
                         let uu____22808 =
                           let uu____22809 = FStar_Syntax_Util.un_uinst hd1
                              in
                           uu____22809.FStar_Syntax_Syntax.n  in
                         (match uu____22808 with
                          | FStar_Syntax_Syntax.Tm_fvar fv ->
                              let uu____22813 = find_prim_step cfg fv  in
                              (match uu____22813 with
                               | FStar_Pervasives_Native.Some
                                   { name = uu____22816; arity = uu____22817;
                                     auto_reflect =
                                       FStar_Pervasives_Native.Some n1;
                                     strong_reduction_ok = uu____22819;
                                     requires_binder_substitution =
                                       uu____22820;
                                     interpretation = uu____22821;_}
                                   when (FStar_List.length args) = n1 ->
                                   norm cfg env1 stack' t1
                               | uu____22836 -> fallback " (3)" ())
                          | uu____22839 -> fallback " (4)" ()))
                | uu____22840 -> fallback " (2)" ())
           | (App (env1,head1,aq,r))::stack1 ->
               let t2 =
                 FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                   FStar_Pervasives_Native.None r
                  in
               rebuild cfg env1 stack1 t2
           | (Match (env',branches,cfg1,r))::stack1 ->
               (log cfg1
                  (fun uu____22861  ->
                     let uu____22862 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1
                       "Rebuilding with match, scrutinee is %s ...\n"
                       uu____22862);
                (let scrutinee_env = env  in
                 let env1 = env'  in
                 let scrutinee = t1  in
                 let norm_and_rebuild_match uu____22871 =
                   log cfg1
                     (fun uu____22876  ->
                        let uu____22877 =
                          FStar_Syntax_Print.term_to_string scrutinee  in
                        let uu____22878 =
                          let uu____22879 =
                            FStar_All.pipe_right branches
                              (FStar_List.map
                                 (fun uu____22896  ->
                                    match uu____22896 with
                                    | (p,uu____22906,uu____22907) ->
                                        FStar_Syntax_Print.pat_to_string p))
                             in
                          FStar_All.pipe_right uu____22879
                            (FStar_String.concat "\n\t")
                           in
                        FStar_Util.print2
                          "match is irreducible: scrutinee=%s\nbranches=%s\n"
                          uu____22877 uu____22878);
                   (let whnf = (cfg1.steps).weak || (cfg1.steps).hnf  in
                    let cfg_exclude_zeta =
                      let new_delta =
                        FStar_All.pipe_right cfg1.delta_level
                          (FStar_List.filter
                             (fun uu___91_22924  ->
                                match uu___91_22924 with
                                | FStar_TypeChecker_Env.Inlining  -> true
                                | FStar_TypeChecker_Env.Eager_unfolding_only 
                                    -> true
                                | uu____22925 -> false))
                         in
                      let steps =
                        let uu___183_22927 = cfg1.steps  in
                        {
                          beta = (uu___183_22927.beta);
                          iota = (uu___183_22927.iota);
                          zeta = false;
                          weak = (uu___183_22927.weak);
                          hnf = (uu___183_22927.hnf);
                          primops = (uu___183_22927.primops);
                          do_not_unfold_pure_lets =
                            (uu___183_22927.do_not_unfold_pure_lets);
                          unfold_until = FStar_Pervasives_Native.None;
                          unfold_only = FStar_Pervasives_Native.None;
                          unfold_fully = (uu___183_22927.unfold_fully);
                          unfold_attr = FStar_Pervasives_Native.None;
                          unfold_tac = false;
                          pure_subterms_within_computations =
                            (uu___183_22927.pure_subterms_within_computations);
                          simplify = (uu___183_22927.simplify);
                          erase_universes = (uu___183_22927.erase_universes);
                          allow_unbound_universes =
                            (uu___183_22927.allow_unbound_universes);
                          reify_ = (uu___183_22927.reify_);
                          compress_uvars = (uu___183_22927.compress_uvars);
                          no_full_norm = (uu___183_22927.no_full_norm);
                          check_no_uvars = (uu___183_22927.check_no_uvars);
                          unmeta = (uu___183_22927.unmeta);
                          unascribe = (uu___183_22927.unascribe);
                          in_full_norm_request =
                            (uu___183_22927.in_full_norm_request)
                        }  in
                      let uu___184_22932 = cfg1  in
                      {
                        steps;
                        tcenv = (uu___184_22932.tcenv);
                        debug = (uu___184_22932.debug);
                        delta_level = new_delta;
                        primitive_steps = (uu___184_22932.primitive_steps);
                        strong = true;
                        memoize_lazy = (uu___184_22932.memoize_lazy);
                        normalize_pure_lets =
                          (uu___184_22932.normalize_pure_lets)
                      }  in
                    let norm_or_whnf env2 t2 =
                      if whnf
                      then closure_as_term cfg_exclude_zeta env2 t2
                      else norm cfg_exclude_zeta env2 [] t2  in
                    let rec norm_pat env2 p =
                      match p.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_constant uu____22972 ->
                          (p, env2)
                      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                          let uu____22993 =
                            FStar_All.pipe_right pats
                              (FStar_List.fold_left
                                 (fun uu____23053  ->
                                    fun uu____23054  ->
                                      match (uu____23053, uu____23054) with
                                      | ((pats1,env3),(p1,b)) ->
                                          let uu____23145 = norm_pat env3 p1
                                             in
                                          (match uu____23145 with
                                           | (p2,env4) ->
                                               (((p2, b) :: pats1), env4)))
                                 ([], env2))
                             in
                          (match uu____22993 with
                           | (pats1,env3) ->
                               ((let uu___185_23227 = p  in
                                 {
                                   FStar_Syntax_Syntax.v =
                                     (FStar_Syntax_Syntax.Pat_cons
                                        (fv, (FStar_List.rev pats1)));
                                   FStar_Syntax_Syntax.p =
                                     (uu___185_23227.FStar_Syntax_Syntax.p)
                                 }), env3))
                      | FStar_Syntax_Syntax.Pat_var x ->
                          let x1 =
                            let uu___186_23246 = x  in
                            let uu____23247 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___186_23246.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___186_23246.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____23247
                            }  in
                          ((let uu___187_23261 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_var x1);
                              FStar_Syntax_Syntax.p =
                                (uu___187_23261.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_wild x ->
                          let x1 =
                            let uu___188_23272 = x  in
                            let uu____23273 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___188_23272.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___188_23272.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____23273
                            }  in
                          ((let uu___189_23287 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_wild x1);
                              FStar_Syntax_Syntax.p =
                                (uu___189_23287.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                          let x1 =
                            let uu___190_23303 = x  in
                            let uu____23304 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___190_23303.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___190_23303.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____23304
                            }  in
                          let t3 = norm_or_whnf env2 t2  in
                          ((let uu___191_23311 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_dot_term (x1, t3));
                              FStar_Syntax_Syntax.p =
                                (uu___191_23311.FStar_Syntax_Syntax.p)
                            }), env2)
                       in
                    let branches1 =
                      match env1 with
                      | [] when whnf -> branches
                      | uu____23321 ->
                          FStar_All.pipe_right branches
                            (FStar_List.map
                               (fun branch1  ->
                                  let uu____23335 =
                                    FStar_Syntax_Subst.open_branch branch1
                                     in
                                  match uu____23335 with
                                  | (p,wopt,e) ->
                                      let uu____23355 = norm_pat env1 p  in
                                      (match uu____23355 with
                                       | (p1,env2) ->
                                           let wopt1 =
                                             match wopt with
                                             | FStar_Pervasives_Native.None 
                                                 ->
                                                 FStar_Pervasives_Native.None
                                             | FStar_Pervasives_Native.Some w
                                                 ->
                                                 let uu____23380 =
                                                   norm_or_whnf env2 w  in
                                                 FStar_Pervasives_Native.Some
                                                   uu____23380
                                              in
                                           let e1 = norm_or_whnf env2 e  in
                                           FStar_Syntax_Util.branch
                                             (p1, wopt1, e1))))
                       in
                    let scrutinee1 =
                      let uu____23387 =
                        (((cfg1.steps).iota &&
                            (Prims.op_Negation (cfg1.steps).weak))
                           && (Prims.op_Negation (cfg1.steps).compress_uvars))
                          && (maybe_weakly_reduced scrutinee)
                         in
                      if uu____23387
                      then norm cfg1 scrutinee_env [] scrutinee
                      else scrutinee  in
                    let uu____23389 =
                      mk
                        (FStar_Syntax_Syntax.Tm_match (scrutinee1, branches1))
                        r
                       in
                    rebuild cfg1 env1 stack1 uu____23389)
                    in
                 let rec is_cons head1 =
                   let uu____23396 =
                     let uu____23397 = FStar_Syntax_Subst.compress head1  in
                     uu____23397.FStar_Syntax_Syntax.n  in
                   match uu____23396 with
                   | FStar_Syntax_Syntax.Tm_uinst (h,uu____23401) ->
                       is_cons h
                   | FStar_Syntax_Syntax.Tm_constant uu____23406 -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____23407;
                         FStar_Syntax_Syntax.fv_delta = uu____23408;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Data_ctor );_}
                       -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____23409;
                         FStar_Syntax_Syntax.fv_delta = uu____23410;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Record_ctor uu____23411);_}
                       -> true
                   | uu____23418 -> false  in
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
                   let uu____23579 =
                     FStar_Syntax_Util.head_and_args scrutinee1  in
                   match uu____23579 with
                   | (head1,args) ->
                       (match p.FStar_Syntax_Syntax.v with
                        | FStar_Syntax_Syntax.Pat_var bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_wild bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_dot_term uu____23666 ->
                            FStar_Util.Inl []
                        | FStar_Syntax_Syntax.Pat_constant s ->
                            (match scrutinee1.FStar_Syntax_Syntax.n with
                             | FStar_Syntax_Syntax.Tm_constant s' when
                                 FStar_Const.eq_const s s' ->
                                 FStar_Util.Inl []
                             | uu____23705 ->
                                 let uu____23706 =
                                   let uu____23707 = is_cons head1  in
                                   Prims.op_Negation uu____23707  in
                                 FStar_Util.Inr uu____23706)
                        | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                            let uu____23732 =
                              let uu____23733 =
                                FStar_Syntax_Util.un_uinst head1  in
                              uu____23733.FStar_Syntax_Syntax.n  in
                            (match uu____23732 with
                             | FStar_Syntax_Syntax.Tm_fvar fv' when
                                 FStar_Syntax_Syntax.fv_eq fv fv' ->
                                 matches_args [] args arg_pats
                             | uu____23751 ->
                                 let uu____23752 =
                                   let uu____23753 = is_cons head1  in
                                   Prims.op_Negation uu____23753  in
                                 FStar_Util.Inr uu____23752))
                 
                 and matches_args out a p =
                   match (a, p) with
                   | ([],[]) -> FStar_Util.Inl out
                   | ((t2,uu____23822)::rest_a,(p1,uu____23825)::rest_p) ->
                       let uu____23869 = matches_pat t2 p1  in
                       (match uu____23869 with
                        | FStar_Util.Inl s ->
                            matches_args (FStar_List.append out s) rest_a
                              rest_p
                        | m -> m)
                   | uu____23918 -> FStar_Util.Inr false
                  in
                 let rec matches scrutinee1 p =
                   match p with
                   | [] -> norm_and_rebuild_match ()
                   | (p1,wopt,b)::rest ->
                       let uu____24028 = matches_pat scrutinee1 p1  in
                       (match uu____24028 with
                        | FStar_Util.Inr (false ) -> matches scrutinee1 rest
                        | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                        | FStar_Util.Inl s ->
                            (log cfg1
                               (fun uu____24068  ->
                                  let uu____24069 =
                                    FStar_Syntax_Print.pat_to_string p1  in
                                  let uu____24070 =
                                    let uu____24071 =
                                      FStar_List.map
                                        (fun uu____24081  ->
                                           match uu____24081 with
                                           | (uu____24086,t2) ->
                                               FStar_Syntax_Print.term_to_string
                                                 t2) s
                                       in
                                    FStar_All.pipe_right uu____24071
                                      (FStar_String.concat "; ")
                                     in
                                  FStar_Util.print2
                                    "Matches pattern %s with subst = %s\n"
                                    uu____24069 uu____24070);
                             (let env0 = env1  in
                              let env2 =
                                FStar_List.fold_left
                                  (fun env2  ->
                                     fun uu____24118  ->
                                       match uu____24118 with
                                       | (bv,t2) ->
                                           let uu____24141 =
                                             let uu____24148 =
                                               let uu____24151 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   bv
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 uu____24151
                                                in
                                             let uu____24152 =
                                               let uu____24153 =
                                                 let uu____24184 =
                                                   FStar_Util.mk_ref
                                                     (FStar_Pervasives_Native.Some
                                                        ([], t2))
                                                    in
                                                 ([], t2, uu____24184, false)
                                                  in
                                               Clos uu____24153  in
                                             (uu____24148, uu____24152)  in
                                           uu____24141 :: env2) env1 s
                                 in
                              let uu____24301 = guard_when_clause wopt b rest
                                 in
                              norm cfg1 env2 stack1 uu____24301)))
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
    let uu____24328 =
      let uu____24331 = FStar_ST.op_Bang plugins  in p :: uu____24331  in
    FStar_ST.op_Colon_Equals plugins uu____24328  in
  let retrieve uu____24439 = FStar_ST.op_Bang plugins  in
  (register, retrieve) 
let (register_plugin : primitive_step -> unit) =
  fun p  -> FStar_Pervasives_Native.fst plugins p 
let (retrieve_plugins : unit -> primitive_step Prims.list) =
  fun uu____24516  -> FStar_Pervasives_Native.snd plugins () 
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
               (fun uu___92_24557  ->
                  match uu___92_24557 with
                  | UnfoldUntil k -> [FStar_TypeChecker_Env.Unfold k]
                  | Eager_unfolding  ->
                      [FStar_TypeChecker_Env.Eager_unfolding_only]
                  | Inlining  -> [FStar_TypeChecker_Env.Inlining]
                  | UnfoldTac  -> [FStar_TypeChecker_Env.UnfoldTac]
                  | uu____24561 -> []))
           in
        let d1 =
          match d with
          | [] -> [FStar_TypeChecker_Env.NoDelta]
          | uu____24567 -> d  in
        let uu____24570 = to_fsteps s  in
        let uu____24571 =
          let uu____24572 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Norm")  in
          let uu____24573 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Primops")  in
          let uu____24574 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "380")  in
          let uu____24575 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "NormDelayed")
             in
          let uu____24576 =
            FStar_TypeChecker_Env.debug e
              (FStar_Options.Other "print_normalized_terms")
             in
          {
            gen = uu____24572;
            primop = uu____24573;
            b380 = uu____24574;
            norm_delayed = uu____24575;
            print_normalized = uu____24576
          }  in
        let uu____24577 =
          let uu____24580 =
            let uu____24583 = retrieve_plugins ()  in
            FStar_List.append uu____24583 psteps  in
          add_steps built_in_primitive_steps uu____24580  in
        let uu____24586 =
          (FStar_Options.normalize_pure_terms_for_extraction ()) ||
            (let uu____24588 =
               FStar_All.pipe_right s
                 (FStar_List.contains PureSubtermsWithinComputations)
                in
             Prims.op_Negation uu____24588)
           in
        {
          steps = uu____24570;
          tcenv = e;
          debug = uu____24571;
          delta_level = d1;
          primitive_steps = uu____24577;
          strong = false;
          memoize_lazy = true;
          normalize_pure_lets = uu____24586
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
      fun t  -> let uu____24670 = config s e  in norm_comp uu____24670 [] t
  
let (normalize_universe :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun u  ->
      let uu____24687 = config [] env  in norm_universe uu____24687 [] u
  
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
        let uu____24711 = norm cfg [] [] t  in
        FStar_Syntax_Util.non_informative uu____24711  in
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____24718 -> c
      | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
          let uu___192_24737 = c  in
          {
            FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
            FStar_Syntax_Syntax.pos =
              (uu___192_24737.FStar_Syntax_Syntax.pos);
            FStar_Syntax_Syntax.vars =
              (uu___192_24737.FStar_Syntax_Syntax.vars)
          }
      | FStar_Syntax_Syntax.Comp ct ->
          let l =
            FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
              ct.FStar_Syntax_Syntax.effect_name
             in
          let uu____24744 =
            (FStar_Syntax_Util.is_ghost_effect l) &&
              (non_info ct.FStar_Syntax_Syntax.result_typ)
             in
          if uu____24744
          then
            let ct1 =
              let uu____24746 =
                downgrade_ghost_effect_name
                  ct.FStar_Syntax_Syntax.effect_name
                 in
              match uu____24746 with
              | FStar_Pervasives_Native.Some pure_eff ->
                  let flags1 =
                    let uu____24753 =
                      FStar_Ident.lid_equals pure_eff
                        FStar_Parser_Const.effect_Tot_lid
                       in
                    if uu____24753
                    then FStar_Syntax_Syntax.TOTAL ::
                      (ct.FStar_Syntax_Syntax.flags)
                    else ct.FStar_Syntax_Syntax.flags  in
                  let uu___193_24757 = ct  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___193_24757.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name = pure_eff;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___193_24757.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___193_24757.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags = flags1
                  }
              | FStar_Pervasives_Native.None  ->
                  let ct1 =
                    FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c
                     in
                  let uu___194_24759 = ct1  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___194_24759.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name =
                      FStar_Parser_Const.effect_PURE_lid;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___194_24759.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___194_24759.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags =
                      (uu___194_24759.FStar_Syntax_Syntax.flags)
                  }
               in
            let uu___195_24760 = c  in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
              FStar_Syntax_Syntax.pos =
                (uu___195_24760.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___195_24760.FStar_Syntax_Syntax.vars)
            }
          else c
      | uu____24762 -> c
  
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
        let uu____24780 = norm cfg [] [] t  in
        FStar_Syntax_Util.non_informative uu____24780  in
      let uu____24787 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ)
         in
      if uu____24787
      then
        let uu____24788 =
          downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name  in
        match uu____24788 with
        | FStar_Pervasives_Native.Some pure_eff ->
            FStar_Syntax_Syntax.mk_lcomp pure_eff
              lc.FStar_Syntax_Syntax.res_typ lc.FStar_Syntax_Syntax.cflags
              (fun uu____24794  ->
                 let uu____24795 = FStar_Syntax_Syntax.lcomp_comp lc  in
                 ghost_to_pure env uu____24795)
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
            ((let uu____24816 =
                let uu____24821 =
                  let uu____24822 = FStar_Util.message_of_exn e  in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____24822
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____24821)  in
              FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____24816);
             t)
         in
      FStar_Syntax_Print.term_to_string' env.FStar_TypeChecker_Env.dsenv t1
  
let (comp_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string) =
  fun env  ->
    fun c  ->
      let c1 =
        try
          let uu____24837 = config [AllowUnboundUniverses] env  in
          norm_comp uu____24837 [] c
        with
        | e ->
            ((let uu____24850 =
                let uu____24855 =
                  let uu____24856 = FStar_Util.message_of_exn e  in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____24856
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____24855)  in
              FStar_Errors.log_issue c.FStar_Syntax_Syntax.pos uu____24850);
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
                   let uu____24901 =
                     let uu____24902 =
                       let uu____24909 = FStar_Syntax_Util.mk_conj phi1 phi
                          in
                       (y, uu____24909)  in
                     FStar_Syntax_Syntax.Tm_refine uu____24902  in
                   mk uu____24901 t01.FStar_Syntax_Syntax.pos
               | uu____24914 -> t2)
          | uu____24915 -> t2  in
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
        let uu____24979 = FStar_Syntax_Util.arrow_formals_comp t_e  in
        match uu____24979 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____25008 ->
                 let uu____25015 = FStar_Syntax_Util.abs_formals e  in
                 (match uu____25015 with
                  | (actuals,uu____25025,uu____25026) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____25040 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders
                            in
                         match uu____25040 with
                         | (binders,args) ->
                             let uu____25057 =
                               FStar_Syntax_Syntax.mk_Tm_app e args
                                 FStar_Pervasives_Native.None
                                 e.FStar_Syntax_Syntax.pos
                                in
                             FStar_Syntax_Util.abs binders uu____25057
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
      | uu____25069 ->
          let uu____25070 = FStar_Syntax_Util.head_and_args t  in
          (match uu____25070 with
           | (head1,args) ->
               let uu____25107 =
                 let uu____25108 = FStar_Syntax_Subst.compress head1  in
                 uu____25108.FStar_Syntax_Syntax.n  in
               (match uu____25107 with
                | FStar_Syntax_Syntax.Tm_uvar (uu____25111,thead) ->
                    let uu____25137 = FStar_Syntax_Util.arrow_formals thead
                       in
                    (match uu____25137 with
                     | (formals,tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____25179 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___200_25187 = env  in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___200_25187.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___200_25187.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___200_25187.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___200_25187.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___200_25187.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___200_25187.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___200_25187.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___200_25187.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___200_25187.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___200_25187.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___200_25187.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___200_25187.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___200_25187.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___200_25187.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___200_25187.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___200_25187.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___200_25187.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___200_25187.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___200_25187.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___200_25187.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___200_25187.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___200_25187.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___200_25187.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___200_25187.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                     =
                                     (uu___200_25187.FStar_TypeChecker_Env.qtbl_name_and_index);
                                   FStar_TypeChecker_Env.normalized_eff_names
                                     =
                                     (uu___200_25187.FStar_TypeChecker_Env.normalized_eff_names);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___200_25187.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth_hook =
                                     (uu___200_25187.FStar_TypeChecker_Env.synth_hook);
                                   FStar_TypeChecker_Env.splice =
                                     (uu___200_25187.FStar_TypeChecker_Env.splice);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___200_25187.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___200_25187.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___200_25187.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___200_25187.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.dep_graph =
                                     (uu___200_25187.FStar_TypeChecker_Env.dep_graph)
                                 }) t
                               in
                            match uu____25179 with
                            | (uu____25188,ty,uu____25190) ->
                                eta_expand_with_type env t ty))
                | uu____25191 ->
                    let uu____25192 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___201_25200 = env  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___201_25200.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___201_25200.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___201_25200.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___201_25200.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___201_25200.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___201_25200.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___201_25200.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___201_25200.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___201_25200.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___201_25200.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___201_25200.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___201_25200.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___201_25200.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___201_25200.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___201_25200.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___201_25200.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___201_25200.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___201_25200.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.failhard =
                             (uu___201_25200.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___201_25200.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___201_25200.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___201_25200.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___201_25200.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___201_25200.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qtbl_name_and_index =
                             (uu___201_25200.FStar_TypeChecker_Env.qtbl_name_and_index);
                           FStar_TypeChecker_Env.normalized_eff_names =
                             (uu___201_25200.FStar_TypeChecker_Env.normalized_eff_names);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___201_25200.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth_hook =
                             (uu___201_25200.FStar_TypeChecker_Env.synth_hook);
                           FStar_TypeChecker_Env.splice =
                             (uu___201_25200.FStar_TypeChecker_Env.splice);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___201_25200.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___201_25200.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___201_25200.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___201_25200.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.dep_graph =
                             (uu___201_25200.FStar_TypeChecker_Env.dep_graph)
                         }) t
                       in
                    (match uu____25192 with
                     | (uu____25201,ty,uu____25203) ->
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
      let uu___202_25276 = x  in
      let uu____25277 = elim_delayed_subst_term x.FStar_Syntax_Syntax.sort
         in
      {
        FStar_Syntax_Syntax.ppname =
          (uu___202_25276.FStar_Syntax_Syntax.ppname);
        FStar_Syntax_Syntax.index =
          (uu___202_25276.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = uu____25277
      }  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____25280 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_bvar uu____25305 -> t1
    | FStar_Syntax_Syntax.Tm_name uu____25306 -> t1
    | FStar_Syntax_Syntax.Tm_fvar uu____25307 -> t1
    | FStar_Syntax_Syntax.Tm_uinst uu____25308 -> t1
    | FStar_Syntax_Syntax.Tm_constant uu____25315 -> t1
    | FStar_Syntax_Syntax.Tm_type uu____25316 -> t1
    | FStar_Syntax_Syntax.Tm_lazy uu____25317 -> t1
    | FStar_Syntax_Syntax.Tm_unknown  -> t1
    | FStar_Syntax_Syntax.Tm_abs (bs,t2,rc_opt) ->
        let elim_rc rc =
          let uu___203_25347 = rc  in
          let uu____25348 =
            FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
              elim_delayed_subst_term
             in
          let uu____25355 =
            elim_delayed_subst_cflags rc.FStar_Syntax_Syntax.residual_flags
             in
          {
            FStar_Syntax_Syntax.residual_effect =
              (uu___203_25347.FStar_Syntax_Syntax.residual_effect);
            FStar_Syntax_Syntax.residual_typ = uu____25348;
            FStar_Syntax_Syntax.residual_flags = uu____25355
          }  in
        let uu____25358 =
          let uu____25359 =
            let uu____25376 = elim_delayed_subst_binders bs  in
            let uu____25383 = elim_delayed_subst_term t2  in
            let uu____25384 = FStar_Util.map_opt rc_opt elim_rc  in
            (uu____25376, uu____25383, uu____25384)  in
          FStar_Syntax_Syntax.Tm_abs uu____25359  in
        mk1 uu____25358
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____25413 =
          let uu____25414 =
            let uu____25427 = elim_delayed_subst_binders bs  in
            let uu____25434 = elim_delayed_subst_comp c  in
            (uu____25427, uu____25434)  in
          FStar_Syntax_Syntax.Tm_arrow uu____25414  in
        mk1 uu____25413
    | FStar_Syntax_Syntax.Tm_refine (bv,phi) ->
        let uu____25447 =
          let uu____25448 =
            let uu____25455 = elim_bv bv  in
            let uu____25456 = elim_delayed_subst_term phi  in
            (uu____25455, uu____25456)  in
          FStar_Syntax_Syntax.Tm_refine uu____25448  in
        mk1 uu____25447
    | FStar_Syntax_Syntax.Tm_app (t2,args) ->
        let uu____25479 =
          let uu____25480 =
            let uu____25495 = elim_delayed_subst_term t2  in
            let uu____25496 = elim_delayed_subst_args args  in
            (uu____25495, uu____25496)  in
          FStar_Syntax_Syntax.Tm_app uu____25480  in
        mk1 uu____25479
    | FStar_Syntax_Syntax.Tm_match (t2,branches) ->
        let rec elim_pat p =
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_var x ->
              let uu___204_25562 = p  in
              let uu____25563 =
                let uu____25564 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_var uu____25564  in
              {
                FStar_Syntax_Syntax.v = uu____25563;
                FStar_Syntax_Syntax.p =
                  (uu___204_25562.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_wild x ->
              let uu___205_25566 = p  in
              let uu____25567 =
                let uu____25568 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_wild uu____25568  in
              {
                FStar_Syntax_Syntax.v = uu____25567;
                FStar_Syntax_Syntax.p =
                  (uu___205_25566.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
              let uu___206_25575 = p  in
              let uu____25576 =
                let uu____25577 =
                  let uu____25584 = elim_bv x  in
                  let uu____25585 = elim_delayed_subst_term t0  in
                  (uu____25584, uu____25585)  in
                FStar_Syntax_Syntax.Pat_dot_term uu____25577  in
              {
                FStar_Syntax_Syntax.v = uu____25576;
                FStar_Syntax_Syntax.p =
                  (uu___206_25575.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
              let uu___207_25604 = p  in
              let uu____25605 =
                let uu____25606 =
                  let uu____25619 =
                    FStar_List.map
                      (fun uu____25642  ->
                         match uu____25642 with
                         | (x,b) ->
                             let uu____25655 = elim_pat x  in
                             (uu____25655, b)) pats
                     in
                  (fv, uu____25619)  in
                FStar_Syntax_Syntax.Pat_cons uu____25606  in
              {
                FStar_Syntax_Syntax.v = uu____25605;
                FStar_Syntax_Syntax.p =
                  (uu___207_25604.FStar_Syntax_Syntax.p)
              }
          | uu____25668 -> p  in
        let elim_branch uu____25692 =
          match uu____25692 with
          | (pat,wopt,t3) ->
              let uu____25718 = elim_pat pat  in
              let uu____25721 =
                FStar_Util.map_opt wopt elim_delayed_subst_term  in
              let uu____25724 = elim_delayed_subst_term t3  in
              (uu____25718, uu____25721, uu____25724)
           in
        let uu____25729 =
          let uu____25730 =
            let uu____25753 = elim_delayed_subst_term t2  in
            let uu____25754 = FStar_List.map elim_branch branches  in
            (uu____25753, uu____25754)  in
          FStar_Syntax_Syntax.Tm_match uu____25730  in
        mk1 uu____25729
    | FStar_Syntax_Syntax.Tm_ascribed (t2,a,lopt) ->
        let elim_ascription uu____25865 =
          match uu____25865 with
          | (tc,topt) ->
              let uu____25900 =
                match tc with
                | FStar_Util.Inl t3 ->
                    let uu____25910 = elim_delayed_subst_term t3  in
                    FStar_Util.Inl uu____25910
                | FStar_Util.Inr c ->
                    let uu____25912 = elim_delayed_subst_comp c  in
                    FStar_Util.Inr uu____25912
                 in
              let uu____25913 =
                FStar_Util.map_opt topt elim_delayed_subst_term  in
              (uu____25900, uu____25913)
           in
        let uu____25922 =
          let uu____25923 =
            let uu____25950 = elim_delayed_subst_term t2  in
            let uu____25951 = elim_ascription a  in
            (uu____25950, uu____25951, lopt)  in
          FStar_Syntax_Syntax.Tm_ascribed uu____25923  in
        mk1 uu____25922
    | FStar_Syntax_Syntax.Tm_let (lbs,t2) ->
        let elim_lb lb =
          let uu___208_25998 = lb  in
          let uu____25999 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbtyp  in
          let uu____26002 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbdef  in
          {
            FStar_Syntax_Syntax.lbname =
              (uu___208_25998.FStar_Syntax_Syntax.lbname);
            FStar_Syntax_Syntax.lbunivs =
              (uu___208_25998.FStar_Syntax_Syntax.lbunivs);
            FStar_Syntax_Syntax.lbtyp = uu____25999;
            FStar_Syntax_Syntax.lbeff =
              (uu___208_25998.FStar_Syntax_Syntax.lbeff);
            FStar_Syntax_Syntax.lbdef = uu____26002;
            FStar_Syntax_Syntax.lbattrs =
              (uu___208_25998.FStar_Syntax_Syntax.lbattrs);
            FStar_Syntax_Syntax.lbpos =
              (uu___208_25998.FStar_Syntax_Syntax.lbpos)
          }  in
        let uu____26005 =
          let uu____26006 =
            let uu____26019 =
              let uu____26026 =
                FStar_List.map elim_lb (FStar_Pervasives_Native.snd lbs)  in
              ((FStar_Pervasives_Native.fst lbs), uu____26026)  in
            let uu____26035 = elim_delayed_subst_term t2  in
            (uu____26019, uu____26035)  in
          FStar_Syntax_Syntax.Tm_let uu____26006  in
        mk1 uu____26005
    | FStar_Syntax_Syntax.Tm_uvar (uv,t2) ->
        let uu____26068 =
          let uu____26069 =
            let uu____26086 = elim_delayed_subst_term t2  in
            (uv, uu____26086)  in
          FStar_Syntax_Syntax.Tm_uvar uu____26069  in
        mk1 uu____26068
    | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
        let qi1 =
          FStar_Syntax_Syntax.on_antiquoted elim_delayed_subst_term qi  in
        let uu____26104 =
          let uu____26105 =
            let uu____26112 = elim_delayed_subst_term tm  in
            (uu____26112, qi1)  in
          FStar_Syntax_Syntax.Tm_quoted uu____26105  in
        mk1 uu____26104
    | FStar_Syntax_Syntax.Tm_meta (t2,md) ->
        let uu____26119 =
          let uu____26120 =
            let uu____26127 = elim_delayed_subst_term t2  in
            let uu____26128 = elim_delayed_subst_meta md  in
            (uu____26127, uu____26128)  in
          FStar_Syntax_Syntax.Tm_meta uu____26120  in
        mk1 uu____26119

and (elim_delayed_subst_cflags :
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun flags1  ->
    FStar_List.map
      (fun uu___93_26135  ->
         match uu___93_26135 with
         | FStar_Syntax_Syntax.DECREASES t ->
             let uu____26139 = elim_delayed_subst_term t  in
             FStar_Syntax_Syntax.DECREASES uu____26139
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
        let uu____26162 =
          let uu____26163 =
            let uu____26172 = elim_delayed_subst_term t  in
            (uu____26172, uopt)  in
          FStar_Syntax_Syntax.Total uu____26163  in
        mk1 uu____26162
    | FStar_Syntax_Syntax.GTotal (t,uopt) ->
        let uu____26185 =
          let uu____26186 =
            let uu____26195 = elim_delayed_subst_term t  in
            (uu____26195, uopt)  in
          FStar_Syntax_Syntax.GTotal uu____26186  in
        mk1 uu____26185
    | FStar_Syntax_Syntax.Comp ct ->
        let ct1 =
          let uu___209_26200 = ct  in
          let uu____26201 =
            elim_delayed_subst_term ct.FStar_Syntax_Syntax.result_typ  in
          let uu____26204 =
            elim_delayed_subst_args ct.FStar_Syntax_Syntax.effect_args  in
          let uu____26213 =
            elim_delayed_subst_cflags ct.FStar_Syntax_Syntax.flags  in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___209_26200.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___209_26200.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ = uu____26201;
            FStar_Syntax_Syntax.effect_args = uu____26204;
            FStar_Syntax_Syntax.flags = uu____26213
          }  in
        mk1 (FStar_Syntax_Syntax.Comp ct1)

and (elim_delayed_subst_meta :
  FStar_Syntax_Syntax.metadata -> FStar_Syntax_Syntax.metadata) =
  fun uu___94_26216  ->
    match uu___94_26216 with
    | FStar_Syntax_Syntax.Meta_pattern args ->
        let uu____26228 = FStar_List.map elim_delayed_subst_args args  in
        FStar_Syntax_Syntax.Meta_pattern uu____26228
    | FStar_Syntax_Syntax.Meta_monadic (m,t) ->
        let uu____26261 =
          let uu____26268 = elim_delayed_subst_term t  in (m, uu____26268)
           in
        FStar_Syntax_Syntax.Meta_monadic uu____26261
    | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,t) ->
        let uu____26276 =
          let uu____26285 = elim_delayed_subst_term t  in
          (m1, m2, uu____26285)  in
        FStar_Syntax_Syntax.Meta_monadic_lift uu____26276
    | m -> m

and (elim_delayed_subst_args :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun args  ->
    FStar_List.map
      (fun uu____26308  ->
         match uu____26308 with
         | (t,q) ->
             let uu____26319 = elim_delayed_subst_term t  in (uu____26319, q))
      args

and (elim_delayed_subst_binders :
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun bs  ->
    FStar_List.map
      (fun uu____26339  ->
         match uu____26339 with
         | (x,q) ->
             let uu____26350 =
               let uu___210_26351 = x  in
               let uu____26352 =
                 elim_delayed_subst_term x.FStar_Syntax_Syntax.sort  in
               {
                 FStar_Syntax_Syntax.ppname =
                   (uu___210_26351.FStar_Syntax_Syntax.ppname);
                 FStar_Syntax_Syntax.index =
                   (uu___210_26351.FStar_Syntax_Syntax.index);
                 FStar_Syntax_Syntax.sort = uu____26352
               }  in
             (uu____26350, q)) bs

let (elim_uvars_aux_tc :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.univ_names ->
      FStar_Syntax_Syntax.binders ->
        (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.comp) FStar_Util.either
          ->
          (FStar_Syntax_Syntax.univ_names,(FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
                                            FStar_Pervasives_Native.tuple2
                                            Prims.list,(FStar_Syntax_Syntax.term,
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
            | (uu____26436,FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c))
                  FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
            | (uu____26442,FStar_Util.Inl t) ->
                let uu____26448 =
                  let uu____26455 =
                    let uu____26456 =
                      let uu____26469 = FStar_Syntax_Syntax.mk_Total t  in
                      (binders, uu____26469)  in
                    FStar_Syntax_Syntax.Tm_arrow uu____26456  in
                  FStar_Syntax_Syntax.mk uu____26455  in
                uu____26448 FStar_Pervasives_Native.None
                  t.FStar_Syntax_Syntax.pos
             in
          let uu____26473 = FStar_Syntax_Subst.open_univ_vars univ_names t
             in
          match uu____26473 with
          | (univ_names1,t1) ->
              let t2 = remove_uvar_solutions env t1  in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2  in
              let t4 = elim_delayed_subst_term t3  in
              let uu____26501 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t4))
                | uu____26556 ->
                    let uu____26557 =
                      let uu____26566 =
                        let uu____26567 = FStar_Syntax_Subst.compress t4  in
                        uu____26567.FStar_Syntax_Syntax.n  in
                      (uu____26566, tc)  in
                    (match uu____26557 with
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inr uu____26592) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inl uu____26629) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____26668,FStar_Util.Inl uu____26669) ->
                         ([], (FStar_Util.Inl t4))
                     | uu____26692 -> failwith "Impossible")
                 in
              (match uu____26501 with
               | (binders1,tc1) -> (univ_names1, binders1, tc1))
  
let (elim_uvars_aux_t :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.univ_names ->
      FStar_Syntax_Syntax.binders ->
        FStar_Syntax_Syntax.typ ->
          (FStar_Syntax_Syntax.univ_names,(FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
                                            FStar_Pervasives_Native.tuple2
                                            Prims.list,FStar_Syntax_Syntax.term)
            FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun univ_names  ->
      fun binders  ->
        fun t  ->
          let uu____26805 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl t)  in
          match uu____26805 with
          | (univ_names1,binders1,tc) ->
              let uu____26863 = FStar_Util.left tc  in
              (univ_names1, binders1, uu____26863)
  
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
          let uu____26906 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr c)  in
          match uu____26906 with
          | (univ_names1,binders1,tc) ->
              let uu____26966 = FStar_Util.right tc  in
              (univ_names1, binders1, uu____26966)
  
let rec (elim_uvars :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt)
  =
  fun env  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univ_names,binders,typ,lids,lids') ->
          let uu____27003 = elim_uvars_aux_t env univ_names binders typ  in
          (match uu____27003 with
           | (univ_names1,binders1,typ1) ->
               let uu___211_27031 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___211_27031.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___211_27031.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___211_27031.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___211_27031.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
          let uu___212_27052 = s  in
          let uu____27053 =
            let uu____27054 =
              let uu____27063 = FStar_List.map (elim_uvars env) sigs  in
              (uu____27063, lids)  in
            FStar_Syntax_Syntax.Sig_bundle uu____27054  in
          {
            FStar_Syntax_Syntax.sigel = uu____27053;
            FStar_Syntax_Syntax.sigrng =
              (uu___212_27052.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___212_27052.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___212_27052.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___212_27052.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_datacon (lid,univ_names,typ,lident,i,lids) ->
          let uu____27080 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____27080 with
           | (univ_names1,uu____27098,typ1) ->
               let uu___213_27112 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___213_27112.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___213_27112.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___213_27112.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___213_27112.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univ_names,typ) ->
          let uu____27118 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____27118 with
           | (univ_names1,uu____27136,typ1) ->
               let uu___214_27150 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___214_27150.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___214_27150.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___214_27150.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___214_27150.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____27184 =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs
                       in
                    match uu____27184 with
                    | (opening,lbunivs) ->
                        let elim t =
                          let uu____27209 =
                            let uu____27210 =
                              let uu____27211 =
                                FStar_Syntax_Subst.subst opening t  in
                              remove_uvar_solutions env uu____27211  in
                            FStar_Syntax_Subst.close_univ_vars lbunivs
                              uu____27210
                             in
                          elim_delayed_subst_term uu____27209  in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp  in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef  in
                        let uu___215_27214 = lb  in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___215_27214.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___215_27214.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___215_27214.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___215_27214.FStar_Syntax_Syntax.lbpos)
                        }))
             in
          let uu___216_27215 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids));
            FStar_Syntax_Syntax.sigrng =
              (uu___216_27215.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___216_27215.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___216_27215.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___216_27215.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_main t ->
          let uu___217_27227 = s  in
          let uu____27228 =
            let uu____27229 = remove_uvar_solutions env t  in
            FStar_Syntax_Syntax.Sig_main uu____27229  in
          {
            FStar_Syntax_Syntax.sigel = uu____27228;
            FStar_Syntax_Syntax.sigrng =
              (uu___217_27227.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___217_27227.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___217_27227.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___217_27227.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_assume (l,us,t) ->
          let uu____27233 = elim_uvars_aux_t env us [] t  in
          (match uu____27233 with
           | (us1,uu____27251,t1) ->
               let uu___218_27265 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___218_27265.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___218_27265.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___218_27265.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___218_27265.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____27266 ->
          failwith "Impossible: should have been desugared already"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____27268 =
            elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature
             in
          (match uu____27268 with
           | (univs1,binders,signature) ->
               let uu____27296 =
                 let uu____27305 = FStar_Syntax_Subst.univ_var_opening univs1
                    in
                 match uu____27305 with
                 | (univs_opening,univs2) ->
                     let uu____27332 =
                       FStar_Syntax_Subst.univ_var_closing univs2  in
                     (univs_opening, uu____27332)
                  in
               (match uu____27296 with
                | (univs_opening,univs_closing) ->
                    let uu____27349 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders
                         in
                      let uu____27355 =
                        FStar_Syntax_Subst.opening_of_binders binders1  in
                      let uu____27356 =
                        FStar_Syntax_Subst.closing_of_binders binders1  in
                      (uu____27355, uu____27356)  in
                    (match uu____27349 with
                     | (b_opening,b_closing) ->
                         let n1 = FStar_List.length univs1  in
                         let n_binders = FStar_List.length binders  in
                         let elim_tscheme uu____27380 =
                           match uu____27380 with
                           | (us,t) ->
                               let n_us = FStar_List.length us  in
                               let uu____27398 =
                                 FStar_Syntax_Subst.open_univ_vars us t  in
                               (match uu____27398 with
                                | (us1,t1) ->
                                    let uu____27409 =
                                      let uu____27414 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      let uu____27421 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      (uu____27414, uu____27421)  in
                                    (match uu____27409 with
                                     | (b_opening1,b_closing1) ->
                                         let uu____27434 =
                                           let uu____27439 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us)
                                              in
                                           let uu____27448 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us)
                                              in
                                           (uu____27439, uu____27448)  in
                                         (match uu____27434 with
                                          | (univs_opening1,univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____27464 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1
                                                   in
                                                FStar_Syntax_Subst.subst
                                                  univs_opening1 uu____27464
                                                 in
                                              let uu____27465 =
                                                elim_uvars_aux_t env [] [] t2
                                                 in
                                              (match uu____27465 with
                                               | (uu____27486,uu____27487,t3)
                                                   ->
                                                   let t4 =
                                                     let uu____27502 =
                                                       let uu____27503 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3
                                                          in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
                                                         uu____27503
                                                        in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____27502
                                                      in
                                                   (us1, t4)))))
                            in
                         let elim_term t =
                           let uu____27510 =
                             elim_uvars_aux_t env univs1 binders t  in
                           match uu____27510 with
                           | (uu____27523,uu____27524,t1) -> t1  in
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
                             | uu____27586 ->
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_abs
                                      ((a.FStar_Syntax_Syntax.action_params),
                                        body, FStar_Pervasives_Native.None))
                                   FStar_Pervasives_Native.None
                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                              in
                           let destruct_action_body body =
                             let uu____27605 =
                               let uu____27606 =
                                 FStar_Syntax_Subst.compress body  in
                               uu____27606.FStar_Syntax_Syntax.n  in
                             match uu____27605 with
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,(FStar_Util.Inl
                                        typ,FStar_Pervasives_Native.None ),FStar_Pervasives_Native.None
                                  )
                                 -> (defn, typ)
                             | uu____27665 -> failwith "Impossible"  in
                           let destruct_action_typ_templ t =
                             let uu____27696 =
                               let uu____27697 =
                                 FStar_Syntax_Subst.compress t  in
                               uu____27697.FStar_Syntax_Syntax.n  in
                             match uu____27696 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (pars,body,uu____27718) ->
                                 let uu____27739 = destruct_action_body body
                                    in
                                 (match uu____27739 with
                                  | (defn,typ) -> (pars, defn, typ))
                             | uu____27784 ->
                                 let uu____27785 = destruct_action_body t  in
                                 (match uu____27785 with
                                  | (defn,typ) -> ([], defn, typ))
                              in
                           let uu____27834 =
                             elim_tscheme
                               ((a.FStar_Syntax_Syntax.action_univs),
                                 action_typ_templ)
                              in
                           match uu____27834 with
                           | (action_univs,t) ->
                               let uu____27843 = destruct_action_typ_templ t
                                  in
                               (match uu____27843 with
                                | (action_params,action_defn,action_typ) ->
                                    let a' =
                                      let uu___219_27884 = a  in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___219_27884.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___219_27884.FStar_Syntax_Syntax.action_unqualified_name);
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
                           let uu___220_27886 = ed  in
                           let uu____27887 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ret_wp  in
                           let uu____27888 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_wp  in
                           let uu____27889 =
                             elim_tscheme ed.FStar_Syntax_Syntax.if_then_else
                              in
                           let uu____27890 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ite_wp  in
                           let uu____27891 =
                             elim_tscheme ed.FStar_Syntax_Syntax.stronger  in
                           let uu____27892 =
                             elim_tscheme ed.FStar_Syntax_Syntax.close_wp  in
                           let uu____27893 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assert_p  in
                           let uu____27894 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assume_p  in
                           let uu____27895 =
                             elim_tscheme ed.FStar_Syntax_Syntax.null_wp  in
                           let uu____27896 =
                             elim_tscheme ed.FStar_Syntax_Syntax.trivial  in
                           let uu____27897 =
                             elim_term ed.FStar_Syntax_Syntax.repr  in
                           let uu____27898 =
                             elim_tscheme ed.FStar_Syntax_Syntax.return_repr
                              in
                           let uu____27899 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_repr
                              in
                           let uu____27900 =
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions
                              in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___220_27886.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___220_27886.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs = univs1;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp = uu____27887;
                             FStar_Syntax_Syntax.bind_wp = uu____27888;
                             FStar_Syntax_Syntax.if_then_else = uu____27889;
                             FStar_Syntax_Syntax.ite_wp = uu____27890;
                             FStar_Syntax_Syntax.stronger = uu____27891;
                             FStar_Syntax_Syntax.close_wp = uu____27892;
                             FStar_Syntax_Syntax.assert_p = uu____27893;
                             FStar_Syntax_Syntax.assume_p = uu____27894;
                             FStar_Syntax_Syntax.null_wp = uu____27895;
                             FStar_Syntax_Syntax.trivial = uu____27896;
                             FStar_Syntax_Syntax.repr = uu____27897;
                             FStar_Syntax_Syntax.return_repr = uu____27898;
                             FStar_Syntax_Syntax.bind_repr = uu____27899;
                             FStar_Syntax_Syntax.actions = uu____27900;
                             FStar_Syntax_Syntax.eff_attrs =
                               (uu___220_27886.FStar_Syntax_Syntax.eff_attrs)
                           }  in
                         let uu___221_27903 = s  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___221_27903.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___221_27903.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___221_27903.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___221_27903.FStar_Syntax_Syntax.sigattrs)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___95_27922 =
            match uu___95_27922 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (us,t) ->
                let uu____27949 = elim_uvars_aux_t env us [] t  in
                (match uu____27949 with
                 | (us1,uu____27973,t1) ->
                     FStar_Pervasives_Native.Some (us1, t1))
             in
          let sub_eff1 =
            let uu___222_27992 = sub_eff  in
            let uu____27993 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp  in
            let uu____27996 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift  in
            {
              FStar_Syntax_Syntax.source =
                (uu___222_27992.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___222_27992.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____27993;
              FStar_Syntax_Syntax.lift = uu____27996
            }  in
          let uu___223_27999 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___223_27999.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___223_27999.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___223_27999.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___223_27999.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,univ_names,binders,comp,flags1) ->
          let uu____28009 = elim_uvars_aux_c env univ_names binders comp  in
          (match uu____28009 with
           | (univ_names1,binders1,comp1) ->
               let uu___224_28043 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___224_28043.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___224_28043.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___224_28043.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___224_28043.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____28054 -> s
      | FStar_Syntax_Syntax.Sig_splice uu____28055 -> s
  
let (erase_universes :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  -> normalize [EraseUniverses; AllowUnboundUniverses] env t
  