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
  | NoDeltaSteps 
  | UnfoldUntil of FStar_Syntax_Syntax.delta_depth 
  | UnfoldOnly of FStar_Ident.lid Prims.list 
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
  fun projectee  -> match projectee with | Beta  -> true | uu____22 -> false 
let (uu___is_Iota : step -> Prims.bool) =
  fun projectee  -> match projectee with | Iota  -> true | uu____26 -> false 
let (uu___is_Zeta : step -> Prims.bool) =
  fun projectee  -> match projectee with | Zeta  -> true | uu____30 -> false 
let (uu___is_Exclude : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Exclude _0 -> true | uu____35 -> false
  
let (__proj__Exclude__item___0 : step -> step) =
  fun projectee  -> match projectee with | Exclude _0 -> _0 
let (uu___is_Weak : step -> Prims.bool) =
  fun projectee  -> match projectee with | Weak  -> true | uu____46 -> false 
let (uu___is_HNF : step -> Prims.bool) =
  fun projectee  -> match projectee with | HNF  -> true | uu____50 -> false 
let (uu___is_Primops : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Primops  -> true | uu____54 -> false
  
let (uu___is_Eager_unfolding : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Eager_unfolding  -> true | uu____58 -> false
  
let (uu___is_Inlining : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Inlining  -> true | uu____62 -> false
  
let (uu___is_NoDeltaSteps : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoDeltaSteps  -> true | uu____66 -> false
  
let (uu___is_UnfoldUntil : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldUntil _0 -> true | uu____71 -> false
  
let (__proj__UnfoldUntil__item___0 : step -> FStar_Syntax_Syntax.delta_depth)
  = fun projectee  -> match projectee with | UnfoldUntil _0 -> _0 
let (uu___is_UnfoldOnly : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldOnly _0 -> true | uu____85 -> false
  
let (__proj__UnfoldOnly__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldOnly _0 -> _0 
let (uu___is_UnfoldAttr : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldAttr _0 -> true | uu____103 -> false
  
let (__proj__UnfoldAttr__item___0 : step -> FStar_Syntax_Syntax.attribute) =
  fun projectee  -> match projectee with | UnfoldAttr _0 -> _0 
let (uu___is_UnfoldTac : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldTac  -> true | uu____114 -> false
  
let (uu___is_PureSubtermsWithinComputations : step -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | PureSubtermsWithinComputations  -> true
    | uu____118 -> false
  
let (uu___is_Simplify : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Simplify  -> true | uu____122 -> false
  
let (uu___is_EraseUniverses : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | EraseUniverses  -> true | uu____126 -> false
  
let (uu___is_AllowUnboundUniverses : step -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | AllowUnboundUniverses  -> true
    | uu____130 -> false
  
let (uu___is_Reify : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reify  -> true | uu____134 -> false
  
let (uu___is_CompressUvars : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | CompressUvars  -> true | uu____138 -> false
  
let (uu___is_NoFullNorm : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoFullNorm  -> true | uu____142 -> false
  
let (uu___is_CheckNoUvars : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | CheckNoUvars  -> true | uu____146 -> false
  
let (uu___is_Unmeta : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unmeta  -> true | uu____150 -> false
  
let (uu___is_Unascribe : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unascribe  -> true | uu____154 -> false
  
type steps = step Prims.list[@@deriving show]
let cases :
  'Auu____162 'Auu____163 .
    ('Auu____163 -> 'Auu____162) ->
      'Auu____162 ->
        'Auu____163 FStar_Pervasives_Native.option -> 'Auu____162
  =
  fun f  ->
    fun d  ->
      fun uu___74_180  ->
        match uu___74_180 with
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
  eager_unfolding: Prims.bool ;
  inlining: Prims.bool ;
  no_delta_steps: Prims.bool ;
  unfold_until:
    FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option ;
  unfold_only: FStar_Ident.lid Prims.list FStar_Pervasives_Native.option ;
  unfold_attr: FStar_Syntax_Syntax.attribute FStar_Pervasives_Native.option ;
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
  unascribe: Prims.bool }[@@deriving show]
let (__proj__Mkfsteps__item__beta : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        eager_unfolding = __fname__eager_unfolding;
        inlining = __fname__inlining;
        no_delta_steps = __fname__no_delta_steps;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;_} -> __fname__beta
  
let (__proj__Mkfsteps__item__iota : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        eager_unfolding = __fname__eager_unfolding;
        inlining = __fname__inlining;
        no_delta_steps = __fname__no_delta_steps;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;_} -> __fname__iota
  
let (__proj__Mkfsteps__item__zeta : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        eager_unfolding = __fname__eager_unfolding;
        inlining = __fname__inlining;
        no_delta_steps = __fname__no_delta_steps;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;_} -> __fname__zeta
  
let (__proj__Mkfsteps__item__weak : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        eager_unfolding = __fname__eager_unfolding;
        inlining = __fname__inlining;
        no_delta_steps = __fname__no_delta_steps;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;_} -> __fname__weak
  
let (__proj__Mkfsteps__item__hnf : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        eager_unfolding = __fname__eager_unfolding;
        inlining = __fname__inlining;
        no_delta_steps = __fname__no_delta_steps;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;_} -> __fname__hnf
  
let (__proj__Mkfsteps__item__primops : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        eager_unfolding = __fname__eager_unfolding;
        inlining = __fname__inlining;
        no_delta_steps = __fname__no_delta_steps;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;_} -> __fname__primops
  
let (__proj__Mkfsteps__item__eager_unfolding : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        eager_unfolding = __fname__eager_unfolding;
        inlining = __fname__inlining;
        no_delta_steps = __fname__no_delta_steps;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;_} -> __fname__eager_unfolding
  
let (__proj__Mkfsteps__item__inlining : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        eager_unfolding = __fname__eager_unfolding;
        inlining = __fname__inlining;
        no_delta_steps = __fname__no_delta_steps;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;_} -> __fname__inlining
  
let (__proj__Mkfsteps__item__no_delta_steps : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        eager_unfolding = __fname__eager_unfolding;
        inlining = __fname__inlining;
        no_delta_steps = __fname__no_delta_steps;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;_} -> __fname__no_delta_steps
  
let (__proj__Mkfsteps__item__unfold_until :
  fsteps -> FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option) =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        eager_unfolding = __fname__eager_unfolding;
        inlining = __fname__inlining;
        no_delta_steps = __fname__no_delta_steps;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;_} -> __fname__unfold_until
  
let (__proj__Mkfsteps__item__unfold_only :
  fsteps -> FStar_Ident.lid Prims.list FStar_Pervasives_Native.option) =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        eager_unfolding = __fname__eager_unfolding;
        inlining = __fname__inlining;
        no_delta_steps = __fname__no_delta_steps;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;_} -> __fname__unfold_only
  
let (__proj__Mkfsteps__item__unfold_attr :
  fsteps -> FStar_Syntax_Syntax.attribute FStar_Pervasives_Native.option) =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        eager_unfolding = __fname__eager_unfolding;
        inlining = __fname__inlining;
        no_delta_steps = __fname__no_delta_steps;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;_} -> __fname__unfold_attr
  
let (__proj__Mkfsteps__item__unfold_tac : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        eager_unfolding = __fname__eager_unfolding;
        inlining = __fname__inlining;
        no_delta_steps = __fname__no_delta_steps;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;_} -> __fname__unfold_tac
  
let (__proj__Mkfsteps__item__pure_subterms_within_computations :
  fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        eager_unfolding = __fname__eager_unfolding;
        inlining = __fname__inlining;
        no_delta_steps = __fname__no_delta_steps;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;_} ->
        __fname__pure_subterms_within_computations
  
let (__proj__Mkfsteps__item__simplify : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        eager_unfolding = __fname__eager_unfolding;
        inlining = __fname__inlining;
        no_delta_steps = __fname__no_delta_steps;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;_} -> __fname__simplify
  
let (__proj__Mkfsteps__item__erase_universes : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        eager_unfolding = __fname__eager_unfolding;
        inlining = __fname__inlining;
        no_delta_steps = __fname__no_delta_steps;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;_} -> __fname__erase_universes
  
let (__proj__Mkfsteps__item__allow_unbound_universes : fsteps -> Prims.bool)
  =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        eager_unfolding = __fname__eager_unfolding;
        inlining = __fname__inlining;
        no_delta_steps = __fname__no_delta_steps;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;_} -> __fname__allow_unbound_universes
  
let (__proj__Mkfsteps__item__reify_ : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        eager_unfolding = __fname__eager_unfolding;
        inlining = __fname__inlining;
        no_delta_steps = __fname__no_delta_steps;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;_} -> __fname__reify_
  
let (__proj__Mkfsteps__item__compress_uvars : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        eager_unfolding = __fname__eager_unfolding;
        inlining = __fname__inlining;
        no_delta_steps = __fname__no_delta_steps;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;_} -> __fname__compress_uvars
  
let (__proj__Mkfsteps__item__no_full_norm : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        eager_unfolding = __fname__eager_unfolding;
        inlining = __fname__inlining;
        no_delta_steps = __fname__no_delta_steps;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;_} -> __fname__no_full_norm
  
let (__proj__Mkfsteps__item__check_no_uvars : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        eager_unfolding = __fname__eager_unfolding;
        inlining = __fname__inlining;
        no_delta_steps = __fname__no_delta_steps;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;_} -> __fname__check_no_uvars
  
let (__proj__Mkfsteps__item__unmeta : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        eager_unfolding = __fname__eager_unfolding;
        inlining = __fname__inlining;
        no_delta_steps = __fname__no_delta_steps;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;_} -> __fname__unmeta
  
let (__proj__Mkfsteps__item__unascribe : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        eager_unfolding = __fname__eager_unfolding;
        inlining = __fname__inlining;
        no_delta_steps = __fname__no_delta_steps;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;_} -> __fname__unascribe
  
let (default_steps : fsteps) =
  {
    beta = true;
    iota = true;
    zeta = true;
    weak = false;
    hnf = false;
    primops = false;
    eager_unfolding = false;
    inlining = false;
    no_delta_steps = false;
    unfold_until = FStar_Pervasives_Native.None;
    unfold_only = FStar_Pervasives_Native.None;
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
    unascribe = false
  } 
let rec (to_fsteps : step Prims.list -> fsteps) =
  fun s  ->
    let add_one1 s1 fs =
      match s1 with
      | Beta  ->
          let uu___92_1100 = fs  in
          {
            beta = true;
            iota = (uu___92_1100.iota);
            zeta = (uu___92_1100.zeta);
            weak = (uu___92_1100.weak);
            hnf = (uu___92_1100.hnf);
            primops = (uu___92_1100.primops);
            eager_unfolding = (uu___92_1100.eager_unfolding);
            inlining = (uu___92_1100.inlining);
            no_delta_steps = (uu___92_1100.no_delta_steps);
            unfold_until = (uu___92_1100.unfold_until);
            unfold_only = (uu___92_1100.unfold_only);
            unfold_attr = (uu___92_1100.unfold_attr);
            unfold_tac = (uu___92_1100.unfold_tac);
            pure_subterms_within_computations =
              (uu___92_1100.pure_subterms_within_computations);
            simplify = (uu___92_1100.simplify);
            erase_universes = (uu___92_1100.erase_universes);
            allow_unbound_universes = (uu___92_1100.allow_unbound_universes);
            reify_ = (uu___92_1100.reify_);
            compress_uvars = (uu___92_1100.compress_uvars);
            no_full_norm = (uu___92_1100.no_full_norm);
            check_no_uvars = (uu___92_1100.check_no_uvars);
            unmeta = (uu___92_1100.unmeta);
            unascribe = (uu___92_1100.unascribe)
          }
      | Iota  ->
          let uu___93_1101 = fs  in
          {
            beta = (uu___93_1101.beta);
            iota = true;
            zeta = (uu___93_1101.zeta);
            weak = (uu___93_1101.weak);
            hnf = (uu___93_1101.hnf);
            primops = (uu___93_1101.primops);
            eager_unfolding = (uu___93_1101.eager_unfolding);
            inlining = (uu___93_1101.inlining);
            no_delta_steps = (uu___93_1101.no_delta_steps);
            unfold_until = (uu___93_1101.unfold_until);
            unfold_only = (uu___93_1101.unfold_only);
            unfold_attr = (uu___93_1101.unfold_attr);
            unfold_tac = (uu___93_1101.unfold_tac);
            pure_subterms_within_computations =
              (uu___93_1101.pure_subterms_within_computations);
            simplify = (uu___93_1101.simplify);
            erase_universes = (uu___93_1101.erase_universes);
            allow_unbound_universes = (uu___93_1101.allow_unbound_universes);
            reify_ = (uu___93_1101.reify_);
            compress_uvars = (uu___93_1101.compress_uvars);
            no_full_norm = (uu___93_1101.no_full_norm);
            check_no_uvars = (uu___93_1101.check_no_uvars);
            unmeta = (uu___93_1101.unmeta);
            unascribe = (uu___93_1101.unascribe)
          }
      | Zeta  ->
          let uu___94_1102 = fs  in
          {
            beta = (uu___94_1102.beta);
            iota = (uu___94_1102.iota);
            zeta = true;
            weak = (uu___94_1102.weak);
            hnf = (uu___94_1102.hnf);
            primops = (uu___94_1102.primops);
            eager_unfolding = (uu___94_1102.eager_unfolding);
            inlining = (uu___94_1102.inlining);
            no_delta_steps = (uu___94_1102.no_delta_steps);
            unfold_until = (uu___94_1102.unfold_until);
            unfold_only = (uu___94_1102.unfold_only);
            unfold_attr = (uu___94_1102.unfold_attr);
            unfold_tac = (uu___94_1102.unfold_tac);
            pure_subterms_within_computations =
              (uu___94_1102.pure_subterms_within_computations);
            simplify = (uu___94_1102.simplify);
            erase_universes = (uu___94_1102.erase_universes);
            allow_unbound_universes = (uu___94_1102.allow_unbound_universes);
            reify_ = (uu___94_1102.reify_);
            compress_uvars = (uu___94_1102.compress_uvars);
            no_full_norm = (uu___94_1102.no_full_norm);
            check_no_uvars = (uu___94_1102.check_no_uvars);
            unmeta = (uu___94_1102.unmeta);
            unascribe = (uu___94_1102.unascribe)
          }
      | Exclude (Beta ) ->
          let uu___95_1103 = fs  in
          {
            beta = false;
            iota = (uu___95_1103.iota);
            zeta = (uu___95_1103.zeta);
            weak = (uu___95_1103.weak);
            hnf = (uu___95_1103.hnf);
            primops = (uu___95_1103.primops);
            eager_unfolding = (uu___95_1103.eager_unfolding);
            inlining = (uu___95_1103.inlining);
            no_delta_steps = (uu___95_1103.no_delta_steps);
            unfold_until = (uu___95_1103.unfold_until);
            unfold_only = (uu___95_1103.unfold_only);
            unfold_attr = (uu___95_1103.unfold_attr);
            unfold_tac = (uu___95_1103.unfold_tac);
            pure_subterms_within_computations =
              (uu___95_1103.pure_subterms_within_computations);
            simplify = (uu___95_1103.simplify);
            erase_universes = (uu___95_1103.erase_universes);
            allow_unbound_universes = (uu___95_1103.allow_unbound_universes);
            reify_ = (uu___95_1103.reify_);
            compress_uvars = (uu___95_1103.compress_uvars);
            no_full_norm = (uu___95_1103.no_full_norm);
            check_no_uvars = (uu___95_1103.check_no_uvars);
            unmeta = (uu___95_1103.unmeta);
            unascribe = (uu___95_1103.unascribe)
          }
      | Exclude (Iota ) ->
          let uu___96_1104 = fs  in
          {
            beta = (uu___96_1104.beta);
            iota = false;
            zeta = (uu___96_1104.zeta);
            weak = (uu___96_1104.weak);
            hnf = (uu___96_1104.hnf);
            primops = (uu___96_1104.primops);
            eager_unfolding = (uu___96_1104.eager_unfolding);
            inlining = (uu___96_1104.inlining);
            no_delta_steps = (uu___96_1104.no_delta_steps);
            unfold_until = (uu___96_1104.unfold_until);
            unfold_only = (uu___96_1104.unfold_only);
            unfold_attr = (uu___96_1104.unfold_attr);
            unfold_tac = (uu___96_1104.unfold_tac);
            pure_subterms_within_computations =
              (uu___96_1104.pure_subterms_within_computations);
            simplify = (uu___96_1104.simplify);
            erase_universes = (uu___96_1104.erase_universes);
            allow_unbound_universes = (uu___96_1104.allow_unbound_universes);
            reify_ = (uu___96_1104.reify_);
            compress_uvars = (uu___96_1104.compress_uvars);
            no_full_norm = (uu___96_1104.no_full_norm);
            check_no_uvars = (uu___96_1104.check_no_uvars);
            unmeta = (uu___96_1104.unmeta);
            unascribe = (uu___96_1104.unascribe)
          }
      | Exclude (Zeta ) ->
          let uu___97_1105 = fs  in
          {
            beta = (uu___97_1105.beta);
            iota = (uu___97_1105.iota);
            zeta = false;
            weak = (uu___97_1105.weak);
            hnf = (uu___97_1105.hnf);
            primops = (uu___97_1105.primops);
            eager_unfolding = (uu___97_1105.eager_unfolding);
            inlining = (uu___97_1105.inlining);
            no_delta_steps = (uu___97_1105.no_delta_steps);
            unfold_until = (uu___97_1105.unfold_until);
            unfold_only = (uu___97_1105.unfold_only);
            unfold_attr = (uu___97_1105.unfold_attr);
            unfold_tac = (uu___97_1105.unfold_tac);
            pure_subterms_within_computations =
              (uu___97_1105.pure_subterms_within_computations);
            simplify = (uu___97_1105.simplify);
            erase_universes = (uu___97_1105.erase_universes);
            allow_unbound_universes = (uu___97_1105.allow_unbound_universes);
            reify_ = (uu___97_1105.reify_);
            compress_uvars = (uu___97_1105.compress_uvars);
            no_full_norm = (uu___97_1105.no_full_norm);
            check_no_uvars = (uu___97_1105.check_no_uvars);
            unmeta = (uu___97_1105.unmeta);
            unascribe = (uu___97_1105.unascribe)
          }
      | Exclude uu____1106 -> failwith "Bad exclude"
      | Weak  ->
          let uu___98_1107 = fs  in
          {
            beta = (uu___98_1107.beta);
            iota = (uu___98_1107.iota);
            zeta = (uu___98_1107.zeta);
            weak = true;
            hnf = (uu___98_1107.hnf);
            primops = (uu___98_1107.primops);
            eager_unfolding = (uu___98_1107.eager_unfolding);
            inlining = (uu___98_1107.inlining);
            no_delta_steps = (uu___98_1107.no_delta_steps);
            unfold_until = (uu___98_1107.unfold_until);
            unfold_only = (uu___98_1107.unfold_only);
            unfold_attr = (uu___98_1107.unfold_attr);
            unfold_tac = (uu___98_1107.unfold_tac);
            pure_subterms_within_computations =
              (uu___98_1107.pure_subterms_within_computations);
            simplify = (uu___98_1107.simplify);
            erase_universes = (uu___98_1107.erase_universes);
            allow_unbound_universes = (uu___98_1107.allow_unbound_universes);
            reify_ = (uu___98_1107.reify_);
            compress_uvars = (uu___98_1107.compress_uvars);
            no_full_norm = (uu___98_1107.no_full_norm);
            check_no_uvars = (uu___98_1107.check_no_uvars);
            unmeta = (uu___98_1107.unmeta);
            unascribe = (uu___98_1107.unascribe)
          }
      | HNF  ->
          let uu___99_1108 = fs  in
          {
            beta = (uu___99_1108.beta);
            iota = (uu___99_1108.iota);
            zeta = (uu___99_1108.zeta);
            weak = (uu___99_1108.weak);
            hnf = true;
            primops = (uu___99_1108.primops);
            eager_unfolding = (uu___99_1108.eager_unfolding);
            inlining = (uu___99_1108.inlining);
            no_delta_steps = (uu___99_1108.no_delta_steps);
            unfold_until = (uu___99_1108.unfold_until);
            unfold_only = (uu___99_1108.unfold_only);
            unfold_attr = (uu___99_1108.unfold_attr);
            unfold_tac = (uu___99_1108.unfold_tac);
            pure_subterms_within_computations =
              (uu___99_1108.pure_subterms_within_computations);
            simplify = (uu___99_1108.simplify);
            erase_universes = (uu___99_1108.erase_universes);
            allow_unbound_universes = (uu___99_1108.allow_unbound_universes);
            reify_ = (uu___99_1108.reify_);
            compress_uvars = (uu___99_1108.compress_uvars);
            no_full_norm = (uu___99_1108.no_full_norm);
            check_no_uvars = (uu___99_1108.check_no_uvars);
            unmeta = (uu___99_1108.unmeta);
            unascribe = (uu___99_1108.unascribe)
          }
      | Primops  ->
          let uu___100_1109 = fs  in
          {
            beta = (uu___100_1109.beta);
            iota = (uu___100_1109.iota);
            zeta = (uu___100_1109.zeta);
            weak = (uu___100_1109.weak);
            hnf = (uu___100_1109.hnf);
            primops = true;
            eager_unfolding = (uu___100_1109.eager_unfolding);
            inlining = (uu___100_1109.inlining);
            no_delta_steps = (uu___100_1109.no_delta_steps);
            unfold_until = (uu___100_1109.unfold_until);
            unfold_only = (uu___100_1109.unfold_only);
            unfold_attr = (uu___100_1109.unfold_attr);
            unfold_tac = (uu___100_1109.unfold_tac);
            pure_subterms_within_computations =
              (uu___100_1109.pure_subterms_within_computations);
            simplify = (uu___100_1109.simplify);
            erase_universes = (uu___100_1109.erase_universes);
            allow_unbound_universes = (uu___100_1109.allow_unbound_universes);
            reify_ = (uu___100_1109.reify_);
            compress_uvars = (uu___100_1109.compress_uvars);
            no_full_norm = (uu___100_1109.no_full_norm);
            check_no_uvars = (uu___100_1109.check_no_uvars);
            unmeta = (uu___100_1109.unmeta);
            unascribe = (uu___100_1109.unascribe)
          }
      | Eager_unfolding  ->
          let uu___101_1110 = fs  in
          {
            beta = (uu___101_1110.beta);
            iota = (uu___101_1110.iota);
            zeta = (uu___101_1110.zeta);
            weak = (uu___101_1110.weak);
            hnf = (uu___101_1110.hnf);
            primops = (uu___101_1110.primops);
            eager_unfolding = true;
            inlining = (uu___101_1110.inlining);
            no_delta_steps = (uu___101_1110.no_delta_steps);
            unfold_until = (uu___101_1110.unfold_until);
            unfold_only = (uu___101_1110.unfold_only);
            unfold_attr = (uu___101_1110.unfold_attr);
            unfold_tac = (uu___101_1110.unfold_tac);
            pure_subterms_within_computations =
              (uu___101_1110.pure_subterms_within_computations);
            simplify = (uu___101_1110.simplify);
            erase_universes = (uu___101_1110.erase_universes);
            allow_unbound_universes = (uu___101_1110.allow_unbound_universes);
            reify_ = (uu___101_1110.reify_);
            compress_uvars = (uu___101_1110.compress_uvars);
            no_full_norm = (uu___101_1110.no_full_norm);
            check_no_uvars = (uu___101_1110.check_no_uvars);
            unmeta = (uu___101_1110.unmeta);
            unascribe = (uu___101_1110.unascribe)
          }
      | Inlining  ->
          let uu___102_1111 = fs  in
          {
            beta = (uu___102_1111.beta);
            iota = (uu___102_1111.iota);
            zeta = (uu___102_1111.zeta);
            weak = (uu___102_1111.weak);
            hnf = (uu___102_1111.hnf);
            primops = (uu___102_1111.primops);
            eager_unfolding = (uu___102_1111.eager_unfolding);
            inlining = true;
            no_delta_steps = (uu___102_1111.no_delta_steps);
            unfold_until = (uu___102_1111.unfold_until);
            unfold_only = (uu___102_1111.unfold_only);
            unfold_attr = (uu___102_1111.unfold_attr);
            unfold_tac = (uu___102_1111.unfold_tac);
            pure_subterms_within_computations =
              (uu___102_1111.pure_subterms_within_computations);
            simplify = (uu___102_1111.simplify);
            erase_universes = (uu___102_1111.erase_universes);
            allow_unbound_universes = (uu___102_1111.allow_unbound_universes);
            reify_ = (uu___102_1111.reify_);
            compress_uvars = (uu___102_1111.compress_uvars);
            no_full_norm = (uu___102_1111.no_full_norm);
            check_no_uvars = (uu___102_1111.check_no_uvars);
            unmeta = (uu___102_1111.unmeta);
            unascribe = (uu___102_1111.unascribe)
          }
      | NoDeltaSteps  ->
          let uu___103_1112 = fs  in
          {
            beta = (uu___103_1112.beta);
            iota = (uu___103_1112.iota);
            zeta = (uu___103_1112.zeta);
            weak = (uu___103_1112.weak);
            hnf = (uu___103_1112.hnf);
            primops = (uu___103_1112.primops);
            eager_unfolding = (uu___103_1112.eager_unfolding);
            inlining = (uu___103_1112.inlining);
            no_delta_steps = true;
            unfold_until = (uu___103_1112.unfold_until);
            unfold_only = (uu___103_1112.unfold_only);
            unfold_attr = (uu___103_1112.unfold_attr);
            unfold_tac = (uu___103_1112.unfold_tac);
            pure_subterms_within_computations =
              (uu___103_1112.pure_subterms_within_computations);
            simplify = (uu___103_1112.simplify);
            erase_universes = (uu___103_1112.erase_universes);
            allow_unbound_universes = (uu___103_1112.allow_unbound_universes);
            reify_ = (uu___103_1112.reify_);
            compress_uvars = (uu___103_1112.compress_uvars);
            no_full_norm = (uu___103_1112.no_full_norm);
            check_no_uvars = (uu___103_1112.check_no_uvars);
            unmeta = (uu___103_1112.unmeta);
            unascribe = (uu___103_1112.unascribe)
          }
      | UnfoldUntil d ->
          let uu___104_1114 = fs  in
          {
            beta = (uu___104_1114.beta);
            iota = (uu___104_1114.iota);
            zeta = (uu___104_1114.zeta);
            weak = (uu___104_1114.weak);
            hnf = (uu___104_1114.hnf);
            primops = (uu___104_1114.primops);
            eager_unfolding = (uu___104_1114.eager_unfolding);
            inlining = (uu___104_1114.inlining);
            no_delta_steps = (uu___104_1114.no_delta_steps);
            unfold_until = (FStar_Pervasives_Native.Some d);
            unfold_only = (uu___104_1114.unfold_only);
            unfold_attr = (uu___104_1114.unfold_attr);
            unfold_tac = (uu___104_1114.unfold_tac);
            pure_subterms_within_computations =
              (uu___104_1114.pure_subterms_within_computations);
            simplify = (uu___104_1114.simplify);
            erase_universes = (uu___104_1114.erase_universes);
            allow_unbound_universes = (uu___104_1114.allow_unbound_universes);
            reify_ = (uu___104_1114.reify_);
            compress_uvars = (uu___104_1114.compress_uvars);
            no_full_norm = (uu___104_1114.no_full_norm);
            check_no_uvars = (uu___104_1114.check_no_uvars);
            unmeta = (uu___104_1114.unmeta);
            unascribe = (uu___104_1114.unascribe)
          }
      | UnfoldOnly lids ->
          let uu___105_1118 = fs  in
          {
            beta = (uu___105_1118.beta);
            iota = (uu___105_1118.iota);
            zeta = (uu___105_1118.zeta);
            weak = (uu___105_1118.weak);
            hnf = (uu___105_1118.hnf);
            primops = (uu___105_1118.primops);
            eager_unfolding = (uu___105_1118.eager_unfolding);
            inlining = (uu___105_1118.inlining);
            no_delta_steps = (uu___105_1118.no_delta_steps);
            unfold_until = (uu___105_1118.unfold_until);
            unfold_only = (FStar_Pervasives_Native.Some lids);
            unfold_attr = (uu___105_1118.unfold_attr);
            unfold_tac = (uu___105_1118.unfold_tac);
            pure_subterms_within_computations =
              (uu___105_1118.pure_subterms_within_computations);
            simplify = (uu___105_1118.simplify);
            erase_universes = (uu___105_1118.erase_universes);
            allow_unbound_universes = (uu___105_1118.allow_unbound_universes);
            reify_ = (uu___105_1118.reify_);
            compress_uvars = (uu___105_1118.compress_uvars);
            no_full_norm = (uu___105_1118.no_full_norm);
            check_no_uvars = (uu___105_1118.check_no_uvars);
            unmeta = (uu___105_1118.unmeta);
            unascribe = (uu___105_1118.unascribe)
          }
      | UnfoldAttr attr ->
          let uu___106_1122 = fs  in
          {
            beta = (uu___106_1122.beta);
            iota = (uu___106_1122.iota);
            zeta = (uu___106_1122.zeta);
            weak = (uu___106_1122.weak);
            hnf = (uu___106_1122.hnf);
            primops = (uu___106_1122.primops);
            eager_unfolding = (uu___106_1122.eager_unfolding);
            inlining = (uu___106_1122.inlining);
            no_delta_steps = (uu___106_1122.no_delta_steps);
            unfold_until = (uu___106_1122.unfold_until);
            unfold_only = (uu___106_1122.unfold_only);
            unfold_attr = (FStar_Pervasives_Native.Some attr);
            unfold_tac = (uu___106_1122.unfold_tac);
            pure_subterms_within_computations =
              (uu___106_1122.pure_subterms_within_computations);
            simplify = (uu___106_1122.simplify);
            erase_universes = (uu___106_1122.erase_universes);
            allow_unbound_universes = (uu___106_1122.allow_unbound_universes);
            reify_ = (uu___106_1122.reify_);
            compress_uvars = (uu___106_1122.compress_uvars);
            no_full_norm = (uu___106_1122.no_full_norm);
            check_no_uvars = (uu___106_1122.check_no_uvars);
            unmeta = (uu___106_1122.unmeta);
            unascribe = (uu___106_1122.unascribe)
          }
      | UnfoldTac  ->
          let uu___107_1123 = fs  in
          {
            beta = (uu___107_1123.beta);
            iota = (uu___107_1123.iota);
            zeta = (uu___107_1123.zeta);
            weak = (uu___107_1123.weak);
            hnf = (uu___107_1123.hnf);
            primops = (uu___107_1123.primops);
            eager_unfolding = (uu___107_1123.eager_unfolding);
            inlining = (uu___107_1123.inlining);
            no_delta_steps = (uu___107_1123.no_delta_steps);
            unfold_until = (uu___107_1123.unfold_until);
            unfold_only = (uu___107_1123.unfold_only);
            unfold_attr = (uu___107_1123.unfold_attr);
            unfold_tac = true;
            pure_subterms_within_computations =
              (uu___107_1123.pure_subterms_within_computations);
            simplify = (uu___107_1123.simplify);
            erase_universes = (uu___107_1123.erase_universes);
            allow_unbound_universes = (uu___107_1123.allow_unbound_universes);
            reify_ = (uu___107_1123.reify_);
            compress_uvars = (uu___107_1123.compress_uvars);
            no_full_norm = (uu___107_1123.no_full_norm);
            check_no_uvars = (uu___107_1123.check_no_uvars);
            unmeta = (uu___107_1123.unmeta);
            unascribe = (uu___107_1123.unascribe)
          }
      | PureSubtermsWithinComputations  ->
          let uu___108_1124 = fs  in
          {
            beta = (uu___108_1124.beta);
            iota = (uu___108_1124.iota);
            zeta = (uu___108_1124.zeta);
            weak = (uu___108_1124.weak);
            hnf = (uu___108_1124.hnf);
            primops = (uu___108_1124.primops);
            eager_unfolding = (uu___108_1124.eager_unfolding);
            inlining = (uu___108_1124.inlining);
            no_delta_steps = (uu___108_1124.no_delta_steps);
            unfold_until = (uu___108_1124.unfold_until);
            unfold_only = (uu___108_1124.unfold_only);
            unfold_attr = (uu___108_1124.unfold_attr);
            unfold_tac = (uu___108_1124.unfold_tac);
            pure_subterms_within_computations = true;
            simplify = (uu___108_1124.simplify);
            erase_universes = (uu___108_1124.erase_universes);
            allow_unbound_universes = (uu___108_1124.allow_unbound_universes);
            reify_ = (uu___108_1124.reify_);
            compress_uvars = (uu___108_1124.compress_uvars);
            no_full_norm = (uu___108_1124.no_full_norm);
            check_no_uvars = (uu___108_1124.check_no_uvars);
            unmeta = (uu___108_1124.unmeta);
            unascribe = (uu___108_1124.unascribe)
          }
      | Simplify  ->
          let uu___109_1125 = fs  in
          {
            beta = (uu___109_1125.beta);
            iota = (uu___109_1125.iota);
            zeta = (uu___109_1125.zeta);
            weak = (uu___109_1125.weak);
            hnf = (uu___109_1125.hnf);
            primops = (uu___109_1125.primops);
            eager_unfolding = (uu___109_1125.eager_unfolding);
            inlining = (uu___109_1125.inlining);
            no_delta_steps = (uu___109_1125.no_delta_steps);
            unfold_until = (uu___109_1125.unfold_until);
            unfold_only = (uu___109_1125.unfold_only);
            unfold_attr = (uu___109_1125.unfold_attr);
            unfold_tac = (uu___109_1125.unfold_tac);
            pure_subterms_within_computations =
              (uu___109_1125.pure_subterms_within_computations);
            simplify = true;
            erase_universes = (uu___109_1125.erase_universes);
            allow_unbound_universes = (uu___109_1125.allow_unbound_universes);
            reify_ = (uu___109_1125.reify_);
            compress_uvars = (uu___109_1125.compress_uvars);
            no_full_norm = (uu___109_1125.no_full_norm);
            check_no_uvars = (uu___109_1125.check_no_uvars);
            unmeta = (uu___109_1125.unmeta);
            unascribe = (uu___109_1125.unascribe)
          }
      | EraseUniverses  ->
          let uu___110_1126 = fs  in
          {
            beta = (uu___110_1126.beta);
            iota = (uu___110_1126.iota);
            zeta = (uu___110_1126.zeta);
            weak = (uu___110_1126.weak);
            hnf = (uu___110_1126.hnf);
            primops = (uu___110_1126.primops);
            eager_unfolding = (uu___110_1126.eager_unfolding);
            inlining = (uu___110_1126.inlining);
            no_delta_steps = (uu___110_1126.no_delta_steps);
            unfold_until = (uu___110_1126.unfold_until);
            unfold_only = (uu___110_1126.unfold_only);
            unfold_attr = (uu___110_1126.unfold_attr);
            unfold_tac = (uu___110_1126.unfold_tac);
            pure_subterms_within_computations =
              (uu___110_1126.pure_subterms_within_computations);
            simplify = (uu___110_1126.simplify);
            erase_universes = true;
            allow_unbound_universes = (uu___110_1126.allow_unbound_universes);
            reify_ = (uu___110_1126.reify_);
            compress_uvars = (uu___110_1126.compress_uvars);
            no_full_norm = (uu___110_1126.no_full_norm);
            check_no_uvars = (uu___110_1126.check_no_uvars);
            unmeta = (uu___110_1126.unmeta);
            unascribe = (uu___110_1126.unascribe)
          }
      | AllowUnboundUniverses  ->
          let uu___111_1127 = fs  in
          {
            beta = (uu___111_1127.beta);
            iota = (uu___111_1127.iota);
            zeta = (uu___111_1127.zeta);
            weak = (uu___111_1127.weak);
            hnf = (uu___111_1127.hnf);
            primops = (uu___111_1127.primops);
            eager_unfolding = (uu___111_1127.eager_unfolding);
            inlining = (uu___111_1127.inlining);
            no_delta_steps = (uu___111_1127.no_delta_steps);
            unfold_until = (uu___111_1127.unfold_until);
            unfold_only = (uu___111_1127.unfold_only);
            unfold_attr = (uu___111_1127.unfold_attr);
            unfold_tac = (uu___111_1127.unfold_tac);
            pure_subterms_within_computations =
              (uu___111_1127.pure_subterms_within_computations);
            simplify = (uu___111_1127.simplify);
            erase_universes = (uu___111_1127.erase_universes);
            allow_unbound_universes = true;
            reify_ = (uu___111_1127.reify_);
            compress_uvars = (uu___111_1127.compress_uvars);
            no_full_norm = (uu___111_1127.no_full_norm);
            check_no_uvars = (uu___111_1127.check_no_uvars);
            unmeta = (uu___111_1127.unmeta);
            unascribe = (uu___111_1127.unascribe)
          }
      | Reify  ->
          let uu___112_1128 = fs  in
          {
            beta = (uu___112_1128.beta);
            iota = (uu___112_1128.iota);
            zeta = (uu___112_1128.zeta);
            weak = (uu___112_1128.weak);
            hnf = (uu___112_1128.hnf);
            primops = (uu___112_1128.primops);
            eager_unfolding = (uu___112_1128.eager_unfolding);
            inlining = (uu___112_1128.inlining);
            no_delta_steps = (uu___112_1128.no_delta_steps);
            unfold_until = (uu___112_1128.unfold_until);
            unfold_only = (uu___112_1128.unfold_only);
            unfold_attr = (uu___112_1128.unfold_attr);
            unfold_tac = (uu___112_1128.unfold_tac);
            pure_subterms_within_computations =
              (uu___112_1128.pure_subterms_within_computations);
            simplify = (uu___112_1128.simplify);
            erase_universes = (uu___112_1128.erase_universes);
            allow_unbound_universes = (uu___112_1128.allow_unbound_universes);
            reify_ = true;
            compress_uvars = (uu___112_1128.compress_uvars);
            no_full_norm = (uu___112_1128.no_full_norm);
            check_no_uvars = (uu___112_1128.check_no_uvars);
            unmeta = (uu___112_1128.unmeta);
            unascribe = (uu___112_1128.unascribe)
          }
      | CompressUvars  ->
          let uu___113_1129 = fs  in
          {
            beta = (uu___113_1129.beta);
            iota = (uu___113_1129.iota);
            zeta = (uu___113_1129.zeta);
            weak = (uu___113_1129.weak);
            hnf = (uu___113_1129.hnf);
            primops = (uu___113_1129.primops);
            eager_unfolding = (uu___113_1129.eager_unfolding);
            inlining = (uu___113_1129.inlining);
            no_delta_steps = (uu___113_1129.no_delta_steps);
            unfold_until = (uu___113_1129.unfold_until);
            unfold_only = (uu___113_1129.unfold_only);
            unfold_attr = (uu___113_1129.unfold_attr);
            unfold_tac = (uu___113_1129.unfold_tac);
            pure_subterms_within_computations =
              (uu___113_1129.pure_subterms_within_computations);
            simplify = (uu___113_1129.simplify);
            erase_universes = (uu___113_1129.erase_universes);
            allow_unbound_universes = (uu___113_1129.allow_unbound_universes);
            reify_ = (uu___113_1129.reify_);
            compress_uvars = true;
            no_full_norm = (uu___113_1129.no_full_norm);
            check_no_uvars = (uu___113_1129.check_no_uvars);
            unmeta = (uu___113_1129.unmeta);
            unascribe = (uu___113_1129.unascribe)
          }
      | NoFullNorm  ->
          let uu___114_1130 = fs  in
          {
            beta = (uu___114_1130.beta);
            iota = (uu___114_1130.iota);
            zeta = (uu___114_1130.zeta);
            weak = (uu___114_1130.weak);
            hnf = (uu___114_1130.hnf);
            primops = (uu___114_1130.primops);
            eager_unfolding = (uu___114_1130.eager_unfolding);
            inlining = (uu___114_1130.inlining);
            no_delta_steps = (uu___114_1130.no_delta_steps);
            unfold_until = (uu___114_1130.unfold_until);
            unfold_only = (uu___114_1130.unfold_only);
            unfold_attr = (uu___114_1130.unfold_attr);
            unfold_tac = (uu___114_1130.unfold_tac);
            pure_subterms_within_computations =
              (uu___114_1130.pure_subterms_within_computations);
            simplify = (uu___114_1130.simplify);
            erase_universes = (uu___114_1130.erase_universes);
            allow_unbound_universes = (uu___114_1130.allow_unbound_universes);
            reify_ = (uu___114_1130.reify_);
            compress_uvars = (uu___114_1130.compress_uvars);
            no_full_norm = true;
            check_no_uvars = (uu___114_1130.check_no_uvars);
            unmeta = (uu___114_1130.unmeta);
            unascribe = (uu___114_1130.unascribe)
          }
      | CheckNoUvars  ->
          let uu___115_1131 = fs  in
          {
            beta = (uu___115_1131.beta);
            iota = (uu___115_1131.iota);
            zeta = (uu___115_1131.zeta);
            weak = (uu___115_1131.weak);
            hnf = (uu___115_1131.hnf);
            primops = (uu___115_1131.primops);
            eager_unfolding = (uu___115_1131.eager_unfolding);
            inlining = (uu___115_1131.inlining);
            no_delta_steps = (uu___115_1131.no_delta_steps);
            unfold_until = (uu___115_1131.unfold_until);
            unfold_only = (uu___115_1131.unfold_only);
            unfold_attr = (uu___115_1131.unfold_attr);
            unfold_tac = (uu___115_1131.unfold_tac);
            pure_subterms_within_computations =
              (uu___115_1131.pure_subterms_within_computations);
            simplify = (uu___115_1131.simplify);
            erase_universes = (uu___115_1131.erase_universes);
            allow_unbound_universes = (uu___115_1131.allow_unbound_universes);
            reify_ = (uu___115_1131.reify_);
            compress_uvars = (uu___115_1131.compress_uvars);
            no_full_norm = (uu___115_1131.no_full_norm);
            check_no_uvars = true;
            unmeta = (uu___115_1131.unmeta);
            unascribe = (uu___115_1131.unascribe)
          }
      | Unmeta  ->
          let uu___116_1132 = fs  in
          {
            beta = (uu___116_1132.beta);
            iota = (uu___116_1132.iota);
            zeta = (uu___116_1132.zeta);
            weak = (uu___116_1132.weak);
            hnf = (uu___116_1132.hnf);
            primops = (uu___116_1132.primops);
            eager_unfolding = (uu___116_1132.eager_unfolding);
            inlining = (uu___116_1132.inlining);
            no_delta_steps = (uu___116_1132.no_delta_steps);
            unfold_until = (uu___116_1132.unfold_until);
            unfold_only = (uu___116_1132.unfold_only);
            unfold_attr = (uu___116_1132.unfold_attr);
            unfold_tac = (uu___116_1132.unfold_tac);
            pure_subterms_within_computations =
              (uu___116_1132.pure_subterms_within_computations);
            simplify = (uu___116_1132.simplify);
            erase_universes = (uu___116_1132.erase_universes);
            allow_unbound_universes = (uu___116_1132.allow_unbound_universes);
            reify_ = (uu___116_1132.reify_);
            compress_uvars = (uu___116_1132.compress_uvars);
            no_full_norm = (uu___116_1132.no_full_norm);
            check_no_uvars = (uu___116_1132.check_no_uvars);
            unmeta = true;
            unascribe = (uu___116_1132.unascribe)
          }
      | Unascribe  ->
          let uu___117_1133 = fs  in
          {
            beta = (uu___117_1133.beta);
            iota = (uu___117_1133.iota);
            zeta = (uu___117_1133.zeta);
            weak = (uu___117_1133.weak);
            hnf = (uu___117_1133.hnf);
            primops = (uu___117_1133.primops);
            eager_unfolding = (uu___117_1133.eager_unfolding);
            inlining = (uu___117_1133.inlining);
            no_delta_steps = (uu___117_1133.no_delta_steps);
            unfold_until = (uu___117_1133.unfold_until);
            unfold_only = (uu___117_1133.unfold_only);
            unfold_attr = (uu___117_1133.unfold_attr);
            unfold_tac = (uu___117_1133.unfold_tac);
            pure_subterms_within_computations =
              (uu___117_1133.pure_subterms_within_computations);
            simplify = (uu___117_1133.simplify);
            erase_universes = (uu___117_1133.erase_universes);
            allow_unbound_universes = (uu___117_1133.allow_unbound_universes);
            reify_ = (uu___117_1133.reify_);
            compress_uvars = (uu___117_1133.compress_uvars);
            no_full_norm = (uu___117_1133.no_full_norm);
            check_no_uvars = (uu___117_1133.check_no_uvars);
            unmeta = (uu___117_1133.unmeta);
            unascribe = true
          }
       in
    FStar_List.fold_right add_one1 s default_steps
  
type psc =
  {
  psc_range: FStar_Range.range ;
  psc_subst: Prims.unit -> FStar_Syntax_Syntax.subst_t }[@@deriving show]
let (__proj__Mkpsc__item__psc_range : psc -> FStar_Range.range) =
  fun projectee  ->
    match projectee with
    | { psc_range = __fname__psc_range; psc_subst = __fname__psc_subst;_} ->
        __fname__psc_range
  
let (__proj__Mkpsc__item__psc_subst :
  psc -> Prims.unit -> FStar_Syntax_Syntax.subst_t) =
  fun projectee  ->
    match projectee with
    | { psc_range = __fname__psc_range; psc_subst = __fname__psc_subst;_} ->
        __fname__psc_subst
  
let (null_psc : psc) =
  { psc_range = FStar_Range.dummyRange; psc_subst = (fun uu____1165  -> []) } 
let (psc_range : psc -> FStar_Range.range) = fun psc  -> psc.psc_range 
let (psc_subst : psc -> FStar_Syntax_Syntax.subst_t) =
  fun psc  -> psc.psc_subst () 
type primitive_step =
  {
  name: FStar_Ident.lid ;
  arity: Prims.int ;
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
        strong_reduction_ok = __fname__strong_reduction_ok;
        requires_binder_substitution = __fname__requires_binder_substitution;
        interpretation = __fname__interpretation;_} -> __fname__name
  
let (__proj__Mkprimitive_step__item__arity : primitive_step -> Prims.int) =
  fun projectee  ->
    match projectee with
    | { name = __fname__name; arity = __fname__arity;
        strong_reduction_ok = __fname__strong_reduction_ok;
        requires_binder_substitution = __fname__requires_binder_substitution;
        interpretation = __fname__interpretation;_} -> __fname__arity
  
let (__proj__Mkprimitive_step__item__strong_reduction_ok :
  primitive_step -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { name = __fname__name; arity = __fname__arity;
        strong_reduction_ok = __fname__strong_reduction_ok;
        requires_binder_substitution = __fname__requires_binder_substitution;
        interpretation = __fname__interpretation;_} ->
        __fname__strong_reduction_ok
  
let (__proj__Mkprimitive_step__item__requires_binder_substitution :
  primitive_step -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { name = __fname__name; arity = __fname__arity;
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
    match projectee with | Clos _0 -> true | uu____1366 -> false
  
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
    match projectee with | Univ _0 -> true | uu____1468 -> false
  
let (__proj__Univ__item___0 : closure -> FStar_Syntax_Syntax.universe) =
  fun projectee  -> match projectee with | Univ _0 -> _0 
let (uu___is_Dummy : closure -> Prims.bool) =
  fun projectee  ->
    match projectee with | Dummy  -> true | uu____1479 -> false
  
type env =
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
    FStar_Pervasives_Native.tuple2 Prims.list[@@deriving show]
let (dummy :
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
    FStar_Pervasives_Native.tuple2)
  = (FStar_Pervasives_Native.None, Dummy) 
let (closure_to_string : closure -> Prims.string) =
  fun uu___75_1498  ->
    match uu___75_1498 with
    | Clos (uu____1499,t,uu____1501,uu____1502) ->
        FStar_Syntax_Print.term_to_string t
    | Univ uu____1547 -> "Univ"
    | Dummy  -> "dummy"
  
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
             FStar_Util.psmap_add m1 (FStar_Ident.text_of_lid p.name) p) l m
  
let (prim_from_list :
  primitive_step Prims.list -> primitive_step FStar_Util.psmap) =
  fun l  ->
    let uu____1809 = FStar_Util.psmap_empty ()  in add_steps uu____1809 l
  
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
  | Match of (env,branches,FStar_Range.range) FStar_Pervasives_Native.tuple3
  
  | Abs of
  (env,FStar_Syntax_Syntax.binders,env,FStar_Syntax_Syntax.residual_comp
                                         FStar_Pervasives_Native.option,
  FStar_Range.range) FStar_Pervasives_Native.tuple5 
  | App of
  (env,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual,FStar_Range.range)
  FStar_Pervasives_Native.tuple4 
  | Meta of (FStar_Syntax_Syntax.metadata,FStar_Range.range)
  FStar_Pervasives_Native.tuple2 
  | Let of
  (env,FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.letbinding,FStar_Range.range)
  FStar_Pervasives_Native.tuple4 
  | Cfg of cfg 
  | Debug of (FStar_Syntax_Syntax.term,FStar_Util.time)
  FStar_Pervasives_Native.tuple2 [@@deriving show]
let (uu___is_Arg : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Arg _0 -> true | uu____1953 -> false
  
let (__proj__Arg__item___0 :
  stack_elt ->
    (closure,FStar_Syntax_Syntax.aqual,FStar_Range.range)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | Arg _0 -> _0 
let (uu___is_UnivArgs : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnivArgs _0 -> true | uu____1989 -> false
  
let (__proj__UnivArgs__item___0 :
  stack_elt ->
    (FStar_Syntax_Syntax.universe Prims.list,FStar_Range.range)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | UnivArgs _0 -> _0 
let (uu___is_MemoLazy : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | MemoLazy _0 -> true | uu____2025 -> false
  
let (__proj__MemoLazy__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.term) FStar_Pervasives_Native.tuple2
      FStar_Syntax_Syntax.memo)
  = fun projectee  -> match projectee with | MemoLazy _0 -> _0 
let (uu___is_Match : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____2094 -> false
  
let (__proj__Match__item___0 :
  stack_elt ->
    (env,branches,FStar_Range.range) FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | Match _0 -> _0 
let (uu___is_Abs : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Abs _0 -> true | uu____2136 -> false
  
let (__proj__Abs__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.binders,env,FStar_Syntax_Syntax.residual_comp
                                           FStar_Pervasives_Native.option,
      FStar_Range.range) FStar_Pervasives_Native.tuple5)
  = fun projectee  -> match projectee with | Abs _0 -> _0 
let (uu___is_App : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____2192 -> false
  
let (__proj__App__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual,FStar_Range.range)
      FStar_Pervasives_Native.tuple4)
  = fun projectee  -> match projectee with | App _0 -> _0 
let (uu___is_Meta : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Meta _0 -> true | uu____2232 -> false
  
let (__proj__Meta__item___0 :
  stack_elt ->
    (FStar_Syntax_Syntax.metadata,FStar_Range.range)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Meta _0 -> _0 
let (uu___is_Let : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Let _0 -> true | uu____2264 -> false
  
let (__proj__Let__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.letbinding,FStar_Range.range)
      FStar_Pervasives_Native.tuple4)
  = fun projectee  -> match projectee with | Let _0 -> _0 
let (uu___is_Cfg : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Cfg _0 -> true | uu____2300 -> false
  
let (__proj__Cfg__item___0 : stack_elt -> cfg) =
  fun projectee  -> match projectee with | Cfg _0 -> _0 
let (uu___is_Debug : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Debug _0 -> true | uu____2316 -> false
  
let (__proj__Debug__item___0 :
  stack_elt ->
    (FStar_Syntax_Syntax.term,FStar_Util.time) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Debug _0 -> _0 
type stack = stack_elt Prims.list[@@deriving show]
let mk :
  'Auu____2341 .
    'Auu____2341 ->
      FStar_Range.range -> 'Auu____2341 FStar_Syntax_Syntax.syntax
  =
  fun t  -> fun r  -> FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None r 
let set_memo : 'a . cfg -> 'a FStar_Syntax_Syntax.memo -> 'a -> Prims.unit =
  fun cfg  ->
    fun r  ->
      fun t  ->
        if cfg.memoize_lazy
        then
          let uu____2395 = FStar_ST.op_Bang r  in
          match uu____2395 with
          | FStar_Pervasives_Native.Some uu____2443 ->
              failwith "Unexpected set_memo: thunk already evaluated"
          | FStar_Pervasives_Native.None  ->
              FStar_ST.op_Colon_Equals r (FStar_Pervasives_Native.Some t)
        else ()
  
let (env_to_string : closure Prims.list -> Prims.string) =
  fun env  ->
    let uu____2497 = FStar_List.map closure_to_string env  in
    FStar_All.pipe_right uu____2497 (FStar_String.concat "; ")
  
let (stack_elt_to_string : stack_elt -> Prims.string) =
  fun uu___76_2504  ->
    match uu___76_2504 with
    | Arg (c,uu____2506,uu____2507) ->
        let uu____2508 = closure_to_string c  in
        FStar_Util.format1 "Closure %s" uu____2508
    | MemoLazy uu____2509 -> "MemoLazy"
    | Abs (uu____2516,bs,uu____2518,uu____2519,uu____2520) ->
        let uu____2525 =
          FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs)
           in
        FStar_Util.format1 "Abs %s" uu____2525
    | UnivArgs uu____2530 -> "UnivArgs"
    | Match uu____2537 -> "Match"
    | App (uu____2544,t,uu____2546,uu____2547) ->
        let uu____2548 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "App %s" uu____2548
    | Meta (m,uu____2550) -> "Meta"
    | Let uu____2551 -> "Let"
    | Cfg uu____2560 -> "Cfg"
    | Debug (t,uu____2562) ->
        let uu____2563 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "Debug %s" uu____2563
  
let (stack_to_string : stack_elt Prims.list -> Prims.string) =
  fun s  ->
    let uu____2571 = FStar_List.map stack_elt_to_string s  in
    FStar_All.pipe_right uu____2571 (FStar_String.concat "; ")
  
let (log : cfg -> (Prims.unit -> Prims.unit) -> Prims.unit) =
  fun cfg  -> fun f  -> if (cfg.debug).gen then f () else () 
let (log_primops : cfg -> (Prims.unit -> Prims.unit) -> Prims.unit) =
  fun cfg  -> fun f  -> if (cfg.debug).primop then f () else () 
let is_empty : 'Auu____2602 . 'Auu____2602 Prims.list -> Prims.bool =
  fun uu___77_2608  ->
    match uu___77_2608 with | [] -> true | uu____2611 -> false
  
let lookup_bvar :
  'Auu____2618 'Auu____2619 .
    ('Auu____2619,'Auu____2618) FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Syntax_Syntax.bv -> 'Auu____2618
  =
  fun env  ->
    fun x  ->
      try
        let uu____2643 = FStar_List.nth env x.FStar_Syntax_Syntax.index  in
        FStar_Pervasives_Native.snd uu____2643
      with
      | uu____2656 ->
          let uu____2657 =
            let uu____2658 = FStar_Syntax_Print.db_to_string x  in
            FStar_Util.format1 "Failed to find %s\n" uu____2658  in
          failwith uu____2657
  
let (downgrade_ghost_effect_name :
  FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option) =
  fun l  ->
    if FStar_Ident.lid_equals l FStar_Parser_Const.effect_Ghost_lid
    then FStar_Pervasives_Native.Some FStar_Parser_Const.effect_Pure_lid
    else
      if FStar_Ident.lid_equals l FStar_Parser_Const.effect_GTot_lid
      then FStar_Pervasives_Native.Some FStar_Parser_Const.effect_Tot_lid
      else
        if FStar_Ident.lid_equals l FStar_Parser_Const.effect_GHOST_lid
        then FStar_Pervasives_Native.Some FStar_Parser_Const.effect_PURE_lid
        else FStar_Pervasives_Native.None
  
let (norm_universe :
  cfg -> env -> FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe)
  =
  fun cfg  ->
    fun env  ->
      fun u  ->
        let norm_univs us =
          let us1 = FStar_Util.sort_with FStar_Syntax_Util.compare_univs us
             in
          let uu____2695 =
            FStar_List.fold_left
              (fun uu____2721  ->
                 fun u1  ->
                   match uu____2721 with
                   | (cur_kernel,cur_max,out) ->
                       let uu____2746 = FStar_Syntax_Util.univ_kernel u1  in
                       (match uu____2746 with
                        | (k_u,n1) ->
                            let uu____2761 =
                              FStar_Syntax_Util.eq_univs cur_kernel k_u  in
                            if uu____2761
                            then (cur_kernel, u1, out)
                            else (k_u, u1, (cur_max :: out))))
              (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero, [])
              us1
             in
          match uu____2695 with
          | (uu____2779,u1,out) -> FStar_List.rev (u1 :: out)  in
        let rec aux u1 =
          let u2 = FStar_Syntax_Subst.compress_univ u1  in
          match u2 with
          | FStar_Syntax_Syntax.U_bvar x ->
              (try
                 let uu____2804 =
                   let uu____2805 = FStar_List.nth env x  in
                   FStar_Pervasives_Native.snd uu____2805  in
                 match uu____2804 with
                 | Univ u3 -> aux u3
                 | Dummy  -> [u2]
                 | uu____2823 ->
                     failwith "Impossible: universe variable bound to a term"
               with
               | uu____2831 ->
                   if (cfg.steps).allow_unbound_universes
                   then [FStar_Syntax_Syntax.U_unknown]
                   else failwith "Universe variable not found")
          | FStar_Syntax_Syntax.U_unif uu____2837 when
              (cfg.steps).check_no_uvars -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_zero  -> [u2]
          | FStar_Syntax_Syntax.U_unif uu____2846 -> [u2]
          | FStar_Syntax_Syntax.U_name uu____2855 -> [u2]
          | FStar_Syntax_Syntax.U_unknown  -> [u2]
          | FStar_Syntax_Syntax.U_max [] -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_max us ->
              let us1 =
                let uu____2862 = FStar_List.collect aux us  in
                FStar_All.pipe_right uu____2862 norm_univs  in
              (match us1 with
               | u_k::hd1::rest ->
                   let rest1 = hd1 :: rest  in
                   let uu____2879 = FStar_Syntax_Util.univ_kernel u_k  in
                   (match uu____2879 with
                    | (FStar_Syntax_Syntax.U_zero ,n1) ->
                        let uu____2887 =
                          FStar_All.pipe_right rest1
                            (FStar_List.for_all
                               (fun u3  ->
                                  let uu____2895 =
                                    FStar_Syntax_Util.univ_kernel u3  in
                                  match uu____2895 with
                                  | (uu____2900,m) -> n1 <= m))
                           in
                        if uu____2887 then rest1 else us1
                    | uu____2905 -> us1)
               | uu____2910 -> us1)
          | FStar_Syntax_Syntax.U_succ u3 ->
              let uu____2914 = aux u3  in
              FStar_List.map (fun _0_40  -> FStar_Syntax_Syntax.U_succ _0_40)
                uu____2914
           in
        if (cfg.steps).erase_universes
        then FStar_Syntax_Syntax.U_unknown
        else
          (let uu____2918 = aux u  in
           match uu____2918 with
           | [] -> FStar_Syntax_Syntax.U_zero
           | (FStar_Syntax_Syntax.U_zero )::[] -> FStar_Syntax_Syntax.U_zero
           | (FStar_Syntax_Syntax.U_zero )::u1::[] -> u1
           | (FStar_Syntax_Syntax.U_zero )::us ->
               FStar_Syntax_Syntax.U_max us
           | u1::[] -> u1
           | us -> FStar_Syntax_Syntax.U_max us)
  
let rec (closure_as_term :
  cfg -> env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun cfg  ->
    fun env  ->
      fun t  ->
        log cfg
          (fun uu____3022  ->
             let uu____3023 = FStar_Syntax_Print.tag_of_term t  in
             let uu____3024 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.print2 ">>> %s Closure_as_term %s\n" uu____3023
               uu____3024);
        (match env with
         | [] when
             FStar_All.pipe_left Prims.op_Negation (cfg.steps).compress_uvars
             -> t
         | uu____3031 ->
             let t1 = FStar_Syntax_Subst.compress t  in
             (match t1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_delayed uu____3033 ->
                  failwith "Impossible"
              | FStar_Syntax_Syntax.Tm_unknown  -> t1
              | FStar_Syntax_Syntax.Tm_constant uu____3058 -> t1
              | FStar_Syntax_Syntax.Tm_name uu____3059 -> t1
              | FStar_Syntax_Syntax.Tm_fvar uu____3060 -> t1
              | FStar_Syntax_Syntax.Tm_uvar uu____3061 ->
                  if (cfg.steps).check_no_uvars
                  then
                    let uu____3078 =
                      let uu____3079 =
                        FStar_Range.string_of_range
                          t1.FStar_Syntax_Syntax.pos
                         in
                      let uu____3080 = FStar_Syntax_Print.term_to_string t1
                         in
                      FStar_Util.format2
                        "(%s): CheckNoUvars: Unexpected unification variable remains: %s"
                        uu____3079 uu____3080
                       in
                    failwith uu____3078
                  else t1
              | FStar_Syntax_Syntax.Tm_type u ->
                  let uu____3083 =
                    let uu____3084 = norm_universe cfg env u  in
                    FStar_Syntax_Syntax.Tm_type uu____3084  in
                  mk uu____3083 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
                  let uu____3091 = FStar_List.map (norm_universe cfg env) us
                     in
                  FStar_Syntax_Syntax.mk_Tm_uinst t' uu____3091
              | FStar_Syntax_Syntax.Tm_bvar x ->
                  let uu____3093 = lookup_bvar env x  in
                  (match uu____3093 with
                   | Univ uu____3096 ->
                       failwith
                         "Impossible: term variable is bound to a universe"
                   | Dummy  -> t1
                   | Clos (env1,t0,uu____3099,uu____3100) ->
                       closure_as_term cfg env1 t0)
              | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                  let head2 = closure_as_term_delayed cfg env head1  in
                  let args1 = closures_as_args_delayed cfg env args  in
                  mk (FStar_Syntax_Syntax.Tm_app (head2, args1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
                  let uu____3212 = closures_as_binders_delayed cfg env bs  in
                  (match uu____3212 with
                   | (bs1,env1) ->
                       let body1 = closure_as_term_delayed cfg env1 body  in
                       let uu____3240 =
                         let uu____3241 =
                           let uu____3258 = close_lcomp_opt cfg env1 lopt  in
                           (bs1, body1, uu____3258)  in
                         FStar_Syntax_Syntax.Tm_abs uu____3241  in
                       mk uu____3240 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                  let uu____3289 = closures_as_binders_delayed cfg env bs  in
                  (match uu____3289 with
                   | (bs1,env1) ->
                       let c1 = close_comp cfg env1 c  in
                       mk (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
                         t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
                  let uu____3331 =
                    let uu____3342 =
                      let uu____3349 = FStar_Syntax_Syntax.mk_binder x  in
                      [uu____3349]  in
                    closures_as_binders_delayed cfg env uu____3342  in
                  (match uu____3331 with
                   | (x1,env1) ->
                       let phi1 = closure_as_term_delayed cfg env1 phi  in
                       let uu____3367 =
                         let uu____3368 =
                           let uu____3375 =
                             let uu____3376 = FStar_List.hd x1  in
                             FStar_All.pipe_right uu____3376
                               FStar_Pervasives_Native.fst
                              in
                           (uu____3375, phi1)  in
                         FStar_Syntax_Syntax.Tm_refine uu____3368  in
                       mk uu____3367 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_ascribed (t11,(annot,tacopt),lopt) ->
                  let annot1 =
                    match annot with
                    | FStar_Util.Inl t2 ->
                        let uu____3467 = closure_as_term_delayed cfg env t2
                           in
                        FStar_Util.Inl uu____3467
                    | FStar_Util.Inr c ->
                        let uu____3481 = close_comp cfg env c  in
                        FStar_Util.Inr uu____3481
                     in
                  let tacopt1 =
                    FStar_Util.map_opt tacopt
                      (closure_as_term_delayed cfg env)
                     in
                  let uu____3497 =
                    let uu____3498 =
                      let uu____3525 = closure_as_term_delayed cfg env t11
                         in
                      (uu____3525, (annot1, tacopt1), lopt)  in
                    FStar_Syntax_Syntax.Tm_ascribed uu____3498  in
                  mk uu____3497 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_pattern args) ->
                  let uu____3576 =
                    let uu____3577 =
                      let uu____3584 = closure_as_term_delayed cfg env t'  in
                      let uu____3587 =
                        let uu____3588 =
                          FStar_All.pipe_right args
                            (FStar_List.map
                               (closures_as_args_delayed cfg env))
                           in
                        FStar_Syntax_Syntax.Meta_pattern uu____3588  in
                      (uu____3584, uu____3587)  in
                    FStar_Syntax_Syntax.Tm_meta uu____3577  in
                  mk uu____3576 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic (m,tbody)) ->
                  let uu____3648 =
                    let uu____3649 =
                      let uu____3656 = closure_as_term_delayed cfg env t'  in
                      let uu____3659 =
                        let uu____3660 =
                          let uu____3667 =
                            closure_as_term_delayed cfg env tbody  in
                          (m, uu____3667)  in
                        FStar_Syntax_Syntax.Meta_monadic uu____3660  in
                      (uu____3656, uu____3659)  in
                    FStar_Syntax_Syntax.Tm_meta uu____3649  in
                  mk uu____3648 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,tbody)) ->
                  let uu____3686 =
                    let uu____3687 =
                      let uu____3694 = closure_as_term_delayed cfg env t'  in
                      let uu____3697 =
                        let uu____3698 =
                          let uu____3707 =
                            closure_as_term_delayed cfg env tbody  in
                          (m1, m2, uu____3707)  in
                        FStar_Syntax_Syntax.Meta_monadic_lift uu____3698  in
                      (uu____3694, uu____3697)  in
                    FStar_Syntax_Syntax.Tm_meta uu____3687  in
                  mk uu____3686 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta (t',m) ->
                  let uu____3720 =
                    let uu____3721 =
                      let uu____3728 = closure_as_term_delayed cfg env t'  in
                      (uu____3728, m)  in
                    FStar_Syntax_Syntax.Tm_meta uu____3721  in
                  mk uu____3720 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                  let env0 = env  in
                  let env1 =
                    FStar_List.fold_left
                      (fun env1  -> fun uu____3768  -> dummy :: env1) env
                      lb.FStar_Syntax_Syntax.lbunivs
                     in
                  let typ =
                    closure_as_term_delayed cfg env1
                      lb.FStar_Syntax_Syntax.lbtyp
                     in
                  let def =
                    closure_as_term cfg env1 lb.FStar_Syntax_Syntax.lbdef  in
                  let uu____3787 =
                    let uu____3798 = FStar_Syntax_Syntax.is_top_level [lb]
                       in
                    if uu____3798
                    then ((lb.FStar_Syntax_Syntax.lbname), body)
                    else
                      (let x = FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                          in
                       let uu____3817 =
                         closure_as_term cfg (dummy :: env0) body  in
                       ((FStar_Util.Inl
                           (let uu___122_3829 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___122_3829.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___122_3829.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = typ
                            })), uu____3817))
                     in
                  (match uu____3787 with
                   | (nm,body1) ->
                       let lb1 =
                         let uu___123_3845 = lb  in
                         {
                           FStar_Syntax_Syntax.lbname = nm;
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___123_3845.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp = typ;
                           FStar_Syntax_Syntax.lbeff =
                             (uu___123_3845.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef = def;
                           FStar_Syntax_Syntax.lbattrs =
                             (uu___123_3845.FStar_Syntax_Syntax.lbattrs)
                         }  in
                       mk
                         (FStar_Syntax_Syntax.Tm_let ((false, [lb1]), body1))
                         t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_let ((uu____3856,lbs),body) ->
                  let norm_one_lb env1 lb =
                    let env_univs =
                      FStar_List.fold_right
                        (fun uu____3915  -> fun env2  -> dummy :: env2)
                        lb.FStar_Syntax_Syntax.lbunivs env1
                       in
                    let env2 =
                      let uu____3940 = FStar_Syntax_Syntax.is_top_level lbs
                         in
                      if uu____3940
                      then env_univs
                      else
                        FStar_List.fold_right
                          (fun uu____3960  -> fun env2  -> dummy :: env2) lbs
                          env_univs
                       in
                    let ty =
                      closure_as_term cfg env_univs
                        lb.FStar_Syntax_Syntax.lbtyp
                       in
                    let nm =
                      let uu____3982 = FStar_Syntax_Syntax.is_top_level lbs
                         in
                      if uu____3982
                      then lb.FStar_Syntax_Syntax.lbname
                      else
                        (let x =
                           FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                         FStar_All.pipe_right
                           (let uu___124_3994 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___124_3994.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___124_3994.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = ty
                            }) (fun _0_41  -> FStar_Util.Inl _0_41))
                       in
                    let uu___125_3995 = lb  in
                    let uu____3996 =
                      closure_as_term cfg env2 lb.FStar_Syntax_Syntax.lbdef
                       in
                    {
                      FStar_Syntax_Syntax.lbname = nm;
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___125_3995.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = ty;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___125_3995.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = uu____3996;
                      FStar_Syntax_Syntax.lbattrs =
                        (uu___125_3995.FStar_Syntax_Syntax.lbattrs)
                    }  in
                  let lbs1 =
                    FStar_All.pipe_right lbs
                      (FStar_List.map (norm_one_lb env))
                     in
                  let body1 =
                    let body_env =
                      FStar_List.fold_right
                        (fun uu____4026  -> fun env1  -> dummy :: env1) lbs1
                        env
                       in
                    closure_as_term cfg body_env body  in
                  mk (FStar_Syntax_Syntax.Tm_let ((true, lbs1), body1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
                  let head2 = closure_as_term cfg env head1  in
                  let norm_one_branch env1 uu____4115 =
                    match uu____4115 with
                    | (pat,w_opt,tm) ->
                        let rec norm_pat env2 p =
                          match p.FStar_Syntax_Syntax.v with
                          | FStar_Syntax_Syntax.Pat_constant uu____4170 ->
                              (p, env2)
                          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                              let uu____4191 =
                                FStar_All.pipe_right pats
                                  (FStar_List.fold_left
                                     (fun uu____4251  ->
                                        fun uu____4252  ->
                                          match (uu____4251, uu____4252) with
                                          | ((pats1,env3),(p1,b)) ->
                                              let uu____4343 =
                                                norm_pat env3 p1  in
                                              (match uu____4343 with
                                               | (p2,env4) ->
                                                   (((p2, b) :: pats1), env4)))
                                     ([], env2))
                                 in
                              (match uu____4191 with
                               | (pats1,env3) ->
                                   ((let uu___126_4425 = p  in
                                     {
                                       FStar_Syntax_Syntax.v =
                                         (FStar_Syntax_Syntax.Pat_cons
                                            (fv, (FStar_List.rev pats1)));
                                       FStar_Syntax_Syntax.p =
                                         (uu___126_4425.FStar_Syntax_Syntax.p)
                                     }), env3))
                          | FStar_Syntax_Syntax.Pat_var x ->
                              let x1 =
                                let uu___127_4444 = x  in
                                let uu____4445 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort
                                   in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___127_4444.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___127_4444.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____4445
                                }  in
                              ((let uu___128_4459 = p  in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_var x1);
                                  FStar_Syntax_Syntax.p =
                                    (uu___128_4459.FStar_Syntax_Syntax.p)
                                }), (dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_wild x ->
                              let x1 =
                                let uu___129_4470 = x  in
                                let uu____4471 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort
                                   in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___129_4470.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___129_4470.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____4471
                                }  in
                              ((let uu___130_4485 = p  in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_wild x1);
                                  FStar_Syntax_Syntax.p =
                                    (uu___130_4485.FStar_Syntax_Syntax.p)
                                }), (dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                              let x1 =
                                let uu___131_4501 = x  in
                                let uu____4502 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort
                                   in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___131_4501.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___131_4501.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____4502
                                }  in
                              let t3 = closure_as_term cfg env2 t2  in
                              ((let uu___132_4509 = p  in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_dot_term
                                       (x1, t3));
                                  FStar_Syntax_Syntax.p =
                                    (uu___132_4509.FStar_Syntax_Syntax.p)
                                }), env2)
                           in
                        let uu____4512 = norm_pat env1 pat  in
                        (match uu____4512 with
                         | (pat1,env2) ->
                             let w_opt1 =
                               match w_opt with
                               | FStar_Pervasives_Native.None  ->
                                   FStar_Pervasives_Native.None
                               | FStar_Pervasives_Native.Some w ->
                                   let uu____4541 =
                                     closure_as_term cfg env2 w  in
                                   FStar_Pervasives_Native.Some uu____4541
                                in
                             let tm1 = closure_as_term cfg env2 tm  in
                             (pat1, w_opt1, tm1))
                     in
                  let uu____4547 =
                    let uu____4548 =
                      let uu____4571 =
                        FStar_All.pipe_right branches
                          (FStar_List.map (norm_one_branch env))
                         in
                      (head2, uu____4571)  in
                    FStar_Syntax_Syntax.Tm_match uu____4548  in
                  mk uu____4547 t1.FStar_Syntax_Syntax.pos))

and (closure_as_term_delayed :
  cfg ->
    env ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun cfg  ->
    fun env  ->
      fun t  ->
        match env with
        | [] when
            FStar_All.pipe_left Prims.op_Negation (cfg.steps).compress_uvars
            -> t
        | uu____4657 -> closure_as_term cfg env t

and (closures_as_args_delayed :
  cfg ->
    env ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
          FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun cfg  ->
    fun env  ->
      fun args  ->
        match env with
        | [] when
            FStar_All.pipe_left Prims.op_Negation (cfg.steps).compress_uvars
            -> args
        | uu____4683 ->
            FStar_List.map
              (fun uu____4700  ->
                 match uu____4700 with
                 | (x,imp) ->
                     let uu____4719 = closure_as_term_delayed cfg env x  in
                     (uu____4719, imp)) args

and (closures_as_binders_delayed :
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
        let uu____4733 =
          FStar_All.pipe_right bs
            (FStar_List.fold_left
               (fun uu____4782  ->
                  fun uu____4783  ->
                    match (uu____4782, uu____4783) with
                    | ((env1,out),(b,imp)) ->
                        let b1 =
                          let uu___133_4853 = b  in
                          let uu____4854 =
                            closure_as_term_delayed cfg env1
                              b.FStar_Syntax_Syntax.sort
                             in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___133_4853.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___133_4853.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = uu____4854
                          }  in
                        let env2 = dummy :: env1  in
                        (env2, ((b1, imp) :: out))) (env, []))
           in
        match uu____4733 with | (env1,bs1) -> ((FStar_List.rev bs1), env1)

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
        | uu____4947 ->
            (match c.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Total (t,uopt) ->
                 let uu____4960 = closure_as_term_delayed cfg env t  in
                 let uu____4961 =
                   FStar_Option.map (norm_universe cfg env) uopt  in
                 FStar_Syntax_Syntax.mk_Total' uu____4960 uu____4961
             | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                 let uu____4974 = closure_as_term_delayed cfg env t  in
                 let uu____4975 =
                   FStar_Option.map (norm_universe cfg env) uopt  in
                 FStar_Syntax_Syntax.mk_GTotal' uu____4974 uu____4975
             | FStar_Syntax_Syntax.Comp c1 ->
                 let rt =
                   closure_as_term_delayed cfg env
                     c1.FStar_Syntax_Syntax.result_typ
                    in
                 let args =
                   closures_as_args_delayed cfg env
                     c1.FStar_Syntax_Syntax.effect_args
                    in
                 let flags1 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_List.map
                        (fun uu___78_5001  ->
                           match uu___78_5001 with
                           | FStar_Syntax_Syntax.DECREASES t ->
                               let uu____5005 =
                                 closure_as_term_delayed cfg env t  in
                               FStar_Syntax_Syntax.DECREASES uu____5005
                           | f -> f))
                    in
                 let uu____5009 =
                   let uu___134_5010 = c1  in
                   let uu____5011 =
                     FStar_List.map (norm_universe cfg env)
                       c1.FStar_Syntax_Syntax.comp_univs
                      in
                   {
                     FStar_Syntax_Syntax.comp_univs = uu____5011;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___134_5010.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ = rt;
                     FStar_Syntax_Syntax.effect_args = args;
                     FStar_Syntax_Syntax.flags = flags1
                   }  in
                 FStar_Syntax_Syntax.mk_Comp uu____5009)

and (filter_out_lcomp_cflags :
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun flags1  ->
    FStar_All.pipe_right flags1
      (FStar_List.filter
         (fun uu___79_5021  ->
            match uu___79_5021 with
            | FStar_Syntax_Syntax.DECREASES uu____5022 -> false
            | uu____5025 -> true))

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
                   (fun uu___80_5043  ->
                      match uu___80_5043 with
                      | FStar_Syntax_Syntax.DECREASES uu____5044 -> false
                      | uu____5047 -> true))
               in
            let rc1 =
              let uu___135_5049 = rc  in
              let uu____5050 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (closure_as_term cfg env)
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___135_5049.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____5050;
                FStar_Syntax_Syntax.residual_flags = flags1
              }  in
            FStar_Pervasives_Native.Some rc1
        | uu____5057 -> lopt

let (built_in_primitive_steps : primitive_step FStar_Util.psmap) =
  let arg_as_int a =
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a)
      FStar_Syntax_Embeddings.unembed_int_safe
     in
  let arg_as_bool a =
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a)
      FStar_Syntax_Embeddings.unembed_bool_safe
     in
  let arg_as_char a =
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a)
      FStar_Syntax_Embeddings.unembed_char_safe
     in
  let arg_as_string a =
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a)
      FStar_Syntax_Embeddings.unembed_string_safe
     in
  let arg_as_list a u a =
    let uu____5142 = FStar_Syntax_Embeddings.unembed_list_safe u  in
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a) uu____5142  in
  let arg_as_bounded_int uu____5170 =
    match uu____5170 with
    | (a,uu____5182) ->
        let uu____5189 =
          let uu____5190 = FStar_Syntax_Subst.compress a  in
          uu____5190.FStar_Syntax_Syntax.n  in
        (match uu____5189 with
         | FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv1;
                FStar_Syntax_Syntax.pos = uu____5200;
                FStar_Syntax_Syntax.vars = uu____5201;_},({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_constant
                                                              (FStar_Const.Const_int
                                                              (i,FStar_Pervasives_Native.None
                                                               ));
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____5203;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____5204;_},uu____5205)::[])
             when
             FStar_Util.ends_with
               (FStar_Ident.text_of_lid
                  (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
               "int_to_t"
             ->
             let uu____5244 =
               let uu____5249 = FStar_BigInt.big_int_of_string i  in
               (fv1, uu____5249)  in
             FStar_Pervasives_Native.Some uu____5244
         | uu____5254 -> FStar_Pervasives_Native.None)
     in
  let lift_unary a b f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a)::[] ->
        let uu____5294 = f a  in FStar_Pervasives_Native.Some uu____5294
    | uu____5295 -> FStar_Pervasives_Native.None  in
  let lift_binary a b f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a0)::(FStar_Pervasives_Native.Some
        a1)::[] ->
        let uu____5343 = f a0 a1  in FStar_Pervasives_Native.Some uu____5343
    | uu____5344 -> FStar_Pervasives_Native.None  in
  let unary_op a416 a417 a418 a419 a420 =
    (Obj.magic
       (fun a  ->
          fun as_a  ->
            fun f  ->
              fun res  ->
                fun args  ->
                  let uu____5386 = FStar_List.map as_a args  in
                  lift_unary () ()
                    (fun a415  -> (Obj.magic (f res.psc_range)) a415)
                    uu____5386)) a416 a417 a418 a419 a420
     in
  let binary_op a423 a424 a425 a426 a427 =
    (Obj.magic
       (fun a  ->
          fun as_a  ->
            fun f  ->
              fun res  ->
                fun args  ->
                  let uu____5435 = FStar_List.map as_a args  in
                  lift_binary () ()
                    (fun a421  ->
                       fun a422  -> (Obj.magic (f res.psc_range)) a421 a422)
                    uu____5435)) a423 a424 a425 a426 a427
     in
  let as_primitive_step uu____5459 =
    match uu____5459 with
    | (l,arity,f) ->
        {
          name = l;
          arity;
          strong_reduction_ok = true;
          requires_binder_substitution = false;
          interpretation = f
        }
     in
  let unary_int_op f =
    unary_op () (fun a428  -> (Obj.magic arg_as_int) a428)
      (fun a429  ->
         fun a430  ->
           (Obj.magic
              (fun r  ->
                 fun x  ->
                   let uu____5507 = f x  in
                   FStar_Syntax_Embeddings.embed_int r uu____5507)) a429 a430)
     in
  let binary_int_op f =
    binary_op () (fun a431  -> (Obj.magic arg_as_int) a431)
      (fun a432  ->
         fun a433  ->
           fun a434  ->
             (Obj.magic
                (fun r  ->
                   fun x  ->
                     fun y  ->
                       let uu____5535 = f x y  in
                       FStar_Syntax_Embeddings.embed_int r uu____5535)) a432
               a433 a434)
     in
  let unary_bool_op f =
    unary_op () (fun a435  -> (Obj.magic arg_as_bool) a435)
      (fun a436  ->
         fun a437  ->
           (Obj.magic
              (fun r  ->
                 fun x  ->
                   let uu____5556 = f x  in
                   FStar_Syntax_Embeddings.embed_bool r uu____5556)) a436
             a437)
     in
  let binary_bool_op f =
    binary_op () (fun a438  -> (Obj.magic arg_as_bool) a438)
      (fun a439  ->
         fun a440  ->
           fun a441  ->
             (Obj.magic
                (fun r  ->
                   fun x  ->
                     fun y  ->
                       let uu____5584 = f x y  in
                       FStar_Syntax_Embeddings.embed_bool r uu____5584)) a439
               a440 a441)
     in
  let binary_string_op f =
    binary_op () (fun a442  -> (Obj.magic arg_as_string) a442)
      (fun a443  ->
         fun a444  ->
           fun a445  ->
             (Obj.magic
                (fun r  ->
                   fun x  ->
                     fun y  ->
                       let uu____5612 = f x y  in
                       FStar_Syntax_Embeddings.embed_string r uu____5612))
               a443 a444 a445)
     in
  let mixed_binary_op a b c as_a as_b embed_c f res args =
    match args with
    | a::b::[] ->
        let uu____5720 =
          let uu____5729 = as_a a  in
          let uu____5732 = as_b b  in (uu____5729, uu____5732)  in
        (match uu____5720 with
         | (FStar_Pervasives_Native.Some a1,FStar_Pervasives_Native.Some b1)
             ->
             let uu____5747 =
               let uu____5748 = f res.psc_range a1 b1  in
               embed_c res.psc_range uu____5748  in
             FStar_Pervasives_Native.Some uu____5747
         | uu____5749 -> FStar_Pervasives_Native.None)
    | uu____5758 -> FStar_Pervasives_Native.None  in
  let list_of_string' rng s =
    let name l =
      let uu____5772 =
        let uu____5773 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant
            FStar_Pervasives_Native.None
           in
        FStar_Syntax_Syntax.Tm_fvar uu____5773  in
      mk uu____5772 rng  in
    let char_t = name FStar_Parser_Const.char_lid  in
    let charterm c =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c)) rng  in
    let uu____5783 =
      let uu____5786 = FStar_String.list_of_string s  in
      FStar_List.map charterm uu____5786  in
    FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu____5783  in
  let string_of_list' rng l =
    let s = FStar_String.string_of_list l  in FStar_Syntax_Util.exp_string s
     in
  let string_compare' rng s1 s2 =
    let r = FStar_String.compare s1 s2  in
    let uu____5818 =
      let uu____5819 = FStar_Util.string_of_int r  in
      FStar_BigInt.big_int_of_string uu____5819  in
    FStar_Syntax_Embeddings.embed_int rng uu____5818  in
  let string_concat' psc args =
    match args with
    | a1::a2::[] ->
        let uu____5837 = arg_as_string a1  in
        (match uu____5837 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____5843 =
               Obj.magic
                 (arg_as_list ()
                    (Obj.magic FStar_Syntax_Embeddings.unembed_string_safe)
                    a2)
                in
             (match uu____5843 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2  in
                  let uu____5856 =
                    FStar_Syntax_Embeddings.embed_string psc.psc_range r  in
                  FStar_Pervasives_Native.Some uu____5856
              | uu____5857 -> FStar_Pervasives_Native.None)
         | uu____5862 -> FStar_Pervasives_Native.None)
    | uu____5865 -> FStar_Pervasives_Native.None  in
  let string_of_int1 rng i =
    let uu____5875 = FStar_BigInt.string_of_big_int i  in
    FStar_Syntax_Embeddings.embed_string rng uu____5875  in
  let string_of_bool1 rng b =
    FStar_Syntax_Embeddings.embed_string rng (if b then "true" else "false")
     in
  let term_of_range r =
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range r))
      FStar_Pervasives_Native.None r
     in
  let mk_range1 uu____5899 args =
    match args with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____5910 =
          let uu____5931 = arg_as_string fn  in
          let uu____5934 = arg_as_int from_line  in
          let uu____5937 = arg_as_int from_col  in
          let uu____5940 = arg_as_int to_line  in
          let uu____5943 = arg_as_int to_col  in
          (uu____5931, uu____5934, uu____5937, uu____5940, uu____5943)  in
        (match uu____5910 with
         | (FStar_Pervasives_Native.Some fn1,FStar_Pervasives_Native.Some
            from_l,FStar_Pervasives_Native.Some
            from_c,FStar_Pervasives_Native.Some
            to_l,FStar_Pervasives_Native.Some to_c) ->
             let r =
               let uu____5974 =
                 let uu____5975 = FStar_BigInt.to_int_fs from_l  in
                 let uu____5976 = FStar_BigInt.to_int_fs from_c  in
                 FStar_Range.mk_pos uu____5975 uu____5976  in
               let uu____5977 =
                 let uu____5978 = FStar_BigInt.to_int_fs to_l  in
                 let uu____5979 = FStar_BigInt.to_int_fs to_c  in
                 FStar_Range.mk_pos uu____5978 uu____5979  in
               FStar_Range.mk_range fn1 uu____5974 uu____5977  in
             let uu____5980 = term_of_range r  in
             FStar_Pervasives_Native.Some uu____5980
         | uu____5985 -> FStar_Pervasives_Native.None)
    | uu____6006 -> FStar_Pervasives_Native.None  in
  let decidable_eq neg psc args =
    let r = psc.psc_range  in
    let tru =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool true)) r
       in
    let fal =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool false)) r
       in
    match args with
    | (_typ,uu____6033)::(a1,uu____6035)::(a2,uu____6037)::[] ->
        let uu____6074 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____6074 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some (if neg then fal else tru)
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some (if neg then tru else fal)
         | uu____6087 -> FStar_Pervasives_Native.None)
    | uu____6088 -> failwith "Unexpected number of arguments"  in
  let idstep psc args =
    match args with
    | (a1,uu____6115)::[] -> FStar_Pervasives_Native.Some a1
    | uu____6124 -> failwith "Unexpected number of arguments"  in
  let basic_ops =
    let uu____6148 =
      let uu____6163 =
        let uu____6178 =
          let uu____6193 =
            let uu____6208 =
              let uu____6223 =
                let uu____6238 =
                  let uu____6253 =
                    let uu____6268 =
                      let uu____6283 =
                        let uu____6298 =
                          let uu____6313 =
                            let uu____6328 =
                              let uu____6343 =
                                let uu____6358 =
                                  let uu____6373 =
                                    let uu____6388 =
                                      let uu____6403 =
                                        let uu____6418 =
                                          let uu____6433 =
                                            let uu____6448 =
                                              let uu____6463 =
                                                let uu____6476 =
                                                  FStar_Parser_Const.p2l
                                                    ["FStar";
                                                    "String";
                                                    "list_of_string"]
                                                   in
                                                (uu____6476,
                                                  (Prims.parse_int "1"),
                                                  (unary_op ()
                                                     (fun a446  ->
                                                        (Obj.magic
                                                           arg_as_string)
                                                          a446)
                                                     (fun a447  ->
                                                        fun a448  ->
                                                          (Obj.magic
                                                             list_of_string')
                                                            a447 a448)))
                                                 in
                                              let uu____6483 =
                                                let uu____6498 =
                                                  let uu____6511 =
                                                    FStar_Parser_Const.p2l
                                                      ["FStar";
                                                      "String";
                                                      "string_of_list"]
                                                     in
                                                  (uu____6511,
                                                    (Prims.parse_int "1"),
                                                    (unary_op ()
                                                       (fun a449  ->
                                                          (Obj.magic
                                                             (arg_as_list ()
                                                                (Obj.magic
                                                                   FStar_Syntax_Embeddings.unembed_char_safe)))
                                                            a449)
                                                       (fun a450  ->
                                                          fun a451  ->
                                                            (Obj.magic
                                                               string_of_list')
                                                              a450 a451)))
                                                   in
                                                let uu____6518 =
                                                  let uu____6533 =
                                                    let uu____6548 =
                                                      FStar_Parser_Const.p2l
                                                        ["FStar";
                                                        "String";
                                                        "concat"]
                                                       in
                                                    (uu____6548,
                                                      (Prims.parse_int "2"),
                                                      string_concat')
                                                     in
                                                  let uu____6557 =
                                                    let uu____6574 =
                                                      let uu____6589 =
                                                        FStar_Parser_Const.p2l
                                                          ["Prims";
                                                          "mk_range"]
                                                         in
                                                      (uu____6589,
                                                        (Prims.parse_int "5"),
                                                        mk_range1)
                                                       in
                                                    let uu____6598 =
                                                      let uu____6615 =
                                                        let uu____6634 =
                                                          FStar_Parser_Const.p2l
                                                            ["FStar";
                                                            "Range";
                                                            "prims_to_fstar_range"]
                                                           in
                                                        (uu____6634,
                                                          (Prims.parse_int "1"),
                                                          idstep)
                                                         in
                                                      [uu____6615]  in
                                                    uu____6574 :: uu____6598
                                                     in
                                                  uu____6533 :: uu____6557
                                                   in
                                                uu____6498 :: uu____6518  in
                                              uu____6463 :: uu____6483  in
                                            (FStar_Parser_Const.op_notEq,
                                              (Prims.parse_int "3"),
                                              (decidable_eq true)) ::
                                              uu____6448
                                             in
                                          (FStar_Parser_Const.op_Eq,
                                            (Prims.parse_int "3"),
                                            (decidable_eq false)) ::
                                            uu____6433
                                           in
                                        (FStar_Parser_Const.string_compare,
                                          (Prims.parse_int "2"),
                                          (binary_op ()
                                             (fun a452  ->
                                                (Obj.magic arg_as_string)
                                                  a452)
                                             (fun a453  ->
                                                fun a454  ->
                                                  fun a455  ->
                                                    (Obj.magic
                                                       string_compare') a453
                                                      a454 a455)))
                                          :: uu____6418
                                         in
                                      (FStar_Parser_Const.string_of_bool_lid,
                                        (Prims.parse_int "1"),
                                        (unary_op ()
                                           (fun a456  ->
                                              (Obj.magic arg_as_bool) a456)
                                           (fun a457  ->
                                              fun a458  ->
                                                (Obj.magic string_of_bool1)
                                                  a457 a458)))
                                        :: uu____6403
                                       in
                                    (FStar_Parser_Const.string_of_int_lid,
                                      (Prims.parse_int "1"),
                                      (unary_op ()
                                         (fun a459  ->
                                            (Obj.magic arg_as_int) a459)
                                         (fun a460  ->
                                            fun a461  ->
                                              (Obj.magic string_of_int1) a460
                                                a461)))
                                      :: uu____6388
                                     in
                                  (FStar_Parser_Const.str_make_lid,
                                    (Prims.parse_int "2"),
                                    (mixed_binary_op () () ()
                                       (fun a462  ->
                                          (Obj.magic arg_as_int) a462)
                                       (fun a463  ->
                                          (Obj.magic arg_as_char) a463)
                                       (fun a464  ->
                                          fun a465  ->
                                            (Obj.magic
                                               FStar_Syntax_Embeddings.embed_string)
                                              a464 a465)
                                       (fun a466  ->
                                          fun a467  ->
                                            fun a468  ->
                                              (Obj.magic
                                                 (fun r  ->
                                                    fun x  ->
                                                      fun y  ->
                                                        let uu____6851 =
                                                          FStar_BigInt.to_int_fs
                                                            x
                                                           in
                                                        FStar_String.make
                                                          uu____6851 y)) a466
                                                a467 a468)))
                                    :: uu____6373
                                   in
                                (FStar_Parser_Const.strcat_lid',
                                  (Prims.parse_int "2"),
                                  (binary_string_op
                                     (fun x  -> fun y  -> Prims.strcat x y)))
                                  :: uu____6358
                                 in
                              (FStar_Parser_Const.strcat_lid,
                                (Prims.parse_int "2"),
                                (binary_string_op
                                   (fun x  -> fun y  -> Prims.strcat x y)))
                                :: uu____6343
                               in
                            (FStar_Parser_Const.op_Or, (Prims.parse_int "2"),
                              (binary_bool_op (fun x  -> fun y  -> x || y)))
                              :: uu____6328
                             in
                          (FStar_Parser_Const.op_And, (Prims.parse_int "2"),
                            (binary_bool_op (fun x  -> fun y  -> x && y))) ::
                            uu____6313
                           in
                        (FStar_Parser_Const.op_Negation,
                          (Prims.parse_int "1"),
                          (unary_bool_op (fun x  -> Prims.op_Negation x))) ::
                          uu____6298
                         in
                      (FStar_Parser_Const.op_Modulus, (Prims.parse_int "2"),
                        (binary_int_op
                           (fun x  -> fun y  -> FStar_BigInt.mod_big_int x y)))
                        :: uu____6283
                       in
                    (FStar_Parser_Const.op_GTE, (Prims.parse_int "2"),
                      (binary_op ()
                         (fun a469  -> (Obj.magic arg_as_int) a469)
                         (fun a470  ->
                            fun a471  ->
                              fun a472  ->
                                (Obj.magic
                                   (fun r  ->
                                      fun x  ->
                                        fun y  ->
                                          let uu____7018 =
                                            FStar_BigInt.ge_big_int x y  in
                                          FStar_Syntax_Embeddings.embed_bool
                                            r uu____7018)) a470 a471 a472)))
                      :: uu____6268
                     in
                  (FStar_Parser_Const.op_GT, (Prims.parse_int "2"),
                    (binary_op () (fun a473  -> (Obj.magic arg_as_int) a473)
                       (fun a474  ->
                          fun a475  ->
                            fun a476  ->
                              (Obj.magic
                                 (fun r  ->
                                    fun x  ->
                                      fun y  ->
                                        let uu____7044 =
                                          FStar_BigInt.gt_big_int x y  in
                                        FStar_Syntax_Embeddings.embed_bool r
                                          uu____7044)) a474 a475 a476)))
                    :: uu____6253
                   in
                (FStar_Parser_Const.op_LTE, (Prims.parse_int "2"),
                  (binary_op () (fun a477  -> (Obj.magic arg_as_int) a477)
                     (fun a478  ->
                        fun a479  ->
                          fun a480  ->
                            (Obj.magic
                               (fun r  ->
                                  fun x  ->
                                    fun y  ->
                                      let uu____7070 =
                                        FStar_BigInt.le_big_int x y  in
                                      FStar_Syntax_Embeddings.embed_bool r
                                        uu____7070)) a478 a479 a480)))
                  :: uu____6238
                 in
              (FStar_Parser_Const.op_LT, (Prims.parse_int "2"),
                (binary_op () (fun a481  -> (Obj.magic arg_as_int) a481)
                   (fun a482  ->
                      fun a483  ->
                        fun a484  ->
                          (Obj.magic
                             (fun r  ->
                                fun x  ->
                                  fun y  ->
                                    let uu____7096 =
                                      FStar_BigInt.lt_big_int x y  in
                                    FStar_Syntax_Embeddings.embed_bool r
                                      uu____7096)) a482 a483 a484)))
                :: uu____6223
               in
            (FStar_Parser_Const.op_Division, (Prims.parse_int "2"),
              (binary_int_op
                 (fun x  -> fun y  -> FStar_BigInt.div_big_int x y)))
              :: uu____6208
             in
          (FStar_Parser_Const.op_Multiply, (Prims.parse_int "2"),
            (binary_int_op
               (fun x  -> fun y  -> FStar_BigInt.mult_big_int x y)))
            :: uu____6193
           in
        (FStar_Parser_Const.op_Subtraction, (Prims.parse_int "2"),
          (binary_int_op (fun x  -> fun y  -> FStar_BigInt.sub_big_int x y)))
          :: uu____6178
         in
      (FStar_Parser_Const.op_Addition, (Prims.parse_int "2"),
        (binary_int_op (fun x  -> fun y  -> FStar_BigInt.add_big_int x y)))
        :: uu____6163
       in
    (FStar_Parser_Const.op_Minus, (Prims.parse_int "1"),
      (unary_int_op (fun x  -> FStar_BigInt.minus_big_int x))) :: uu____6148
     in
  let bounded_arith_ops =
    let bounded_signed_int_types = ["Int8"; "Int16"; "Int32"; "Int64"]  in
    let bounded_unsigned_int_types =
      ["UInt8"; "UInt16"; "UInt32"; "UInt64"; "UInt128"]  in
    let int_as_bounded r int_to_t1 n1 =
      let c = FStar_Syntax_Embeddings.embed_int r n1  in
      let int_to_t2 = FStar_Syntax_Syntax.fv_to_tm int_to_t1  in
      let uu____7249 =
        let uu____7250 =
          let uu____7251 = FStar_Syntax_Syntax.as_arg c  in [uu____7251]  in
        FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____7250  in
      uu____7249 FStar_Pervasives_Native.None r  in
    let add_sub_mul_v =
      FStar_All.pipe_right
        (FStar_List.append bounded_signed_int_types
           bounded_unsigned_int_types)
        (FStar_List.collect
           (fun m  ->
              let uu____7301 =
                let uu____7314 = FStar_Parser_Const.p2l ["FStar"; m; "add"]
                   in
                (uu____7314, (Prims.parse_int "2"),
                  (binary_op ()
                     (fun a485  -> (Obj.magic arg_as_bounded_int) a485)
                     (fun a486  ->
                        fun a487  ->
                          fun a488  ->
                            (Obj.magic
                               (fun r  ->
                                  fun uu____7330  ->
                                    fun uu____7331  ->
                                      match (uu____7330, uu____7331) with
                                      | ((int_to_t1,x),(uu____7350,y)) ->
                                          let uu____7360 =
                                            FStar_BigInt.add_big_int x y  in
                                          int_as_bounded r int_to_t1
                                            uu____7360)) a486 a487 a488)))
                 in
              let uu____7361 =
                let uu____7376 =
                  let uu____7389 = FStar_Parser_Const.p2l ["FStar"; m; "sub"]
                     in
                  (uu____7389, (Prims.parse_int "2"),
                    (binary_op ()
                       (fun a489  -> (Obj.magic arg_as_bounded_int) a489)
                       (fun a490  ->
                          fun a491  ->
                            fun a492  ->
                              (Obj.magic
                                 (fun r  ->
                                    fun uu____7405  ->
                                      fun uu____7406  ->
                                        match (uu____7405, uu____7406) with
                                        | ((int_to_t1,x),(uu____7425,y)) ->
                                            let uu____7435 =
                                              FStar_BigInt.sub_big_int x y
                                               in
                                            int_as_bounded r int_to_t1
                                              uu____7435)) a490 a491 a492)))
                   in
                let uu____7436 =
                  let uu____7451 =
                    let uu____7464 =
                      FStar_Parser_Const.p2l ["FStar"; m; "mul"]  in
                    (uu____7464, (Prims.parse_int "2"),
                      (binary_op ()
                         (fun a493  -> (Obj.magic arg_as_bounded_int) a493)
                         (fun a494  ->
                            fun a495  ->
                              fun a496  ->
                                (Obj.magic
                                   (fun r  ->
                                      fun uu____7480  ->
                                        fun uu____7481  ->
                                          match (uu____7480, uu____7481) with
                                          | ((int_to_t1,x),(uu____7500,y)) ->
                                              let uu____7510 =
                                                FStar_BigInt.mult_big_int x y
                                                 in
                                              int_as_bounded r int_to_t1
                                                uu____7510)) a494 a495 a496)))
                     in
                  let uu____7511 =
                    let uu____7526 =
                      let uu____7539 =
                        FStar_Parser_Const.p2l ["FStar"; m; "v"]  in
                      (uu____7539, (Prims.parse_int "1"),
                        (unary_op ()
                           (fun a497  -> (Obj.magic arg_as_bounded_int) a497)
                           (fun a498  ->
                              fun a499  ->
                                (Obj.magic
                                   (fun r  ->
                                      fun uu____7551  ->
                                        match uu____7551 with
                                        | (int_to_t1,x) ->
                                            FStar_Syntax_Embeddings.embed_int
                                              r x)) a498 a499)))
                       in
                    [uu____7526]  in
                  uu____7451 :: uu____7511  in
                uu____7376 :: uu____7436  in
              uu____7301 :: uu____7361))
       in
    let div_mod_unsigned =
      FStar_All.pipe_right bounded_unsigned_int_types
        (FStar_List.collect
           (fun m  ->
              let uu____7665 =
                let uu____7678 = FStar_Parser_Const.p2l ["FStar"; m; "div"]
                   in
                (uu____7678, (Prims.parse_int "2"),
                  (binary_op ()
                     (fun a500  -> (Obj.magic arg_as_bounded_int) a500)
                     (fun a501  ->
                        fun a502  ->
                          fun a503  ->
                            (Obj.magic
                               (fun r  ->
                                  fun uu____7694  ->
                                    fun uu____7695  ->
                                      match (uu____7694, uu____7695) with
                                      | ((int_to_t1,x),(uu____7714,y)) ->
                                          let uu____7724 =
                                            FStar_BigInt.div_big_int x y  in
                                          int_as_bounded r int_to_t1
                                            uu____7724)) a501 a502 a503)))
                 in
              let uu____7725 =
                let uu____7740 =
                  let uu____7753 = FStar_Parser_Const.p2l ["FStar"; m; "rem"]
                     in
                  (uu____7753, (Prims.parse_int "2"),
                    (binary_op ()
                       (fun a504  -> (Obj.magic arg_as_bounded_int) a504)
                       (fun a505  ->
                          fun a506  ->
                            fun a507  ->
                              (Obj.magic
                                 (fun r  ->
                                    fun uu____7769  ->
                                      fun uu____7770  ->
                                        match (uu____7769, uu____7770) with
                                        | ((int_to_t1,x),(uu____7789,y)) ->
                                            let uu____7799 =
                                              FStar_BigInt.mod_big_int x y
                                               in
                                            int_as_bounded r int_to_t1
                                              uu____7799)) a505 a506 a507)))
                   in
                [uu____7740]  in
              uu____7665 :: uu____7725))
       in
    FStar_List.append add_sub_mul_v div_mod_unsigned  in
  let uu____7848 =
    FStar_List.map as_primitive_step
      (FStar_List.append basic_ops bounded_arith_ops)
     in
  FStar_All.pipe_left prim_from_list uu____7848 
let (equality_ops : primitive_step FStar_Util.psmap) =
  let interp_prop psc args =
    let r = psc.psc_range  in
    match args with
    | (_typ,uu____7896)::(a1,uu____7898)::(a2,uu____7900)::[] ->
        let uu____7937 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____7937 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___136_7943 = FStar_Syntax_Util.t_true  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___136_7943.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___136_7943.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___137_7947 = FStar_Syntax_Util.t_false  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___137_7947.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___137_7947.FStar_Syntax_Syntax.vars)
                })
         | uu____7948 -> FStar_Pervasives_Native.None)
    | (_typ,uu____7950)::uu____7951::(a1,uu____7953)::(a2,uu____7955)::[] ->
        let uu____8004 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____8004 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___136_8010 = FStar_Syntax_Util.t_true  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___136_8010.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___136_8010.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___137_8014 = FStar_Syntax_Util.t_false  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___137_8014.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___137_8014.FStar_Syntax_Syntax.vars)
                })
         | uu____8015 -> FStar_Pervasives_Native.None)
    | uu____8016 -> failwith "Unexpected number of arguments"  in
  let propositional_equality =
    {
      name = FStar_Parser_Const.eq2_lid;
      arity = (Prims.parse_int "3");
      strong_reduction_ok = true;
      requires_binder_substitution = false;
      interpretation = interp_prop
    }  in
  let hetero_propositional_equality =
    {
      name = FStar_Parser_Const.eq3_lid;
      arity = (Prims.parse_int "4");
      strong_reduction_ok = true;
      requires_binder_substitution = false;
      interpretation = interp_prop
    }  in
  prim_from_list [propositional_equality; hetero_propositional_equality] 
let (unembed_binder :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option)
  =
  fun t  ->
    try
      let uu____8035 =
        let uu____8036 = FStar_Syntax_Util.un_alien t  in
        FStar_All.pipe_right uu____8036 FStar_Dyn.undyn  in
      FStar_Pervasives_Native.Some uu____8035
    with | uu____8042 -> FStar_Pervasives_Native.None
  
let mk_psc_subst :
  'Auu____8046 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____8046) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_Syntax_Syntax.subst_elt Prims.list
  =
  fun cfg  ->
    fun env  ->
      FStar_List.fold_right
        (fun uu____8106  ->
           fun subst1  ->
             match uu____8106 with
             | (binder_opt,closure) ->
                 (match (binder_opt, closure) with
                  | (FStar_Pervasives_Native.Some b,Clos
                     (env1,term,uu____8147,uu____8148)) ->
                      let uu____8207 = b  in
                      (match uu____8207 with
                       | (bv,uu____8215) ->
                           let uu____8216 =
                             let uu____8217 =
                               FStar_Syntax_Util.is_constructed_typ
                                 bv.FStar_Syntax_Syntax.sort
                                 FStar_Parser_Const.fstar_reflection_types_binder_lid
                                in
                             Prims.op_Negation uu____8217  in
                           if uu____8216
                           then subst1
                           else
                             (let term1 = closure_as_term cfg env1 term  in
                              let uu____8222 = unembed_binder term1  in
                              match uu____8222 with
                              | FStar_Pervasives_Native.None  -> subst1
                              | FStar_Pervasives_Native.Some x ->
                                  let b1 =
                                    let uu____8229 =
                                      let uu___140_8230 = bv  in
                                      let uu____8231 =
                                        FStar_Syntax_Subst.subst subst1
                                          (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort
                                         in
                                      {
                                        FStar_Syntax_Syntax.ppname =
                                          (uu___140_8230.FStar_Syntax_Syntax.ppname);
                                        FStar_Syntax_Syntax.index =
                                          (uu___140_8230.FStar_Syntax_Syntax.index);
                                        FStar_Syntax_Syntax.sort = uu____8231
                                      }  in
                                    FStar_Syntax_Syntax.freshen_bv uu____8229
                                     in
                                  let b_for_x =
                                    let uu____8235 =
                                      let uu____8242 =
                                        FStar_Syntax_Syntax.bv_to_name b1  in
                                      ((FStar_Pervasives_Native.fst x),
                                        uu____8242)
                                       in
                                    FStar_Syntax_Syntax.NT uu____8235  in
                                  let subst2 =
                                    FStar_List.filter
                                      (fun uu___81_8251  ->
                                         match uu___81_8251 with
                                         | FStar_Syntax_Syntax.NT
                                             (uu____8252,{
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_name
                                                             b';
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____8254;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____8255;_})
                                             ->
                                             Prims.op_Negation
                                               (FStar_Ident.ident_equals
                                                  b1.FStar_Syntax_Syntax.ppname
                                                  b'.FStar_Syntax_Syntax.ppname)
                                         | uu____8260 -> true) subst1
                                     in
                                  b_for_x :: subst2))
                  | uu____8261 -> subst1)) env []
  
let reduce_primops :
  'Auu____8278 'Auu____8279 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____8279) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____8278 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          if Prims.op_Negation (cfg.steps).primops
          then tm
          else
            (let uu____8321 = FStar_Syntax_Util.head_and_args tm  in
             match uu____8321 with
             | (head1,args) ->
                 let uu____8358 =
                   let uu____8359 = FStar_Syntax_Util.un_uinst head1  in
                   uu____8359.FStar_Syntax_Syntax.n  in
                 (match uu____8358 with
                  | FStar_Syntax_Syntax.Tm_fvar fv ->
                      let uu____8363 =
                        FStar_Util.psmap_try_find cfg.primitive_steps
                          (FStar_Ident.text_of_lid
                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                         in
                      (match uu____8363 with
                       | FStar_Pervasives_Native.Some prim_step when
                           prim_step.strong_reduction_ok ||
                             (Prims.op_Negation cfg.strong)
                           ->
                           if (FStar_List.length args) < prim_step.arity
                           then
                             (log_primops cfg
                                (fun uu____8378  ->
                                   let uu____8379 =
                                     FStar_Syntax_Print.lid_to_string
                                       prim_step.name
                                      in
                                   let uu____8380 =
                                     FStar_Util.string_of_int
                                       (FStar_List.length args)
                                      in
                                   let uu____8387 =
                                     FStar_Util.string_of_int prim_step.arity
                                      in
                                   FStar_Util.print3
                                     "primop: found partially applied %s (%s/%s args)\n"
                                     uu____8379 uu____8380 uu____8387);
                              tm)
                           else
                             (log_primops cfg
                                (fun uu____8392  ->
                                   let uu____8393 =
                                     FStar_Syntax_Print.term_to_string tm  in
                                   FStar_Util.print1
                                     "primop: trying to reduce <%s>\n"
                                     uu____8393);
                              (let psc =
                                 {
                                   psc_range =
                                     (head1.FStar_Syntax_Syntax.pos);
                                   psc_subst =
                                     (fun uu____8396  ->
                                        if
                                          prim_step.requires_binder_substitution
                                        then mk_psc_subst cfg env
                                        else [])
                                 }  in
                               let uu____8398 =
                                 prim_step.interpretation psc args  in
                               match uu____8398 with
                               | FStar_Pervasives_Native.None  ->
                                   (log_primops cfg
                                      (fun uu____8404  ->
                                         let uu____8405 =
                                           FStar_Syntax_Print.term_to_string
                                             tm
                                            in
                                         FStar_Util.print1
                                           "primop: <%s> did not reduce\n"
                                           uu____8405);
                                    tm)
                               | FStar_Pervasives_Native.Some reduced ->
                                   (log_primops cfg
                                      (fun uu____8411  ->
                                         let uu____8412 =
                                           FStar_Syntax_Print.term_to_string
                                             tm
                                            in
                                         let uu____8413 =
                                           FStar_Syntax_Print.term_to_string
                                             reduced
                                            in
                                         FStar_Util.print2
                                           "primop: <%s> reduced to <%s>\n"
                                           uu____8412 uu____8413);
                                    reduced)))
                       | FStar_Pervasives_Native.Some uu____8414 ->
                           (log_primops cfg
                              (fun uu____8418  ->
                                 let uu____8419 =
                                   FStar_Syntax_Print.term_to_string tm  in
                                 FStar_Util.print1
                                   "primop: not reducing <%s> since we're doing strong reduction\n"
                                   uu____8419);
                            tm)
                       | FStar_Pervasives_Native.None  -> tm)
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_range_of ) when
                      Prims.op_Negation cfg.strong ->
                      (log_primops cfg
                         (fun uu____8423  ->
                            let uu____8424 =
                              FStar_Syntax_Print.term_to_string tm  in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____8424);
                       (match args with
                        | (a1,uu____8426)::[] ->
                            FStar_Syntax_Embeddings.embed_range
                              tm.FStar_Syntax_Syntax.pos
                              a1.FStar_Syntax_Syntax.pos
                        | uu____8443 -> tm))
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_set_range_of ) when
                      Prims.op_Negation cfg.strong ->
                      (log_primops cfg
                         (fun uu____8455  ->
                            let uu____8456 =
                              FStar_Syntax_Print.term_to_string tm  in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____8456);
                       (match args with
                        | (t,uu____8458)::(r,uu____8460)::[] ->
                            let uu____8487 =
                              FStar_Syntax_Embeddings.unembed_range r  in
                            (match uu____8487 with
                             | FStar_Pervasives_Native.Some rng ->
                                 let uu___141_8491 = t  in
                                 {
                                   FStar_Syntax_Syntax.n =
                                     (uu___141_8491.FStar_Syntax_Syntax.n);
                                   FStar_Syntax_Syntax.pos = rng;
                                   FStar_Syntax_Syntax.vars =
                                     (uu___141_8491.FStar_Syntax_Syntax.vars)
                                 }
                             | FStar_Pervasives_Native.None  -> tm)
                        | uu____8494 -> tm))
                  | uu____8503 -> tm))
  
let reduce_equality :
  'Auu____8508 'Auu____8509 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____8509) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____8508 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun tm  ->
      reduce_primops
        (let uu___142_8547 = cfg  in
         {
           steps =
             (let uu___143_8550 = default_steps  in
              {
                beta = (uu___143_8550.beta);
                iota = (uu___143_8550.iota);
                zeta = (uu___143_8550.zeta);
                weak = (uu___143_8550.weak);
                hnf = (uu___143_8550.hnf);
                primops = true;
                eager_unfolding = (uu___143_8550.eager_unfolding);
                inlining = (uu___143_8550.inlining);
                no_delta_steps = (uu___143_8550.no_delta_steps);
                unfold_until = (uu___143_8550.unfold_until);
                unfold_only = (uu___143_8550.unfold_only);
                unfold_attr = (uu___143_8550.unfold_attr);
                unfold_tac = (uu___143_8550.unfold_tac);
                pure_subterms_within_computations =
                  (uu___143_8550.pure_subterms_within_computations);
                simplify = (uu___143_8550.simplify);
                erase_universes = (uu___143_8550.erase_universes);
                allow_unbound_universes =
                  (uu___143_8550.allow_unbound_universes);
                reify_ = (uu___143_8550.reify_);
                compress_uvars = (uu___143_8550.compress_uvars);
                no_full_norm = (uu___143_8550.no_full_norm);
                check_no_uvars = (uu___143_8550.check_no_uvars);
                unmeta = (uu___143_8550.unmeta);
                unascribe = (uu___143_8550.unascribe)
              });
           tcenv = (uu___142_8547.tcenv);
           debug = (uu___142_8547.debug);
           delta_level = (uu___142_8547.delta_level);
           primitive_steps = equality_ops;
           strong = (uu___142_8547.strong);
           memoize_lazy = (uu___142_8547.memoize_lazy);
           normalize_pure_lets = (uu___142_8547.normalize_pure_lets)
         }) tm
  
let maybe_simplify_aux :
  'Auu____8557 'Auu____8558 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____8558) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____8557 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          let tm1 = reduce_primops cfg env stack tm  in
          let uu____8600 =
            FStar_All.pipe_left Prims.op_Negation (cfg.steps).simplify  in
          if uu____8600
          then tm1
          else
            (let w t =
               let uu___144_8612 = t  in
               {
                 FStar_Syntax_Syntax.n =
                   (uu___144_8612.FStar_Syntax_Syntax.n);
                 FStar_Syntax_Syntax.pos = (tm1.FStar_Syntax_Syntax.pos);
                 FStar_Syntax_Syntax.vars =
                   (uu___144_8612.FStar_Syntax_Syntax.vars)
               }  in
             let simp_t t =
               match t.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_meta
                   ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                      FStar_Syntax_Syntax.pos = uu____8628;
                      FStar_Syntax_Syntax.vars = uu____8629;_},uu____8630)
                   when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_Pervasives_Native.Some true
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_Pervasives_Native.Some true
               | FStar_Syntax_Syntax.Tm_meta
                   ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                      FStar_Syntax_Syntax.pos = uu____8637;
                      FStar_Syntax_Syntax.vars = uu____8638;_},uu____8639)
                   when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.false_lid
                   -> FStar_Pervasives_Native.Some false
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.false_lid
                   -> FStar_Pervasives_Native.Some false
               | uu____8645 -> FStar_Pervasives_Native.None  in
             let maybe_auto_squash t =
               let uu____8650 = FStar_Syntax_Util.is_sub_singleton t  in
               if uu____8650
               then t
               else
                 FStar_Syntax_Util.mk_auto_squash FStar_Syntax_Syntax.U_zero
                   t
                in
             let squashed_head_un_auto_squash_args t =
               let maybe_un_auto_squash_arg uu____8671 =
                 match uu____8671 with
                 | (t1,q) ->
                     let uu____8684 = FStar_Syntax_Util.is_auto_squash t1  in
                     (match uu____8684 with
                      | FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.U_zero ,t2) -> (t2, q)
                      | uu____8712 -> (t1, q))
                  in
               let uu____8721 = FStar_Syntax_Util.head_and_args t  in
               match uu____8721 with
               | (head1,args) ->
                   let args1 = FStar_List.map maybe_un_auto_squash_arg args
                      in
                   FStar_Syntax_Syntax.mk_Tm_app head1 args1
                     FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
                in
             let simplify1 arg =
               ((simp_t (FStar_Pervasives_Native.fst arg)), arg)  in
             match tm1.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____8818;
                         FStar_Syntax_Syntax.vars = uu____8819;_},uu____8820);
                    FStar_Syntax_Syntax.pos = uu____8821;
                    FStar_Syntax_Syntax.vars = uu____8822;_},args)
                 ->
                 let uu____8848 =
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.and_lid
                    in
                 if uu____8848
                 then
                   let uu____8849 =
                     FStar_All.pipe_right args (FStar_List.map simplify1)  in
                   (match uu____8849 with
                    | (FStar_Pervasives_Native.Some (true ),uu____8904)::
                        (uu____8905,(arg,uu____8907))::[] ->
                        maybe_auto_squash arg
                    | (uu____8972,(arg,uu____8974))::(FStar_Pervasives_Native.Some
                                                      (true ),uu____8975)::[]
                        -> maybe_auto_squash arg
                    | (FStar_Pervasives_Native.Some (false ),uu____9040)::uu____9041::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____9104::(FStar_Pervasives_Native.Some (false
                                   ),uu____9105)::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____9168 -> squashed_head_un_auto_squash_args tm1)
                 else
                   (let uu____9184 =
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.or_lid
                       in
                    if uu____9184
                    then
                      let uu____9185 =
                        FStar_All.pipe_right args (FStar_List.map simplify1)
                         in
                      match uu____9185 with
                      | (FStar_Pervasives_Native.Some (true ),uu____9240)::uu____9241::[]
                          -> w FStar_Syntax_Util.t_true
                      | uu____9304::(FStar_Pervasives_Native.Some (true
                                     ),uu____9305)::[]
                          -> w FStar_Syntax_Util.t_true
                      | (FStar_Pervasives_Native.Some (false ),uu____9368)::
                          (uu____9369,(arg,uu____9371))::[] ->
                          maybe_auto_squash arg
                      | (uu____9436,(arg,uu____9438))::(FStar_Pervasives_Native.Some
                                                        (false ),uu____9439)::[]
                          -> maybe_auto_squash arg
                      | uu____9504 -> squashed_head_un_auto_squash_args tm1
                    else
                      (let uu____9520 =
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.imp_lid
                          in
                       if uu____9520
                       then
                         let uu____9521 =
                           FStar_All.pipe_right args
                             (FStar_List.map simplify1)
                            in
                         match uu____9521 with
                         | uu____9576::(FStar_Pervasives_Native.Some (true
                                        ),uu____9577)::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (false ),uu____9640)::uu____9641::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (true ),uu____9704)::
                             (uu____9705,(arg,uu____9707))::[] ->
                             maybe_auto_squash arg
                         | (uu____9772,(p,uu____9774))::(uu____9775,(q,uu____9777))::[]
                             ->
                             let uu____9842 = FStar_Syntax_Util.term_eq p q
                                in
                             (if uu____9842
                              then w FStar_Syntax_Util.t_true
                              else squashed_head_un_auto_squash_args tm1)
                         | uu____9844 ->
                             squashed_head_un_auto_squash_args tm1
                       else
                         (let uu____9860 =
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.not_lid
                             in
                          if uu____9860
                          then
                            let uu____9861 =
                              FStar_All.pipe_right args
                                (FStar_List.map simplify1)
                               in
                            match uu____9861 with
                            | (FStar_Pervasives_Native.Some (true
                               ),uu____9916)::[] ->
                                w FStar_Syntax_Util.t_false
                            | (FStar_Pervasives_Native.Some (false
                               ),uu____9955)::[] ->
                                w FStar_Syntax_Util.t_true
                            | uu____9994 ->
                                squashed_head_un_auto_squash_args tm1
                          else
                            (let uu____10010 =
                               FStar_Syntax_Syntax.fv_eq_lid fv
                                 FStar_Parser_Const.forall_lid
                                in
                             if uu____10010
                             then
                               match args with
                               | (t,uu____10012)::[] ->
                                   let uu____10029 =
                                     let uu____10030 =
                                       FStar_Syntax_Subst.compress t  in
                                     uu____10030.FStar_Syntax_Syntax.n  in
                                   (match uu____10029 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____10033::[],body,uu____10035) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____10062 -> tm1)
                                    | uu____10065 -> tm1)
                               | (uu____10066,FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Syntax.Implicit uu____10067))::
                                   (t,uu____10069)::[] ->
                                   let uu____10108 =
                                     let uu____10109 =
                                       FStar_Syntax_Subst.compress t  in
                                     uu____10109.FStar_Syntax_Syntax.n  in
                                   (match uu____10108 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____10112::[],body,uu____10114) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____10141 -> tm1)
                                    | uu____10144 -> tm1)
                               | uu____10145 -> tm1
                             else
                               (let uu____10155 =
                                  FStar_Syntax_Syntax.fv_eq_lid fv
                                    FStar_Parser_Const.exists_lid
                                   in
                                if uu____10155
                                then
                                  match args with
                                  | (t,uu____10157)::[] ->
                                      let uu____10174 =
                                        let uu____10175 =
                                          FStar_Syntax_Subst.compress t  in
                                        uu____10175.FStar_Syntax_Syntax.n  in
                                      (match uu____10174 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____10178::[],body,uu____10180)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____10207 -> tm1)
                                       | uu____10210 -> tm1)
                                  | (uu____10211,FStar_Pervasives_Native.Some
                                     (FStar_Syntax_Syntax.Implicit
                                     uu____10212))::(t,uu____10214)::[] ->
                                      let uu____10253 =
                                        let uu____10254 =
                                          FStar_Syntax_Subst.compress t  in
                                        uu____10254.FStar_Syntax_Syntax.n  in
                                      (match uu____10253 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____10257::[],body,uu____10259)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____10286 -> tm1)
                                       | uu____10289 -> tm1)
                                  | uu____10290 -> tm1
                                else
                                  (let uu____10300 =
                                     FStar_Syntax_Syntax.fv_eq_lid fv
                                       FStar_Parser_Const.b2t_lid
                                      in
                                   if uu____10300
                                   then
                                     match args with
                                     | ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_bool (true ));
                                          FStar_Syntax_Syntax.pos =
                                            uu____10301;
                                          FStar_Syntax_Syntax.vars =
                                            uu____10302;_},uu____10303)::[]
                                         -> w FStar_Syntax_Util.t_true
                                     | ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_bool (false ));
                                          FStar_Syntax_Syntax.pos =
                                            uu____10320;
                                          FStar_Syntax_Syntax.vars =
                                            uu____10321;_},uu____10322)::[]
                                         -> w FStar_Syntax_Util.t_false
                                     | uu____10339 -> tm1
                                   else
                                     (let uu____10349 =
                                        FStar_Syntax_Util.is_auto_squash tm1
                                         in
                                      match uu____10349 with
                                      | FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.U_zero ,t)
                                          when
                                          FStar_Syntax_Util.is_sub_singleton
                                            t
                                          -> t
                                      | uu____10369 ->
                                          reduce_equality cfg env stack tm1)))))))
             | FStar_Syntax_Syntax.Tm_app
                 ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                    FStar_Syntax_Syntax.pos = uu____10379;
                    FStar_Syntax_Syntax.vars = uu____10380;_},args)
                 ->
                 let uu____10402 =
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.and_lid
                    in
                 if uu____10402
                 then
                   let uu____10403 =
                     FStar_All.pipe_right args (FStar_List.map simplify1)  in
                   (match uu____10403 with
                    | (FStar_Pervasives_Native.Some (true ),uu____10458)::
                        (uu____10459,(arg,uu____10461))::[] ->
                        maybe_auto_squash arg
                    | (uu____10526,(arg,uu____10528))::(FStar_Pervasives_Native.Some
                                                        (true ),uu____10529)::[]
                        -> maybe_auto_squash arg
                    | (FStar_Pervasives_Native.Some (false ),uu____10594)::uu____10595::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____10658::(FStar_Pervasives_Native.Some (false
                                    ),uu____10659)::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____10722 -> squashed_head_un_auto_squash_args tm1)
                 else
                   (let uu____10738 =
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.or_lid
                       in
                    if uu____10738
                    then
                      let uu____10739 =
                        FStar_All.pipe_right args (FStar_List.map simplify1)
                         in
                      match uu____10739 with
                      | (FStar_Pervasives_Native.Some (true ),uu____10794)::uu____10795::[]
                          -> w FStar_Syntax_Util.t_true
                      | uu____10858::(FStar_Pervasives_Native.Some (true
                                      ),uu____10859)::[]
                          -> w FStar_Syntax_Util.t_true
                      | (FStar_Pervasives_Native.Some (false ),uu____10922)::
                          (uu____10923,(arg,uu____10925))::[] ->
                          maybe_auto_squash arg
                      | (uu____10990,(arg,uu____10992))::(FStar_Pervasives_Native.Some
                                                          (false
                                                          ),uu____10993)::[]
                          -> maybe_auto_squash arg
                      | uu____11058 -> squashed_head_un_auto_squash_args tm1
                    else
                      (let uu____11074 =
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.imp_lid
                          in
                       if uu____11074
                       then
                         let uu____11075 =
                           FStar_All.pipe_right args
                             (FStar_List.map simplify1)
                            in
                         match uu____11075 with
                         | uu____11130::(FStar_Pervasives_Native.Some (true
                                         ),uu____11131)::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____11194)::uu____11195::[] ->
                             w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (true ),uu____11258)::
                             (uu____11259,(arg,uu____11261))::[] ->
                             maybe_auto_squash arg
                         | (uu____11326,(p,uu____11328))::(uu____11329,
                                                           (q,uu____11331))::[]
                             ->
                             let uu____11396 = FStar_Syntax_Util.term_eq p q
                                in
                             (if uu____11396
                              then w FStar_Syntax_Util.t_true
                              else squashed_head_un_auto_squash_args tm1)
                         | uu____11398 ->
                             squashed_head_un_auto_squash_args tm1
                       else
                         (let uu____11414 =
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.not_lid
                             in
                          if uu____11414
                          then
                            let uu____11415 =
                              FStar_All.pipe_right args
                                (FStar_List.map simplify1)
                               in
                            match uu____11415 with
                            | (FStar_Pervasives_Native.Some (true
                               ),uu____11470)::[] ->
                                w FStar_Syntax_Util.t_false
                            | (FStar_Pervasives_Native.Some (false
                               ),uu____11509)::[] ->
                                w FStar_Syntax_Util.t_true
                            | uu____11548 ->
                                squashed_head_un_auto_squash_args tm1
                          else
                            (let uu____11564 =
                               FStar_Syntax_Syntax.fv_eq_lid fv
                                 FStar_Parser_Const.forall_lid
                                in
                             if uu____11564
                             then
                               match args with
                               | (t,uu____11566)::[] ->
                                   let uu____11583 =
                                     let uu____11584 =
                                       FStar_Syntax_Subst.compress t  in
                                     uu____11584.FStar_Syntax_Syntax.n  in
                                   (match uu____11583 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____11587::[],body,uu____11589) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____11616 -> tm1)
                                    | uu____11619 -> tm1)
                               | (uu____11620,FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Syntax.Implicit uu____11621))::
                                   (t,uu____11623)::[] ->
                                   let uu____11662 =
                                     let uu____11663 =
                                       FStar_Syntax_Subst.compress t  in
                                     uu____11663.FStar_Syntax_Syntax.n  in
                                   (match uu____11662 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____11666::[],body,uu____11668) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____11695 -> tm1)
                                    | uu____11698 -> tm1)
                               | uu____11699 -> tm1
                             else
                               (let uu____11709 =
                                  FStar_Syntax_Syntax.fv_eq_lid fv
                                    FStar_Parser_Const.exists_lid
                                   in
                                if uu____11709
                                then
                                  match args with
                                  | (t,uu____11711)::[] ->
                                      let uu____11728 =
                                        let uu____11729 =
                                          FStar_Syntax_Subst.compress t  in
                                        uu____11729.FStar_Syntax_Syntax.n  in
                                      (match uu____11728 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____11732::[],body,uu____11734)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____11761 -> tm1)
                                       | uu____11764 -> tm1)
                                  | (uu____11765,FStar_Pervasives_Native.Some
                                     (FStar_Syntax_Syntax.Implicit
                                     uu____11766))::(t,uu____11768)::[] ->
                                      let uu____11807 =
                                        let uu____11808 =
                                          FStar_Syntax_Subst.compress t  in
                                        uu____11808.FStar_Syntax_Syntax.n  in
                                      (match uu____11807 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____11811::[],body,uu____11813)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____11840 -> tm1)
                                       | uu____11843 -> tm1)
                                  | uu____11844 -> tm1
                                else
                                  (let uu____11854 =
                                     FStar_Syntax_Syntax.fv_eq_lid fv
                                       FStar_Parser_Const.b2t_lid
                                      in
                                   if uu____11854
                                   then
                                     match args with
                                     | ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_bool (true ));
                                          FStar_Syntax_Syntax.pos =
                                            uu____11855;
                                          FStar_Syntax_Syntax.vars =
                                            uu____11856;_},uu____11857)::[]
                                         -> w FStar_Syntax_Util.t_true
                                     | ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_bool (false ));
                                          FStar_Syntax_Syntax.pos =
                                            uu____11874;
                                          FStar_Syntax_Syntax.vars =
                                            uu____11875;_},uu____11876)::[]
                                         -> w FStar_Syntax_Util.t_false
                                     | uu____11893 -> tm1
                                   else
                                     (let uu____11903 =
                                        FStar_Syntax_Util.is_auto_squash tm1
                                         in
                                      match uu____11903 with
                                      | FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.U_zero ,t)
                                          when
                                          FStar_Syntax_Util.is_sub_singleton
                                            t
                                          -> t
                                      | uu____11923 ->
                                          reduce_equality cfg env stack tm1)))))))
             | FStar_Syntax_Syntax.Tm_refine (bv,t) ->
                 (match simp_t t with
                  | FStar_Pervasives_Native.Some (true ) ->
                      bv.FStar_Syntax_Syntax.sort
                  | FStar_Pervasives_Native.Some (false ) -> tm1
                  | FStar_Pervasives_Native.None  -> tm1)
             | uu____11938 -> tm1)
  
let maybe_simplify :
  'Auu____11945 'Auu____11946 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____11946) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____11945 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          let tm' = maybe_simplify_aux cfg env stack tm  in
          if (cfg.debug).b380
          then
            (let uu____11989 = FStar_Syntax_Print.term_to_string tm  in
             let uu____11990 = FStar_Syntax_Print.term_to_string tm'  in
             FStar_Util.print3 "%sSimplified\n\t%s to\n\t%s\n"
               (if (cfg.steps).simplify then "" else "NOT ") uu____11989
               uu____11990)
          else ();
          tm'
  
let is_norm_request :
  'Auu____11996 .
    FStar_Syntax_Syntax.term -> 'Auu____11996 Prims.list -> Prims.bool
  =
  fun hd1  ->
    fun args  ->
      let uu____12009 =
        let uu____12016 =
          let uu____12017 = FStar_Syntax_Util.un_uinst hd1  in
          uu____12017.FStar_Syntax_Syntax.n  in
        (uu____12016, args)  in
      match uu____12009 with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____12023::uu____12024::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____12028::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize
      | (FStar_Syntax_Syntax.Tm_fvar fv,steps::uu____12033::uu____12034::[])
          -> FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm
      | uu____12037 -> false
  
let (tr_norm_step : FStar_Syntax_Embeddings.norm_step -> step Prims.list) =
  fun uu___82_12048  ->
    match uu___82_12048 with
    | FStar_Syntax_Embeddings.Zeta  -> [Zeta]
    | FStar_Syntax_Embeddings.Iota  -> [Iota]
    | FStar_Syntax_Embeddings.Delta  ->
        [UnfoldUntil FStar_Syntax_Syntax.Delta_constant]
    | FStar_Syntax_Embeddings.Simpl  -> [Simplify]
    | FStar_Syntax_Embeddings.Weak  -> [Weak]
    | FStar_Syntax_Embeddings.HNF  -> [HNF]
    | FStar_Syntax_Embeddings.Primops  -> [Primops]
    | FStar_Syntax_Embeddings.UnfoldOnly names1 ->
        let uu____12054 =
          let uu____12057 =
            let uu____12058 = FStar_List.map FStar_Ident.lid_of_str names1
               in
            UnfoldOnly uu____12058  in
          [uu____12057]  in
        (UnfoldUntil FStar_Syntax_Syntax.Delta_constant) :: uu____12054
    | FStar_Syntax_Embeddings.UnfoldAttr t ->
        [UnfoldUntil FStar_Syntax_Syntax.Delta_constant; UnfoldAttr t]
  
let (tr_norm_steps :
  FStar_Syntax_Embeddings.norm_step Prims.list -> step Prims.list) =
  fun s  -> FStar_List.concatMap tr_norm_step s 
let get_norm_request :
  'Auu____12074 .
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
      (FStar_Syntax_Syntax.term,'Auu____12074) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (step Prims.list,FStar_Syntax_Syntax.term)
          FStar_Pervasives_Native.tuple2
  =
  fun full_norm  ->
    fun args  ->
      let parse_steps s =
        let uu____12112 =
          let uu____12115 =
            let uu____12120 =
              FStar_Syntax_Embeddings.unembed_list
                FStar_Syntax_Embeddings.unembed_norm_step
               in
            uu____12120 s  in
          FStar_All.pipe_right uu____12115 FStar_Util.must  in
        FStar_All.pipe_right uu____12112 tr_norm_steps  in
      match args with
      | uu____12145::(tm,uu____12147)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify]  in
          (s, tm)
      | (tm,uu____12170)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify]  in
          (s, tm)
      | (steps,uu____12185)::uu____12186::(tm,uu____12188)::[] ->
          let add_exclude s z =
            if Prims.op_Negation (FStar_List.contains z s)
            then (Exclude z) :: s
            else s  in
          let s =
            let uu____12228 =
              let uu____12231 = full_norm steps  in parse_steps uu____12231
               in
            Beta :: uu____12228  in
          let s1 = add_exclude s Zeta  in
          let s2 = add_exclude s1 Iota  in (s2, tm)
      | uu____12240 -> failwith "Impossible"
  
let (is_reify_head : stack_elt Prims.list -> Prims.bool) =
  fun uu___83_12257  ->
    match uu___83_12257 with
    | (App
        (uu____12260,{
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reify );
                       FStar_Syntax_Syntax.pos = uu____12261;
                       FStar_Syntax_Syntax.vars = uu____12262;_},uu____12263,uu____12264))::uu____12265
        -> true
    | uu____12272 -> false
  
let firstn :
  'Auu____12278 .
    Prims.int ->
      'Auu____12278 Prims.list ->
        ('Auu____12278 Prims.list,'Auu____12278 Prims.list)
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
          (uu____12314,{
                         FStar_Syntax_Syntax.n =
                           FStar_Syntax_Syntax.Tm_constant
                           (FStar_Const.Const_reify );
                         FStar_Syntax_Syntax.pos = uu____12315;
                         FStar_Syntax_Syntax.vars = uu____12316;_},uu____12317,uu____12318))::uu____12319
          -> (cfg.steps).reify_
      | uu____12326 -> false
  
let (attr_eq :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun a  ->
    fun a'  ->
      let r =
        let uu____12336 = FStar_Syntax_Util.eq_tm a a'  in
        match uu____12336 with
        | FStar_Syntax_Util.Equal  -> true
        | uu____12337 -> false  in
      r
  
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
               | FStar_Syntax_Syntax.Tm_delayed uu____12479 ->
                   let uu____12504 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print1 "NORM delayed: %s\n" uu____12504
               | uu____12505 -> ())
            else ();
            FStar_Syntax_Subst.compress t  in
          log cfg
            (fun uu____12513  ->
               let uu____12514 = FStar_Syntax_Print.tag_of_term t1  in
               let uu____12515 = FStar_Syntax_Print.term_to_string t1  in
               let uu____12516 =
                 FStar_Util.string_of_int (FStar_List.length env)  in
               let uu____12523 =
                 let uu____12524 =
                   let uu____12527 = firstn (Prims.parse_int "4") stack  in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____12527
                    in
                 stack_to_string uu____12524  in
               FStar_Util.print4
                 ">>> %s\nNorm %s with with %s env elements top of the stack %s \n"
                 uu____12514 uu____12515 uu____12516 uu____12523);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_constant uu____12550 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_name uu____12551 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____12552;
                 FStar_Syntax_Syntax.fv_delta =
                   FStar_Syntax_Syntax.Delta_constant ;
                 FStar_Syntax_Syntax.fv_qual = uu____12553;_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____12556;
                 FStar_Syntax_Syntax.fv_delta = uu____12557;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Data_ctor );_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____12558;
                 FStar_Syntax_Syntax.fv_delta = uu____12559;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor uu____12560);_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               ((FStar_Syntax_Util.is_fstar_tactics_embed hd1) ||
                  ((FStar_Syntax_Util.is_fstar_tactics_quote hd1) &&
                     (cfg.steps).no_delta_steps))
                 || (FStar_Syntax_Util.is_fstar_tactics_by_tactic hd1)
               ->
               let args1 = closures_as_args_delayed cfg env args  in
               let hd2 = closure_as_term cfg env hd1  in
               let t2 =
                 let uu___145_12602 = t1  in
                 {
                   FStar_Syntax_Syntax.n =
                     (FStar_Syntax_Syntax.Tm_app (hd2, args1));
                   FStar_Syntax_Syntax.pos =
                     (uu___145_12602.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___145_12602.FStar_Syntax_Syntax.vars)
                 }  in
               rebuild cfg env stack t2
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               ((Prims.op_Negation (cfg.steps).no_full_norm) &&
                  (is_norm_request hd1 args))
                 &&
                 (Prims.op_Negation
                    (FStar_Ident.lid_equals
                       (cfg.tcenv).FStar_TypeChecker_Env.curmodule
                       FStar_Parser_Const.prims_lid))
               ->
               let cfg' =
                 let uu___146_12640 = cfg  in
                 {
                   steps =
                     (let uu___147_12643 = cfg.steps  in
                      {
                        beta = (uu___147_12643.beta);
                        iota = (uu___147_12643.iota);
                        zeta = (uu___147_12643.zeta);
                        weak = (uu___147_12643.weak);
                        hnf = (uu___147_12643.hnf);
                        primops = (uu___147_12643.primops);
                        eager_unfolding = (uu___147_12643.eager_unfolding);
                        inlining = (uu___147_12643.inlining);
                        no_delta_steps = false;
                        unfold_until = (uu___147_12643.unfold_until);
                        unfold_only = FStar_Pervasives_Native.None;
                        unfold_attr = (uu___147_12643.unfold_attr);
                        unfold_tac = (uu___147_12643.unfold_tac);
                        pure_subterms_within_computations =
                          (uu___147_12643.pure_subterms_within_computations);
                        simplify = (uu___147_12643.simplify);
                        erase_universes = (uu___147_12643.erase_universes);
                        allow_unbound_universes =
                          (uu___147_12643.allow_unbound_universes);
                        reify_ = (uu___147_12643.reify_);
                        compress_uvars = (uu___147_12643.compress_uvars);
                        no_full_norm = (uu___147_12643.no_full_norm);
                        check_no_uvars = (uu___147_12643.check_no_uvars);
                        unmeta = (uu___147_12643.unmeta);
                        unascribe = (uu___147_12643.unascribe)
                      });
                   tcenv = (uu___146_12640.tcenv);
                   debug = (uu___146_12640.debug);
                   delta_level =
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.Delta_constant];
                   primitive_steps = (uu___146_12640.primitive_steps);
                   strong = (uu___146_12640.strong);
                   memoize_lazy = (uu___146_12640.memoize_lazy);
                   normalize_pure_lets = true
                 }  in
               let uu____12646 = get_norm_request (norm cfg' env []) args  in
               (match uu____12646 with
                | (s,tm) ->
                    let delta_level =
                      let uu____12662 =
                        FStar_All.pipe_right s
                          (FStar_Util.for_some
                             (fun uu___84_12667  ->
                                match uu___84_12667 with
                                | UnfoldUntil uu____12668 -> true
                                | UnfoldOnly uu____12669 -> true
                                | uu____12672 -> false))
                         in
                      if uu____12662
                      then
                        [FStar_TypeChecker_Env.Unfold
                           FStar_Syntax_Syntax.Delta_constant]
                      else [FStar_TypeChecker_Env.NoDelta]  in
                    let cfg'1 =
                      let uu___148_12677 = cfg  in
                      let uu____12678 = to_fsteps s  in
                      {
                        steps = uu____12678;
                        tcenv = (uu___148_12677.tcenv);
                        debug = (uu___148_12677.debug);
                        delta_level;
                        primitive_steps = (uu___148_12677.primitive_steps);
                        strong = (uu___148_12677.strong);
                        memoize_lazy = (uu___148_12677.memoize_lazy);
                        normalize_pure_lets = true
                      }  in
                    let stack' =
                      let tail1 = (Cfg cfg) :: stack  in
                      if (cfg.debug).print_normalized
                      then
                        let uu____12687 =
                          let uu____12688 =
                            let uu____12693 = FStar_Util.now ()  in
                            (t1, uu____12693)  in
                          Debug uu____12688  in
                        uu____12687 :: tail1
                      else tail1  in
                    norm cfg'1 env stack' tm)
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u  in
               let uu____12697 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack uu____12697
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               if (cfg.steps).erase_universes
               then norm cfg env stack t'
               else
                 (let us1 =
                    let uu____12706 =
                      let uu____12713 =
                        FStar_List.map (norm_universe cfg env) us  in
                      (uu____12713, (t1.FStar_Syntax_Syntax.pos))  in
                    UnivArgs uu____12706  in
                  let stack1 = us1 :: stack  in norm cfg env stack1 t')
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let qninfo =
                 let uu____12723 = FStar_Syntax_Syntax.lid_of_fv fv  in
                 FStar_TypeChecker_Env.lookup_qname cfg.tcenv uu____12723  in
               let uu____12724 =
                 FStar_TypeChecker_Env.qninfo_is_action qninfo  in
               if uu____12724
               then
                 let b = should_reify cfg stack  in
                 (log cfg
                    (fun uu____12730  ->
                       let uu____12731 = FStar_Syntax_Print.term_to_string t1
                          in
                       let uu____12732 = FStar_Util.string_of_bool b  in
                       FStar_Util.print2
                         ">>> For DM4F action %s, should_reify = %s\n"
                         uu____12731 uu____12732);
                  if b
                  then
                    (let uu____12733 = FStar_List.tl stack  in
                     do_unfold_fv cfg env uu____12733 t1 qninfo fv)
                  else rebuild cfg env stack t1)
               else
                 (let should_delta =
                    FStar_All.pipe_right cfg.delta_level
                      (FStar_Util.for_some
                         (fun uu___85_12742  ->
                            match uu___85_12742 with
                            | FStar_TypeChecker_Env.UnfoldTac  -> false
                            | FStar_TypeChecker_Env.NoDelta  -> false
                            | FStar_TypeChecker_Env.Inlining  -> true
                            | FStar_TypeChecker_Env.Eager_unfolding_only  ->
                                true
                            | FStar_TypeChecker_Env.Unfold l ->
                                FStar_TypeChecker_Common.delta_depth_greater_than
                                  fv.FStar_Syntax_Syntax.fv_delta l))
                     in
                  let should_delta1 =
                    should_delta &&
                      (match (cfg.steps).unfold_only with
                       | FStar_Pervasives_Native.None  -> true
                       | FStar_Pervasives_Native.Some lids ->
                           FStar_Util.for_some
                             (FStar_Syntax_Syntax.fv_eq_lid fv) lids)
                     in
                  let should_delta2 =
                    if Prims.op_Negation should_delta1
                    then false
                    else
                      (let tac_opaque_attr =
                         FStar_Syntax_Util.exp_string "tac_opaque"  in
                       let attrs =
                         FStar_TypeChecker_Env.attrs_of_qninfo qninfo  in
                       (match (attrs, ((cfg.steps).unfold_attr)) with
                        | (FStar_Pervasives_Native.None
                           ,FStar_Pervasives_Native.Some at) -> false
                        | (FStar_Pervasives_Native.Some
                           ats,FStar_Pervasives_Native.Some at) ->
                            FStar_Util.for_some (attr_eq at) ats
                        | (uu____12789,uu____12790) -> true) &&
                         (if (cfg.steps).unfold_tac
                          then
                            let uu____12804 =
                              cases
                                (FStar_Util.for_some
                                   (attr_eq tac_opaque_attr)) false attrs
                               in
                            FStar_All.pipe_left Prims.op_Negation uu____12804
                          else true))
                     in
                  log cfg
                    (fun uu____12813  ->
                       let uu____12814 = FStar_Syntax_Print.term_to_string t1
                          in
                       let uu____12815 =
                         FStar_Range.string_of_range
                           t1.FStar_Syntax_Syntax.pos
                          in
                       let uu____12816 =
                         FStar_Util.string_of_bool should_delta2  in
                       FStar_Util.print3
                         ">>> For %s (%s), should_delta = %s\n" uu____12814
                         uu____12815 uu____12816);
                  if should_delta2
                  then do_unfold_fv cfg env stack t1 qninfo fv
                  else rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____12819 = lookup_bvar env x  in
               (match uu____12819 with
                | Univ uu____12822 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if (Prims.op_Negation fix) || (cfg.steps).zeta
                    then
                      let uu____12871 = FStar_ST.op_Bang r  in
                      (match uu____12871 with
                       | FStar_Pervasives_Native.Some (env2,t') ->
                           (log cfg
                              (fun uu____12989  ->
                                 let uu____12990 =
                                   FStar_Syntax_Print.term_to_string t1  in
                                 let uu____12991 =
                                   FStar_Syntax_Print.term_to_string t'  in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____12990
                                   uu____12991);
                            (let uu____12992 =
                               let uu____12993 =
                                 FStar_Syntax_Subst.compress t'  in
                               uu____12993.FStar_Syntax_Syntax.n  in
                             match uu____12992 with
                             | FStar_Syntax_Syntax.Tm_abs uu____12996 ->
                                 norm cfg env2 stack t'
                             | uu____13013 -> rebuild cfg env2 stack t'))
                       | FStar_Pervasives_Native.None  ->
                           norm cfg env1 ((MemoLazy r) :: stack) t0)
                    else norm cfg env1 stack t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack with
                | (UnivArgs uu____13083)::uu____13084 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Match uu____13093)::uu____13094 ->
                    failwith
                      "Ill-typed term: cannot pattern match an abstraction"
                | (Arg (c,uu____13104,uu____13105))::stack_rest ->
                    (match c with
                     | Univ uu____13109 ->
                         norm cfg ((FStar_Pervasives_Native.None, c) :: env)
                           stack_rest t1
                     | uu____13118 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | b::[] ->
                              (log cfg
                                 (fun uu____13139  ->
                                    let uu____13140 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____13140);
                               norm cfg
                                 (((FStar_Pervasives_Native.Some b), c) ::
                                 env) stack_rest body)
                          | b::tl1 ->
                              (log cfg
                                 (fun uu____13180  ->
                                    let uu____13181 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____13181);
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
                       (fun uu____13259  ->
                          let uu____13260 =
                            FStar_Syntax_Print.term_to_string t1  in
                          FStar_Util.print1 "\tSet memo %s\n" uu____13260);
                     norm cfg env stack1 t1)
                | (Debug uu____13261)::uu____13262 ->
                    if (cfg.steps).weak
                    then
                      let uu____13269 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____13269
                    else
                      (let uu____13271 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____13271 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____13313  -> dummy :: env1) env)
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
                                          let uu____13350 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____13350)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___149_13355 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___149_13355.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___149_13355.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____13356 -> lopt  in
                           (log cfg
                              (fun uu____13362  ->
                                 let uu____13363 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____13363);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___150_13372 = cfg  in
                               {
                                 steps = (uu___150_13372.steps);
                                 tcenv = (uu___150_13372.tcenv);
                                 debug = (uu___150_13372.debug);
                                 delta_level = (uu___150_13372.delta_level);
                                 primitive_steps =
                                   (uu___150_13372.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___150_13372.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___150_13372.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Meta uu____13383)::uu____13384 ->
                    if (cfg.steps).weak
                    then
                      let uu____13391 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____13391
                    else
                      (let uu____13393 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____13393 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____13435  -> dummy :: env1) env)
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
                                          let uu____13472 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____13472)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___149_13477 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___149_13477.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___149_13477.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____13478 -> lopt  in
                           (log cfg
                              (fun uu____13484  ->
                                 let uu____13485 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____13485);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___150_13494 = cfg  in
                               {
                                 steps = (uu___150_13494.steps);
                                 tcenv = (uu___150_13494.tcenv);
                                 debug = (uu___150_13494.debug);
                                 delta_level = (uu___150_13494.delta_level);
                                 primitive_steps =
                                   (uu___150_13494.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___150_13494.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___150_13494.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Let uu____13505)::uu____13506 ->
                    if (cfg.steps).weak
                    then
                      let uu____13517 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____13517
                    else
                      (let uu____13519 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____13519 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____13561  -> dummy :: env1) env)
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
                                          let uu____13598 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____13598)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___149_13603 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___149_13603.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___149_13603.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____13604 -> lopt  in
                           (log cfg
                              (fun uu____13610  ->
                                 let uu____13611 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____13611);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___150_13620 = cfg  in
                               {
                                 steps = (uu___150_13620.steps);
                                 tcenv = (uu___150_13620.tcenv);
                                 debug = (uu___150_13620.debug);
                                 delta_level = (uu___150_13620.delta_level);
                                 primitive_steps =
                                   (uu___150_13620.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___150_13620.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___150_13620.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (App uu____13631)::uu____13632 ->
                    if (cfg.steps).weak
                    then
                      let uu____13643 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____13643
                    else
                      (let uu____13645 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____13645 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____13687  -> dummy :: env1) env)
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
                                          let uu____13724 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____13724)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___149_13729 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___149_13729.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___149_13729.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____13730 -> lopt  in
                           (log cfg
                              (fun uu____13736  ->
                                 let uu____13737 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____13737);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___150_13746 = cfg  in
                               {
                                 steps = (uu___150_13746.steps);
                                 tcenv = (uu___150_13746.tcenv);
                                 debug = (uu___150_13746.debug);
                                 delta_level = (uu___150_13746.delta_level);
                                 primitive_steps =
                                   (uu___150_13746.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___150_13746.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___150_13746.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Abs uu____13757)::uu____13758 ->
                    if (cfg.steps).weak
                    then
                      let uu____13773 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____13773
                    else
                      (let uu____13775 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____13775 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____13817  -> dummy :: env1) env)
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
                                          let uu____13854 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____13854)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___149_13859 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___149_13859.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___149_13859.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____13860 -> lopt  in
                           (log cfg
                              (fun uu____13866  ->
                                 let uu____13867 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____13867);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___150_13876 = cfg  in
                               {
                                 steps = (uu___150_13876.steps);
                                 tcenv = (uu___150_13876.tcenv);
                                 debug = (uu___150_13876.debug);
                                 delta_level = (uu___150_13876.delta_level);
                                 primitive_steps =
                                   (uu___150_13876.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___150_13876.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___150_13876.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | [] ->
                    if (cfg.steps).weak
                    then
                      let uu____13887 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____13887
                    else
                      (let uu____13889 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____13889 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____13931  -> dummy :: env1) env)
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
                                          let uu____13968 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____13968)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___149_13973 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___149_13973.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___149_13973.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____13974 -> lopt  in
                           (log cfg
                              (fun uu____13980  ->
                                 let uu____13981 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____13981);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___150_13990 = cfg  in
                               {
                                 steps = (uu___150_13990.steps);
                                 tcenv = (uu___150_13990.tcenv);
                                 debug = (uu___150_13990.debug);
                                 delta_level = (uu___150_13990.delta_level);
                                 primitive_steps =
                                   (uu___150_13990.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___150_13990.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___150_13990.normalize_pure_lets)
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
                      (fun uu____14039  ->
                         fun stack1  ->
                           match uu____14039 with
                           | (a,aq) ->
                               let uu____14051 =
                                 let uu____14052 =
                                   let uu____14059 =
                                     let uu____14060 =
                                       let uu____14091 =
                                         FStar_Util.mk_ref
                                           FStar_Pervasives_Native.None
                                          in
                                       (env, a, uu____14091, false)  in
                                     Clos uu____14060  in
                                   (uu____14059, aq,
                                     (t1.FStar_Syntax_Syntax.pos))
                                    in
                                 Arg uu____14052  in
                               uu____14051 :: stack1) args)
                  in
               (log cfg
                  (fun uu____14175  ->
                     let uu____14176 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args)
                        in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____14176);
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
                             ((let uu___151_14212 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___151_14212.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___151_14212.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos
                         in
                      rebuild cfg env stack t2
                  | uu____14213 ->
                      let uu____14218 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____14218)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort  in
                  let uu____14221 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] f
                     in
                  match uu____14221 with
                  | (closing,f1) ->
                      let f2 = norm cfg (dummy :: env) [] f1  in
                      let t2 =
                        let uu____14252 =
                          let uu____14253 =
                            let uu____14260 =
                              FStar_Syntax_Subst.close closing f2  in
                            ((let uu___152_14262 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___152_14262.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___152_14262.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____14260)
                             in
                          FStar_Syntax_Syntax.Tm_refine uu____14253  in
                        mk uu____14252 t1.FStar_Syntax_Syntax.pos  in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if (cfg.steps).weak
               then
                 let uu____14281 = closure_as_term cfg env t1  in
                 rebuild cfg env stack uu____14281
               else
                 (let uu____14283 = FStar_Syntax_Subst.open_comp bs c  in
                  match uu____14283 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____14291 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun uu____14315  -> dummy :: env1) env)
                           in
                        norm_comp cfg uu____14291 c1  in
                      let t2 =
                        let uu____14337 = norm_binders cfg env bs1  in
                        FStar_Syntax_Util.arrow uu____14337 c2  in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) when
               (cfg.steps).unascribe -> norm cfg env stack t11
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack with
                | (Match uu____14448)::uu____14449 ->
                    (log cfg
                       (fun uu____14460  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (Arg uu____14461)::uu____14462 ->
                    (log cfg
                       (fun uu____14473  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (App
                    (uu____14474,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_constant
                                     (FStar_Const.Const_reify );
                                   FStar_Syntax_Syntax.pos = uu____14475;
                                   FStar_Syntax_Syntax.vars = uu____14476;_},uu____14477,uu____14478))::uu____14479
                    ->
                    (log cfg
                       (fun uu____14488  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (MemoLazy uu____14489)::uu____14490 ->
                    (log cfg
                       (fun uu____14501  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | uu____14502 ->
                    (log cfg
                       (fun uu____14505  ->
                          FStar_Util.print_string "+++ Keeping ascription \n");
                     (let t12 = norm cfg env [] t11  in
                      log cfg
                        (fun uu____14509  ->
                           FStar_Util.print_string
                             "+++ Normalizing ascription \n");
                      (let tc1 =
                         match tc with
                         | FStar_Util.Inl t2 ->
                             let uu____14526 = norm cfg env [] t2  in
                             FStar_Util.Inl uu____14526
                         | FStar_Util.Inr c ->
                             let uu____14534 = norm_comp cfg env c  in
                             FStar_Util.Inr uu____14534
                          in
                       let tacopt1 =
                         FStar_Util.map_opt tacopt (norm cfg env [])  in
                       match stack with
                       | (Cfg cfg1)::stack1 ->
                           let t2 =
                             let uu____14547 =
                               let uu____14548 =
                                 let uu____14575 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____14575, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____14548
                                in
                             mk uu____14547 t1.FStar_Syntax_Syntax.pos  in
                           norm cfg1 env stack1 t2
                       | uu____14594 ->
                           let uu____14595 =
                             let uu____14596 =
                               let uu____14597 =
                                 let uu____14624 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____14624, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____14597
                                in
                             mk uu____14596 t1.FStar_Syntax_Syntax.pos  in
                           rebuild cfg env stack uu____14595))))
           | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
               let stack1 =
                 (Match (env, branches, (t1.FStar_Syntax_Syntax.pos))) ::
                 stack  in
               norm cfg env stack1 head1
           | FStar_Syntax_Syntax.Tm_let ((b,lbs),lbody) when
               (FStar_Syntax_Syntax.is_top_level lbs) &&
                 (cfg.steps).compress_uvars
               ->
               let lbs1 =
                 FStar_All.pipe_right lbs
                   (FStar_List.map
                      (fun lb  ->
                         let uu____14734 =
                           FStar_Syntax_Subst.univ_var_opening
                             lb.FStar_Syntax_Syntax.lbunivs
                            in
                         match uu____14734 with
                         | (openings,lbunivs) ->
                             let cfg1 =
                               let uu___153_14754 = cfg  in
                               let uu____14755 =
                                 FStar_TypeChecker_Env.push_univ_vars
                                   cfg.tcenv lbunivs
                                  in
                               {
                                 steps = (uu___153_14754.steps);
                                 tcenv = uu____14755;
                                 debug = (uu___153_14754.debug);
                                 delta_level = (uu___153_14754.delta_level);
                                 primitive_steps =
                                   (uu___153_14754.primitive_steps);
                                 strong = (uu___153_14754.strong);
                                 memoize_lazy = (uu___153_14754.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___153_14754.normalize_pure_lets)
                               }  in
                             let norm1 t2 =
                               let uu____14760 =
                                 let uu____14761 =
                                   FStar_Syntax_Subst.subst openings t2  in
                                 norm cfg1 env [] uu____14761  in
                               FStar_Syntax_Subst.close_univ_vars lbunivs
                                 uu____14760
                                in
                             let lbtyp = norm1 lb.FStar_Syntax_Syntax.lbtyp
                                in
                             let lbdef = norm1 lb.FStar_Syntax_Syntax.lbdef
                                in
                             let uu___154_14764 = lb  in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___154_14764.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs = lbunivs;
                               FStar_Syntax_Syntax.lbtyp = lbtyp;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___154_14764.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = lbdef;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___154_14764.FStar_Syntax_Syntax.lbattrs)
                             }))
                  in
               let uu____14765 =
                 mk (FStar_Syntax_Syntax.Tm_let ((b, lbs1), lbody))
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack uu____14765
           | FStar_Syntax_Syntax.Tm_let
               ((uu____14776,{
                               FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                 uu____14777;
                               FStar_Syntax_Syntax.lbunivs = uu____14778;
                               FStar_Syntax_Syntax.lbtyp = uu____14779;
                               FStar_Syntax_Syntax.lbeff = uu____14780;
                               FStar_Syntax_Syntax.lbdef = uu____14781;
                               FStar_Syntax_Syntax.lbattrs = uu____14782;_}::uu____14783),uu____14784)
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff
                  in
               let uu____14824 =
                 (Prims.op_Negation (cfg.steps).no_delta_steps) &&
                   (((FStar_Syntax_Util.is_pure_effect n1) &&
                       (cfg.normalize_pure_lets ||
                          (FStar_Util.for_some
                             (FStar_Syntax_Util.is_fvar
                                FStar_Parser_Const.inline_let_attr)
                             lb.FStar_Syntax_Syntax.lbattrs)))
                      ||
                      ((FStar_Syntax_Util.is_ghost_effect n1) &&
                         (Prims.op_Negation
                            (cfg.steps).pure_subterms_within_computations)))
                  in
               if uu____14824
               then
                 let binder =
                   let uu____14826 =
                     FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                   FStar_Syntax_Syntax.mk_binder uu____14826  in
                 let env1 =
                   let uu____14836 =
                     let uu____14843 =
                       let uu____14844 =
                         let uu____14875 =
                           FStar_Util.mk_ref FStar_Pervasives_Native.None  in
                         (env, (lb.FStar_Syntax_Syntax.lbdef), uu____14875,
                           false)
                          in
                       Clos uu____14844  in
                     ((FStar_Pervasives_Native.Some binder), uu____14843)  in
                   uu____14836 :: env  in
                 (log cfg
                    (fun uu____14968  ->
                       FStar_Util.print_string "+++ Reducing Tm_let\n");
                  norm cfg env1 stack body)
               else
                 if (cfg.steps).weak
                 then
                   (log cfg
                      (fun uu____14972  ->
                         FStar_Util.print_string "+++ Not touching Tm_let\n");
                    (let uu____14973 = closure_as_term cfg env t1  in
                     rebuild cfg env stack uu____14973))
                 else
                   (let uu____14975 =
                      let uu____14980 =
                        let uu____14981 =
                          let uu____14982 =
                            FStar_All.pipe_right
                              lb.FStar_Syntax_Syntax.lbname FStar_Util.left
                             in
                          FStar_All.pipe_right uu____14982
                            FStar_Syntax_Syntax.mk_binder
                           in
                        [uu____14981]  in
                      FStar_Syntax_Subst.open_term uu____14980 body  in
                    match uu____14975 with
                    | (bs,body1) ->
                        (log cfg
                           (fun uu____14991  ->
                              FStar_Util.print_string
                                "+++ Normalizing Tm_let -- type\n");
                         (let ty =
                            norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                          let lbname =
                            let x =
                              let uu____14999 = FStar_List.hd bs  in
                              FStar_Pervasives_Native.fst uu____14999  in
                            FStar_Util.Inl
                              (let uu___155_15009 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___155_15009.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___155_15009.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               })
                             in
                          log cfg
                            (fun uu____15012  ->
                               FStar_Util.print_string
                                 "+++ Normalizing Tm_let -- definiens\n");
                          (let lb1 =
                             let uu___156_15014 = lb  in
                             let uu____15015 =
                               norm cfg env [] lb.FStar_Syntax_Syntax.lbdef
                                in
                             {
                               FStar_Syntax_Syntax.lbname = lbname;
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___156_15014.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp = ty;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___156_15014.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = uu____15015;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___156_15014.FStar_Syntax_Syntax.lbattrs)
                             }  in
                           let env' =
                             FStar_All.pipe_right bs
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____15050  -> dummy :: env1) env)
                              in
                           let stack1 = (Cfg cfg) :: stack  in
                           let cfg1 =
                             let uu___157_15073 = cfg  in
                             {
                               steps = (uu___157_15073.steps);
                               tcenv = (uu___157_15073.tcenv);
                               debug = (uu___157_15073.debug);
                               delta_level = (uu___157_15073.delta_level);
                               primitive_steps =
                                 (uu___157_15073.primitive_steps);
                               strong = true;
                               memoize_lazy = (uu___157_15073.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___157_15073.normalize_pure_lets)
                             }  in
                           log cfg1
                             (fun uu____15076  ->
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
               let uu____15093 = FStar_Syntax_Subst.open_let_rec lbs body  in
               (match uu____15093 with
                | (lbs1,body1) ->
                    let lbs2 =
                      FStar_List.map
                        (fun lb  ->
                           let ty =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                           let lbname =
                             let uu____15129 =
                               let uu___158_15130 =
                                 FStar_Util.left
                                   lb.FStar_Syntax_Syntax.lbname
                                  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___158_15130.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___158_15130.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               }  in
                             FStar_Util.Inl uu____15129  in
                           let uu____15131 =
                             FStar_Syntax_Util.abs_formals
                               lb.FStar_Syntax_Syntax.lbdef
                              in
                           match uu____15131 with
                           | (xs,def_body,lopt) ->
                               let xs1 = norm_binders cfg env xs  in
                               let env1 =
                                 let uu____15157 =
                                   FStar_List.map (fun uu____15173  -> dummy)
                                     lbs1
                                    in
                                 let uu____15174 =
                                   let uu____15183 =
                                     FStar_List.map
                                       (fun uu____15203  -> dummy) xs1
                                      in
                                   FStar_List.append uu____15183 env  in
                                 FStar_List.append uu____15157 uu____15174
                                  in
                               let def_body1 = norm cfg env1 [] def_body  in
                               let lopt1 =
                                 match lopt with
                                 | FStar_Pervasives_Native.Some rc ->
                                     let uu____15227 =
                                       let uu___159_15228 = rc  in
                                       let uu____15229 =
                                         FStar_Util.map_opt
                                           rc.FStar_Syntax_Syntax.residual_typ
                                           (norm cfg env1 [])
                                          in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___159_15228.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           uu____15229;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___159_15228.FStar_Syntax_Syntax.residual_flags)
                                       }  in
                                     FStar_Pervasives_Native.Some uu____15227
                                 | uu____15236 -> lopt  in
                               let def =
                                 FStar_Syntax_Util.abs xs1 def_body1 lopt1
                                  in
                               let uu___160_15240 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname = lbname;
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___160_15240.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp = ty;
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___160_15240.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___160_15240.FStar_Syntax_Syntax.lbattrs)
                               }) lbs1
                       in
                    let env' =
                      let uu____15250 =
                        FStar_List.map (fun uu____15266  -> dummy) lbs2  in
                      FStar_List.append uu____15250 env  in
                    let body2 = norm cfg env' [] body1  in
                    let uu____15274 =
                      FStar_Syntax_Subst.close_let_rec lbs2 body2  in
                    (match uu____15274 with
                     | (lbs3,body3) ->
                         let t2 =
                           let uu___161_15290 = t1  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_let
                                  ((true, lbs3), body3));
                             FStar_Syntax_Syntax.pos =
                               (uu___161_15290.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___161_15290.FStar_Syntax_Syntax.vars)
                           }  in
                         rebuild cfg env stack t2))
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               Prims.op_Negation (cfg.steps).zeta ->
               let uu____15317 = closure_as_term cfg env t1  in
               rebuild cfg env stack uu____15317
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____15336 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____15412  ->
                        match uu____15412 with
                        | (rec_env,memos,i) ->
                            let bv =
                              let uu___162_15533 =
                                FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                                 in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___162_15533.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index = i;
                                FStar_Syntax_Syntax.sort =
                                  (uu___162_15533.FStar_Syntax_Syntax.sort)
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
               (match uu____15336 with
                | (rec_env,memos,uu____15746) ->
                    let uu____15799 =
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
                             let uu____16110 =
                               let uu____16117 =
                                 let uu____16118 =
                                   let uu____16149 =
                                     FStar_Util.mk_ref
                                       FStar_Pervasives_Native.None
                                      in
                                   (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                     uu____16149, false)
                                    in
                                 Clos uu____16118  in
                               (FStar_Pervasives_Native.None, uu____16117)
                                in
                             uu____16110 :: env1)
                        (FStar_Pervasives_Native.snd lbs) env
                       in
                    norm cfg body_env stack body)
           | FStar_Syntax_Syntax.Tm_meta (head1,m) ->
               (log cfg
                  (fun uu____16259  ->
                     let uu____16260 =
                       FStar_Syntax_Print.metadata_to_string m  in
                     FStar_Util.print1 ">> metadata = %s\n" uu____16260);
                (match m with
                 | FStar_Syntax_Syntax.Meta_monadic (m1,t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inl m1) t2
                 | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inr (m1, m')) t2
                 | uu____16282 ->
                     if (cfg.steps).unmeta
                     then norm cfg env stack head1
                     else
                       (match stack with
                        | uu____16284::uu____16285 ->
                            (match m with
                             | FStar_Syntax_Syntax.Meta_labeled
                                 (l,r,uu____16290) ->
                                 norm cfg env ((Meta (m, r)) :: stack) head1
                             | FStar_Syntax_Syntax.Meta_alien uu____16291 ->
                                 rebuild cfg env stack t1
                             | FStar_Syntax_Syntax.Meta_pattern args ->
                                 let args1 = norm_pattern_args cfg env args
                                    in
                                 norm cfg env
                                   ((Meta
                                       ((FStar_Syntax_Syntax.Meta_pattern
                                           args1),
                                         (t1.FStar_Syntax_Syntax.pos))) ::
                                   stack) head1
                             | uu____16322 -> norm cfg env stack head1)
                        | [] ->
                            let head2 = norm cfg env [] head1  in
                            let m1 =
                              match m with
                              | FStar_Syntax_Syntax.Meta_pattern args ->
                                  let uu____16336 =
                                    norm_pattern_args cfg env args  in
                                  FStar_Syntax_Syntax.Meta_pattern
                                    uu____16336
                              | uu____16347 -> m  in
                            let t2 =
                              mk (FStar_Syntax_Syntax.Tm_meta (head2, m1))
                                t1.FStar_Syntax_Syntax.pos
                               in
                            rebuild cfg env stack t2)))
           | FStar_Syntax_Syntax.Tm_delayed uu____16351 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               norm cfg env stack t2
           | FStar_Syntax_Syntax.Tm_uvar uu____16377 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               (match t2.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_uvar uu____16395 ->
                    if (cfg.steps).check_no_uvars
                    then
                      let uu____16412 =
                        let uu____16413 =
                          FStar_Range.string_of_range
                            t2.FStar_Syntax_Syntax.pos
                           in
                        let uu____16414 =
                          FStar_Syntax_Print.term_to_string t2  in
                        FStar_Util.format2
                          "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                          uu____16413 uu____16414
                         in
                      failwith uu____16412
                    else rebuild cfg env stack t2
                | uu____16416 -> norm cfg env stack t2))

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
                let uu____16426 = FStar_Syntax_Syntax.range_of_fv f  in
                FStar_TypeChecker_Env.set_range cfg.tcenv uu____16426  in
              let uu____16427 =
                FStar_TypeChecker_Env.lookup_definition_qninfo
                  cfg.delta_level
                  (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                  qninfo
                 in
              match uu____16427 with
              | FStar_Pervasives_Native.None  ->
                  (log cfg
                     (fun uu____16440  ->
                        FStar_Util.print "Tm_fvar case 2\n" []);
                   rebuild cfg env stack t0)
              | FStar_Pervasives_Native.Some (us,t) ->
                  (log cfg
                     (fun uu____16451  ->
                        let uu____16452 =
                          FStar_Syntax_Print.term_to_string t0  in
                        let uu____16453 = FStar_Syntax_Print.term_to_string t
                           in
                        FStar_Util.print2 ">>> Unfolded %s to %s\n"
                          uu____16452 uu____16453);
                   (let t1 =
                      if
                        ((cfg.steps).unfold_until =
                           (FStar_Pervasives_Native.Some
                              FStar_Syntax_Syntax.Delta_constant))
                          && (Prims.op_Negation (cfg.steps).unfold_tac)
                      then t
                      else
                        FStar_Syntax_Subst.set_use_range
                          (FStar_Ident.range_of_lid
                             (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                          t
                       in
                    let n1 = FStar_List.length us  in
                    if n1 > (Prims.parse_int "0")
                    then
                      match stack with
                      | (UnivArgs (us',uu____16466))::stack1 ->
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
                      | uu____16521 when (cfg.steps).erase_universes ->
                          norm cfg env stack t1
                      | uu____16524 ->
                          let uu____16527 =
                            let uu____16528 =
                              FStar_Syntax_Print.lid_to_string
                                (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                               in
                            FStar_Util.format1
                              "Impossible: missing universe instantiation on %s"
                              uu____16528
                             in
                          failwith uu____16527
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
                  let uu___163_16549 = cfg  in
                  let uu____16550 =
                    to_fsteps
                      [PureSubtermsWithinComputations;
                      Primops;
                      AllowUnboundUniverses;
                      EraseUniverses;
                      Exclude Zeta;
                      NoDeltaSteps]
                     in
                  {
                    steps = uu____16550;
                    tcenv = (uu___163_16549.tcenv);
                    debug = (uu___163_16549.debug);
                    delta_level =
                      [FStar_TypeChecker_Env.Inlining;
                      FStar_TypeChecker_Env.Eager_unfolding_only];
                    primitive_steps = (uu___163_16549.primitive_steps);
                    strong = (uu___163_16549.strong);
                    memoize_lazy = (uu___163_16549.memoize_lazy);
                    normalize_pure_lets =
                      (uu___163_16549.normalize_pure_lets)
                  }
                else
                  (let uu___164_16552 = cfg  in
                   {
                     steps =
                       (let uu___165_16555 = cfg.steps  in
                        {
                          beta = (uu___165_16555.beta);
                          iota = (uu___165_16555.iota);
                          zeta = false;
                          weak = (uu___165_16555.weak);
                          hnf = (uu___165_16555.hnf);
                          primops = (uu___165_16555.primops);
                          eager_unfolding = (uu___165_16555.eager_unfolding);
                          inlining = (uu___165_16555.inlining);
                          no_delta_steps = (uu___165_16555.no_delta_steps);
                          unfold_until = (uu___165_16555.unfold_until);
                          unfold_only = (uu___165_16555.unfold_only);
                          unfold_attr = (uu___165_16555.unfold_attr);
                          unfold_tac = (uu___165_16555.unfold_tac);
                          pure_subterms_within_computations =
                            (uu___165_16555.pure_subterms_within_computations);
                          simplify = (uu___165_16555.simplify);
                          erase_universes = (uu___165_16555.erase_universes);
                          allow_unbound_universes =
                            (uu___165_16555.allow_unbound_universes);
                          reify_ = (uu___165_16555.reify_);
                          compress_uvars = (uu___165_16555.compress_uvars);
                          no_full_norm = (uu___165_16555.no_full_norm);
                          check_no_uvars = (uu___165_16555.check_no_uvars);
                          unmeta = (uu___165_16555.unmeta);
                          unascribe = (uu___165_16555.unascribe)
                        });
                     tcenv = (uu___164_16552.tcenv);
                     debug = (uu___164_16552.debug);
                     delta_level = (uu___164_16552.delta_level);
                     primitive_steps = (uu___164_16552.primitive_steps);
                     strong = (uu___164_16552.strong);
                     memoize_lazy = (uu___164_16552.memoize_lazy);
                     normalize_pure_lets =
                       (uu___164_16552.normalize_pure_lets)
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
                ((Meta (metadata, (head1.FStar_Syntax_Syntax.pos))) ::
                stack1) head1

and (do_reify_monadic :
  (Prims.unit -> FStar_Syntax_Syntax.term) ->
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
                  (fun uu____16585  ->
                     let uu____16586 = FStar_Syntax_Print.tag_of_term head2
                        in
                     let uu____16587 =
                       FStar_Syntax_Print.term_to_string head2  in
                     FStar_Util.print2 "Reifying: (%s) %s\n" uu____16586
                       uu____16587);
                (let uu____16588 =
                   let uu____16589 = FStar_Syntax_Subst.compress head2  in
                   uu____16589.FStar_Syntax_Syntax.n  in
                 match uu____16588 with
                 | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                     let ed =
                       FStar_TypeChecker_Env.get_effect_decl cfg.tcenv m  in
                     let uu____16607 = ed.FStar_Syntax_Syntax.bind_repr  in
                     (match uu____16607 with
                      | (uu____16608,bind_repr) ->
                          (match lb.FStar_Syntax_Syntax.lbname with
                           | FStar_Util.Inr uu____16614 ->
                               failwith
                                 "Cannot reify a top-level let binding"
                           | FStar_Util.Inl x ->
                               let is_return e =
                                 let uu____16622 =
                                   let uu____16623 =
                                     FStar_Syntax_Subst.compress e  in
                                   uu____16623.FStar_Syntax_Syntax.n  in
                                 match uu____16622 with
                                 | FStar_Syntax_Syntax.Tm_meta
                                     (e1,FStar_Syntax_Syntax.Meta_monadic
                                      (uu____16629,uu____16630))
                                     ->
                                     let uu____16639 =
                                       let uu____16640 =
                                         FStar_Syntax_Subst.compress e1  in
                                       uu____16640.FStar_Syntax_Syntax.n  in
                                     (match uu____16639 with
                                      | FStar_Syntax_Syntax.Tm_meta
                                          (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                           (uu____16646,msrc,uu____16648))
                                          when
                                          FStar_Syntax_Util.is_pure_effect
                                            msrc
                                          ->
                                          let uu____16657 =
                                            FStar_Syntax_Subst.compress e2
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____16657
                                      | uu____16658 ->
                                          FStar_Pervasives_Native.None)
                                 | uu____16659 ->
                                     FStar_Pervasives_Native.None
                                  in
                               let uu____16660 =
                                 is_return lb.FStar_Syntax_Syntax.lbdef  in
                               (match uu____16660 with
                                | FStar_Pervasives_Native.Some e ->
                                    let lb1 =
                                      let uu___166_16665 = lb  in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          (uu___166_16665.FStar_Syntax_Syntax.lbname);
                                        FStar_Syntax_Syntax.lbunivs =
                                          (uu___166_16665.FStar_Syntax_Syntax.lbunivs);
                                        FStar_Syntax_Syntax.lbtyp =
                                          (uu___166_16665.FStar_Syntax_Syntax.lbtyp);
                                        FStar_Syntax_Syntax.lbeff =
                                          FStar_Parser_Const.effect_PURE_lid;
                                        FStar_Syntax_Syntax.lbdef = e;
                                        FStar_Syntax_Syntax.lbattrs =
                                          (uu___166_16665.FStar_Syntax_Syntax.lbattrs)
                                      }  in
                                    let uu____16666 = FStar_List.tl stack  in
                                    let uu____16667 =
                                      let uu____16668 =
                                        let uu____16671 =
                                          let uu____16672 =
                                            let uu____16685 =
                                              FStar_Syntax_Util.mk_reify body
                                               in
                                            ((false, [lb1]), uu____16685)  in
                                          FStar_Syntax_Syntax.Tm_let
                                            uu____16672
                                           in
                                        FStar_Syntax_Syntax.mk uu____16671
                                         in
                                      uu____16668
                                        FStar_Pervasives_Native.None
                                        head2.FStar_Syntax_Syntax.pos
                                       in
                                    norm cfg env uu____16666 uu____16667
                                | FStar_Pervasives_Native.None  ->
                                    let uu____16701 =
                                      let uu____16702 = is_return body  in
                                      match uu____16702 with
                                      | FStar_Pervasives_Native.Some
                                          {
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_bvar y;
                                            FStar_Syntax_Syntax.pos =
                                              uu____16706;
                                            FStar_Syntax_Syntax.vars =
                                              uu____16707;_}
                                          -> FStar_Syntax_Syntax.bv_eq x y
                                      | uu____16712 -> false  in
                                    if uu____16701
                                    then
                                      norm cfg env stack
                                        lb.FStar_Syntax_Syntax.lbdef
                                    else
                                      (let rng =
                                         head2.FStar_Syntax_Syntax.pos  in
                                       let head3 =
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
                                         let uu____16735 =
                                           let uu____16738 =
                                             let uu____16739 =
                                               let uu____16756 =
                                                 let uu____16759 =
                                                   FStar_Syntax_Syntax.mk_binder
                                                     x
                                                    in
                                                 [uu____16759]  in
                                               (uu____16756, body1,
                                                 (FStar_Pervasives_Native.Some
                                                    body_rc))
                                                in
                                             FStar_Syntax_Syntax.Tm_abs
                                               uu____16739
                                              in
                                           FStar_Syntax_Syntax.mk uu____16738
                                            in
                                         uu____16735
                                           FStar_Pervasives_Native.None
                                           body1.FStar_Syntax_Syntax.pos
                                          in
                                       let close1 = closure_as_term cfg env
                                          in
                                       let bind_inst =
                                         let uu____16775 =
                                           let uu____16776 =
                                             FStar_Syntax_Subst.compress
                                               bind_repr
                                              in
                                           uu____16776.FStar_Syntax_Syntax.n
                                            in
                                         match uu____16775 with
                                         | FStar_Syntax_Syntax.Tm_uinst
                                             (bind1,uu____16782::uu____16783::[])
                                             ->
                                             let uu____16790 =
                                               let uu____16793 =
                                                 let uu____16794 =
                                                   let uu____16801 =
                                                     let uu____16804 =
                                                       let uu____16805 =
                                                         close1
                                                           lb.FStar_Syntax_Syntax.lbtyp
                                                          in
                                                       (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                         cfg.tcenv
                                                         uu____16805
                                                        in
                                                     let uu____16806 =
                                                       let uu____16809 =
                                                         let uu____16810 =
                                                           close1 t  in
                                                         (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                           cfg.tcenv
                                                           uu____16810
                                                          in
                                                       [uu____16809]  in
                                                     uu____16804 ::
                                                       uu____16806
                                                      in
                                                   (bind1, uu____16801)  in
                                                 FStar_Syntax_Syntax.Tm_uinst
                                                   uu____16794
                                                  in
                                               FStar_Syntax_Syntax.mk
                                                 uu____16793
                                                in
                                             uu____16790
                                               FStar_Pervasives_Native.None
                                               rng
                                         | uu____16818 ->
                                             failwith
                                               "NIY : Reification of indexed effects"
                                          in
                                       let reified =
                                         let uu____16824 =
                                           let uu____16827 =
                                             let uu____16828 =
                                               let uu____16843 =
                                                 let uu____16846 =
                                                   FStar_Syntax_Syntax.as_arg
                                                     lb.FStar_Syntax_Syntax.lbtyp
                                                    in
                                                 let uu____16847 =
                                                   let uu____16850 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       t
                                                      in
                                                   let uu____16851 =
                                                     let uu____16854 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         FStar_Syntax_Syntax.tun
                                                        in
                                                     let uu____16855 =
                                                       let uu____16858 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           head3
                                                          in
                                                       let uu____16859 =
                                                         let uu____16862 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             FStar_Syntax_Syntax.tun
                                                            in
                                                         let uu____16863 =
                                                           let uu____16866 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               body2
                                                              in
                                                           [uu____16866]  in
                                                         uu____16862 ::
                                                           uu____16863
                                                          in
                                                       uu____16858 ::
                                                         uu____16859
                                                        in
                                                     uu____16854 ::
                                                       uu____16855
                                                      in
                                                   uu____16850 :: uu____16851
                                                    in
                                                 uu____16846 :: uu____16847
                                                  in
                                               (bind_inst, uu____16843)  in
                                             FStar_Syntax_Syntax.Tm_app
                                               uu____16828
                                              in
                                           FStar_Syntax_Syntax.mk uu____16827
                                            in
                                         uu____16824
                                           FStar_Pervasives_Native.None rng
                                          in
                                       log cfg
                                         (fun uu____16878  ->
                                            let uu____16879 =
                                              FStar_Syntax_Print.term_to_string
                                                head0
                                               in
                                            let uu____16880 =
                                              FStar_Syntax_Print.term_to_string
                                                reified
                                               in
                                            FStar_Util.print2
                                              "Reified (1) <%s> to %s\n"
                                              uu____16879 uu____16880);
                                       (let uu____16881 = FStar_List.tl stack
                                           in
                                        norm cfg env uu____16881 reified)))))
                 | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                     let ed =
                       FStar_TypeChecker_Env.get_effect_decl cfg.tcenv m  in
                     let uu____16905 = ed.FStar_Syntax_Syntax.bind_repr  in
                     (match uu____16905 with
                      | (uu____16906,bind_repr) ->
                          let maybe_unfold_action head3 =
                            let maybe_extract_fv t1 =
                              let t2 =
                                let uu____16941 =
                                  let uu____16942 =
                                    FStar_Syntax_Subst.compress t1  in
                                  uu____16942.FStar_Syntax_Syntax.n  in
                                match uu____16941 with
                                | FStar_Syntax_Syntax.Tm_uinst
                                    (t2,uu____16948) -> t2
                                | uu____16953 -> head3  in
                              let uu____16954 =
                                let uu____16955 =
                                  FStar_Syntax_Subst.compress t2  in
                                uu____16955.FStar_Syntax_Syntax.n  in
                              match uu____16954 with
                              | FStar_Syntax_Syntax.Tm_fvar x ->
                                  FStar_Pervasives_Native.Some x
                              | uu____16961 -> FStar_Pervasives_Native.None
                               in
                            let uu____16962 = maybe_extract_fv head3  in
                            match uu____16962 with
                            | FStar_Pervasives_Native.Some x when
                                let uu____16972 =
                                  FStar_Syntax_Syntax.lid_of_fv x  in
                                FStar_TypeChecker_Env.is_action cfg.tcenv
                                  uu____16972
                                ->
                                let head4 = norm cfg env [] head3  in
                                let action_unfolded =
                                  let uu____16977 = maybe_extract_fv head4
                                     in
                                  match uu____16977 with
                                  | FStar_Pervasives_Native.Some uu____16982
                                      -> FStar_Pervasives_Native.Some true
                                  | uu____16983 ->
                                      FStar_Pervasives_Native.Some false
                                   in
                                (head4, action_unfolded)
                            | uu____16988 ->
                                (head3, FStar_Pervasives_Native.None)
                             in
                          ((let is_arg_impure uu____17003 =
                              match uu____17003 with
                              | (e,q) ->
                                  let uu____17010 =
                                    let uu____17011 =
                                      FStar_Syntax_Subst.compress e  in
                                    uu____17011.FStar_Syntax_Syntax.n  in
                                  (match uu____17010 with
                                   | FStar_Syntax_Syntax.Tm_meta
                                       (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                        (m1,m2,t'))
                                       ->
                                       Prims.op_Negation
                                         (FStar_Syntax_Util.is_pure_effect m1)
                                   | uu____17026 -> false)
                               in
                            let uu____17027 =
                              let uu____17028 =
                                let uu____17035 =
                                  FStar_Syntax_Syntax.as_arg head_app  in
                                uu____17035 :: args  in
                              FStar_Util.for_some is_arg_impure uu____17028
                               in
                            if uu____17027
                            then
                              let uu____17040 =
                                let uu____17041 =
                                  FStar_Syntax_Print.term_to_string head2  in
                                FStar_Util.format1
                                  "Incompability between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                  uu____17041
                                 in
                              failwith uu____17040
                            else ());
                           (let uu____17043 = maybe_unfold_action head_app
                               in
                            match uu____17043 with
                            | (head_app1,found_action) ->
                                let mk1 tm =
                                  FStar_Syntax_Syntax.mk tm
                                    FStar_Pervasives_Native.None
                                    head2.FStar_Syntax_Syntax.pos
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
                                   (fun uu____17084  ->
                                      let uu____17085 =
                                        FStar_Syntax_Print.term_to_string
                                          head0
                                         in
                                      let uu____17086 =
                                        FStar_Syntax_Print.term_to_string
                                          body1
                                         in
                                      FStar_Util.print2
                                        "Reified (2) <%s> to %s\n"
                                        uu____17085 uu____17086);
                                 (let uu____17087 = FStar_List.tl stack  in
                                  norm cfg env uu____17087 body1)))))
                 | FStar_Syntax_Syntax.Tm_meta
                     (e,FStar_Syntax_Syntax.Meta_monadic uu____17089) ->
                     do_reify_monadic fallback cfg env stack e m t
                 | FStar_Syntax_Syntax.Tm_meta
                     (e,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,t'))
                     ->
                     let lifted =
                       let uu____17113 = closure_as_term cfg env t'  in
                       reify_lift cfg e msrc mtgt uu____17113  in
                     (log cfg
                        (fun uu____17117  ->
                           let uu____17118 =
                             FStar_Syntax_Print.term_to_string lifted  in
                           FStar_Util.print1 "Reified lift to (2): %s\n"
                             uu____17118);
                      (let uu____17119 = FStar_List.tl stack  in
                       norm cfg env uu____17119 lifted))
                 | FStar_Syntax_Syntax.Tm_meta (e,uu____17121) ->
                     do_reify_monadic fallback cfg env stack e m t
                 | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                     let branches1 =
                       FStar_All.pipe_right branches
                         (FStar_List.map
                            (fun uu____17246  ->
                               match uu____17246 with
                               | (pat,wopt,tm) ->
                                   let uu____17294 =
                                     FStar_Syntax_Util.mk_reify tm  in
                                   (pat, wopt, uu____17294)))
                        in
                     let tm =
                       mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                         head2.FStar_Syntax_Syntax.pos
                        in
                     let uu____17326 = FStar_List.tl stack  in
                     norm cfg env uu____17326 tm
                 | uu____17327 -> fallback ())

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
              (fun uu____17341  ->
                 let uu____17342 = FStar_Ident.string_of_lid msrc  in
                 let uu____17343 = FStar_Ident.string_of_lid mtgt  in
                 let uu____17344 = FStar_Syntax_Print.term_to_string e  in
                 FStar_Util.print3 "Reifying lift %s -> %s: %s\n" uu____17342
                   uu____17343 uu____17344);
            if FStar_Syntax_Util.is_pure_effect msrc
            then
              (let ed = FStar_TypeChecker_Env.get_effect_decl env mtgt  in
               let uu____17346 = ed.FStar_Syntax_Syntax.return_repr  in
               match uu____17346 with
               | (uu____17347,return_repr) ->
                   let return_inst =
                     let uu____17356 =
                       let uu____17357 =
                         FStar_Syntax_Subst.compress return_repr  in
                       uu____17357.FStar_Syntax_Syntax.n  in
                     match uu____17356 with
                     | FStar_Syntax_Syntax.Tm_uinst
                         (return_tm,uu____17363::[]) ->
                         let uu____17370 =
                           let uu____17373 =
                             let uu____17374 =
                               let uu____17381 =
                                 let uu____17384 =
                                   env.FStar_TypeChecker_Env.universe_of env
                                     t
                                    in
                                 [uu____17384]  in
                               (return_tm, uu____17381)  in
                             FStar_Syntax_Syntax.Tm_uinst uu____17374  in
                           FStar_Syntax_Syntax.mk uu____17373  in
                         uu____17370 FStar_Pervasives_Native.None
                           e.FStar_Syntax_Syntax.pos
                     | uu____17392 ->
                         failwith "NIY : Reification of indexed effects"
                      in
                   let uu____17395 =
                     let uu____17398 =
                       let uu____17399 =
                         let uu____17414 =
                           let uu____17417 = FStar_Syntax_Syntax.as_arg t  in
                           let uu____17418 =
                             let uu____17421 = FStar_Syntax_Syntax.as_arg e
                                in
                             [uu____17421]  in
                           uu____17417 :: uu____17418  in
                         (return_inst, uu____17414)  in
                       FStar_Syntax_Syntax.Tm_app uu____17399  in
                     FStar_Syntax_Syntax.mk uu____17398  in
                   uu____17395 FStar_Pervasives_Native.None
                     e.FStar_Syntax_Syntax.pos)
            else
              (let uu____17430 =
                 FStar_TypeChecker_Env.monad_leq env msrc mtgt  in
               match uu____17430 with
               | FStar_Pervasives_Native.None  ->
                   let uu____17433 =
                     FStar_Util.format2
                       "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                       (FStar_Ident.text_of_lid msrc)
                       (FStar_Ident.text_of_lid mtgt)
                      in
                   failwith uu____17433
               | FStar_Pervasives_Native.Some
                   { FStar_TypeChecker_Env.msource = uu____17434;
                     FStar_TypeChecker_Env.mtarget = uu____17435;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____17436;
                         FStar_TypeChecker_Env.mlift_term =
                           FStar_Pervasives_Native.None ;_};_}
                   ->
                   let uu____17451 =
                     FStar_Util.format2
                       "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
                       (FStar_Ident.text_of_lid msrc)
                       (FStar_Ident.text_of_lid mtgt)
                      in
                   failwith uu____17451
               | FStar_Pervasives_Native.Some
                   { FStar_TypeChecker_Env.msource = uu____17452;
                     FStar_TypeChecker_Env.mtarget = uu____17453;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____17454;
                         FStar_TypeChecker_Env.mlift_term =
                           FStar_Pervasives_Native.Some lift;_};_}
                   ->
                   let uu____17478 =
                     env.FStar_TypeChecker_Env.universe_of env t  in
                   let uu____17479 = FStar_Syntax_Util.mk_reify e  in
                   lift uu____17478 t FStar_Syntax_Syntax.tun uu____17479)

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
                (fun uu____17535  ->
                   match uu____17535 with
                   | (a,imp) ->
                       let uu____17546 = norm cfg env [] a  in
                       (uu____17546, imp))))

and (norm_comp :
  cfg -> env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp) =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        match comp.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total (t,uopt) ->
            let uu___167_17560 = comp  in
            let uu____17561 =
              let uu____17562 =
                let uu____17571 = norm cfg env [] t  in
                let uu____17572 =
                  FStar_Option.map (norm_universe cfg env) uopt  in
                (uu____17571, uu____17572)  in
              FStar_Syntax_Syntax.Total uu____17562  in
            {
              FStar_Syntax_Syntax.n = uu____17561;
              FStar_Syntax_Syntax.pos =
                (uu___167_17560.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___167_17560.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
            let uu___168_17587 = comp  in
            let uu____17588 =
              let uu____17589 =
                let uu____17598 = norm cfg env [] t  in
                let uu____17599 =
                  FStar_Option.map (norm_universe cfg env) uopt  in
                (uu____17598, uu____17599)  in
              FStar_Syntax_Syntax.GTotal uu____17589  in
            {
              FStar_Syntax_Syntax.n = uu____17588;
              FStar_Syntax_Syntax.pos =
                (uu___168_17587.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___168_17587.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let norm_args args =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____17651  ->
                      match uu____17651 with
                      | (a,i) ->
                          let uu____17662 = norm cfg env [] a  in
                          (uu____17662, i)))
               in
            let flags1 =
              FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                (FStar_List.map
                   (fun uu___86_17673  ->
                      match uu___86_17673 with
                      | FStar_Syntax_Syntax.DECREASES t ->
                          let uu____17677 = norm cfg env [] t  in
                          FStar_Syntax_Syntax.DECREASES uu____17677
                      | f -> f))
               in
            let uu___169_17681 = comp  in
            let uu____17682 =
              let uu____17683 =
                let uu___170_17684 = ct  in
                let uu____17685 =
                  FStar_List.map (norm_universe cfg env)
                    ct.FStar_Syntax_Syntax.comp_univs
                   in
                let uu____17686 =
                  norm cfg env [] ct.FStar_Syntax_Syntax.result_typ  in
                let uu____17689 =
                  norm_args ct.FStar_Syntax_Syntax.effect_args  in
                {
                  FStar_Syntax_Syntax.comp_univs = uu____17685;
                  FStar_Syntax_Syntax.effect_name =
                    (uu___170_17684.FStar_Syntax_Syntax.effect_name);
                  FStar_Syntax_Syntax.result_typ = uu____17686;
                  FStar_Syntax_Syntax.effect_args = uu____17689;
                  FStar_Syntax_Syntax.flags = flags1
                }  in
              FStar_Syntax_Syntax.Comp uu____17683  in
            {
              FStar_Syntax_Syntax.n = uu____17682;
              FStar_Syntax_Syntax.pos =
                (uu___169_17681.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___169_17681.FStar_Syntax_Syntax.vars)
            }

and (norm_binder :
  cfg -> env -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder) =
  fun cfg  ->
    fun env  ->
      fun uu____17700  ->
        match uu____17700 with
        | (x,imp) ->
            let uu____17703 =
              let uu___171_17704 = x  in
              let uu____17705 = norm cfg env [] x.FStar_Syntax_Syntax.sort
                 in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___171_17704.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___171_17704.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____17705
              }  in
            (uu____17703, imp)

and (norm_binders :
  cfg -> env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders) =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____17711 =
          FStar_List.fold_left
            (fun uu____17729  ->
               fun b  ->
                 match uu____17729 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b  in
                     ((b1 :: nbs'), (dummy :: env1))) ([], env) bs
           in
        match uu____17711 with | (nbs,uu____17769) -> FStar_List.rev nbs

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
            let uu____17785 =
              let uu___172_17786 = rc  in
              let uu____17787 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (norm cfg env [])
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___172_17786.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____17787;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___172_17786.FStar_Syntax_Syntax.residual_flags)
              }  in
            FStar_Pervasives_Native.Some uu____17785
        | uu____17794 -> lopt

and (rebuild :
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          log cfg
            (fun uu____17807  ->
               let uu____17808 = FStar_Syntax_Print.tag_of_term t  in
               let uu____17809 = FStar_Syntax_Print.term_to_string t  in
               let uu____17810 =
                 FStar_Util.string_of_int (FStar_List.length env)  in
               let uu____17817 =
                 let uu____17818 =
                   let uu____17821 = firstn (Prims.parse_int "4") stack  in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____17821
                    in
                 stack_to_string uu____17818  in
               FStar_Util.print4
                 ">>> %s\nRebuild %s with %s env elements and top of the stack %s \n"
                 uu____17808 uu____17809 uu____17810 uu____17817);
          (let t1 = maybe_simplify cfg env stack t  in
           match stack with
           | [] -> t1
           | (Debug (tm,time_then))::stack1 ->
               (if (cfg.debug).print_normalized
                then
                  (let time_now = FStar_Util.now ()  in
                   let uu____17852 =
                     let uu____17853 =
                       let uu____17854 =
                         FStar_Util.time_diff time_then time_now  in
                       FStar_Pervasives_Native.snd uu____17854  in
                     FStar_Util.string_of_int uu____17853  in
                   let uu____17859 = FStar_Syntax_Print.term_to_string tm  in
                   let uu____17860 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.print3 "Normalized (%s ms) %s\n\tto %s\n"
                     uu____17852 uu____17859 uu____17860)
                else ();
                rebuild cfg env stack1 t1)
           | (Cfg cfg1)::stack1 -> rebuild cfg1 env stack1 t1
           | (Meta (m,r))::stack1 ->
               let t2 = mk (FStar_Syntax_Syntax.Tm_meta (t1, m)) r  in
               rebuild cfg env stack1 t2
           | (MemoLazy r)::stack1 ->
               (set_memo cfg r (env, t1);
                log cfg
                  (fun uu____17914  ->
                     let uu____17915 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 "\tSet memo %s\n" uu____17915);
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
               let uu____17951 =
                 let uu___173_17952 = FStar_Syntax_Util.abs bs1 t1 lopt1  in
                 {
                   FStar_Syntax_Syntax.n =
                     (uu___173_17952.FStar_Syntax_Syntax.n);
                   FStar_Syntax_Syntax.pos = r;
                   FStar_Syntax_Syntax.vars =
                     (uu___173_17952.FStar_Syntax_Syntax.vars)
                 }  in
               rebuild cfg env stack1 uu____17951
           | (Arg (Univ uu____17953,uu____17954,uu____17955))::uu____17956 ->
               failwith "Impossible"
           | (Arg (Dummy ,uu____17959,uu____17960))::uu____17961 ->
               failwith "Impossible"
           | (UnivArgs (us,r))::stack1 ->
               let t2 = FStar_Syntax_Syntax.mk_Tm_uinst t1 us  in
               rebuild cfg env stack1 t2
           | (Arg (Clos (env_arg,tm,m,uu____17977),aq,r))::stack1 ->
               (log cfg
                  (fun uu____18030  ->
                     let uu____18031 = FStar_Syntax_Print.term_to_string tm
                        in
                     FStar_Util.print1 "Rebuilding with arg %s\n" uu____18031);
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
                  (let uu____18041 = FStar_ST.op_Bang m  in
                   match uu____18041 with
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
                   | FStar_Pervasives_Native.Some (uu____18178,a) ->
                       let t2 =
                         FStar_Syntax_Syntax.extend_app t1 (a, aq)
                           FStar_Pervasives_Native.None r
                          in
                       rebuild cfg env_arg stack1 t2))
           | (App (env1,head1,aq,r))::stack' when should_reify cfg stack ->
               let t0 = t1  in
               let fallback msg uu____18225 =
                 log cfg
                   (fun uu____18229  ->
                      let uu____18230 = FStar_Syntax_Print.term_to_string t1
                         in
                      FStar_Util.print2 "Not reifying%s: %s\n" msg
                        uu____18230);
                 (let t2 =
                    FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                      FStar_Pervasives_Native.None r
                     in
                  rebuild cfg env1 stack' t2)
                  in
               let uu____18234 =
                 let uu____18235 = FStar_Syntax_Subst.compress t1  in
                 uu____18235.FStar_Syntax_Syntax.n  in
               (match uu____18234 with
                | FStar_Syntax_Syntax.Tm_meta
                    (t2,FStar_Syntax_Syntax.Meta_monadic (m,ty)) ->
                    do_reify_monadic (fallback " (1)") cfg env1 stack t2 m ty
                | FStar_Syntax_Syntax.Tm_meta
                    (t2,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,ty))
                    ->
                    let lifted =
                      let uu____18262 = closure_as_term cfg env1 ty  in
                      reify_lift cfg t2 msrc mtgt uu____18262  in
                    (log cfg
                       (fun uu____18266  ->
                          let uu____18267 =
                            FStar_Syntax_Print.term_to_string lifted  in
                          FStar_Util.print1 "Reified lift to (1): %s\n"
                            uu____18267);
                     (let uu____18268 = FStar_List.tl stack  in
                      norm cfg env1 uu____18268 lifted))
                | FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reflect uu____18269);
                       FStar_Syntax_Syntax.pos = uu____18270;
                       FStar_Syntax_Syntax.vars = uu____18271;_},(e,uu____18273)::[])
                    -> norm cfg env1 stack' e
                | uu____18302 -> fallback " (2)" ())
           | (App (env1,head1,aq,r))::stack1 ->
               let t2 =
                 FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                   FStar_Pervasives_Native.None r
                  in
               rebuild cfg env1 stack1 t2
           | (Match (env1,branches,r))::stack1 ->
               (log cfg
                  (fun uu____18322  ->
                     let uu____18323 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1
                       "Rebuilding with match, scrutinee is %s ...\n"
                       uu____18323);
                (let scrutinee = t1  in
                 let norm_and_rebuild_match uu____18328 =
                   log cfg
                     (fun uu____18333  ->
                        let uu____18334 =
                          FStar_Syntax_Print.term_to_string scrutinee  in
                        let uu____18335 =
                          let uu____18336 =
                            FStar_All.pipe_right branches
                              (FStar_List.map
                                 (fun uu____18353  ->
                                    match uu____18353 with
                                    | (p,uu____18363,uu____18364) ->
                                        FStar_Syntax_Print.pat_to_string p))
                             in
                          FStar_All.pipe_right uu____18336
                            (FStar_String.concat "\n\t")
                           in
                        FStar_Util.print2
                          "match is irreducible: scrutinee=%s\nbranches=%s\n"
                          uu____18334 uu____18335);
                   (let whnf = (cfg.steps).weak || (cfg.steps).hnf  in
                    let cfg_exclude_iota_zeta =
                      let new_delta =
                        FStar_All.pipe_right cfg.delta_level
                          (FStar_List.filter
                             (fun uu___87_18381  ->
                                match uu___87_18381 with
                                | FStar_TypeChecker_Env.Inlining  -> true
                                | FStar_TypeChecker_Env.Eager_unfolding_only 
                                    -> true
                                | uu____18382 -> false))
                         in
                      let uu___174_18383 = cfg  in
                      {
                        steps =
                          (let uu___175_18386 = cfg.steps  in
                           {
                             beta = (uu___175_18386.beta);
                             iota = (uu___175_18386.iota);
                             zeta = false;
                             weak = (uu___175_18386.weak);
                             hnf = (uu___175_18386.hnf);
                             primops = (uu___175_18386.primops);
                             eager_unfolding =
                               (uu___175_18386.eager_unfolding);
                             inlining = (uu___175_18386.inlining);
                             no_delta_steps = (uu___175_18386.no_delta_steps);
                             unfold_until = (uu___175_18386.unfold_until);
                             unfold_only = (uu___175_18386.unfold_only);
                             unfold_attr = (uu___175_18386.unfold_attr);
                             unfold_tac = (uu___175_18386.unfold_tac);
                             pure_subterms_within_computations =
                               (uu___175_18386.pure_subterms_within_computations);
                             simplify = (uu___175_18386.simplify);
                             erase_universes =
                               (uu___175_18386.erase_universes);
                             allow_unbound_universes =
                               (uu___175_18386.allow_unbound_universes);
                             reify_ = (uu___175_18386.reify_);
                             compress_uvars = (uu___175_18386.compress_uvars);
                             no_full_norm = (uu___175_18386.no_full_norm);
                             check_no_uvars = (uu___175_18386.check_no_uvars);
                             unmeta = (uu___175_18386.unmeta);
                             unascribe = (uu___175_18386.unascribe)
                           });
                        tcenv = (uu___174_18383.tcenv);
                        debug = (uu___174_18383.debug);
                        delta_level = new_delta;
                        primitive_steps = (uu___174_18383.primitive_steps);
                        strong = true;
                        memoize_lazy = (uu___174_18383.memoize_lazy);
                        normalize_pure_lets =
                          (uu___174_18383.normalize_pure_lets)
                      }  in
                    let norm_or_whnf env2 t2 =
                      if whnf
                      then closure_as_term cfg_exclude_iota_zeta env2 t2
                      else norm cfg_exclude_iota_zeta env2 [] t2  in
                    let rec norm_pat env2 p =
                      match p.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_constant uu____18418 ->
                          (p, env2)
                      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                          let uu____18439 =
                            FStar_All.pipe_right pats
                              (FStar_List.fold_left
                                 (fun uu____18499  ->
                                    fun uu____18500  ->
                                      match (uu____18499, uu____18500) with
                                      | ((pats1,env3),(p1,b)) ->
                                          let uu____18591 = norm_pat env3 p1
                                             in
                                          (match uu____18591 with
                                           | (p2,env4) ->
                                               (((p2, b) :: pats1), env4)))
                                 ([], env2))
                             in
                          (match uu____18439 with
                           | (pats1,env3) ->
                               ((let uu___176_18673 = p  in
                                 {
                                   FStar_Syntax_Syntax.v =
                                     (FStar_Syntax_Syntax.Pat_cons
                                        (fv, (FStar_List.rev pats1)));
                                   FStar_Syntax_Syntax.p =
                                     (uu___176_18673.FStar_Syntax_Syntax.p)
                                 }), env3))
                      | FStar_Syntax_Syntax.Pat_var x ->
                          let x1 =
                            let uu___177_18692 = x  in
                            let uu____18693 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___177_18692.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___177_18692.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____18693
                            }  in
                          ((let uu___178_18707 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_var x1);
                              FStar_Syntax_Syntax.p =
                                (uu___178_18707.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_wild x ->
                          let x1 =
                            let uu___179_18718 = x  in
                            let uu____18719 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___179_18718.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___179_18718.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____18719
                            }  in
                          ((let uu___180_18733 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_wild x1);
                              FStar_Syntax_Syntax.p =
                                (uu___180_18733.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                          let x1 =
                            let uu___181_18749 = x  in
                            let uu____18750 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___181_18749.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___181_18749.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____18750
                            }  in
                          let t3 = norm_or_whnf env2 t2  in
                          ((let uu___182_18757 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_dot_term (x1, t3));
                              FStar_Syntax_Syntax.p =
                                (uu___182_18757.FStar_Syntax_Syntax.p)
                            }), env2)
                       in
                    let branches1 =
                      match env1 with
                      | [] when whnf -> branches
                      | uu____18767 ->
                          FStar_All.pipe_right branches
                            (FStar_List.map
                               (fun branch1  ->
                                  let uu____18781 =
                                    FStar_Syntax_Subst.open_branch branch1
                                     in
                                  match uu____18781 with
                                  | (p,wopt,e) ->
                                      let uu____18801 = norm_pat env1 p  in
                                      (match uu____18801 with
                                       | (p1,env2) ->
                                           let wopt1 =
                                             match wopt with
                                             | FStar_Pervasives_Native.None 
                                                 ->
                                                 FStar_Pervasives_Native.None
                                             | FStar_Pervasives_Native.Some w
                                                 ->
                                                 let uu____18826 =
                                                   norm_or_whnf env2 w  in
                                                 FStar_Pervasives_Native.Some
                                                   uu____18826
                                              in
                                           let e1 = norm_or_whnf env2 e  in
                                           FStar_Syntax_Util.branch
                                             (p1, wopt1, e1))))
                       in
                    let uu____18832 =
                      mk
                        (FStar_Syntax_Syntax.Tm_match (scrutinee, branches1))
                        r
                       in
                    rebuild cfg env1 stack1 uu____18832)
                    in
                 let rec is_cons head1 =
                   match head1.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_uinst (h,uu____18842) ->
                       is_cons h
                   | FStar_Syntax_Syntax.Tm_constant uu____18847 -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____18848;
                         FStar_Syntax_Syntax.fv_delta = uu____18849;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Data_ctor );_}
                       -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____18850;
                         FStar_Syntax_Syntax.fv_delta = uu____18851;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Record_ctor uu____18852);_}
                       -> true
                   | uu____18859 -> false  in
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
                   let uu____19004 =
                     FStar_Syntax_Util.head_and_args scrutinee1  in
                   match uu____19004 with
                   | (head1,args) ->
                       (match p.FStar_Syntax_Syntax.v with
                        | FStar_Syntax_Syntax.Pat_var bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_wild bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_dot_term uu____19091 ->
                            FStar_Util.Inl []
                        | FStar_Syntax_Syntax.Pat_constant s ->
                            (match scrutinee1.FStar_Syntax_Syntax.n with
                             | FStar_Syntax_Syntax.Tm_constant s' when
                                 FStar_Const.eq_const s s' ->
                                 FStar_Util.Inl []
                             | uu____19130 ->
                                 let uu____19131 =
                                   let uu____19132 = is_cons head1  in
                                   Prims.op_Negation uu____19132  in
                                 FStar_Util.Inr uu____19131)
                        | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                            let uu____19157 =
                              let uu____19158 =
                                FStar_Syntax_Util.un_uinst head1  in
                              uu____19158.FStar_Syntax_Syntax.n  in
                            (match uu____19157 with
                             | FStar_Syntax_Syntax.Tm_fvar fv' when
                                 FStar_Syntax_Syntax.fv_eq fv fv' ->
                                 matches_args [] args arg_pats
                             | uu____19176 ->
                                 let uu____19177 =
                                   let uu____19178 = is_cons head1  in
                                   Prims.op_Negation uu____19178  in
                                 FStar_Util.Inr uu____19177))
                 
                 and matches_args out a p =
                   match (a, p) with
                   | ([],[]) -> FStar_Util.Inl out
                   | ((t2,uu____19247)::rest_a,(p1,uu____19250)::rest_p) ->
                       let uu____19294 = matches_pat t2 p1  in
                       (match uu____19294 with
                        | FStar_Util.Inl s ->
                            matches_args (FStar_List.append out s) rest_a
                              rest_p
                        | m -> m)
                   | uu____19343 -> FStar_Util.Inr false
                  in
                 let rec matches scrutinee1 p =
                   match p with
                   | [] -> norm_and_rebuild_match ()
                   | (p1,wopt,b)::rest ->
                       let uu____19449 = matches_pat scrutinee1 p1  in
                       (match uu____19449 with
                        | FStar_Util.Inr (false ) -> matches scrutinee1 rest
                        | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                        | FStar_Util.Inl s ->
                            (log cfg
                               (fun uu____19489  ->
                                  let uu____19490 =
                                    FStar_Syntax_Print.pat_to_string p1  in
                                  let uu____19491 =
                                    let uu____19492 =
                                      FStar_List.map
                                        (fun uu____19502  ->
                                           match uu____19502 with
                                           | (uu____19507,t2) ->
                                               FStar_Syntax_Print.term_to_string
                                                 t2) s
                                       in
                                    FStar_All.pipe_right uu____19492
                                      (FStar_String.concat "; ")
                                     in
                                  FStar_Util.print2
                                    "Matches pattern %s with subst = %s\n"
                                    uu____19490 uu____19491);
                             (let env2 =
                                FStar_List.fold_left
                                  (fun env2  ->
                                     fun uu____19538  ->
                                       match uu____19538 with
                                       | (bv,t2) ->
                                           let uu____19561 =
                                             let uu____19568 =
                                               let uu____19571 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   bv
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 uu____19571
                                                in
                                             let uu____19572 =
                                               let uu____19573 =
                                                 let uu____19604 =
                                                   FStar_Util.mk_ref
                                                     (FStar_Pervasives_Native.Some
                                                        ([], t2))
                                                    in
                                                 ([], t2, uu____19604, false)
                                                  in
                                               Clos uu____19573  in
                                             (uu____19568, uu____19572)  in
                                           uu____19561 :: env2) env1 s
                                 in
                              let uu____19721 = guard_when_clause wopt b rest
                                 in
                              norm cfg env2 stack1 uu____19721)))
                    in
                 if Prims.op_Negation (cfg.steps).iota
                 then norm_and_rebuild_match ()
                 else matches scrutinee branches)))

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
               (fun uu___88_19749  ->
                  match uu___88_19749 with
                  | UnfoldUntil k -> [FStar_TypeChecker_Env.Unfold k]
                  | Eager_unfolding  ->
                      [FStar_TypeChecker_Env.Eager_unfolding_only]
                  | Inlining  -> [FStar_TypeChecker_Env.Inlining]
                  | UnfoldTac  -> [FStar_TypeChecker_Env.UnfoldTac]
                  | uu____19753 -> []))
           in
        let d1 =
          match d with
          | [] -> [FStar_TypeChecker_Env.NoDelta]
          | uu____19759 -> d  in
        let uu____19762 = to_fsteps s  in
        let uu____19763 =
          let uu____19764 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Norm")  in
          let uu____19765 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Primops")  in
          let uu____19766 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "380")  in
          let uu____19767 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "NormDelayed")
             in
          let uu____19768 =
            FStar_TypeChecker_Env.debug e
              (FStar_Options.Other "print_normalized_terms")
             in
          {
            gen = uu____19764;
            primop = uu____19765;
            b380 = uu____19766;
            norm_delayed = uu____19767;
            print_normalized = uu____19768
          }  in
        let uu____19769 = add_steps built_in_primitive_steps psteps  in
        let uu____19772 =
          (FStar_Options.normalize_pure_terms_for_extraction ()) ||
            (let uu____19774 =
               FStar_All.pipe_right s
                 (FStar_List.contains PureSubtermsWithinComputations)
                in
             Prims.op_Negation uu____19774)
           in
        {
          steps = uu____19762;
          tcenv = e;
          debug = uu____19763;
          delta_level = d1;
          primitive_steps = uu____19769;
          strong = false;
          memoize_lazy = true;
          normalize_pure_lets = uu____19772
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
      fun t  -> let uu____19832 = config s e  in norm_comp uu____19832 [] t
  
let (normalize_universe :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun u  ->
      let uu____19845 = config [] env  in norm_universe uu____19845 [] u
  
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
        let uu____19863 = norm cfg [] [] t  in
        FStar_Syntax_Util.non_informative uu____19863  in
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____19870 -> c
      | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
          let uu___183_19889 = c  in
          {
            FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
            FStar_Syntax_Syntax.pos =
              (uu___183_19889.FStar_Syntax_Syntax.pos);
            FStar_Syntax_Syntax.vars =
              (uu___183_19889.FStar_Syntax_Syntax.vars)
          }
      | FStar_Syntax_Syntax.Comp ct ->
          let l =
            FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
              ct.FStar_Syntax_Syntax.effect_name
             in
          let uu____19896 =
            (FStar_Syntax_Util.is_ghost_effect l) &&
              (non_info ct.FStar_Syntax_Syntax.result_typ)
             in
          if uu____19896
          then
            let ct1 =
              match downgrade_ghost_effect_name
                      ct.FStar_Syntax_Syntax.effect_name
              with
              | FStar_Pervasives_Native.Some pure_eff ->
                  let flags1 =
                    if
                      FStar_Ident.lid_equals pure_eff
                        FStar_Parser_Const.effect_Tot_lid
                    then FStar_Syntax_Syntax.TOTAL ::
                      (ct.FStar_Syntax_Syntax.flags)
                    else ct.FStar_Syntax_Syntax.flags  in
                  let uu___184_19905 = ct  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___184_19905.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name = pure_eff;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___184_19905.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___184_19905.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags = flags1
                  }
              | FStar_Pervasives_Native.None  ->
                  let ct1 =
                    FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c
                     in
                  let uu___185_19907 = ct1  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___185_19907.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name =
                      FStar_Parser_Const.effect_PURE_lid;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___185_19907.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___185_19907.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags =
                      (uu___185_19907.FStar_Syntax_Syntax.flags)
                  }
               in
            let uu___186_19908 = c  in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
              FStar_Syntax_Syntax.pos =
                (uu___186_19908.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___186_19908.FStar_Syntax_Syntax.vars)
            }
          else c
      | uu____19910 -> c
  
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
        let uu____19922 = norm cfg [] [] t  in
        FStar_Syntax_Util.non_informative uu____19922  in
      let uu____19929 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ)
         in
      if uu____19929
      then
        match downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name
        with
        | FStar_Pervasives_Native.Some pure_eff ->
            FStar_Syntax_Syntax.mk_lcomp pure_eff
              lc.FStar_Syntax_Syntax.res_typ lc.FStar_Syntax_Syntax.cflags
              (fun uu____19933  ->
                 let uu____19934 = FStar_Syntax_Syntax.lcomp_comp lc  in
                 ghost_to_pure env uu____19934)
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
            ((let uu____19951 =
                let uu____19956 =
                  let uu____19957 = FStar_Util.message_of_exn e  in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____19957
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____19956)  in
              FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____19951);
             t)
         in
      FStar_Syntax_Print.term_to_string t1
  
let (comp_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string) =
  fun env  ->
    fun c  ->
      let c1 =
        try
          let uu____19968 = config [AllowUnboundUniverses] env  in
          norm_comp uu____19968 [] c
        with
        | e ->
            ((let uu____19981 =
                let uu____19986 =
                  let uu____19987 = FStar_Util.message_of_exn e  in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____19987
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____19986)  in
              FStar_Errors.log_issue c.FStar_Syntax_Syntax.pos uu____19981);
             c)
         in
      FStar_Syntax_Print.comp_to_string c1
  
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
                   let uu____20024 =
                     let uu____20025 =
                       let uu____20032 = FStar_Syntax_Util.mk_conj phi1 phi
                          in
                       (y, uu____20032)  in
                     FStar_Syntax_Syntax.Tm_refine uu____20025  in
                   mk uu____20024 t01.FStar_Syntax_Syntax.pos
               | uu____20037 -> t2)
          | uu____20038 -> t2  in
        aux t
  
let (unfold_whnf :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      normalize
        [Weak; HNF; UnfoldUntil FStar_Syntax_Syntax.Delta_constant; Beta] env
        t
  
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
             NoDeltaSteps;
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
        let uu____20078 = FStar_Syntax_Util.arrow_formals_comp t_e  in
        match uu____20078 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____20107 ->
                 let uu____20114 = FStar_Syntax_Util.abs_formals e  in
                 (match uu____20114 with
                  | (actuals,uu____20124,uu____20125) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____20139 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders
                            in
                         match uu____20139 with
                         | (binders,args) ->
                             let uu____20156 =
                               FStar_Syntax_Syntax.mk_Tm_app e args
                                 FStar_Pervasives_Native.None
                                 e.FStar_Syntax_Syntax.pos
                                in
                             FStar_Syntax_Util.abs binders uu____20156
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
      | uu____20164 ->
          let uu____20165 = FStar_Syntax_Util.head_and_args t  in
          (match uu____20165 with
           | (head1,args) ->
               let uu____20202 =
                 let uu____20203 = FStar_Syntax_Subst.compress head1  in
                 uu____20203.FStar_Syntax_Syntax.n  in
               (match uu____20202 with
                | FStar_Syntax_Syntax.Tm_uvar (uu____20206,thead) ->
                    let uu____20232 = FStar_Syntax_Util.arrow_formals thead
                       in
                    (match uu____20232 with
                     | (formals,tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____20274 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___191_20282 = env  in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___191_20282.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___191_20282.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___191_20282.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___191_20282.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___191_20282.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___191_20282.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___191_20282.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___191_20282.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___191_20282.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___191_20282.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___191_20282.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___191_20282.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___191_20282.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___191_20282.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___191_20282.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___191_20282.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___191_20282.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___191_20282.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___191_20282.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___191_20282.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___191_20282.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___191_20282.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___191_20282.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___191_20282.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___191_20282.FStar_TypeChecker_Env.qname_and_index);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___191_20282.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth =
                                     (uu___191_20282.FStar_TypeChecker_Env.synth);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___191_20282.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___191_20282.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___191_20282.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___191_20282.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.dep_graph =
                                     (uu___191_20282.FStar_TypeChecker_Env.dep_graph)
                                 }) t
                               in
                            match uu____20274 with
                            | (uu____20283,ty,uu____20285) ->
                                eta_expand_with_type env t ty))
                | uu____20286 ->
                    let uu____20287 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___192_20295 = env  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___192_20295.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___192_20295.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___192_20295.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___192_20295.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___192_20295.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___192_20295.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___192_20295.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___192_20295.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___192_20295.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___192_20295.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___192_20295.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___192_20295.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___192_20295.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___192_20295.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___192_20295.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___192_20295.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___192_20295.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___192_20295.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.failhard =
                             (uu___192_20295.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___192_20295.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___192_20295.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___192_20295.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___192_20295.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___192_20295.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qname_and_index =
                             (uu___192_20295.FStar_TypeChecker_Env.qname_and_index);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___192_20295.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth =
                             (uu___192_20295.FStar_TypeChecker_Env.synth);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___192_20295.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___192_20295.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___192_20295.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___192_20295.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.dep_graph =
                             (uu___192_20295.FStar_TypeChecker_Env.dep_graph)
                         }) t
                       in
                    (match uu____20287 with
                     | (uu____20296,ty,uu____20298) ->
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
      let uu___193_20355 = x  in
      let uu____20356 = elim_delayed_subst_term x.FStar_Syntax_Syntax.sort
         in
      {
        FStar_Syntax_Syntax.ppname =
          (uu___193_20355.FStar_Syntax_Syntax.ppname);
        FStar_Syntax_Syntax.index =
          (uu___193_20355.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = uu____20356
      }  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____20359 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_bvar uu____20384 -> t1
    | FStar_Syntax_Syntax.Tm_name uu____20385 -> t1
    | FStar_Syntax_Syntax.Tm_fvar uu____20386 -> t1
    | FStar_Syntax_Syntax.Tm_uinst uu____20387 -> t1
    | FStar_Syntax_Syntax.Tm_constant uu____20394 -> t1
    | FStar_Syntax_Syntax.Tm_type uu____20395 -> t1
    | FStar_Syntax_Syntax.Tm_unknown  -> t1
    | FStar_Syntax_Syntax.Tm_abs (bs,t2,rc_opt) ->
        let elim_rc rc =
          let uu___194_20423 = rc  in
          let uu____20424 =
            FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
              elim_delayed_subst_term
             in
          let uu____20431 =
            elim_delayed_subst_cflags rc.FStar_Syntax_Syntax.residual_flags
             in
          {
            FStar_Syntax_Syntax.residual_effect =
              (uu___194_20423.FStar_Syntax_Syntax.residual_effect);
            FStar_Syntax_Syntax.residual_typ = uu____20424;
            FStar_Syntax_Syntax.residual_flags = uu____20431
          }  in
        let uu____20434 =
          let uu____20435 =
            let uu____20452 = elim_delayed_subst_binders bs  in
            let uu____20459 = elim_delayed_subst_term t2  in
            let uu____20460 = FStar_Util.map_opt rc_opt elim_rc  in
            (uu____20452, uu____20459, uu____20460)  in
          FStar_Syntax_Syntax.Tm_abs uu____20435  in
        mk1 uu____20434
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____20489 =
          let uu____20490 =
            let uu____20503 = elim_delayed_subst_binders bs  in
            let uu____20510 = elim_delayed_subst_comp c  in
            (uu____20503, uu____20510)  in
          FStar_Syntax_Syntax.Tm_arrow uu____20490  in
        mk1 uu____20489
    | FStar_Syntax_Syntax.Tm_refine (bv,phi) ->
        let uu____20523 =
          let uu____20524 =
            let uu____20531 = elim_bv bv  in
            let uu____20532 = elim_delayed_subst_term phi  in
            (uu____20531, uu____20532)  in
          FStar_Syntax_Syntax.Tm_refine uu____20524  in
        mk1 uu____20523
    | FStar_Syntax_Syntax.Tm_app (t2,args) ->
        let uu____20555 =
          let uu____20556 =
            let uu____20571 = elim_delayed_subst_term t2  in
            let uu____20572 = elim_delayed_subst_args args  in
            (uu____20571, uu____20572)  in
          FStar_Syntax_Syntax.Tm_app uu____20556  in
        mk1 uu____20555
    | FStar_Syntax_Syntax.Tm_match (t2,branches) ->
        let rec elim_pat p =
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_var x ->
              let uu___195_20636 = p  in
              let uu____20637 =
                let uu____20638 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_var uu____20638  in
              {
                FStar_Syntax_Syntax.v = uu____20637;
                FStar_Syntax_Syntax.p =
                  (uu___195_20636.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_wild x ->
              let uu___196_20640 = p  in
              let uu____20641 =
                let uu____20642 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_wild uu____20642  in
              {
                FStar_Syntax_Syntax.v = uu____20641;
                FStar_Syntax_Syntax.p =
                  (uu___196_20640.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
              let uu___197_20649 = p  in
              let uu____20650 =
                let uu____20651 =
                  let uu____20658 = elim_bv x  in
                  let uu____20659 = elim_delayed_subst_term t0  in
                  (uu____20658, uu____20659)  in
                FStar_Syntax_Syntax.Pat_dot_term uu____20651  in
              {
                FStar_Syntax_Syntax.v = uu____20650;
                FStar_Syntax_Syntax.p =
                  (uu___197_20649.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
              let uu___198_20678 = p  in
              let uu____20679 =
                let uu____20680 =
                  let uu____20693 =
                    FStar_List.map
                      (fun uu____20716  ->
                         match uu____20716 with
                         | (x,b) ->
                             let uu____20729 = elim_pat x  in
                             (uu____20729, b)) pats
                     in
                  (fv, uu____20693)  in
                FStar_Syntax_Syntax.Pat_cons uu____20680  in
              {
                FStar_Syntax_Syntax.v = uu____20679;
                FStar_Syntax_Syntax.p =
                  (uu___198_20678.FStar_Syntax_Syntax.p)
              }
          | uu____20742 -> p  in
        let elim_branch uu____20764 =
          match uu____20764 with
          | (pat,wopt,t3) ->
              let uu____20790 = elim_pat pat  in
              let uu____20793 =
                FStar_Util.map_opt wopt elim_delayed_subst_term  in
              let uu____20796 = elim_delayed_subst_term t3  in
              (uu____20790, uu____20793, uu____20796)
           in
        let uu____20801 =
          let uu____20802 =
            let uu____20825 = elim_delayed_subst_term t2  in
            let uu____20826 = FStar_List.map elim_branch branches  in
            (uu____20825, uu____20826)  in
          FStar_Syntax_Syntax.Tm_match uu____20802  in
        mk1 uu____20801
    | FStar_Syntax_Syntax.Tm_ascribed (t2,a,lopt) ->
        let elim_ascription uu____20935 =
          match uu____20935 with
          | (tc,topt) ->
              let uu____20970 =
                match tc with
                | FStar_Util.Inl t3 ->
                    let uu____20980 = elim_delayed_subst_term t3  in
                    FStar_Util.Inl uu____20980
                | FStar_Util.Inr c ->
                    let uu____20982 = elim_delayed_subst_comp c  in
                    FStar_Util.Inr uu____20982
                 in
              let uu____20983 =
                FStar_Util.map_opt topt elim_delayed_subst_term  in
              (uu____20970, uu____20983)
           in
        let uu____20992 =
          let uu____20993 =
            let uu____21020 = elim_delayed_subst_term t2  in
            let uu____21021 = elim_ascription a  in
            (uu____21020, uu____21021, lopt)  in
          FStar_Syntax_Syntax.Tm_ascribed uu____20993  in
        mk1 uu____20992
    | FStar_Syntax_Syntax.Tm_let (lbs,t2) ->
        let elim_lb lb =
          let uu___199_21066 = lb  in
          let uu____21067 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbtyp  in
          let uu____21070 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbdef  in
          {
            FStar_Syntax_Syntax.lbname =
              (uu___199_21066.FStar_Syntax_Syntax.lbname);
            FStar_Syntax_Syntax.lbunivs =
              (uu___199_21066.FStar_Syntax_Syntax.lbunivs);
            FStar_Syntax_Syntax.lbtyp = uu____21067;
            FStar_Syntax_Syntax.lbeff =
              (uu___199_21066.FStar_Syntax_Syntax.lbeff);
            FStar_Syntax_Syntax.lbdef = uu____21070;
            FStar_Syntax_Syntax.lbattrs =
              (uu___199_21066.FStar_Syntax_Syntax.lbattrs)
          }  in
        let uu____21073 =
          let uu____21074 =
            let uu____21087 =
              let uu____21094 =
                FStar_List.map elim_lb (FStar_Pervasives_Native.snd lbs)  in
              ((FStar_Pervasives_Native.fst lbs), uu____21094)  in
            let uu____21103 = elim_delayed_subst_term t2  in
            (uu____21087, uu____21103)  in
          FStar_Syntax_Syntax.Tm_let uu____21074  in
        mk1 uu____21073
    | FStar_Syntax_Syntax.Tm_uvar (uv,t2) ->
        let uu____21136 =
          let uu____21137 =
            let uu____21154 = elim_delayed_subst_term t2  in
            (uv, uu____21154)  in
          FStar_Syntax_Syntax.Tm_uvar uu____21137  in
        mk1 uu____21136
    | FStar_Syntax_Syntax.Tm_meta (t2,md) ->
        let uu____21171 =
          let uu____21172 =
            let uu____21179 = elim_delayed_subst_term t2  in
            let uu____21180 = elim_delayed_subst_meta md  in
            (uu____21179, uu____21180)  in
          FStar_Syntax_Syntax.Tm_meta uu____21172  in
        mk1 uu____21171

and (elim_delayed_subst_cflags :
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun flags1  ->
    FStar_List.map
      (fun uu___89_21187  ->
         match uu___89_21187 with
         | FStar_Syntax_Syntax.DECREASES t ->
             let uu____21191 = elim_delayed_subst_term t  in
             FStar_Syntax_Syntax.DECREASES uu____21191
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
        let uu____21212 =
          let uu____21213 =
            let uu____21222 = elim_delayed_subst_term t  in
            (uu____21222, uopt)  in
          FStar_Syntax_Syntax.Total uu____21213  in
        mk1 uu____21212
    | FStar_Syntax_Syntax.GTotal (t,uopt) ->
        let uu____21235 =
          let uu____21236 =
            let uu____21245 = elim_delayed_subst_term t  in
            (uu____21245, uopt)  in
          FStar_Syntax_Syntax.GTotal uu____21236  in
        mk1 uu____21235
    | FStar_Syntax_Syntax.Comp ct ->
        let ct1 =
          let uu___200_21250 = ct  in
          let uu____21251 =
            elim_delayed_subst_term ct.FStar_Syntax_Syntax.result_typ  in
          let uu____21254 =
            elim_delayed_subst_args ct.FStar_Syntax_Syntax.effect_args  in
          let uu____21263 =
            elim_delayed_subst_cflags ct.FStar_Syntax_Syntax.flags  in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___200_21250.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___200_21250.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ = uu____21251;
            FStar_Syntax_Syntax.effect_args = uu____21254;
            FStar_Syntax_Syntax.flags = uu____21263
          }  in
        mk1 (FStar_Syntax_Syntax.Comp ct1)

and (elim_delayed_subst_meta :
  FStar_Syntax_Syntax.metadata -> FStar_Syntax_Syntax.metadata) =
  fun uu___90_21266  ->
    match uu___90_21266 with
    | FStar_Syntax_Syntax.Meta_pattern args ->
        let uu____21278 = FStar_List.map elim_delayed_subst_args args  in
        FStar_Syntax_Syntax.Meta_pattern uu____21278
    | FStar_Syntax_Syntax.Meta_monadic (m,t) ->
        let uu____21311 =
          let uu____21318 = elim_delayed_subst_term t  in (m, uu____21318)
           in
        FStar_Syntax_Syntax.Meta_monadic uu____21311
    | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,t) ->
        let uu____21326 =
          let uu____21335 = elim_delayed_subst_term t  in
          (m1, m2, uu____21335)  in
        FStar_Syntax_Syntax.Meta_monadic_lift uu____21326
    | FStar_Syntax_Syntax.Meta_alien (d,s,t) ->
        let uu____21343 =
          let uu____21352 = elim_delayed_subst_term t  in (d, s, uu____21352)
           in
        FStar_Syntax_Syntax.Meta_alien uu____21343
    | m -> m

and (elim_delayed_subst_args :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun args  ->
    FStar_List.map
      (fun uu____21375  ->
         match uu____21375 with
         | (t,q) ->
             let uu____21386 = elim_delayed_subst_term t  in (uu____21386, q))
      args

and (elim_delayed_subst_binders :
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun bs  ->
    FStar_List.map
      (fun uu____21406  ->
         match uu____21406 with
         | (x,q) ->
             let uu____21417 =
               let uu___201_21418 = x  in
               let uu____21419 =
                 elim_delayed_subst_term x.FStar_Syntax_Syntax.sort  in
               {
                 FStar_Syntax_Syntax.ppname =
                   (uu___201_21418.FStar_Syntax_Syntax.ppname);
                 FStar_Syntax_Syntax.index =
                   (uu___201_21418.FStar_Syntax_Syntax.index);
                 FStar_Syntax_Syntax.sort = uu____21419
               }  in
             (uu____21417, q)) bs

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
            | (uu____21495,FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c))
                  FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
            | (uu____21501,FStar_Util.Inl t) ->
                let uu____21507 =
                  let uu____21510 =
                    let uu____21511 =
                      let uu____21524 = FStar_Syntax_Syntax.mk_Total t  in
                      (binders, uu____21524)  in
                    FStar_Syntax_Syntax.Tm_arrow uu____21511  in
                  FStar_Syntax_Syntax.mk uu____21510  in
                uu____21507 FStar_Pervasives_Native.None
                  t.FStar_Syntax_Syntax.pos
             in
          let uu____21528 = FStar_Syntax_Subst.open_univ_vars univ_names t
             in
          match uu____21528 with
          | (univ_names1,t1) ->
              let t2 = remove_uvar_solutions env t1  in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2  in
              let t4 = elim_delayed_subst_term t3  in
              let uu____21556 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t4))
                | uu____21611 ->
                    let uu____21612 =
                      let uu____21621 =
                        let uu____21622 = FStar_Syntax_Subst.compress t4  in
                        uu____21622.FStar_Syntax_Syntax.n  in
                      (uu____21621, tc)  in
                    (match uu____21612 with
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inr uu____21647) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inl uu____21684) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____21723,FStar_Util.Inl uu____21724) ->
                         ([], (FStar_Util.Inl t4))
                     | uu____21747 -> failwith "Impossible")
                 in
              (match uu____21556 with
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
          let uu____21852 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl t)  in
          match uu____21852 with
          | (univ_names1,binders1,tc) ->
              let uu____21910 = FStar_Util.left tc  in
              (univ_names1, binders1, uu____21910)
  
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
          let uu____21945 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr c)  in
          match uu____21945 with
          | (univ_names1,binders1,tc) ->
              let uu____22005 = FStar_Util.right tc  in
              (univ_names1, binders1, uu____22005)
  
let rec (elim_uvars :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt)
  =
  fun env  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univ_names,binders,typ,lids,lids') ->
          let uu____22038 = elim_uvars_aux_t env univ_names binders typ  in
          (match uu____22038 with
           | (univ_names1,binders1,typ1) ->
               let uu___202_22066 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___202_22066.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___202_22066.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___202_22066.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___202_22066.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
          let uu___203_22087 = s  in
          let uu____22088 =
            let uu____22089 =
              let uu____22098 = FStar_List.map (elim_uvars env) sigs  in
              (uu____22098, lids)  in
            FStar_Syntax_Syntax.Sig_bundle uu____22089  in
          {
            FStar_Syntax_Syntax.sigel = uu____22088;
            FStar_Syntax_Syntax.sigrng =
              (uu___203_22087.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___203_22087.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___203_22087.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___203_22087.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_datacon (lid,univ_names,typ,lident,i,lids) ->
          let uu____22115 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____22115 with
           | (univ_names1,uu____22133,typ1) ->
               let uu___204_22147 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___204_22147.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___204_22147.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___204_22147.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___204_22147.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univ_names,typ) ->
          let uu____22153 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____22153 with
           | (univ_names1,uu____22171,typ1) ->
               let uu___205_22185 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___205_22185.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___205_22185.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___205_22185.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___205_22185.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____22219 =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs
                       in
                    match uu____22219 with
                    | (opening,lbunivs) ->
                        let elim t =
                          let uu____22242 =
                            let uu____22243 =
                              let uu____22244 =
                                FStar_Syntax_Subst.subst opening t  in
                              remove_uvar_solutions env uu____22244  in
                            FStar_Syntax_Subst.close_univ_vars lbunivs
                              uu____22243
                             in
                          elim_delayed_subst_term uu____22242  in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp  in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef  in
                        let uu___206_22247 = lb  in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___206_22247.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___206_22247.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___206_22247.FStar_Syntax_Syntax.lbattrs)
                        }))
             in
          let uu___207_22248 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids));
            FStar_Syntax_Syntax.sigrng =
              (uu___207_22248.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___207_22248.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___207_22248.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___207_22248.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_main t ->
          let uu___208_22260 = s  in
          let uu____22261 =
            let uu____22262 = remove_uvar_solutions env t  in
            FStar_Syntax_Syntax.Sig_main uu____22262  in
          {
            FStar_Syntax_Syntax.sigel = uu____22261;
            FStar_Syntax_Syntax.sigrng =
              (uu___208_22260.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___208_22260.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___208_22260.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___208_22260.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_assume (l,us,t) ->
          let uu____22266 = elim_uvars_aux_t env us [] t  in
          (match uu____22266 with
           | (us1,uu____22284,t1) ->
               let uu___209_22298 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___209_22298.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___209_22298.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___209_22298.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___209_22298.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____22299 ->
          failwith "Impossible: should have been desugared already"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____22301 =
            elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature
             in
          (match uu____22301 with
           | (univs1,binders,signature) ->
               let uu____22329 =
                 let uu____22338 = FStar_Syntax_Subst.univ_var_opening univs1
                    in
                 match uu____22338 with
                 | (univs_opening,univs2) ->
                     let uu____22365 =
                       FStar_Syntax_Subst.univ_var_closing univs2  in
                     (univs_opening, uu____22365)
                  in
               (match uu____22329 with
                | (univs_opening,univs_closing) ->
                    let uu____22382 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders
                         in
                      let uu____22388 =
                        FStar_Syntax_Subst.opening_of_binders binders1  in
                      let uu____22389 =
                        FStar_Syntax_Subst.closing_of_binders binders1  in
                      (uu____22388, uu____22389)  in
                    (match uu____22382 with
                     | (b_opening,b_closing) ->
                         let n1 = FStar_List.length univs1  in
                         let n_binders = FStar_List.length binders  in
                         let elim_tscheme uu____22411 =
                           match uu____22411 with
                           | (us,t) ->
                               let n_us = FStar_List.length us  in
                               let uu____22429 =
                                 FStar_Syntax_Subst.open_univ_vars us t  in
                               (match uu____22429 with
                                | (us1,t1) ->
                                    let uu____22440 =
                                      let uu____22445 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      let uu____22452 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      (uu____22445, uu____22452)  in
                                    (match uu____22440 with
                                     | (b_opening1,b_closing1) ->
                                         let uu____22465 =
                                           let uu____22470 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us)
                                              in
                                           let uu____22479 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us)
                                              in
                                           (uu____22470, uu____22479)  in
                                         (match uu____22465 with
                                          | (univs_opening1,univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____22495 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1
                                                   in
                                                FStar_Syntax_Subst.subst
                                                  univs_opening1 uu____22495
                                                 in
                                              let uu____22496 =
                                                elim_uvars_aux_t env [] [] t2
                                                 in
                                              (match uu____22496 with
                                               | (uu____22517,uu____22518,t3)
                                                   ->
                                                   let t4 =
                                                     let uu____22533 =
                                                       let uu____22534 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3
                                                          in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
                                                         uu____22534
                                                        in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____22533
                                                      in
                                                   (us1, t4)))))
                            in
                         let elim_term t =
                           let uu____22539 =
                             elim_uvars_aux_t env univs1 binders t  in
                           match uu____22539 with
                           | (uu____22552,uu____22553,t1) -> t1  in
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
                             | uu____22613 ->
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_abs
                                      ((a.FStar_Syntax_Syntax.action_params),
                                        body, FStar_Pervasives_Native.None))
                                   FStar_Pervasives_Native.None
                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                              in
                           let destruct_action_body body =
                             let uu____22630 =
                               let uu____22631 =
                                 FStar_Syntax_Subst.compress body  in
                               uu____22631.FStar_Syntax_Syntax.n  in
                             match uu____22630 with
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,(FStar_Util.Inl
                                        typ,FStar_Pervasives_Native.None ),FStar_Pervasives_Native.None
                                  )
                                 -> (defn, typ)
                             | uu____22690 -> failwith "Impossible"  in
                           let destruct_action_typ_templ t =
                             let uu____22719 =
                               let uu____22720 =
                                 FStar_Syntax_Subst.compress t  in
                               uu____22720.FStar_Syntax_Syntax.n  in
                             match uu____22719 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (pars,body,uu____22741) ->
                                 let uu____22762 = destruct_action_body body
                                    in
                                 (match uu____22762 with
                                  | (defn,typ) -> (pars, defn, typ))
                             | uu____22807 ->
                                 let uu____22808 = destruct_action_body t  in
                                 (match uu____22808 with
                                  | (defn,typ) -> ([], defn, typ))
                              in
                           let uu____22857 =
                             elim_tscheme
                               ((a.FStar_Syntax_Syntax.action_univs),
                                 action_typ_templ)
                              in
                           match uu____22857 with
                           | (action_univs,t) ->
                               let uu____22866 = destruct_action_typ_templ t
                                  in
                               (match uu____22866 with
                                | (action_params,action_defn,action_typ) ->
                                    let a' =
                                      let uu___210_22907 = a  in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___210_22907.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___210_22907.FStar_Syntax_Syntax.action_unqualified_name);
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
                           let uu___211_22909 = ed  in
                           let uu____22910 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ret_wp  in
                           let uu____22911 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_wp  in
                           let uu____22912 =
                             elim_tscheme ed.FStar_Syntax_Syntax.if_then_else
                              in
                           let uu____22913 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ite_wp  in
                           let uu____22914 =
                             elim_tscheme ed.FStar_Syntax_Syntax.stronger  in
                           let uu____22915 =
                             elim_tscheme ed.FStar_Syntax_Syntax.close_wp  in
                           let uu____22916 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assert_p  in
                           let uu____22917 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assume_p  in
                           let uu____22918 =
                             elim_tscheme ed.FStar_Syntax_Syntax.null_wp  in
                           let uu____22919 =
                             elim_tscheme ed.FStar_Syntax_Syntax.trivial  in
                           let uu____22920 =
                             elim_term ed.FStar_Syntax_Syntax.repr  in
                           let uu____22921 =
                             elim_tscheme ed.FStar_Syntax_Syntax.return_repr
                              in
                           let uu____22922 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_repr
                              in
                           let uu____22923 =
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions
                              in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___211_22909.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___211_22909.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs = univs1;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp = uu____22910;
                             FStar_Syntax_Syntax.bind_wp = uu____22911;
                             FStar_Syntax_Syntax.if_then_else = uu____22912;
                             FStar_Syntax_Syntax.ite_wp = uu____22913;
                             FStar_Syntax_Syntax.stronger = uu____22914;
                             FStar_Syntax_Syntax.close_wp = uu____22915;
                             FStar_Syntax_Syntax.assert_p = uu____22916;
                             FStar_Syntax_Syntax.assume_p = uu____22917;
                             FStar_Syntax_Syntax.null_wp = uu____22918;
                             FStar_Syntax_Syntax.trivial = uu____22919;
                             FStar_Syntax_Syntax.repr = uu____22920;
                             FStar_Syntax_Syntax.return_repr = uu____22921;
                             FStar_Syntax_Syntax.bind_repr = uu____22922;
                             FStar_Syntax_Syntax.actions = uu____22923
                           }  in
                         let uu___212_22926 = s  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___212_22926.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___212_22926.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___212_22926.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___212_22926.FStar_Syntax_Syntax.sigattrs)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___91_22943 =
            match uu___91_22943 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (us,t) ->
                let uu____22970 = elim_uvars_aux_t env us [] t  in
                (match uu____22970 with
                 | (us1,uu____22994,t1) ->
                     FStar_Pervasives_Native.Some (us1, t1))
             in
          let sub_eff1 =
            let uu___213_23013 = sub_eff  in
            let uu____23014 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp  in
            let uu____23017 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift  in
            {
              FStar_Syntax_Syntax.source =
                (uu___213_23013.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___213_23013.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____23014;
              FStar_Syntax_Syntax.lift = uu____23017
            }  in
          let uu___214_23020 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___214_23020.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___214_23020.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___214_23020.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___214_23020.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,univ_names,binders,comp,flags1) ->
          let uu____23030 = elim_uvars_aux_c env univ_names binders comp  in
          (match uu____23030 with
           | (univ_names1,binders1,comp1) ->
               let uu___215_23064 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___215_23064.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___215_23064.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___215_23064.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___215_23064.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____23075 -> s
  
let (erase_universes :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  -> normalize [EraseUniverses; AllowUnboundUniverses] env t
  