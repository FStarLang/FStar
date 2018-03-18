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
    ('Auu____162 -> 'Auu____163) ->
      'Auu____163 ->
        'Auu____162 FStar_Pervasives_Native.option -> 'Auu____163
  =
  fun f  ->
    fun d  ->
      fun uu___75_180  ->
        match uu___75_180 with
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
  no_delta_steps: Prims.bool ;
  unfold_until:
    FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option ;
  unfold_only: FStar_Ident.lid Prims.list FStar_Pervasives_Native.option ;
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
  unascribe: Prims.bool }[@@deriving show]
let (__proj__Mkfsteps__item__beta : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
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
  
let (__proj__Mkfsteps__item__no_delta_steps : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
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
  fsteps ->
    FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
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
let (fstep_add_one : step -> fsteps -> fsteps) =
  fun s  ->
    fun fs  ->
      let add_opt x uu___76_1038 =
        match uu___76_1038 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.Some [x]
        | FStar_Pervasives_Native.Some xs ->
            FStar_Pervasives_Native.Some (x :: xs)
         in
      match s with
      | Beta  ->
          let uu___94_1058 = fs  in
          {
            beta = true;
            iota = (uu___94_1058.iota);
            zeta = (uu___94_1058.zeta);
            weak = (uu___94_1058.weak);
            hnf = (uu___94_1058.hnf);
            primops = (uu___94_1058.primops);
            no_delta_steps = (uu___94_1058.no_delta_steps);
            unfold_until = (uu___94_1058.unfold_until);
            unfold_only = (uu___94_1058.unfold_only);
            unfold_attr = (uu___94_1058.unfold_attr);
            unfold_tac = (uu___94_1058.unfold_tac);
            pure_subterms_within_computations =
              (uu___94_1058.pure_subterms_within_computations);
            simplify = (uu___94_1058.simplify);
            erase_universes = (uu___94_1058.erase_universes);
            allow_unbound_universes = (uu___94_1058.allow_unbound_universes);
            reify_ = (uu___94_1058.reify_);
            compress_uvars = (uu___94_1058.compress_uvars);
            no_full_norm = (uu___94_1058.no_full_norm);
            check_no_uvars = (uu___94_1058.check_no_uvars);
            unmeta = (uu___94_1058.unmeta);
            unascribe = (uu___94_1058.unascribe)
          }
      | Iota  ->
          let uu___95_1059 = fs  in
          {
            beta = (uu___95_1059.beta);
            iota = true;
            zeta = (uu___95_1059.zeta);
            weak = (uu___95_1059.weak);
            hnf = (uu___95_1059.hnf);
            primops = (uu___95_1059.primops);
            no_delta_steps = (uu___95_1059.no_delta_steps);
            unfold_until = (uu___95_1059.unfold_until);
            unfold_only = (uu___95_1059.unfold_only);
            unfold_attr = (uu___95_1059.unfold_attr);
            unfold_tac = (uu___95_1059.unfold_tac);
            pure_subterms_within_computations =
              (uu___95_1059.pure_subterms_within_computations);
            simplify = (uu___95_1059.simplify);
            erase_universes = (uu___95_1059.erase_universes);
            allow_unbound_universes = (uu___95_1059.allow_unbound_universes);
            reify_ = (uu___95_1059.reify_);
            compress_uvars = (uu___95_1059.compress_uvars);
            no_full_norm = (uu___95_1059.no_full_norm);
            check_no_uvars = (uu___95_1059.check_no_uvars);
            unmeta = (uu___95_1059.unmeta);
            unascribe = (uu___95_1059.unascribe)
          }
      | Zeta  ->
          let uu___96_1060 = fs  in
          {
            beta = (uu___96_1060.beta);
            iota = (uu___96_1060.iota);
            zeta = true;
            weak = (uu___96_1060.weak);
            hnf = (uu___96_1060.hnf);
            primops = (uu___96_1060.primops);
            no_delta_steps = (uu___96_1060.no_delta_steps);
            unfold_until = (uu___96_1060.unfold_until);
            unfold_only = (uu___96_1060.unfold_only);
            unfold_attr = (uu___96_1060.unfold_attr);
            unfold_tac = (uu___96_1060.unfold_tac);
            pure_subterms_within_computations =
              (uu___96_1060.pure_subterms_within_computations);
            simplify = (uu___96_1060.simplify);
            erase_universes = (uu___96_1060.erase_universes);
            allow_unbound_universes = (uu___96_1060.allow_unbound_universes);
            reify_ = (uu___96_1060.reify_);
            compress_uvars = (uu___96_1060.compress_uvars);
            no_full_norm = (uu___96_1060.no_full_norm);
            check_no_uvars = (uu___96_1060.check_no_uvars);
            unmeta = (uu___96_1060.unmeta);
            unascribe = (uu___96_1060.unascribe)
          }
      | Exclude (Beta ) ->
          let uu___97_1061 = fs  in
          {
            beta = false;
            iota = (uu___97_1061.iota);
            zeta = (uu___97_1061.zeta);
            weak = (uu___97_1061.weak);
            hnf = (uu___97_1061.hnf);
            primops = (uu___97_1061.primops);
            no_delta_steps = (uu___97_1061.no_delta_steps);
            unfold_until = (uu___97_1061.unfold_until);
            unfold_only = (uu___97_1061.unfold_only);
            unfold_attr = (uu___97_1061.unfold_attr);
            unfold_tac = (uu___97_1061.unfold_tac);
            pure_subterms_within_computations =
              (uu___97_1061.pure_subterms_within_computations);
            simplify = (uu___97_1061.simplify);
            erase_universes = (uu___97_1061.erase_universes);
            allow_unbound_universes = (uu___97_1061.allow_unbound_universes);
            reify_ = (uu___97_1061.reify_);
            compress_uvars = (uu___97_1061.compress_uvars);
            no_full_norm = (uu___97_1061.no_full_norm);
            check_no_uvars = (uu___97_1061.check_no_uvars);
            unmeta = (uu___97_1061.unmeta);
            unascribe = (uu___97_1061.unascribe)
          }
      | Exclude (Iota ) ->
          let uu___98_1062 = fs  in
          {
            beta = (uu___98_1062.beta);
            iota = false;
            zeta = (uu___98_1062.zeta);
            weak = (uu___98_1062.weak);
            hnf = (uu___98_1062.hnf);
            primops = (uu___98_1062.primops);
            no_delta_steps = (uu___98_1062.no_delta_steps);
            unfold_until = (uu___98_1062.unfold_until);
            unfold_only = (uu___98_1062.unfold_only);
            unfold_attr = (uu___98_1062.unfold_attr);
            unfold_tac = (uu___98_1062.unfold_tac);
            pure_subterms_within_computations =
              (uu___98_1062.pure_subterms_within_computations);
            simplify = (uu___98_1062.simplify);
            erase_universes = (uu___98_1062.erase_universes);
            allow_unbound_universes = (uu___98_1062.allow_unbound_universes);
            reify_ = (uu___98_1062.reify_);
            compress_uvars = (uu___98_1062.compress_uvars);
            no_full_norm = (uu___98_1062.no_full_norm);
            check_no_uvars = (uu___98_1062.check_no_uvars);
            unmeta = (uu___98_1062.unmeta);
            unascribe = (uu___98_1062.unascribe)
          }
      | Exclude (Zeta ) ->
          let uu___99_1063 = fs  in
          {
            beta = (uu___99_1063.beta);
            iota = (uu___99_1063.iota);
            zeta = false;
            weak = (uu___99_1063.weak);
            hnf = (uu___99_1063.hnf);
            primops = (uu___99_1063.primops);
            no_delta_steps = (uu___99_1063.no_delta_steps);
            unfold_until = (uu___99_1063.unfold_until);
            unfold_only = (uu___99_1063.unfold_only);
            unfold_attr = (uu___99_1063.unfold_attr);
            unfold_tac = (uu___99_1063.unfold_tac);
            pure_subterms_within_computations =
              (uu___99_1063.pure_subterms_within_computations);
            simplify = (uu___99_1063.simplify);
            erase_universes = (uu___99_1063.erase_universes);
            allow_unbound_universes = (uu___99_1063.allow_unbound_universes);
            reify_ = (uu___99_1063.reify_);
            compress_uvars = (uu___99_1063.compress_uvars);
            no_full_norm = (uu___99_1063.no_full_norm);
            check_no_uvars = (uu___99_1063.check_no_uvars);
            unmeta = (uu___99_1063.unmeta);
            unascribe = (uu___99_1063.unascribe)
          }
      | Exclude uu____1064 -> failwith "Bad exclude"
      | Weak  ->
          let uu___100_1065 = fs  in
          {
            beta = (uu___100_1065.beta);
            iota = (uu___100_1065.iota);
            zeta = (uu___100_1065.zeta);
            weak = true;
            hnf = (uu___100_1065.hnf);
            primops = (uu___100_1065.primops);
            no_delta_steps = (uu___100_1065.no_delta_steps);
            unfold_until = (uu___100_1065.unfold_until);
            unfold_only = (uu___100_1065.unfold_only);
            unfold_attr = (uu___100_1065.unfold_attr);
            unfold_tac = (uu___100_1065.unfold_tac);
            pure_subterms_within_computations =
              (uu___100_1065.pure_subterms_within_computations);
            simplify = (uu___100_1065.simplify);
            erase_universes = (uu___100_1065.erase_universes);
            allow_unbound_universes = (uu___100_1065.allow_unbound_universes);
            reify_ = (uu___100_1065.reify_);
            compress_uvars = (uu___100_1065.compress_uvars);
            no_full_norm = (uu___100_1065.no_full_norm);
            check_no_uvars = (uu___100_1065.check_no_uvars);
            unmeta = (uu___100_1065.unmeta);
            unascribe = (uu___100_1065.unascribe)
          }
      | HNF  ->
          let uu___101_1066 = fs  in
          {
            beta = (uu___101_1066.beta);
            iota = (uu___101_1066.iota);
            zeta = (uu___101_1066.zeta);
            weak = (uu___101_1066.weak);
            hnf = true;
            primops = (uu___101_1066.primops);
            no_delta_steps = (uu___101_1066.no_delta_steps);
            unfold_until = (uu___101_1066.unfold_until);
            unfold_only = (uu___101_1066.unfold_only);
            unfold_attr = (uu___101_1066.unfold_attr);
            unfold_tac = (uu___101_1066.unfold_tac);
            pure_subterms_within_computations =
              (uu___101_1066.pure_subterms_within_computations);
            simplify = (uu___101_1066.simplify);
            erase_universes = (uu___101_1066.erase_universes);
            allow_unbound_universes = (uu___101_1066.allow_unbound_universes);
            reify_ = (uu___101_1066.reify_);
            compress_uvars = (uu___101_1066.compress_uvars);
            no_full_norm = (uu___101_1066.no_full_norm);
            check_no_uvars = (uu___101_1066.check_no_uvars);
            unmeta = (uu___101_1066.unmeta);
            unascribe = (uu___101_1066.unascribe)
          }
      | Primops  ->
          let uu___102_1067 = fs  in
          {
            beta = (uu___102_1067.beta);
            iota = (uu___102_1067.iota);
            zeta = (uu___102_1067.zeta);
            weak = (uu___102_1067.weak);
            hnf = (uu___102_1067.hnf);
            primops = true;
            no_delta_steps = (uu___102_1067.no_delta_steps);
            unfold_until = (uu___102_1067.unfold_until);
            unfold_only = (uu___102_1067.unfold_only);
            unfold_attr = (uu___102_1067.unfold_attr);
            unfold_tac = (uu___102_1067.unfold_tac);
            pure_subterms_within_computations =
              (uu___102_1067.pure_subterms_within_computations);
            simplify = (uu___102_1067.simplify);
            erase_universes = (uu___102_1067.erase_universes);
            allow_unbound_universes = (uu___102_1067.allow_unbound_universes);
            reify_ = (uu___102_1067.reify_);
            compress_uvars = (uu___102_1067.compress_uvars);
            no_full_norm = (uu___102_1067.no_full_norm);
            check_no_uvars = (uu___102_1067.check_no_uvars);
            unmeta = (uu___102_1067.unmeta);
            unascribe = (uu___102_1067.unascribe)
          }
      | Eager_unfolding  -> fs
      | Inlining  -> fs
      | NoDeltaSteps  ->
          let uu___103_1068 = fs  in
          {
            beta = (uu___103_1068.beta);
            iota = (uu___103_1068.iota);
            zeta = (uu___103_1068.zeta);
            weak = (uu___103_1068.weak);
            hnf = (uu___103_1068.hnf);
            primops = (uu___103_1068.primops);
            no_delta_steps = true;
            unfold_until = (uu___103_1068.unfold_until);
            unfold_only = (uu___103_1068.unfold_only);
            unfold_attr = (uu___103_1068.unfold_attr);
            unfold_tac = (uu___103_1068.unfold_tac);
            pure_subterms_within_computations =
              (uu___103_1068.pure_subterms_within_computations);
            simplify = (uu___103_1068.simplify);
            erase_universes = (uu___103_1068.erase_universes);
            allow_unbound_universes = (uu___103_1068.allow_unbound_universes);
            reify_ = (uu___103_1068.reify_);
            compress_uvars = (uu___103_1068.compress_uvars);
            no_full_norm = (uu___103_1068.no_full_norm);
            check_no_uvars = (uu___103_1068.check_no_uvars);
            unmeta = (uu___103_1068.unmeta);
            unascribe = (uu___103_1068.unascribe)
          }
      | UnfoldUntil d ->
          let uu___104_1070 = fs  in
          {
            beta = (uu___104_1070.beta);
            iota = (uu___104_1070.iota);
            zeta = (uu___104_1070.zeta);
            weak = (uu___104_1070.weak);
            hnf = (uu___104_1070.hnf);
            primops = (uu___104_1070.primops);
            no_delta_steps = (uu___104_1070.no_delta_steps);
            unfold_until = (FStar_Pervasives_Native.Some d);
            unfold_only = (uu___104_1070.unfold_only);
            unfold_attr = (uu___104_1070.unfold_attr);
            unfold_tac = (uu___104_1070.unfold_tac);
            pure_subterms_within_computations =
              (uu___104_1070.pure_subterms_within_computations);
            simplify = (uu___104_1070.simplify);
            erase_universes = (uu___104_1070.erase_universes);
            allow_unbound_universes = (uu___104_1070.allow_unbound_universes);
            reify_ = (uu___104_1070.reify_);
            compress_uvars = (uu___104_1070.compress_uvars);
            no_full_norm = (uu___104_1070.no_full_norm);
            check_no_uvars = (uu___104_1070.check_no_uvars);
            unmeta = (uu___104_1070.unmeta);
            unascribe = (uu___104_1070.unascribe)
          }
      | UnfoldOnly lids ->
          let uu___105_1074 = fs  in
          {
            beta = (uu___105_1074.beta);
            iota = (uu___105_1074.iota);
            zeta = (uu___105_1074.zeta);
            weak = (uu___105_1074.weak);
            hnf = (uu___105_1074.hnf);
            primops = (uu___105_1074.primops);
            no_delta_steps = (uu___105_1074.no_delta_steps);
            unfold_until = (uu___105_1074.unfold_until);
            unfold_only = (FStar_Pervasives_Native.Some lids);
            unfold_attr = (uu___105_1074.unfold_attr);
            unfold_tac = (uu___105_1074.unfold_tac);
            pure_subterms_within_computations =
              (uu___105_1074.pure_subterms_within_computations);
            simplify = (uu___105_1074.simplify);
            erase_universes = (uu___105_1074.erase_universes);
            allow_unbound_universes = (uu___105_1074.allow_unbound_universes);
            reify_ = (uu___105_1074.reify_);
            compress_uvars = (uu___105_1074.compress_uvars);
            no_full_norm = (uu___105_1074.no_full_norm);
            check_no_uvars = (uu___105_1074.check_no_uvars);
            unmeta = (uu___105_1074.unmeta);
            unascribe = (uu___105_1074.unascribe)
          }
      | UnfoldAttr attr ->
          let uu___106_1078 = fs  in
          {
            beta = (uu___106_1078.beta);
            iota = (uu___106_1078.iota);
            zeta = (uu___106_1078.zeta);
            weak = (uu___106_1078.weak);
            hnf = (uu___106_1078.hnf);
            primops = (uu___106_1078.primops);
            no_delta_steps = (uu___106_1078.no_delta_steps);
            unfold_until = (uu___106_1078.unfold_until);
            unfold_only = (uu___106_1078.unfold_only);
            unfold_attr = (add_opt attr fs.unfold_attr);
            unfold_tac = (uu___106_1078.unfold_tac);
            pure_subterms_within_computations =
              (uu___106_1078.pure_subterms_within_computations);
            simplify = (uu___106_1078.simplify);
            erase_universes = (uu___106_1078.erase_universes);
            allow_unbound_universes = (uu___106_1078.allow_unbound_universes);
            reify_ = (uu___106_1078.reify_);
            compress_uvars = (uu___106_1078.compress_uvars);
            no_full_norm = (uu___106_1078.no_full_norm);
            check_no_uvars = (uu___106_1078.check_no_uvars);
            unmeta = (uu___106_1078.unmeta);
            unascribe = (uu___106_1078.unascribe)
          }
      | UnfoldTac  ->
          let uu___107_1079 = fs  in
          {
            beta = (uu___107_1079.beta);
            iota = (uu___107_1079.iota);
            zeta = (uu___107_1079.zeta);
            weak = (uu___107_1079.weak);
            hnf = (uu___107_1079.hnf);
            primops = (uu___107_1079.primops);
            no_delta_steps = (uu___107_1079.no_delta_steps);
            unfold_until = (uu___107_1079.unfold_until);
            unfold_only = (uu___107_1079.unfold_only);
            unfold_attr = (uu___107_1079.unfold_attr);
            unfold_tac = true;
            pure_subterms_within_computations =
              (uu___107_1079.pure_subterms_within_computations);
            simplify = (uu___107_1079.simplify);
            erase_universes = (uu___107_1079.erase_universes);
            allow_unbound_universes = (uu___107_1079.allow_unbound_universes);
            reify_ = (uu___107_1079.reify_);
            compress_uvars = (uu___107_1079.compress_uvars);
            no_full_norm = (uu___107_1079.no_full_norm);
            check_no_uvars = (uu___107_1079.check_no_uvars);
            unmeta = (uu___107_1079.unmeta);
            unascribe = (uu___107_1079.unascribe)
          }
      | PureSubtermsWithinComputations  ->
          let uu___108_1080 = fs  in
          {
            beta = (uu___108_1080.beta);
            iota = (uu___108_1080.iota);
            zeta = (uu___108_1080.zeta);
            weak = (uu___108_1080.weak);
            hnf = (uu___108_1080.hnf);
            primops = (uu___108_1080.primops);
            no_delta_steps = (uu___108_1080.no_delta_steps);
            unfold_until = (uu___108_1080.unfold_until);
            unfold_only = (uu___108_1080.unfold_only);
            unfold_attr = (uu___108_1080.unfold_attr);
            unfold_tac = (uu___108_1080.unfold_tac);
            pure_subterms_within_computations = true;
            simplify = (uu___108_1080.simplify);
            erase_universes = (uu___108_1080.erase_universes);
            allow_unbound_universes = (uu___108_1080.allow_unbound_universes);
            reify_ = (uu___108_1080.reify_);
            compress_uvars = (uu___108_1080.compress_uvars);
            no_full_norm = (uu___108_1080.no_full_norm);
            check_no_uvars = (uu___108_1080.check_no_uvars);
            unmeta = (uu___108_1080.unmeta);
            unascribe = (uu___108_1080.unascribe)
          }
      | Simplify  ->
          let uu___109_1081 = fs  in
          {
            beta = (uu___109_1081.beta);
            iota = (uu___109_1081.iota);
            zeta = (uu___109_1081.zeta);
            weak = (uu___109_1081.weak);
            hnf = (uu___109_1081.hnf);
            primops = (uu___109_1081.primops);
            no_delta_steps = (uu___109_1081.no_delta_steps);
            unfold_until = (uu___109_1081.unfold_until);
            unfold_only = (uu___109_1081.unfold_only);
            unfold_attr = (uu___109_1081.unfold_attr);
            unfold_tac = (uu___109_1081.unfold_tac);
            pure_subterms_within_computations =
              (uu___109_1081.pure_subterms_within_computations);
            simplify = true;
            erase_universes = (uu___109_1081.erase_universes);
            allow_unbound_universes = (uu___109_1081.allow_unbound_universes);
            reify_ = (uu___109_1081.reify_);
            compress_uvars = (uu___109_1081.compress_uvars);
            no_full_norm = (uu___109_1081.no_full_norm);
            check_no_uvars = (uu___109_1081.check_no_uvars);
            unmeta = (uu___109_1081.unmeta);
            unascribe = (uu___109_1081.unascribe)
          }
      | EraseUniverses  ->
          let uu___110_1082 = fs  in
          {
            beta = (uu___110_1082.beta);
            iota = (uu___110_1082.iota);
            zeta = (uu___110_1082.zeta);
            weak = (uu___110_1082.weak);
            hnf = (uu___110_1082.hnf);
            primops = (uu___110_1082.primops);
            no_delta_steps = (uu___110_1082.no_delta_steps);
            unfold_until = (uu___110_1082.unfold_until);
            unfold_only = (uu___110_1082.unfold_only);
            unfold_attr = (uu___110_1082.unfold_attr);
            unfold_tac = (uu___110_1082.unfold_tac);
            pure_subterms_within_computations =
              (uu___110_1082.pure_subterms_within_computations);
            simplify = (uu___110_1082.simplify);
            erase_universes = true;
            allow_unbound_universes = (uu___110_1082.allow_unbound_universes);
            reify_ = (uu___110_1082.reify_);
            compress_uvars = (uu___110_1082.compress_uvars);
            no_full_norm = (uu___110_1082.no_full_norm);
            check_no_uvars = (uu___110_1082.check_no_uvars);
            unmeta = (uu___110_1082.unmeta);
            unascribe = (uu___110_1082.unascribe)
          }
      | AllowUnboundUniverses  ->
          let uu___111_1083 = fs  in
          {
            beta = (uu___111_1083.beta);
            iota = (uu___111_1083.iota);
            zeta = (uu___111_1083.zeta);
            weak = (uu___111_1083.weak);
            hnf = (uu___111_1083.hnf);
            primops = (uu___111_1083.primops);
            no_delta_steps = (uu___111_1083.no_delta_steps);
            unfold_until = (uu___111_1083.unfold_until);
            unfold_only = (uu___111_1083.unfold_only);
            unfold_attr = (uu___111_1083.unfold_attr);
            unfold_tac = (uu___111_1083.unfold_tac);
            pure_subterms_within_computations =
              (uu___111_1083.pure_subterms_within_computations);
            simplify = (uu___111_1083.simplify);
            erase_universes = (uu___111_1083.erase_universes);
            allow_unbound_universes = true;
            reify_ = (uu___111_1083.reify_);
            compress_uvars = (uu___111_1083.compress_uvars);
            no_full_norm = (uu___111_1083.no_full_norm);
            check_no_uvars = (uu___111_1083.check_no_uvars);
            unmeta = (uu___111_1083.unmeta);
            unascribe = (uu___111_1083.unascribe)
          }
      | Reify  ->
          let uu___112_1084 = fs  in
          {
            beta = (uu___112_1084.beta);
            iota = (uu___112_1084.iota);
            zeta = (uu___112_1084.zeta);
            weak = (uu___112_1084.weak);
            hnf = (uu___112_1084.hnf);
            primops = (uu___112_1084.primops);
            no_delta_steps = (uu___112_1084.no_delta_steps);
            unfold_until = (uu___112_1084.unfold_until);
            unfold_only = (uu___112_1084.unfold_only);
            unfold_attr = (uu___112_1084.unfold_attr);
            unfold_tac = (uu___112_1084.unfold_tac);
            pure_subterms_within_computations =
              (uu___112_1084.pure_subterms_within_computations);
            simplify = (uu___112_1084.simplify);
            erase_universes = (uu___112_1084.erase_universes);
            allow_unbound_universes = (uu___112_1084.allow_unbound_universes);
            reify_ = true;
            compress_uvars = (uu___112_1084.compress_uvars);
            no_full_norm = (uu___112_1084.no_full_norm);
            check_no_uvars = (uu___112_1084.check_no_uvars);
            unmeta = (uu___112_1084.unmeta);
            unascribe = (uu___112_1084.unascribe)
          }
      | CompressUvars  ->
          let uu___113_1085 = fs  in
          {
            beta = (uu___113_1085.beta);
            iota = (uu___113_1085.iota);
            zeta = (uu___113_1085.zeta);
            weak = (uu___113_1085.weak);
            hnf = (uu___113_1085.hnf);
            primops = (uu___113_1085.primops);
            no_delta_steps = (uu___113_1085.no_delta_steps);
            unfold_until = (uu___113_1085.unfold_until);
            unfold_only = (uu___113_1085.unfold_only);
            unfold_attr = (uu___113_1085.unfold_attr);
            unfold_tac = (uu___113_1085.unfold_tac);
            pure_subterms_within_computations =
              (uu___113_1085.pure_subterms_within_computations);
            simplify = (uu___113_1085.simplify);
            erase_universes = (uu___113_1085.erase_universes);
            allow_unbound_universes = (uu___113_1085.allow_unbound_universes);
            reify_ = (uu___113_1085.reify_);
            compress_uvars = true;
            no_full_norm = (uu___113_1085.no_full_norm);
            check_no_uvars = (uu___113_1085.check_no_uvars);
            unmeta = (uu___113_1085.unmeta);
            unascribe = (uu___113_1085.unascribe)
          }
      | NoFullNorm  ->
          let uu___114_1086 = fs  in
          {
            beta = (uu___114_1086.beta);
            iota = (uu___114_1086.iota);
            zeta = (uu___114_1086.zeta);
            weak = (uu___114_1086.weak);
            hnf = (uu___114_1086.hnf);
            primops = (uu___114_1086.primops);
            no_delta_steps = (uu___114_1086.no_delta_steps);
            unfold_until = (uu___114_1086.unfold_until);
            unfold_only = (uu___114_1086.unfold_only);
            unfold_attr = (uu___114_1086.unfold_attr);
            unfold_tac = (uu___114_1086.unfold_tac);
            pure_subterms_within_computations =
              (uu___114_1086.pure_subterms_within_computations);
            simplify = (uu___114_1086.simplify);
            erase_universes = (uu___114_1086.erase_universes);
            allow_unbound_universes = (uu___114_1086.allow_unbound_universes);
            reify_ = (uu___114_1086.reify_);
            compress_uvars = (uu___114_1086.compress_uvars);
            no_full_norm = true;
            check_no_uvars = (uu___114_1086.check_no_uvars);
            unmeta = (uu___114_1086.unmeta);
            unascribe = (uu___114_1086.unascribe)
          }
      | CheckNoUvars  ->
          let uu___115_1087 = fs  in
          {
            beta = (uu___115_1087.beta);
            iota = (uu___115_1087.iota);
            zeta = (uu___115_1087.zeta);
            weak = (uu___115_1087.weak);
            hnf = (uu___115_1087.hnf);
            primops = (uu___115_1087.primops);
            no_delta_steps = (uu___115_1087.no_delta_steps);
            unfold_until = (uu___115_1087.unfold_until);
            unfold_only = (uu___115_1087.unfold_only);
            unfold_attr = (uu___115_1087.unfold_attr);
            unfold_tac = (uu___115_1087.unfold_tac);
            pure_subterms_within_computations =
              (uu___115_1087.pure_subterms_within_computations);
            simplify = (uu___115_1087.simplify);
            erase_universes = (uu___115_1087.erase_universes);
            allow_unbound_universes = (uu___115_1087.allow_unbound_universes);
            reify_ = (uu___115_1087.reify_);
            compress_uvars = (uu___115_1087.compress_uvars);
            no_full_norm = (uu___115_1087.no_full_norm);
            check_no_uvars = true;
            unmeta = (uu___115_1087.unmeta);
            unascribe = (uu___115_1087.unascribe)
          }
      | Unmeta  ->
          let uu___116_1088 = fs  in
          {
            beta = (uu___116_1088.beta);
            iota = (uu___116_1088.iota);
            zeta = (uu___116_1088.zeta);
            weak = (uu___116_1088.weak);
            hnf = (uu___116_1088.hnf);
            primops = (uu___116_1088.primops);
            no_delta_steps = (uu___116_1088.no_delta_steps);
            unfold_until = (uu___116_1088.unfold_until);
            unfold_only = (uu___116_1088.unfold_only);
            unfold_attr = (uu___116_1088.unfold_attr);
            unfold_tac = (uu___116_1088.unfold_tac);
            pure_subterms_within_computations =
              (uu___116_1088.pure_subterms_within_computations);
            simplify = (uu___116_1088.simplify);
            erase_universes = (uu___116_1088.erase_universes);
            allow_unbound_universes = (uu___116_1088.allow_unbound_universes);
            reify_ = (uu___116_1088.reify_);
            compress_uvars = (uu___116_1088.compress_uvars);
            no_full_norm = (uu___116_1088.no_full_norm);
            check_no_uvars = (uu___116_1088.check_no_uvars);
            unmeta = true;
            unascribe = (uu___116_1088.unascribe)
          }
      | Unascribe  ->
          let uu___117_1089 = fs  in
          {
            beta = (uu___117_1089.beta);
            iota = (uu___117_1089.iota);
            zeta = (uu___117_1089.zeta);
            weak = (uu___117_1089.weak);
            hnf = (uu___117_1089.hnf);
            primops = (uu___117_1089.primops);
            no_delta_steps = (uu___117_1089.no_delta_steps);
            unfold_until = (uu___117_1089.unfold_until);
            unfold_only = (uu___117_1089.unfold_only);
            unfold_attr = (uu___117_1089.unfold_attr);
            unfold_tac = (uu___117_1089.unfold_tac);
            pure_subterms_within_computations =
              (uu___117_1089.pure_subterms_within_computations);
            simplify = (uu___117_1089.simplify);
            erase_universes = (uu___117_1089.erase_universes);
            allow_unbound_universes = (uu___117_1089.allow_unbound_universes);
            reify_ = (uu___117_1089.reify_);
            compress_uvars = (uu___117_1089.compress_uvars);
            no_full_norm = (uu___117_1089.no_full_norm);
            check_no_uvars = (uu___117_1089.check_no_uvars);
            unmeta = (uu___117_1089.unmeta);
            unascribe = true
          }
  
let rec (to_fsteps : step Prims.list -> fsteps) =
  fun s  -> FStar_List.fold_right fstep_add_one s default_steps 
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
  { psc_range = FStar_Range.dummyRange; psc_subst = (fun uu____1128  -> []) } 
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
    match projectee with | Clos _0 -> true | uu____1371 -> false
  
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
    match projectee with | Univ _0 -> true | uu____1473 -> false
  
let (__proj__Univ__item___0 : closure -> FStar_Syntax_Syntax.universe) =
  fun projectee  -> match projectee with | Univ _0 -> _0 
let (uu___is_Dummy : closure -> Prims.bool) =
  fun projectee  ->
    match projectee with | Dummy  -> true | uu____1484 -> false
  
type env =
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
    FStar_Pervasives_Native.tuple2 Prims.list[@@deriving show]
let (dummy :
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
    FStar_Pervasives_Native.tuple2)
  = (FStar_Pervasives_Native.None, Dummy) 
let (closure_to_string : closure -> Prims.string) =
  fun uu___77_1503  ->
    match uu___77_1503 with
    | Clos (uu____1504,t,uu____1506,uu____1507) ->
        FStar_Syntax_Print.term_to_string t
    | Univ uu____1552 -> "Univ"
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
    let uu____1814 = FStar_Util.psmap_empty ()  in add_steps uu____1814 l
  
let (find_prim_step :
  cfg ->
    FStar_Syntax_Syntax.fv -> primitive_step FStar_Pervasives_Native.option)
  =
  fun cfg  ->
    fun fv  ->
      FStar_Util.psmap_try_find cfg.primitive_steps
        (FStar_Ident.text_of_lid
           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
  
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
    match projectee with | Arg _0 -> true | uu____1966 -> false
  
let (__proj__Arg__item___0 :
  stack_elt ->
    (closure,FStar_Syntax_Syntax.aqual,FStar_Range.range)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | Arg _0 -> _0 
let (uu___is_UnivArgs : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnivArgs _0 -> true | uu____2002 -> false
  
let (__proj__UnivArgs__item___0 :
  stack_elt ->
    (FStar_Syntax_Syntax.universe Prims.list,FStar_Range.range)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | UnivArgs _0 -> _0 
let (uu___is_MemoLazy : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | MemoLazy _0 -> true | uu____2038 -> false
  
let (__proj__MemoLazy__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.term) FStar_Pervasives_Native.tuple2
      FStar_Syntax_Syntax.memo)
  = fun projectee  -> match projectee with | MemoLazy _0 -> _0 
let (uu___is_Match : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____2107 -> false
  
let (__proj__Match__item___0 :
  stack_elt ->
    (env,branches,FStar_Range.range) FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | Match _0 -> _0 
let (uu___is_Abs : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Abs _0 -> true | uu____2149 -> false
  
let (__proj__Abs__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.binders,env,FStar_Syntax_Syntax.residual_comp
                                           FStar_Pervasives_Native.option,
      FStar_Range.range) FStar_Pervasives_Native.tuple5)
  = fun projectee  -> match projectee with | Abs _0 -> _0 
let (uu___is_App : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____2205 -> false
  
let (__proj__App__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual,FStar_Range.range)
      FStar_Pervasives_Native.tuple4)
  = fun projectee  -> match projectee with | App _0 -> _0 
let (uu___is_Meta : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Meta _0 -> true | uu____2245 -> false
  
let (__proj__Meta__item___0 :
  stack_elt ->
    (FStar_Syntax_Syntax.metadata,FStar_Range.range)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Meta _0 -> _0 
let (uu___is_Let : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Let _0 -> true | uu____2277 -> false
  
let (__proj__Let__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.letbinding,FStar_Range.range)
      FStar_Pervasives_Native.tuple4)
  = fun projectee  -> match projectee with | Let _0 -> _0 
let (uu___is_Cfg : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Cfg _0 -> true | uu____2313 -> false
  
let (__proj__Cfg__item___0 : stack_elt -> cfg) =
  fun projectee  -> match projectee with | Cfg _0 -> _0 
let (uu___is_Debug : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Debug _0 -> true | uu____2329 -> false
  
let (__proj__Debug__item___0 :
  stack_elt ->
    (FStar_Syntax_Syntax.term,FStar_Util.time) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Debug _0 -> _0 
type stack = stack_elt Prims.list[@@deriving show]
let (head_of : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____2354 = FStar_Syntax_Util.head_and_args' t  in
    match uu____2354 with | (hd1,uu____2368) -> hd1
  
let mk :
  'Auu____2388 .
    'Auu____2388 ->
      FStar_Range.range -> 'Auu____2388 FStar_Syntax_Syntax.syntax
  =
  fun t  -> fun r  -> FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None r 
let set_memo : 'a . cfg -> 'a FStar_Syntax_Syntax.memo -> 'a -> Prims.unit =
  fun cfg  ->
    fun r  ->
      fun t  ->
        if cfg.memoize_lazy
        then
          let uu____2442 = FStar_ST.op_Bang r  in
          match uu____2442 with
          | FStar_Pervasives_Native.Some uu____2490 ->
              failwith "Unexpected set_memo: thunk already evaluated"
          | FStar_Pervasives_Native.None  ->
              FStar_ST.op_Colon_Equals r (FStar_Pervasives_Native.Some t)
        else ()
  
let (env_to_string : closure Prims.list -> Prims.string) =
  fun env  ->
    let uu____2544 = FStar_List.map closure_to_string env  in
    FStar_All.pipe_right uu____2544 (FStar_String.concat "; ")
  
let (stack_elt_to_string : stack_elt -> Prims.string) =
  fun uu___78_2551  ->
    match uu___78_2551 with
    | Arg (c,uu____2553,uu____2554) ->
        let uu____2555 = closure_to_string c  in
        FStar_Util.format1 "Closure %s" uu____2555
    | MemoLazy uu____2556 -> "MemoLazy"
    | Abs (uu____2563,bs,uu____2565,uu____2566,uu____2567) ->
        let uu____2572 =
          FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs)
           in
        FStar_Util.format1 "Abs %s" uu____2572
    | UnivArgs uu____2577 -> "UnivArgs"
    | Match uu____2584 -> "Match"
    | App (uu____2591,t,uu____2593,uu____2594) ->
        let uu____2595 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "App %s" uu____2595
    | Meta (m,uu____2597) -> "Meta"
    | Let uu____2598 -> "Let"
    | Cfg uu____2607 -> "Cfg"
    | Debug (t,uu____2609) ->
        let uu____2610 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "Debug %s" uu____2610
  
let (stack_to_string : stack_elt Prims.list -> Prims.string) =
  fun s  ->
    let uu____2618 = FStar_List.map stack_elt_to_string s  in
    FStar_All.pipe_right uu____2618 (FStar_String.concat "; ")
  
let (log : cfg -> (Prims.unit -> Prims.unit) -> Prims.unit) =
  fun cfg  -> fun f  -> if (cfg.debug).gen then f () else () 
let (log_primops : cfg -> (Prims.unit -> Prims.unit) -> Prims.unit) =
  fun cfg  -> fun f  -> if (cfg.debug).primop then f () else () 
let is_empty : 'Auu____2649 . 'Auu____2649 Prims.list -> Prims.bool =
  fun uu___79_2655  ->
    match uu___79_2655 with | [] -> true | uu____2658 -> false
  
let lookup_bvar :
  'Auu____2665 'Auu____2666 .
    ('Auu____2665,'Auu____2666) FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Syntax_Syntax.bv -> 'Auu____2666
  =
  fun env  ->
    fun x  ->
      try
        let uu____2690 = FStar_List.nth env x.FStar_Syntax_Syntax.index  in
        FStar_Pervasives_Native.snd uu____2690
      with
      | uu____2703 ->
          let uu____2704 =
            let uu____2705 = FStar_Syntax_Print.db_to_string x  in
            FStar_Util.format1 "Failed to find %s\n" uu____2705  in
          failwith uu____2704
  
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
          let uu____2742 =
            FStar_List.fold_left
              (fun uu____2768  ->
                 fun u1  ->
                   match uu____2768 with
                   | (cur_kernel,cur_max,out) ->
                       let uu____2793 = FStar_Syntax_Util.univ_kernel u1  in
                       (match uu____2793 with
                        | (k_u,n1) ->
                            let uu____2808 =
                              FStar_Syntax_Util.eq_univs cur_kernel k_u  in
                            if uu____2808
                            then (cur_kernel, u1, out)
                            else (k_u, u1, (cur_max :: out))))
              (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero, [])
              us1
             in
          match uu____2742 with
          | (uu____2826,u1,out) -> FStar_List.rev (u1 :: out)  in
        let rec aux u1 =
          let u2 = FStar_Syntax_Subst.compress_univ u1  in
          match u2 with
          | FStar_Syntax_Syntax.U_bvar x ->
              (try
                 let uu____2851 =
                   let uu____2852 = FStar_List.nth env x  in
                   FStar_Pervasives_Native.snd uu____2852  in
                 match uu____2851 with
                 | Univ u3 -> aux u3
                 | Dummy  -> [u2]
                 | uu____2870 ->
                     failwith "Impossible: universe variable bound to a term"
               with
               | uu____2878 ->
                   if (cfg.steps).allow_unbound_universes
                   then [FStar_Syntax_Syntax.U_unknown]
                   else failwith "Universe variable not found")
          | FStar_Syntax_Syntax.U_unif uu____2884 when
              (cfg.steps).check_no_uvars -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_zero  -> [u2]
          | FStar_Syntax_Syntax.U_unif uu____2893 -> [u2]
          | FStar_Syntax_Syntax.U_name uu____2902 -> [u2]
          | FStar_Syntax_Syntax.U_unknown  -> [u2]
          | FStar_Syntax_Syntax.U_max [] -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_max us ->
              let us1 =
                let uu____2909 = FStar_List.collect aux us  in
                FStar_All.pipe_right uu____2909 norm_univs  in
              (match us1 with
               | u_k::hd1::rest ->
                   let rest1 = hd1 :: rest  in
                   let uu____2926 = FStar_Syntax_Util.univ_kernel u_k  in
                   (match uu____2926 with
                    | (FStar_Syntax_Syntax.U_zero ,n1) ->
                        let uu____2934 =
                          FStar_All.pipe_right rest1
                            (FStar_List.for_all
                               (fun u3  ->
                                  let uu____2942 =
                                    FStar_Syntax_Util.univ_kernel u3  in
                                  match uu____2942 with
                                  | (uu____2947,m) -> n1 <= m))
                           in
                        if uu____2934 then rest1 else us1
                    | uu____2952 -> us1)
               | uu____2957 -> us1)
          | FStar_Syntax_Syntax.U_succ u3 ->
              let uu____2961 = aux u3  in
              FStar_List.map (fun _0_40  -> FStar_Syntax_Syntax.U_succ _0_40)
                uu____2961
           in
        if (cfg.steps).erase_universes
        then FStar_Syntax_Syntax.U_unknown
        else
          (let uu____2965 = aux u  in
           match uu____2965 with
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
          (fun uu____3069  ->
             let uu____3070 = FStar_Syntax_Print.tag_of_term t  in
             let uu____3071 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.print2 ">>> %s Closure_as_term %s\n" uu____3070
               uu____3071);
        (match env with
         | [] when
             FStar_All.pipe_left Prims.op_Negation (cfg.steps).compress_uvars
             -> t
         | uu____3078 ->
             let t1 = FStar_Syntax_Subst.compress t  in
             (match t1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_delayed uu____3080 ->
                  failwith "Impossible"
              | FStar_Syntax_Syntax.Tm_unknown  -> t1
              | FStar_Syntax_Syntax.Tm_constant uu____3105 -> t1
              | FStar_Syntax_Syntax.Tm_name uu____3106 -> t1
              | FStar_Syntax_Syntax.Tm_lazy uu____3107 -> t1
              | FStar_Syntax_Syntax.Tm_fvar uu____3108 -> t1
              | FStar_Syntax_Syntax.Tm_uvar uu____3109 ->
                  if (cfg.steps).check_no_uvars
                  then
                    let uu____3126 =
                      let uu____3127 =
                        FStar_Range.string_of_range
                          t1.FStar_Syntax_Syntax.pos
                         in
                      let uu____3128 = FStar_Syntax_Print.term_to_string t1
                         in
                      FStar_Util.format2
                        "(%s): CheckNoUvars: Unexpected unification variable remains: %s"
                        uu____3127 uu____3128
                       in
                    failwith uu____3126
                  else t1
              | FStar_Syntax_Syntax.Tm_type u ->
                  let uu____3131 =
                    let uu____3132 = norm_universe cfg env u  in
                    FStar_Syntax_Syntax.Tm_type uu____3132  in
                  mk uu____3131 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
                  let uu____3139 = FStar_List.map (norm_universe cfg env) us
                     in
                  FStar_Syntax_Syntax.mk_Tm_uinst t' uu____3139
              | FStar_Syntax_Syntax.Tm_bvar x ->
                  let uu____3141 = lookup_bvar env x  in
                  (match uu____3141 with
                   | Univ uu____3144 ->
                       failwith
                         "Impossible: term variable is bound to a universe"
                   | Dummy  -> t1
                   | Clos (env1,t0,uu____3147,uu____3148) ->
                       closure_as_term cfg env1 t0)
              | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                  let head2 = closure_as_term_delayed cfg env head1  in
                  let args1 = closures_as_args_delayed cfg env args  in
                  mk (FStar_Syntax_Syntax.Tm_app (head2, args1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
                  let uu____3260 = closures_as_binders_delayed cfg env bs  in
                  (match uu____3260 with
                   | (bs1,env1) ->
                       let body1 = closure_as_term_delayed cfg env1 body  in
                       let uu____3288 =
                         let uu____3289 =
                           let uu____3306 = close_lcomp_opt cfg env1 lopt  in
                           (bs1, body1, uu____3306)  in
                         FStar_Syntax_Syntax.Tm_abs uu____3289  in
                       mk uu____3288 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                  let uu____3337 = closures_as_binders_delayed cfg env bs  in
                  (match uu____3337 with
                   | (bs1,env1) ->
                       let c1 = close_comp cfg env1 c  in
                       mk (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
                         t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
                  let uu____3379 =
                    let uu____3390 =
                      let uu____3397 = FStar_Syntax_Syntax.mk_binder x  in
                      [uu____3397]  in
                    closures_as_binders_delayed cfg env uu____3390  in
                  (match uu____3379 with
                   | (x1,env1) ->
                       let phi1 = closure_as_term_delayed cfg env1 phi  in
                       let uu____3415 =
                         let uu____3416 =
                           let uu____3423 =
                             let uu____3424 = FStar_List.hd x1  in
                             FStar_All.pipe_right uu____3424
                               FStar_Pervasives_Native.fst
                              in
                           (uu____3423, phi1)  in
                         FStar_Syntax_Syntax.Tm_refine uu____3416  in
                       mk uu____3415 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_ascribed (t11,(annot,tacopt),lopt) ->
                  let annot1 =
                    match annot with
                    | FStar_Util.Inl t2 ->
                        let uu____3515 = closure_as_term_delayed cfg env t2
                           in
                        FStar_Util.Inl uu____3515
                    | FStar_Util.Inr c ->
                        let uu____3529 = close_comp cfg env c  in
                        FStar_Util.Inr uu____3529
                     in
                  let tacopt1 =
                    FStar_Util.map_opt tacopt
                      (closure_as_term_delayed cfg env)
                     in
                  let uu____3545 =
                    let uu____3546 =
                      let uu____3573 = closure_as_term_delayed cfg env t11
                         in
                      (uu____3573, (annot1, tacopt1), lopt)  in
                    FStar_Syntax_Syntax.Tm_ascribed uu____3546  in
                  mk uu____3545 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_pattern args) ->
                  let uu____3624 =
                    let uu____3625 =
                      let uu____3632 = closure_as_term_delayed cfg env t'  in
                      let uu____3635 =
                        let uu____3636 =
                          FStar_All.pipe_right args
                            (FStar_List.map
                               (closures_as_args_delayed cfg env))
                           in
                        FStar_Syntax_Syntax.Meta_pattern uu____3636  in
                      (uu____3632, uu____3635)  in
                    FStar_Syntax_Syntax.Tm_meta uu____3625  in
                  mk uu____3624 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic (m,tbody)) ->
                  let uu____3696 =
                    let uu____3697 =
                      let uu____3704 = closure_as_term_delayed cfg env t'  in
                      let uu____3707 =
                        let uu____3708 =
                          let uu____3715 =
                            closure_as_term_delayed cfg env tbody  in
                          (m, uu____3715)  in
                        FStar_Syntax_Syntax.Meta_monadic uu____3708  in
                      (uu____3704, uu____3707)  in
                    FStar_Syntax_Syntax.Tm_meta uu____3697  in
                  mk uu____3696 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,tbody)) ->
                  let uu____3734 =
                    let uu____3735 =
                      let uu____3742 = closure_as_term_delayed cfg env t'  in
                      let uu____3745 =
                        let uu____3746 =
                          let uu____3755 =
                            closure_as_term_delayed cfg env tbody  in
                          (m1, m2, uu____3755)  in
                        FStar_Syntax_Syntax.Meta_monadic_lift uu____3746  in
                      (uu____3742, uu____3745)  in
                    FStar_Syntax_Syntax.Tm_meta uu____3735  in
                  mk uu____3734 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_quoted (t'',qi)) ->
                  if qi.FStar_Syntax_Syntax.qopen
                  then
                    let uu____3773 =
                      let uu____3774 =
                        let uu____3781 = closure_as_term_delayed cfg env t'
                           in
                        let uu____3784 =
                          let uu____3785 =
                            let uu____3792 =
                              closure_as_term_delayed cfg env t''  in
                            (uu____3792, qi)  in
                          FStar_Syntax_Syntax.Meta_quoted uu____3785  in
                        (uu____3781, uu____3784)  in
                      FStar_Syntax_Syntax.Tm_meta uu____3774  in
                    mk uu____3773 t1.FStar_Syntax_Syntax.pos
                  else
                    (let uu____3800 =
                       let uu____3801 =
                         let uu____3808 = closure_as_term_delayed cfg env t'
                            in
                         (uu____3808,
                           (FStar_Syntax_Syntax.Meta_quoted (t'', qi)))
                          in
                       FStar_Syntax_Syntax.Tm_meta uu____3801  in
                     mk uu____3800 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_meta (t',m) ->
                  let uu____3821 =
                    let uu____3822 =
                      let uu____3829 = closure_as_term_delayed cfg env t'  in
                      (uu____3829, m)  in
                    FStar_Syntax_Syntax.Tm_meta uu____3822  in
                  mk uu____3821 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                  let env0 = env  in
                  let env1 =
                    FStar_List.fold_left
                      (fun env1  -> fun uu____3869  -> dummy :: env1) env
                      lb.FStar_Syntax_Syntax.lbunivs
                     in
                  let typ =
                    closure_as_term_delayed cfg env1
                      lb.FStar_Syntax_Syntax.lbtyp
                     in
                  let def =
                    closure_as_term cfg env1 lb.FStar_Syntax_Syntax.lbdef  in
                  let uu____3888 =
                    let uu____3899 = FStar_Syntax_Syntax.is_top_level [lb]
                       in
                    if uu____3899
                    then ((lb.FStar_Syntax_Syntax.lbname), body)
                    else
                      (let x = FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                          in
                       let uu____3918 =
                         closure_as_term cfg (dummy :: env0) body  in
                       ((FStar_Util.Inl
                           (let uu___122_3930 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___122_3930.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___122_3930.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = typ
                            })), uu____3918))
                     in
                  (match uu____3888 with
                   | (nm,body1) ->
                       let lb1 =
                         let uu___123_3946 = lb  in
                         {
                           FStar_Syntax_Syntax.lbname = nm;
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___123_3946.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp = typ;
                           FStar_Syntax_Syntax.lbeff =
                             (uu___123_3946.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef = def;
                           FStar_Syntax_Syntax.lbattrs =
                             (uu___123_3946.FStar_Syntax_Syntax.lbattrs);
                           FStar_Syntax_Syntax.lbpos =
                             (uu___123_3946.FStar_Syntax_Syntax.lbpos)
                         }  in
                       mk
                         (FStar_Syntax_Syntax.Tm_let ((false, [lb1]), body1))
                         t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_let ((uu____3957,lbs),body) ->
                  let norm_one_lb env1 lb =
                    let env_univs =
                      FStar_List.fold_right
                        (fun uu____4016  -> fun env2  -> dummy :: env2)
                        lb.FStar_Syntax_Syntax.lbunivs env1
                       in
                    let env2 =
                      let uu____4041 = FStar_Syntax_Syntax.is_top_level lbs
                         in
                      if uu____4041
                      then env_univs
                      else
                        FStar_List.fold_right
                          (fun uu____4061  -> fun env2  -> dummy :: env2) lbs
                          env_univs
                       in
                    let ty =
                      closure_as_term cfg env_univs
                        lb.FStar_Syntax_Syntax.lbtyp
                       in
                    let nm =
                      let uu____4083 = FStar_Syntax_Syntax.is_top_level lbs
                         in
                      if uu____4083
                      then lb.FStar_Syntax_Syntax.lbname
                      else
                        (let x =
                           FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                         FStar_All.pipe_right
                           (let uu___124_4095 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___124_4095.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___124_4095.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = ty
                            }) (fun _0_41  -> FStar_Util.Inl _0_41))
                       in
                    let uu___125_4096 = lb  in
                    let uu____4097 =
                      closure_as_term cfg env2 lb.FStar_Syntax_Syntax.lbdef
                       in
                    {
                      FStar_Syntax_Syntax.lbname = nm;
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___125_4096.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = ty;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___125_4096.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = uu____4097;
                      FStar_Syntax_Syntax.lbattrs =
                        (uu___125_4096.FStar_Syntax_Syntax.lbattrs);
                      FStar_Syntax_Syntax.lbpos =
                        (uu___125_4096.FStar_Syntax_Syntax.lbpos)
                    }  in
                  let lbs1 =
                    FStar_All.pipe_right lbs
                      (FStar_List.map (norm_one_lb env))
                     in
                  let body1 =
                    let body_env =
                      FStar_List.fold_right
                        (fun uu____4127  -> fun env1  -> dummy :: env1) lbs1
                        env
                       in
                    closure_as_term cfg body_env body  in
                  mk (FStar_Syntax_Syntax.Tm_let ((true, lbs1), body1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
                  let head2 = closure_as_term cfg env head1  in
                  let norm_one_branch env1 uu____4216 =
                    match uu____4216 with
                    | (pat,w_opt,tm) ->
                        let rec norm_pat env2 p =
                          match p.FStar_Syntax_Syntax.v with
                          | FStar_Syntax_Syntax.Pat_constant uu____4271 ->
                              (p, env2)
                          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                              let uu____4292 =
                                FStar_All.pipe_right pats
                                  (FStar_List.fold_left
                                     (fun uu____4352  ->
                                        fun uu____4353  ->
                                          match (uu____4352, uu____4353) with
                                          | ((pats1,env3),(p1,b)) ->
                                              let uu____4444 =
                                                norm_pat env3 p1  in
                                              (match uu____4444 with
                                               | (p2,env4) ->
                                                   (((p2, b) :: pats1), env4)))
                                     ([], env2))
                                 in
                              (match uu____4292 with
                               | (pats1,env3) ->
                                   ((let uu___126_4526 = p  in
                                     {
                                       FStar_Syntax_Syntax.v =
                                         (FStar_Syntax_Syntax.Pat_cons
                                            (fv, (FStar_List.rev pats1)));
                                       FStar_Syntax_Syntax.p =
                                         (uu___126_4526.FStar_Syntax_Syntax.p)
                                     }), env3))
                          | FStar_Syntax_Syntax.Pat_var x ->
                              let x1 =
                                let uu___127_4545 = x  in
                                let uu____4546 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort
                                   in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___127_4545.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___127_4545.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____4546
                                }  in
                              ((let uu___128_4560 = p  in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_var x1);
                                  FStar_Syntax_Syntax.p =
                                    (uu___128_4560.FStar_Syntax_Syntax.p)
                                }), (dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_wild x ->
                              let x1 =
                                let uu___129_4571 = x  in
                                let uu____4572 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort
                                   in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___129_4571.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___129_4571.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____4572
                                }  in
                              ((let uu___130_4586 = p  in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_wild x1);
                                  FStar_Syntax_Syntax.p =
                                    (uu___130_4586.FStar_Syntax_Syntax.p)
                                }), (dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                              let x1 =
                                let uu___131_4602 = x  in
                                let uu____4603 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort
                                   in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___131_4602.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___131_4602.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____4603
                                }  in
                              let t3 = closure_as_term cfg env2 t2  in
                              ((let uu___132_4610 = p  in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_dot_term
                                       (x1, t3));
                                  FStar_Syntax_Syntax.p =
                                    (uu___132_4610.FStar_Syntax_Syntax.p)
                                }), env2)
                           in
                        let uu____4613 = norm_pat env1 pat  in
                        (match uu____4613 with
                         | (pat1,env2) ->
                             let w_opt1 =
                               match w_opt with
                               | FStar_Pervasives_Native.None  ->
                                   FStar_Pervasives_Native.None
                               | FStar_Pervasives_Native.Some w ->
                                   let uu____4642 =
                                     closure_as_term cfg env2 w  in
                                   FStar_Pervasives_Native.Some uu____4642
                                in
                             let tm1 = closure_as_term cfg env2 tm  in
                             (pat1, w_opt1, tm1))
                     in
                  let uu____4648 =
                    let uu____4649 =
                      let uu____4672 =
                        FStar_All.pipe_right branches
                          (FStar_List.map (norm_one_branch env))
                         in
                      (head2, uu____4672)  in
                    FStar_Syntax_Syntax.Tm_match uu____4649  in
                  mk uu____4648 t1.FStar_Syntax_Syntax.pos))

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
        | uu____4758 -> closure_as_term cfg env t

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
        | uu____4784 ->
            FStar_List.map
              (fun uu____4801  ->
                 match uu____4801 with
                 | (x,imp) ->
                     let uu____4820 = closure_as_term_delayed cfg env x  in
                     (uu____4820, imp)) args

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
        let uu____4834 =
          FStar_All.pipe_right bs
            (FStar_List.fold_left
               (fun uu____4883  ->
                  fun uu____4884  ->
                    match (uu____4883, uu____4884) with
                    | ((env1,out),(b,imp)) ->
                        let b1 =
                          let uu___133_4954 = b  in
                          let uu____4955 =
                            closure_as_term_delayed cfg env1
                              b.FStar_Syntax_Syntax.sort
                             in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___133_4954.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___133_4954.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = uu____4955
                          }  in
                        let env2 = dummy :: env1  in
                        (env2, ((b1, imp) :: out))) (env, []))
           in
        match uu____4834 with | (env1,bs1) -> ((FStar_List.rev bs1), env1)

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
        | uu____5048 ->
            (match c.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Total (t,uopt) ->
                 let uu____5061 = closure_as_term_delayed cfg env t  in
                 let uu____5062 =
                   FStar_Option.map (norm_universe cfg env) uopt  in
                 FStar_Syntax_Syntax.mk_Total' uu____5061 uu____5062
             | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                 let uu____5075 = closure_as_term_delayed cfg env t  in
                 let uu____5076 =
                   FStar_Option.map (norm_universe cfg env) uopt  in
                 FStar_Syntax_Syntax.mk_GTotal' uu____5075 uu____5076
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
                        (fun uu___80_5102  ->
                           match uu___80_5102 with
                           | FStar_Syntax_Syntax.DECREASES t ->
                               let uu____5106 =
                                 closure_as_term_delayed cfg env t  in
                               FStar_Syntax_Syntax.DECREASES uu____5106
                           | f -> f))
                    in
                 let uu____5110 =
                   let uu___134_5111 = c1  in
                   let uu____5112 =
                     FStar_List.map (norm_universe cfg env)
                       c1.FStar_Syntax_Syntax.comp_univs
                      in
                   {
                     FStar_Syntax_Syntax.comp_univs = uu____5112;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___134_5111.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ = rt;
                     FStar_Syntax_Syntax.effect_args = args;
                     FStar_Syntax_Syntax.flags = flags1
                   }  in
                 FStar_Syntax_Syntax.mk_Comp uu____5110)

and (filter_out_lcomp_cflags :
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun flags1  ->
    FStar_All.pipe_right flags1
      (FStar_List.filter
         (fun uu___81_5122  ->
            match uu___81_5122 with
            | FStar_Syntax_Syntax.DECREASES uu____5123 -> false
            | uu____5126 -> true))

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
                   (fun uu___82_5144  ->
                      match uu___82_5144 with
                      | FStar_Syntax_Syntax.DECREASES uu____5145 -> false
                      | uu____5148 -> true))
               in
            let rc1 =
              let uu___135_5150 = rc  in
              let uu____5151 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (closure_as_term cfg env)
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___135_5150.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____5151;
                FStar_Syntax_Syntax.residual_flags = flags1
              }  in
            FStar_Pervasives_Native.Some rc1
        | uu____5158 -> lopt

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
    let uu____5243 = FStar_Syntax_Embeddings.unembed_list_safe u  in
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a) uu____5243  in
  let arg_as_bounded_int uu____5271 =
    match uu____5271 with
    | (a,uu____5283) ->
        let uu____5290 =
          let uu____5291 = FStar_Syntax_Subst.compress a  in
          uu____5291.FStar_Syntax_Syntax.n  in
        (match uu____5290 with
         | FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv1;
                FStar_Syntax_Syntax.pos = uu____5301;
                FStar_Syntax_Syntax.vars = uu____5302;_},({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_constant
                                                              (FStar_Const.Const_int
                                                              (i,FStar_Pervasives_Native.None
                                                               ));
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____5304;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____5305;_},uu____5306)::[])
             when
             FStar_Util.ends_with
               (FStar_Ident.text_of_lid
                  (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
               "int_to_t"
             ->
             let uu____5345 =
               let uu____5350 = FStar_BigInt.big_int_of_string i  in
               (fv1, uu____5350)  in
             FStar_Pervasives_Native.Some uu____5345
         | uu____5355 -> FStar_Pervasives_Native.None)
     in
  let lift_unary a b f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a)::[] ->
        let uu____5395 = f a  in FStar_Pervasives_Native.Some uu____5395
    | uu____5396 -> FStar_Pervasives_Native.None  in
  let lift_binary a b f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a0)::(FStar_Pervasives_Native.Some
        a1)::[] ->
        let uu____5444 = f a0 a1  in FStar_Pervasives_Native.Some uu____5444
    | uu____5445 -> FStar_Pervasives_Native.None  in
  let unary_op a416 a417 a418 a419 a420 =
    (Obj.magic
       (fun a  ->
          fun as_a  ->
            fun f  ->
              fun res  ->
                fun args  ->
                  let uu____5487 = FStar_List.map as_a args  in
                  lift_unary () ()
                    (fun a415  -> (Obj.magic (f res.psc_range)) a415)
                    uu____5487)) a416 a417 a418 a419 a420
     in
  let binary_op a423 a424 a425 a426 a427 =
    (Obj.magic
       (fun a  ->
          fun as_a  ->
            fun f  ->
              fun res  ->
                fun args  ->
                  let uu____5536 = FStar_List.map as_a args  in
                  lift_binary () ()
                    (fun a421  ->
                       fun a422  -> (Obj.magic (f res.psc_range)) a421 a422)
                    uu____5536)) a423 a424 a425 a426 a427
     in
  let as_primitive_step is_strong uu____5563 =
    match uu____5563 with
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
    unary_op () (fun a428  -> (Obj.magic arg_as_int) a428)
      (fun a429  ->
         fun a430  ->
           (Obj.magic
              (fun r  ->
                 fun x  ->
                   let uu____5611 = f x  in
                   FStar_Syntax_Embeddings.embed_int r uu____5611)) a429 a430)
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
                       let uu____5639 = f x y  in
                       FStar_Syntax_Embeddings.embed_int r uu____5639)) a432
               a433 a434)
     in
  let unary_bool_op f =
    unary_op () (fun a435  -> (Obj.magic arg_as_bool) a435)
      (fun a436  ->
         fun a437  ->
           (Obj.magic
              (fun r  ->
                 fun x  ->
                   let uu____5660 = f x  in
                   FStar_Syntax_Embeddings.embed_bool r uu____5660)) a436
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
                       let uu____5688 = f x y  in
                       FStar_Syntax_Embeddings.embed_bool r uu____5688)) a439
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
                       let uu____5716 = f x y  in
                       FStar_Syntax_Embeddings.embed_string r uu____5716))
               a443 a444 a445)
     in
  let mixed_binary_op a b c as_a as_b embed_c f res args =
    match args with
    | a::b::[] ->
        let uu____5824 =
          let uu____5833 = as_a a  in
          let uu____5836 = as_b b  in (uu____5833, uu____5836)  in
        (match uu____5824 with
         | (FStar_Pervasives_Native.Some a1,FStar_Pervasives_Native.Some b1)
             ->
             let uu____5851 =
               let uu____5852 = f res.psc_range a1 b1  in
               embed_c res.psc_range uu____5852  in
             FStar_Pervasives_Native.Some uu____5851
         | uu____5853 -> FStar_Pervasives_Native.None)
    | uu____5862 -> FStar_Pervasives_Native.None  in
  let list_of_string' rng s =
    let name l =
      let uu____5876 =
        let uu____5877 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant
            FStar_Pervasives_Native.None
           in
        FStar_Syntax_Syntax.Tm_fvar uu____5877  in
      mk uu____5876 rng  in
    let char_t = name FStar_Parser_Const.char_lid  in
    let charterm c =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c)) rng  in
    let uu____5887 =
      let uu____5890 = FStar_String.list_of_string s  in
      FStar_List.map charterm uu____5890  in
    FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu____5887  in
  let string_of_list' rng l =
    let s = FStar_String.string_of_list l  in FStar_Syntax_Util.exp_string s
     in
  let string_compare' rng s1 s2 =
    let r = FStar_String.compare s1 s2  in
    let uu____5922 =
      let uu____5923 = FStar_Util.string_of_int r  in
      FStar_BigInt.big_int_of_string uu____5923  in
    FStar_Syntax_Embeddings.embed_int rng uu____5922  in
  let string_concat' psc args =
    match args with
    | a1::a2::[] ->
        let uu____5941 = arg_as_string a1  in
        (match uu____5941 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____5947 =
               Obj.magic
                 (arg_as_list ()
                    (Obj.magic FStar_Syntax_Embeddings.unembed_string_safe)
                    a2)
                in
             (match uu____5947 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2  in
                  let uu____5960 =
                    FStar_Syntax_Embeddings.embed_string psc.psc_range r  in
                  FStar_Pervasives_Native.Some uu____5960
              | uu____5961 -> FStar_Pervasives_Native.None)
         | uu____5966 -> FStar_Pervasives_Native.None)
    | uu____5969 -> FStar_Pervasives_Native.None  in
  let string_of_int1 rng i =
    let uu____5979 = FStar_BigInt.string_of_big_int i  in
    FStar_Syntax_Embeddings.embed_string rng uu____5979  in
  let string_of_bool1 rng b =
    FStar_Syntax_Embeddings.embed_string rng (if b then "true" else "false")
     in
  let mk_range1 psc args =
    match args with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____6008 =
          let uu____6029 = arg_as_string fn  in
          let uu____6032 = arg_as_int from_line  in
          let uu____6035 = arg_as_int from_col  in
          let uu____6038 = arg_as_int to_line  in
          let uu____6041 = arg_as_int to_col  in
          (uu____6029, uu____6032, uu____6035, uu____6038, uu____6041)  in
        (match uu____6008 with
         | (FStar_Pervasives_Native.Some fn1,FStar_Pervasives_Native.Some
            from_l,FStar_Pervasives_Native.Some
            from_c,FStar_Pervasives_Native.Some
            to_l,FStar_Pervasives_Native.Some to_c) ->
             let r =
               let uu____6072 =
                 let uu____6073 = FStar_BigInt.to_int_fs from_l  in
                 let uu____6074 = FStar_BigInt.to_int_fs from_c  in
                 FStar_Range.mk_pos uu____6073 uu____6074  in
               let uu____6075 =
                 let uu____6076 = FStar_BigInt.to_int_fs to_l  in
                 let uu____6077 = FStar_BigInt.to_int_fs to_c  in
                 FStar_Range.mk_pos uu____6076 uu____6077  in
               FStar_Range.mk_range fn1 uu____6072 uu____6075  in
             let uu____6078 =
               FStar_Syntax_Embeddings.embed_range psc.psc_range r  in
             FStar_Pervasives_Native.Some uu____6078
         | uu____6079 -> FStar_Pervasives_Native.None)
    | uu____6100 -> FStar_Pervasives_Native.None  in
  let decidable_eq neg psc args =
    let r = psc.psc_range  in
    let tru =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool true)) r
       in
    let fal =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool false)) r
       in
    match args with
    | (_typ,uu____6127)::(a1,uu____6129)::(a2,uu____6131)::[] ->
        let uu____6168 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____6168 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some (if neg then fal else tru)
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some (if neg then tru else fal)
         | uu____6181 -> FStar_Pervasives_Native.None)
    | uu____6182 -> failwith "Unexpected number of arguments"  in
  let prims_to_fstar_range_step psc args =
    match args with
    | (a1,uu____6209)::[] ->
        let uu____6218 = FStar_Syntax_Embeddings.unembed_range_safe a1  in
        (match uu____6218 with
         | FStar_Pervasives_Native.Some r ->
             let uu____6224 =
               FStar_Syntax_Embeddings.embed_range psc.psc_range r  in
             FStar_Pervasives_Native.Some uu____6224
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
    | uu____6225 -> failwith "Unexpected number of arguments"  in
  let basic_ops =
    let uu____6249 =
      let uu____6264 =
        let uu____6279 =
          let uu____6294 =
            let uu____6309 =
              let uu____6324 =
                let uu____6339 =
                  let uu____6354 =
                    let uu____6369 =
                      let uu____6384 =
                        let uu____6399 =
                          let uu____6414 =
                            let uu____6429 =
                              let uu____6444 =
                                let uu____6459 =
                                  let uu____6474 =
                                    let uu____6489 =
                                      let uu____6504 =
                                        let uu____6519 =
                                          let uu____6534 =
                                            let uu____6549 =
                                              let uu____6564 =
                                                let uu____6577 =
                                                  FStar_Parser_Const.p2l
                                                    ["FStar";
                                                    "String";
                                                    "list_of_string"]
                                                   in
                                                (uu____6577,
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
                                              let uu____6584 =
                                                let uu____6599 =
                                                  let uu____6612 =
                                                    FStar_Parser_Const.p2l
                                                      ["FStar";
                                                      "String";
                                                      "string_of_list"]
                                                     in
                                                  (uu____6612,
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
                                                let uu____6619 =
                                                  let uu____6634 =
                                                    let uu____6649 =
                                                      FStar_Parser_Const.p2l
                                                        ["FStar";
                                                        "String";
                                                        "concat"]
                                                       in
                                                    (uu____6649,
                                                      (Prims.parse_int "2"),
                                                      string_concat')
                                                     in
                                                  let uu____6658 =
                                                    let uu____6675 =
                                                      let uu____6690 =
                                                        FStar_Parser_Const.p2l
                                                          ["Prims";
                                                          "mk_range"]
                                                         in
                                                      (uu____6690,
                                                        (Prims.parse_int "5"),
                                                        mk_range1)
                                                       in
                                                    [uu____6675]  in
                                                  uu____6634 :: uu____6658
                                                   in
                                                uu____6599 :: uu____6619  in
                                              uu____6564 :: uu____6584  in
                                            (FStar_Parser_Const.op_notEq,
                                              (Prims.parse_int "3"),
                                              (decidable_eq true)) ::
                                              uu____6549
                                             in
                                          (FStar_Parser_Const.op_Eq,
                                            (Prims.parse_int "3"),
                                            (decidable_eq false)) ::
                                            uu____6534
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
                                          :: uu____6519
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
                                        :: uu____6504
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
                                      :: uu____6489
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
                                                        let uu____6881 =
                                                          FStar_BigInt.to_int_fs
                                                            x
                                                           in
                                                        FStar_String.make
                                                          uu____6881 y)) a466
                                                a467 a468)))
                                    :: uu____6474
                                   in
                                (FStar_Parser_Const.strcat_lid',
                                  (Prims.parse_int "2"),
                                  (binary_string_op
                                     (fun x  -> fun y  -> Prims.strcat x y)))
                                  :: uu____6459
                                 in
                              (FStar_Parser_Const.strcat_lid,
                                (Prims.parse_int "2"),
                                (binary_string_op
                                   (fun x  -> fun y  -> Prims.strcat x y)))
                                :: uu____6444
                               in
                            (FStar_Parser_Const.op_Or, (Prims.parse_int "2"),
                              (binary_bool_op (fun x  -> fun y  -> x || y)))
                              :: uu____6429
                             in
                          (FStar_Parser_Const.op_And, (Prims.parse_int "2"),
                            (binary_bool_op (fun x  -> fun y  -> x && y))) ::
                            uu____6414
                           in
                        (FStar_Parser_Const.op_Negation,
                          (Prims.parse_int "1"),
                          (unary_bool_op (fun x  -> Prims.op_Negation x))) ::
                          uu____6399
                         in
                      (FStar_Parser_Const.op_Modulus, (Prims.parse_int "2"),
                        (binary_int_op
                           (fun x  -> fun y  -> FStar_BigInt.mod_big_int x y)))
                        :: uu____6384
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
                                          let uu____7048 =
                                            FStar_BigInt.ge_big_int x y  in
                                          FStar_Syntax_Embeddings.embed_bool
                                            r uu____7048)) a470 a471 a472)))
                      :: uu____6369
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
                                        let uu____7074 =
                                          FStar_BigInt.gt_big_int x y  in
                                        FStar_Syntax_Embeddings.embed_bool r
                                          uu____7074)) a474 a475 a476)))
                    :: uu____6354
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
                                      let uu____7100 =
                                        FStar_BigInt.le_big_int x y  in
                                      FStar_Syntax_Embeddings.embed_bool r
                                        uu____7100)) a478 a479 a480)))
                  :: uu____6339
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
                                    let uu____7126 =
                                      FStar_BigInt.lt_big_int x y  in
                                    FStar_Syntax_Embeddings.embed_bool r
                                      uu____7126)) a482 a483 a484)))
                :: uu____6324
               in
            (FStar_Parser_Const.op_Division, (Prims.parse_int "2"),
              (binary_int_op
                 (fun x  -> fun y  -> FStar_BigInt.div_big_int x y)))
              :: uu____6309
             in
          (FStar_Parser_Const.op_Multiply, (Prims.parse_int "2"),
            (binary_int_op
               (fun x  -> fun y  -> FStar_BigInt.mult_big_int x y)))
            :: uu____6294
           in
        (FStar_Parser_Const.op_Subtraction, (Prims.parse_int "2"),
          (binary_int_op (fun x  -> fun y  -> FStar_BigInt.sub_big_int x y)))
          :: uu____6279
         in
      (FStar_Parser_Const.op_Addition, (Prims.parse_int "2"),
        (binary_int_op (fun x  -> fun y  -> FStar_BigInt.add_big_int x y)))
        :: uu____6264
       in
    (FStar_Parser_Const.op_Minus, (Prims.parse_int "1"),
      (unary_int_op (fun x  -> FStar_BigInt.minus_big_int x))) :: uu____6249
     in
  let weak_ops =
    let uu____7265 =
      let uu____7284 =
        FStar_Parser_Const.p2l ["FStar"; "Range"; "prims_to_fstar_range"]  in
      (uu____7284, (Prims.parse_int "1"), prims_to_fstar_range_step)  in
    [uu____7265]  in
  let bounded_arith_ops =
    let bounded_signed_int_types = ["Int8"; "Int16"; "Int32"; "Int64"]  in
    let bounded_unsigned_int_types =
      ["UInt8"; "UInt16"; "UInt32"; "UInt64"; "UInt128"]  in
    let int_as_bounded r int_to_t1 n1 =
      let c = FStar_Syntax_Embeddings.embed_int r n1  in
      let int_to_t2 = FStar_Syntax_Syntax.fv_to_tm int_to_t1  in
      let uu____7368 =
        let uu____7369 =
          let uu____7370 = FStar_Syntax_Syntax.as_arg c  in [uu____7370]  in
        FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____7369  in
      uu____7368 FStar_Pervasives_Native.None r  in
    let add_sub_mul_v =
      FStar_All.pipe_right
        (FStar_List.append bounded_signed_int_types
           bounded_unsigned_int_types)
        (FStar_List.collect
           (fun m  ->
              let uu____7420 =
                let uu____7433 = FStar_Parser_Const.p2l ["FStar"; m; "add"]
                   in
                (uu____7433, (Prims.parse_int "2"),
                  (binary_op ()
                     (fun a485  -> (Obj.magic arg_as_bounded_int) a485)
                     (fun a486  ->
                        fun a487  ->
                          fun a488  ->
                            (Obj.magic
                               (fun r  ->
                                  fun uu____7449  ->
                                    fun uu____7450  ->
                                      match (uu____7449, uu____7450) with
                                      | ((int_to_t1,x),(uu____7469,y)) ->
                                          let uu____7479 =
                                            FStar_BigInt.add_big_int x y  in
                                          int_as_bounded r int_to_t1
                                            uu____7479)) a486 a487 a488)))
                 in
              let uu____7480 =
                let uu____7495 =
                  let uu____7508 = FStar_Parser_Const.p2l ["FStar"; m; "sub"]
                     in
                  (uu____7508, (Prims.parse_int "2"),
                    (binary_op ()
                       (fun a489  -> (Obj.magic arg_as_bounded_int) a489)
                       (fun a490  ->
                          fun a491  ->
                            fun a492  ->
                              (Obj.magic
                                 (fun r  ->
                                    fun uu____7524  ->
                                      fun uu____7525  ->
                                        match (uu____7524, uu____7525) with
                                        | ((int_to_t1,x),(uu____7544,y)) ->
                                            let uu____7554 =
                                              FStar_BigInt.sub_big_int x y
                                               in
                                            int_as_bounded r int_to_t1
                                              uu____7554)) a490 a491 a492)))
                   in
                let uu____7555 =
                  let uu____7570 =
                    let uu____7583 =
                      FStar_Parser_Const.p2l ["FStar"; m; "mul"]  in
                    (uu____7583, (Prims.parse_int "2"),
                      (binary_op ()
                         (fun a493  -> (Obj.magic arg_as_bounded_int) a493)
                         (fun a494  ->
                            fun a495  ->
                              fun a496  ->
                                (Obj.magic
                                   (fun r  ->
                                      fun uu____7599  ->
                                        fun uu____7600  ->
                                          match (uu____7599, uu____7600) with
                                          | ((int_to_t1,x),(uu____7619,y)) ->
                                              let uu____7629 =
                                                FStar_BigInt.mult_big_int x y
                                                 in
                                              int_as_bounded r int_to_t1
                                                uu____7629)) a494 a495 a496)))
                     in
                  let uu____7630 =
                    let uu____7645 =
                      let uu____7658 =
                        FStar_Parser_Const.p2l ["FStar"; m; "v"]  in
                      (uu____7658, (Prims.parse_int "1"),
                        (unary_op ()
                           (fun a497  -> (Obj.magic arg_as_bounded_int) a497)
                           (fun a498  ->
                              fun a499  ->
                                (Obj.magic
                                   (fun r  ->
                                      fun uu____7670  ->
                                        match uu____7670 with
                                        | (int_to_t1,x) ->
                                            FStar_Syntax_Embeddings.embed_int
                                              r x)) a498 a499)))
                       in
                    [uu____7645]  in
                  uu____7570 :: uu____7630  in
                uu____7495 :: uu____7555  in
              uu____7420 :: uu____7480))
       in
    let div_mod_unsigned =
      FStar_All.pipe_right bounded_unsigned_int_types
        (FStar_List.collect
           (fun m  ->
              let uu____7784 =
                let uu____7797 = FStar_Parser_Const.p2l ["FStar"; m; "div"]
                   in
                (uu____7797, (Prims.parse_int "2"),
                  (binary_op ()
                     (fun a500  -> (Obj.magic arg_as_bounded_int) a500)
                     (fun a501  ->
                        fun a502  ->
                          fun a503  ->
                            (Obj.magic
                               (fun r  ->
                                  fun uu____7813  ->
                                    fun uu____7814  ->
                                      match (uu____7813, uu____7814) with
                                      | ((int_to_t1,x),(uu____7833,y)) ->
                                          let uu____7843 =
                                            FStar_BigInt.div_big_int x y  in
                                          int_as_bounded r int_to_t1
                                            uu____7843)) a501 a502 a503)))
                 in
              let uu____7844 =
                let uu____7859 =
                  let uu____7872 = FStar_Parser_Const.p2l ["FStar"; m; "rem"]
                     in
                  (uu____7872, (Prims.parse_int "2"),
                    (binary_op ()
                       (fun a504  -> (Obj.magic arg_as_bounded_int) a504)
                       (fun a505  ->
                          fun a506  ->
                            fun a507  ->
                              (Obj.magic
                                 (fun r  ->
                                    fun uu____7888  ->
                                      fun uu____7889  ->
                                        match (uu____7888, uu____7889) with
                                        | ((int_to_t1,x),(uu____7908,y)) ->
                                            let uu____7918 =
                                              FStar_BigInt.mod_big_int x y
                                               in
                                            int_as_bounded r int_to_t1
                                              uu____7918)) a505 a506 a507)))
                   in
                [uu____7859]  in
              uu____7784 :: uu____7844))
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
    | (_typ,uu____8030)::(a1,uu____8032)::(a2,uu____8034)::[] ->
        let uu____8071 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____8071 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___136_8077 = FStar_Syntax_Util.t_true  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___136_8077.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___136_8077.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___137_8081 = FStar_Syntax_Util.t_false  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___137_8081.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___137_8081.FStar_Syntax_Syntax.vars)
                })
         | uu____8082 -> FStar_Pervasives_Native.None)
    | (_typ,uu____8084)::uu____8085::(a1,uu____8087)::(a2,uu____8089)::[] ->
        let uu____8138 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____8138 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___136_8144 = FStar_Syntax_Util.t_true  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___136_8144.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___136_8144.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___137_8148 = FStar_Syntax_Util.t_false  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___137_8148.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___137_8148.FStar_Syntax_Syntax.vars)
                })
         | uu____8149 -> FStar_Pervasives_Native.None)
    | uu____8150 -> failwith "Unexpected number of arguments"  in
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
  FStar_Syntax_Syntax.binder FStar_Syntax_Embeddings.unembedder
    FStar_Pervasives_Native.option FStar_ST.ref)
  = FStar_Util.mk_ref FStar_Pervasives_Native.None 
let (unembed_binder :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____8202 = FStar_ST.op_Bang unembed_binder_knot  in
    match uu____8202 with
    | FStar_Pervasives_Native.Some f -> f t
    | FStar_Pervasives_Native.None  ->
        (FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos
           (FStar_Errors.Warning_UnembedBinderKnot,
             "unembed_binder_knot is unset!");
         FStar_Pervasives_Native.None)
  
let mk_psc_subst :
  'Auu____8249 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____8249) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_Syntax_Syntax.subst_elt Prims.list
  =
  fun cfg  ->
    fun env  ->
      FStar_List.fold_right
        (fun uu____8309  ->
           fun subst1  ->
             match uu____8309 with
             | (binder_opt,closure) ->
                 (match (binder_opt, closure) with
                  | (FStar_Pervasives_Native.Some b,Clos
                     (env1,term,uu____8350,uu____8351)) ->
                      let uu____8410 = b  in
                      (match uu____8410 with
                       | (bv,uu____8418) ->
                           let uu____8419 =
                             let uu____8420 =
                               FStar_Syntax_Util.is_constructed_typ
                                 bv.FStar_Syntax_Syntax.sort
                                 FStar_Parser_Const.binder_lid
                                in
                             Prims.op_Negation uu____8420  in
                           if uu____8419
                           then subst1
                           else
                             (let term1 = closure_as_term cfg env1 term  in
                              let uu____8425 = unembed_binder term1  in
                              match uu____8425 with
                              | FStar_Pervasives_Native.None  -> subst1
                              | FStar_Pervasives_Native.Some x ->
                                  let b1 =
                                    let uu____8432 =
                                      let uu___138_8433 = bv  in
                                      let uu____8434 =
                                        FStar_Syntax_Subst.subst subst1
                                          (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort
                                         in
                                      {
                                        FStar_Syntax_Syntax.ppname =
                                          (uu___138_8433.FStar_Syntax_Syntax.ppname);
                                        FStar_Syntax_Syntax.index =
                                          (uu___138_8433.FStar_Syntax_Syntax.index);
                                        FStar_Syntax_Syntax.sort = uu____8434
                                      }  in
                                    FStar_Syntax_Syntax.freshen_bv uu____8432
                                     in
                                  let b_for_x =
                                    let uu____8438 =
                                      let uu____8445 =
                                        FStar_Syntax_Syntax.bv_to_name b1  in
                                      ((FStar_Pervasives_Native.fst x),
                                        uu____8445)
                                       in
                                    FStar_Syntax_Syntax.NT uu____8438  in
                                  let subst2 =
                                    FStar_List.filter
                                      (fun uu___83_8454  ->
                                         match uu___83_8454 with
                                         | FStar_Syntax_Syntax.NT
                                             (uu____8455,{
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_name
                                                             b';
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____8457;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____8458;_})
                                             ->
                                             Prims.op_Negation
                                               (FStar_Ident.ident_equals
                                                  b1.FStar_Syntax_Syntax.ppname
                                                  b'.FStar_Syntax_Syntax.ppname)
                                         | uu____8463 -> true) subst1
                                     in
                                  b_for_x :: subst2))
                  | uu____8464 -> subst1)) env []
  
let reduce_primops :
  'Auu____8481 'Auu____8482 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____8481) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____8482 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          if Prims.op_Negation (cfg.steps).primops
          then tm
          else
            (let uu____8524 = FStar_Syntax_Util.head_and_args tm  in
             match uu____8524 with
             | (head1,args) ->
                 let uu____8561 =
                   let uu____8562 = FStar_Syntax_Util.un_uinst head1  in
                   uu____8562.FStar_Syntax_Syntax.n  in
                 (match uu____8561 with
                  | FStar_Syntax_Syntax.Tm_fvar fv ->
                      let uu____8566 = find_prim_step cfg fv  in
                      (match uu____8566 with
                       | FStar_Pervasives_Native.Some prim_step when
                           prim_step.strong_reduction_ok ||
                             (Prims.op_Negation cfg.strong)
                           ->
                           if (FStar_List.length args) < prim_step.arity
                           then
                             (log_primops cfg
                                (fun uu____8581  ->
                                   let uu____8582 =
                                     FStar_Syntax_Print.lid_to_string
                                       prim_step.name
                                      in
                                   let uu____8583 =
                                     FStar_Util.string_of_int
                                       (FStar_List.length args)
                                      in
                                   let uu____8590 =
                                     FStar_Util.string_of_int prim_step.arity
                                      in
                                   FStar_Util.print3
                                     "primop: found partially applied %s (%s/%s args)\n"
                                     uu____8582 uu____8583 uu____8590);
                              tm)
                           else
                             (log_primops cfg
                                (fun uu____8595  ->
                                   let uu____8596 =
                                     FStar_Syntax_Print.term_to_string tm  in
                                   FStar_Util.print1
                                     "primop: trying to reduce <%s>\n"
                                     uu____8596);
                              (let psc =
                                 {
                                   psc_range =
                                     (head1.FStar_Syntax_Syntax.pos);
                                   psc_subst =
                                     (fun uu____8599  ->
                                        if
                                          prim_step.requires_binder_substitution
                                        then mk_psc_subst cfg env
                                        else [])
                                 }  in
                               let uu____8601 =
                                 prim_step.interpretation psc args  in
                               match uu____8601 with
                               | FStar_Pervasives_Native.None  ->
                                   (log_primops cfg
                                      (fun uu____8607  ->
                                         let uu____8608 =
                                           FStar_Syntax_Print.term_to_string
                                             tm
                                            in
                                         FStar_Util.print1
                                           "primop: <%s> did not reduce\n"
                                           uu____8608);
                                    tm)
                               | FStar_Pervasives_Native.Some reduced ->
                                   (log_primops cfg
                                      (fun uu____8614  ->
                                         let uu____8615 =
                                           FStar_Syntax_Print.term_to_string
                                             tm
                                            in
                                         let uu____8616 =
                                           FStar_Syntax_Print.term_to_string
                                             reduced
                                            in
                                         FStar_Util.print2
                                           "primop: <%s> reduced to <%s>\n"
                                           uu____8615 uu____8616);
                                    reduced)))
                       | FStar_Pervasives_Native.Some uu____8617 ->
                           (log_primops cfg
                              (fun uu____8621  ->
                                 let uu____8622 =
                                   FStar_Syntax_Print.term_to_string tm  in
                                 FStar_Util.print1
                                   "primop: not reducing <%s> since we're doing strong reduction\n"
                                   uu____8622);
                            tm)
                       | FStar_Pervasives_Native.None  -> tm)
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_range_of ) when
                      Prims.op_Negation cfg.strong ->
                      (log_primops cfg
                         (fun uu____8626  ->
                            let uu____8627 =
                              FStar_Syntax_Print.term_to_string tm  in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____8627);
                       (match args with
                        | (a1,uu____8629)::[] ->
                            FStar_Syntax_Embeddings.embed_range
                              tm.FStar_Syntax_Syntax.pos
                              a1.FStar_Syntax_Syntax.pos
                        | uu____8646 -> tm))
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_set_range_of ) when
                      Prims.op_Negation cfg.strong ->
                      (log_primops cfg
                         (fun uu____8658  ->
                            let uu____8659 =
                              FStar_Syntax_Print.term_to_string tm  in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____8659);
                       (match args with
                        | (t,uu____8661)::(r,uu____8663)::[] ->
                            let uu____8690 =
                              FStar_Syntax_Embeddings.unembed_range r  in
                            (match uu____8690 with
                             | FStar_Pervasives_Native.Some rng ->
                                 let uu___139_8694 = t  in
                                 {
                                   FStar_Syntax_Syntax.n =
                                     (uu___139_8694.FStar_Syntax_Syntax.n);
                                   FStar_Syntax_Syntax.pos = rng;
                                   FStar_Syntax_Syntax.vars =
                                     (uu___139_8694.FStar_Syntax_Syntax.vars)
                                 }
                             | FStar_Pervasives_Native.None  -> tm)
                        | uu____8697 -> tm))
                  | uu____8706 -> tm))
  
let reduce_equality :
  'Auu____8711 'Auu____8712 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____8711) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____8712 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun tm  ->
      reduce_primops
        (let uu___140_8750 = cfg  in
         {
           steps =
             (let uu___141_8753 = default_steps  in
              {
                beta = (uu___141_8753.beta);
                iota = (uu___141_8753.iota);
                zeta = (uu___141_8753.zeta);
                weak = (uu___141_8753.weak);
                hnf = (uu___141_8753.hnf);
                primops = true;
                no_delta_steps = (uu___141_8753.no_delta_steps);
                unfold_until = (uu___141_8753.unfold_until);
                unfold_only = (uu___141_8753.unfold_only);
                unfold_attr = (uu___141_8753.unfold_attr);
                unfold_tac = (uu___141_8753.unfold_tac);
                pure_subterms_within_computations =
                  (uu___141_8753.pure_subterms_within_computations);
                simplify = (uu___141_8753.simplify);
                erase_universes = (uu___141_8753.erase_universes);
                allow_unbound_universes =
                  (uu___141_8753.allow_unbound_universes);
                reify_ = (uu___141_8753.reify_);
                compress_uvars = (uu___141_8753.compress_uvars);
                no_full_norm = (uu___141_8753.no_full_norm);
                check_no_uvars = (uu___141_8753.check_no_uvars);
                unmeta = (uu___141_8753.unmeta);
                unascribe = (uu___141_8753.unascribe)
              });
           tcenv = (uu___140_8750.tcenv);
           debug = (uu___140_8750.debug);
           delta_level = (uu___140_8750.delta_level);
           primitive_steps = equality_ops;
           strong = (uu___140_8750.strong);
           memoize_lazy = (uu___140_8750.memoize_lazy);
           normalize_pure_lets = (uu___140_8750.normalize_pure_lets)
         }) tm
  
let is_norm_request :
  'Auu____8757 .
    FStar_Syntax_Syntax.term -> 'Auu____8757 Prims.list -> Prims.bool
  =
  fun hd1  ->
    fun args  ->
      let uu____8770 =
        let uu____8777 =
          let uu____8778 = FStar_Syntax_Util.un_uinst hd1  in
          uu____8778.FStar_Syntax_Syntax.n  in
        (uu____8777, args)  in
      match uu____8770 with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____8784::uu____8785::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____8789::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize
      | (FStar_Syntax_Syntax.Tm_fvar fv,steps::uu____8794::uu____8795::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm
      | uu____8798 -> false
  
let (tr_norm_step : FStar_Syntax_Embeddings.norm_step -> step Prims.list) =
  fun uu___84_8809  ->
    match uu___84_8809 with
    | FStar_Syntax_Embeddings.Zeta  -> [Zeta]
    | FStar_Syntax_Embeddings.Iota  -> [Iota]
    | FStar_Syntax_Embeddings.Delta  ->
        [UnfoldUntil FStar_Syntax_Syntax.Delta_constant]
    | FStar_Syntax_Embeddings.Simpl  -> [Simplify]
    | FStar_Syntax_Embeddings.Weak  -> [Weak]
    | FStar_Syntax_Embeddings.HNF  -> [HNF]
    | FStar_Syntax_Embeddings.Primops  -> [Primops]
    | FStar_Syntax_Embeddings.UnfoldOnly names1 ->
        let uu____8815 =
          let uu____8818 =
            let uu____8819 = FStar_List.map FStar_Ident.lid_of_str names1  in
            UnfoldOnly uu____8819  in
          [uu____8818]  in
        (UnfoldUntil FStar_Syntax_Syntax.Delta_constant) :: uu____8815
    | FStar_Syntax_Embeddings.UnfoldAttr t ->
        [UnfoldUntil FStar_Syntax_Syntax.Delta_constant; UnfoldAttr t]
  
let (tr_norm_steps :
  FStar_Syntax_Embeddings.norm_step Prims.list -> step Prims.list) =
  fun s  -> FStar_List.concatMap tr_norm_step s 
let get_norm_request :
  'Auu____8835 .
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
      (FStar_Syntax_Syntax.term,'Auu____8835) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (step Prims.list,FStar_Syntax_Syntax.term)
          FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun full_norm  ->
    fun args  ->
      let parse_steps s =
        try
          let uu____8888 =
            let uu____8891 =
              let uu____8894 =
                let uu____8899 =
                  FStar_Syntax_Embeddings.unembed_list_safe
                    FStar_Syntax_Embeddings.unembed_norm_step
                   in
                uu____8899 s  in
              FStar_All.pipe_right uu____8894 FStar_Util.must  in
            FStar_All.pipe_right uu____8891 tr_norm_steps  in
          FStar_Pervasives_Native.Some uu____8888
        with | uu____8927 -> FStar_Pervasives_Native.None  in
      match args with
      | uu____8938::(tm,uu____8940)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify]  in
          FStar_Pervasives_Native.Some (s, tm)
      | (tm,uu____8969)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify]  in
          FStar_Pervasives_Native.Some (s, tm)
      | (steps,uu____8990)::uu____8991::(tm,uu____8993)::[] ->
          let add_exclude s z =
            if FStar_List.contains z s then s else (Exclude z) :: s  in
          let uu____9030 =
            let uu____9035 = full_norm steps  in parse_steps uu____9035  in
          (match uu____9030 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some s ->
               let s1 = Beta :: s  in
               let s2 = add_exclude s1 Zeta  in
               let s3 = add_exclude s2 Iota  in
               FStar_Pervasives_Native.Some (s3, tm))
      | uu____9074 -> FStar_Pervasives_Native.None
  
let (is_reify_head : stack_elt Prims.list -> Prims.bool) =
  fun uu___85_9091  ->
    match uu___85_9091 with
    | (App
        (uu____9094,{
                      FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                        (FStar_Const.Const_reify );
                      FStar_Syntax_Syntax.pos = uu____9095;
                      FStar_Syntax_Syntax.vars = uu____9096;_},uu____9097,uu____9098))::uu____9099
        -> true
    | uu____9106 -> false
  
let firstn :
  'Auu____9112 .
    Prims.int ->
      'Auu____9112 Prims.list ->
        ('Auu____9112 Prims.list,'Auu____9112 Prims.list)
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
          (uu____9148,{
                        FStar_Syntax_Syntax.n =
                          FStar_Syntax_Syntax.Tm_constant
                          (FStar_Const.Const_reify );
                        FStar_Syntax_Syntax.pos = uu____9149;
                        FStar_Syntax_Syntax.vars = uu____9150;_},uu____9151,uu____9152))::uu____9153
          -> (cfg.steps).reify_
      | uu____9160 -> false
  
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
               | FStar_Syntax_Syntax.Tm_delayed uu____9344 ->
                   let uu____9369 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print1 "NORM delayed: %s\n" uu____9369
               | uu____9370 -> ())
            else ();
            FStar_Syntax_Subst.compress t  in
          log cfg
            (fun uu____9378  ->
               let uu____9379 = FStar_Syntax_Print.tag_of_term t1  in
               let uu____9380 = FStar_Syntax_Print.term_to_string t1  in
               let uu____9381 =
                 FStar_Util.string_of_int (FStar_List.length env)  in
               let uu____9388 =
                 let uu____9389 =
                   let uu____9392 = firstn (Prims.parse_int "4") stack  in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst uu____9392
                    in
                 stack_to_string uu____9389  in
               FStar_Util.print4
                 ">>> %s\nNorm %s with with %s env elements top of the stack %s \n"
                 uu____9379 uu____9380 uu____9381 uu____9388);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_constant uu____9415 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_name uu____9416 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_lazy uu____9417 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____9418;
                 FStar_Syntax_Syntax.fv_delta =
                   FStar_Syntax_Syntax.Delta_constant ;
                 FStar_Syntax_Syntax.fv_qual = uu____9419;_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____9422;
                 FStar_Syntax_Syntax.fv_delta = uu____9423;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Data_ctor );_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____9424;
                 FStar_Syntax_Syntax.fv_delta = uu____9425;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor uu____9426);_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_meta
               (t0,FStar_Syntax_Syntax.Meta_quoted (t11,qi)) ->
               let t01 = closure_as_term cfg env t0  in
               let t12 =
                 if qi.FStar_Syntax_Syntax.qopen
                 then closure_as_term cfg env t11
                 else t11  in
               let t2 =
                 let uu___144_9450 = t1  in
                 {
                   FStar_Syntax_Syntax.n =
                     (FStar_Syntax_Syntax.Tm_meta
                        (t01, (FStar_Syntax_Syntax.Meta_quoted (t12, qi))));
                   FStar_Syntax_Syntax.pos =
                     (uu___144_9450.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___144_9450.FStar_Syntax_Syntax.vars)
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
                 let uu___145_9480 = cfg  in
                 {
                   steps =
                     (let uu___146_9483 = cfg.steps  in
                      {
                        beta = (uu___146_9483.beta);
                        iota = (uu___146_9483.iota);
                        zeta = (uu___146_9483.zeta);
                        weak = (uu___146_9483.weak);
                        hnf = (uu___146_9483.hnf);
                        primops = (uu___146_9483.primops);
                        no_delta_steps = false;
                        unfold_until = (uu___146_9483.unfold_until);
                        unfold_only = FStar_Pervasives_Native.None;
                        unfold_attr = (uu___146_9483.unfold_attr);
                        unfold_tac = (uu___146_9483.unfold_tac);
                        pure_subterms_within_computations =
                          (uu___146_9483.pure_subterms_within_computations);
                        simplify = (uu___146_9483.simplify);
                        erase_universes = (uu___146_9483.erase_universes);
                        allow_unbound_universes =
                          (uu___146_9483.allow_unbound_universes);
                        reify_ = (uu___146_9483.reify_);
                        compress_uvars = (uu___146_9483.compress_uvars);
                        no_full_norm = (uu___146_9483.no_full_norm);
                        check_no_uvars = (uu___146_9483.check_no_uvars);
                        unmeta = (uu___146_9483.unmeta);
                        unascribe = (uu___146_9483.unascribe)
                      });
                   tcenv = (uu___145_9480.tcenv);
                   debug = (uu___145_9480.debug);
                   delta_level =
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.Delta_constant];
                   primitive_steps = (uu___145_9480.primitive_steps);
                   strong = (uu___145_9480.strong);
                   memoize_lazy = (uu___145_9480.memoize_lazy);
                   normalize_pure_lets = true
                 }  in
               let uu____9486 = get_norm_request (norm cfg' env []) args  in
               (match uu____9486 with
                | FStar_Pervasives_Native.None  ->
                    let stack1 =
                      FStar_All.pipe_right stack
                        (FStar_List.fold_right
                           (fun uu____9517  ->
                              fun stack1  ->
                                match uu____9517 with
                                | (a,aq) ->
                                    let uu____9529 =
                                      let uu____9530 =
                                        let uu____9537 =
                                          let uu____9538 =
                                            let uu____9569 =
                                              FStar_Util.mk_ref
                                                FStar_Pervasives_Native.None
                                               in
                                            (env, a, uu____9569, false)  in
                                          Clos uu____9538  in
                                        (uu____9537, aq,
                                          (t1.FStar_Syntax_Syntax.pos))
                                         in
                                      Arg uu____9530  in
                                    uu____9529 :: stack1) args)
                       in
                    (log cfg
                       (fun uu____9653  ->
                          let uu____9654 =
                            FStar_All.pipe_left FStar_Util.string_of_int
                              (FStar_List.length args)
                             in
                          FStar_Util.print1 "\tPushed %s arguments\n"
                            uu____9654);
                     norm cfg env stack1 hd1)
                | FStar_Pervasives_Native.Some (s,tm) ->
                    let delta_level =
                      let uu____9676 =
                        FStar_All.pipe_right s
                          (FStar_Util.for_some
                             (fun uu___86_9681  ->
                                match uu___86_9681 with
                                | UnfoldUntil uu____9682 -> true
                                | UnfoldOnly uu____9683 -> true
                                | uu____9686 -> false))
                         in
                      if uu____9676
                      then
                        [FStar_TypeChecker_Env.Unfold
                           FStar_Syntax_Syntax.Delta_constant]
                      else [FStar_TypeChecker_Env.NoDelta]  in
                    let cfg'1 =
                      let uu___147_9691 = cfg  in
                      let uu____9692 = to_fsteps s  in
                      {
                        steps = uu____9692;
                        tcenv = (uu___147_9691.tcenv);
                        debug = (uu___147_9691.debug);
                        delta_level;
                        primitive_steps = (uu___147_9691.primitive_steps);
                        strong = (uu___147_9691.strong);
                        memoize_lazy = (uu___147_9691.memoize_lazy);
                        normalize_pure_lets = true
                      }  in
                    let stack' =
                      let tail1 = (Cfg cfg) :: stack  in
                      if (cfg.debug).print_normalized
                      then
                        let uu____9701 =
                          let uu____9702 =
                            let uu____9707 = FStar_Util.now ()  in
                            (t1, uu____9707)  in
                          Debug uu____9702  in
                        uu____9701 :: tail1
                      else tail1  in
                    norm cfg'1 env stack' tm)
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u  in
               let uu____9711 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack uu____9711
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               if (cfg.steps).erase_universes
               then norm cfg env stack t'
               else
                 (let us1 =
                    let uu____9720 =
                      let uu____9727 =
                        FStar_List.map (norm_universe cfg env) us  in
                      (uu____9727, (t1.FStar_Syntax_Syntax.pos))  in
                    UnivArgs uu____9720  in
                  let stack1 = us1 :: stack  in norm cfg env stack1 t')
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let qninfo =
                 let uu____9737 = FStar_Syntax_Syntax.lid_of_fv fv  in
                 FStar_TypeChecker_Env.lookup_qname cfg.tcenv uu____9737  in
               let uu____9738 = FStar_TypeChecker_Env.qninfo_is_action qninfo
                  in
               if uu____9738
               then
                 let b = should_reify cfg stack  in
                 (log cfg
                    (fun uu____9744  ->
                       let uu____9745 = FStar_Syntax_Print.term_to_string t1
                          in
                       let uu____9746 = FStar_Util.string_of_bool b  in
                       FStar_Util.print2
                         ">>> For DM4F action %s, should_reify = %s\n"
                         uu____9745 uu____9746);
                  if b
                  then
                    (let uu____9747 = FStar_List.tl stack  in
                     do_unfold_fv cfg env uu____9747 t1 qninfo fv)
                  else rebuild cfg env stack t1)
               else
                 (let should_delta =
                    (let uu____9755 = find_prim_step cfg fv  in
                     FStar_Option.isNone uu____9755) &&
                      (FStar_All.pipe_right cfg.delta_level
                         (FStar_Util.for_some
                            (fun uu___87_9761  ->
                               match uu___87_9761 with
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
                          (let uu____9771 =
                             cases
                               (FStar_Util.for_some
                                  (FStar_Syntax_Util.attr_eq
                                     FStar_Syntax_Util.tac_opaque_attr))
                               false attrs
                              in
                           Prims.op_Negation uu____9771))
                         &&
                         ((match (cfg.steps).unfold_only with
                           | FStar_Pervasives_Native.None  -> true
                           | FStar_Pervasives_Native.Some lids ->
                               FStar_Util.for_some
                                 (FStar_Syntax_Syntax.fv_eq_lid fv) lids)
                            ||
                            (match (attrs, ((cfg.steps).unfold_attr)) with
                             | (FStar_Pervasives_Native.None
                                ,FStar_Pervasives_Native.Some uu____9790) ->
                                 false
                             | (FStar_Pervasives_Native.Some
                                ats,FStar_Pervasives_Native.Some ats') ->
                                 FStar_Util.for_some
                                   (fun at  ->
                                      FStar_Util.for_some
                                        (FStar_Syntax_Util.attr_eq at) ats')
                                   ats
                             | (uu____9825,uu____9826) -> false)))
                     in
                  log cfg
                    (fun uu____9848  ->
                       let uu____9849 = FStar_Syntax_Print.term_to_string t1
                          in
                       let uu____9850 =
                         FStar_Range.string_of_range
                           t1.FStar_Syntax_Syntax.pos
                          in
                       let uu____9851 =
                         FStar_Util.string_of_bool should_delta1  in
                       FStar_Util.print3
                         ">>> For %s (%s), should_delta = %s\n" uu____9849
                         uu____9850 uu____9851);
                  if should_delta1
                  then do_unfold_fv cfg env stack t1 qninfo fv
                  else rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____9854 = lookup_bvar env x  in
               (match uu____9854 with
                | Univ uu____9857 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if (Prims.op_Negation fix) || (cfg.steps).zeta
                    then
                      let uu____9906 = FStar_ST.op_Bang r  in
                      (match uu____9906 with
                       | FStar_Pervasives_Native.Some (env2,t') ->
                           (log cfg
                              (fun uu____10024  ->
                                 let uu____10025 =
                                   FStar_Syntax_Print.term_to_string t1  in
                                 let uu____10026 =
                                   FStar_Syntax_Print.term_to_string t'  in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____10025
                                   uu____10026);
                            (let uu____10027 =
                               let uu____10028 =
                                 FStar_Syntax_Subst.compress t'  in
                               uu____10028.FStar_Syntax_Syntax.n  in
                             match uu____10027 with
                             | FStar_Syntax_Syntax.Tm_abs uu____10031 ->
                                 norm cfg env2 stack t'
                             | uu____10048 -> rebuild cfg env2 stack t'))
                       | FStar_Pervasives_Native.None  ->
                           norm cfg env1 ((MemoLazy r) :: stack) t0)
                    else norm cfg env1 stack t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack with
                | (UnivArgs uu____10118)::uu____10119 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Match uu____10128)::uu____10129 ->
                    failwith
                      "Ill-typed term: cannot pattern match an abstraction"
                | (Arg (c,uu____10139,uu____10140))::stack_rest ->
                    (match c with
                     | Univ uu____10144 ->
                         norm cfg ((FStar_Pervasives_Native.None, c) :: env)
                           stack_rest t1
                     | uu____10153 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | b::[] ->
                              (log cfg
                                 (fun uu____10174  ->
                                    let uu____10175 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____10175);
                               norm cfg
                                 (((FStar_Pervasives_Native.Some b), c) ::
                                 env) stack_rest body)
                          | b::tl1 ->
                              (log cfg
                                 (fun uu____10215  ->
                                    let uu____10216 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____10216);
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
                       (fun uu____10294  ->
                          let uu____10295 =
                            FStar_Syntax_Print.term_to_string t1  in
                          FStar_Util.print1 "\tSet memo %s\n" uu____10295);
                     norm cfg env stack1 t1)
                | (Debug uu____10296)::uu____10297 ->
                    if (cfg.steps).weak
                    then
                      let uu____10304 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____10304
                    else
                      (let uu____10306 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____10306 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____10348  -> dummy :: env1) env)
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
                                          let uu____10385 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____10385)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___148_10390 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___148_10390.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___148_10390.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____10391 -> lopt  in
                           (log cfg
                              (fun uu____10397  ->
                                 let uu____10398 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____10398);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___149_10407 = cfg  in
                               {
                                 steps = (uu___149_10407.steps);
                                 tcenv = (uu___149_10407.tcenv);
                                 debug = (uu___149_10407.debug);
                                 delta_level = (uu___149_10407.delta_level);
                                 primitive_steps =
                                   (uu___149_10407.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___149_10407.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___149_10407.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Meta uu____10418)::uu____10419 ->
                    if (cfg.steps).weak
                    then
                      let uu____10426 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____10426
                    else
                      (let uu____10428 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____10428 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____10470  -> dummy :: env1) env)
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
                                          let uu____10507 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____10507)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___148_10512 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___148_10512.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___148_10512.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____10513 -> lopt  in
                           (log cfg
                              (fun uu____10519  ->
                                 let uu____10520 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____10520);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___149_10529 = cfg  in
                               {
                                 steps = (uu___149_10529.steps);
                                 tcenv = (uu___149_10529.tcenv);
                                 debug = (uu___149_10529.debug);
                                 delta_level = (uu___149_10529.delta_level);
                                 primitive_steps =
                                   (uu___149_10529.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___149_10529.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___149_10529.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Let uu____10540)::uu____10541 ->
                    if (cfg.steps).weak
                    then
                      let uu____10552 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____10552
                    else
                      (let uu____10554 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____10554 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____10596  -> dummy :: env1) env)
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
                                          let uu____10633 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____10633)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___148_10638 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___148_10638.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___148_10638.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____10639 -> lopt  in
                           (log cfg
                              (fun uu____10645  ->
                                 let uu____10646 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____10646);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___149_10655 = cfg  in
                               {
                                 steps = (uu___149_10655.steps);
                                 tcenv = (uu___149_10655.tcenv);
                                 debug = (uu___149_10655.debug);
                                 delta_level = (uu___149_10655.delta_level);
                                 primitive_steps =
                                   (uu___149_10655.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___149_10655.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___149_10655.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (App uu____10666)::uu____10667 ->
                    if (cfg.steps).weak
                    then
                      let uu____10678 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____10678
                    else
                      (let uu____10680 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____10680 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____10722  -> dummy :: env1) env)
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
                                          let uu____10759 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____10759)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___148_10764 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___148_10764.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___148_10764.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____10765 -> lopt  in
                           (log cfg
                              (fun uu____10771  ->
                                 let uu____10772 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____10772);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___149_10781 = cfg  in
                               {
                                 steps = (uu___149_10781.steps);
                                 tcenv = (uu___149_10781.tcenv);
                                 debug = (uu___149_10781.debug);
                                 delta_level = (uu___149_10781.delta_level);
                                 primitive_steps =
                                   (uu___149_10781.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___149_10781.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___149_10781.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Abs uu____10792)::uu____10793 ->
                    if (cfg.steps).weak
                    then
                      let uu____10808 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____10808
                    else
                      (let uu____10810 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____10810 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____10852  -> dummy :: env1) env)
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
                                          let uu____10889 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____10889)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___148_10894 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___148_10894.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___148_10894.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____10895 -> lopt  in
                           (log cfg
                              (fun uu____10901  ->
                                 let uu____10902 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____10902);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___149_10911 = cfg  in
                               {
                                 steps = (uu___149_10911.steps);
                                 tcenv = (uu___149_10911.tcenv);
                                 debug = (uu___149_10911.debug);
                                 delta_level = (uu___149_10911.delta_level);
                                 primitive_steps =
                                   (uu___149_10911.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___149_10911.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___149_10911.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | [] ->
                    if (cfg.steps).weak
                    then
                      let uu____10922 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____10922
                    else
                      (let uu____10924 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____10924 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____10966  -> dummy :: env1) env)
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
                                          let uu____11003 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____11003)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___148_11008 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___148_11008.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___148_11008.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11009 -> lopt  in
                           (log cfg
                              (fun uu____11015  ->
                                 let uu____11016 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11016);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___149_11025 = cfg  in
                               {
                                 steps = (uu___149_11025.steps);
                                 tcenv = (uu___149_11025.tcenv);
                                 debug = (uu___149_11025.debug);
                                 delta_level = (uu___149_11025.delta_level);
                                 primitive_steps =
                                   (uu___149_11025.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___149_11025.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___149_11025.normalize_pure_lets)
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
                      (fun uu____11074  ->
                         fun stack1  ->
                           match uu____11074 with
                           | (a,aq) ->
                               let uu____11086 =
                                 let uu____11087 =
                                   let uu____11094 =
                                     let uu____11095 =
                                       let uu____11126 =
                                         FStar_Util.mk_ref
                                           FStar_Pervasives_Native.None
                                          in
                                       (env, a, uu____11126, false)  in
                                     Clos uu____11095  in
                                   (uu____11094, aq,
                                     (t1.FStar_Syntax_Syntax.pos))
                                    in
                                 Arg uu____11087  in
                               uu____11086 :: stack1) args)
                  in
               (log cfg
                  (fun uu____11210  ->
                     let uu____11211 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args)
                        in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____11211);
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
                             ((let uu___150_11247 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___150_11247.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___150_11247.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos
                         in
                      rebuild cfg env stack t2
                  | uu____11248 ->
                      let uu____11253 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____11253)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort  in
                  let uu____11256 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] f
                     in
                  match uu____11256 with
                  | (closing,f1) ->
                      let f2 = norm cfg (dummy :: env) [] f1  in
                      let t2 =
                        let uu____11287 =
                          let uu____11288 =
                            let uu____11295 =
                              FStar_Syntax_Subst.close closing f2  in
                            ((let uu___151_11297 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___151_11297.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___151_11297.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____11295)
                             in
                          FStar_Syntax_Syntax.Tm_refine uu____11288  in
                        mk uu____11287 t1.FStar_Syntax_Syntax.pos  in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if (cfg.steps).weak
               then
                 let uu____11316 = closure_as_term cfg env t1  in
                 rebuild cfg env stack uu____11316
               else
                 (let uu____11318 = FStar_Syntax_Subst.open_comp bs c  in
                  match uu____11318 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____11326 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun uu____11350  -> dummy :: env1) env)
                           in
                        norm_comp cfg uu____11326 c1  in
                      let t2 =
                        let uu____11372 = norm_binders cfg env bs1  in
                        FStar_Syntax_Util.arrow uu____11372 c2  in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) when
               (cfg.steps).unascribe -> norm cfg env stack t11
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack with
                | (Match uu____11483)::uu____11484 ->
                    (log cfg
                       (fun uu____11495  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (Arg uu____11496)::uu____11497 ->
                    (log cfg
                       (fun uu____11508  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (App
                    (uu____11509,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_constant
                                     (FStar_Const.Const_reify );
                                   FStar_Syntax_Syntax.pos = uu____11510;
                                   FStar_Syntax_Syntax.vars = uu____11511;_},uu____11512,uu____11513))::uu____11514
                    ->
                    (log cfg
                       (fun uu____11523  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (MemoLazy uu____11524)::uu____11525 ->
                    (log cfg
                       (fun uu____11536  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | uu____11537 ->
                    (log cfg
                       (fun uu____11540  ->
                          FStar_Util.print_string "+++ Keeping ascription \n");
                     (let t12 = norm cfg env [] t11  in
                      log cfg
                        (fun uu____11544  ->
                           FStar_Util.print_string
                             "+++ Normalizing ascription \n");
                      (let tc1 =
                         match tc with
                         | FStar_Util.Inl t2 ->
                             let uu____11561 = norm cfg env [] t2  in
                             FStar_Util.Inl uu____11561
                         | FStar_Util.Inr c ->
                             let uu____11569 = norm_comp cfg env c  in
                             FStar_Util.Inr uu____11569
                          in
                       let tacopt1 =
                         FStar_Util.map_opt tacopt (norm cfg env [])  in
                       match stack with
                       | (Cfg cfg1)::stack1 ->
                           let t2 =
                             let uu____11582 =
                               let uu____11583 =
                                 let uu____11610 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____11610, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____11583
                                in
                             mk uu____11582 t1.FStar_Syntax_Syntax.pos  in
                           norm cfg1 env stack1 t2
                       | uu____11629 ->
                           let uu____11630 =
                             let uu____11631 =
                               let uu____11632 =
                                 let uu____11659 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____11659, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____11632
                                in
                             mk uu____11631 t1.FStar_Syntax_Syntax.pos  in
                           rebuild cfg env stack uu____11630))))
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
                         let uu____11769 =
                           FStar_Syntax_Subst.univ_var_opening
                             lb.FStar_Syntax_Syntax.lbunivs
                            in
                         match uu____11769 with
                         | (openings,lbunivs) ->
                             let cfg1 =
                               let uu___152_11789 = cfg  in
                               let uu____11790 =
                                 FStar_TypeChecker_Env.push_univ_vars
                                   cfg.tcenv lbunivs
                                  in
                               {
                                 steps = (uu___152_11789.steps);
                                 tcenv = uu____11790;
                                 debug = (uu___152_11789.debug);
                                 delta_level = (uu___152_11789.delta_level);
                                 primitive_steps =
                                   (uu___152_11789.primitive_steps);
                                 strong = (uu___152_11789.strong);
                                 memoize_lazy = (uu___152_11789.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___152_11789.normalize_pure_lets)
                               }  in
                             let norm1 t2 =
                               let uu____11795 =
                                 let uu____11796 =
                                   FStar_Syntax_Subst.subst openings t2  in
                                 norm cfg1 env [] uu____11796  in
                               FStar_Syntax_Subst.close_univ_vars lbunivs
                                 uu____11795
                                in
                             let lbtyp = norm1 lb.FStar_Syntax_Syntax.lbtyp
                                in
                             let lbdef = norm1 lb.FStar_Syntax_Syntax.lbdef
                                in
                             let uu___153_11799 = lb  in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___153_11799.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs = lbunivs;
                               FStar_Syntax_Syntax.lbtyp = lbtyp;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___153_11799.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = lbdef;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___153_11799.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___153_11799.FStar_Syntax_Syntax.lbpos)
                             }))
                  in
               let uu____11800 =
                 mk (FStar_Syntax_Syntax.Tm_let ((b, lbs1), lbody))
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack uu____11800
           | FStar_Syntax_Syntax.Tm_let
               ((uu____11811,{
                               FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                 uu____11812;
                               FStar_Syntax_Syntax.lbunivs = uu____11813;
                               FStar_Syntax_Syntax.lbtyp = uu____11814;
                               FStar_Syntax_Syntax.lbeff = uu____11815;
                               FStar_Syntax_Syntax.lbdef = uu____11816;
                               FStar_Syntax_Syntax.lbattrs = uu____11817;
                               FStar_Syntax_Syntax.lbpos = uu____11818;_}::uu____11819),uu____11820)
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff
                  in
               let uu____11860 =
                 (Prims.op_Negation (cfg.steps).no_delta_steps) &&
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
               if uu____11860
               then
                 let binder =
                   let uu____11862 =
                     FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                   FStar_Syntax_Syntax.mk_binder uu____11862  in
                 let env1 =
                   let uu____11872 =
                     let uu____11879 =
                       let uu____11880 =
                         let uu____11911 =
                           FStar_Util.mk_ref FStar_Pervasives_Native.None  in
                         (env, (lb.FStar_Syntax_Syntax.lbdef), uu____11911,
                           false)
                          in
                       Clos uu____11880  in
                     ((FStar_Pervasives_Native.Some binder), uu____11879)  in
                   uu____11872 :: env  in
                 (log cfg
                    (fun uu____12004  ->
                       FStar_Util.print_string "+++ Reducing Tm_let\n");
                  norm cfg env1 stack body)
               else
                 if (cfg.steps).weak
                 then
                   (log cfg
                      (fun uu____12008  ->
                         FStar_Util.print_string "+++ Not touching Tm_let\n");
                    (let uu____12009 = closure_as_term cfg env t1  in
                     rebuild cfg env stack uu____12009))
                 else
                   (let uu____12011 =
                      let uu____12016 =
                        let uu____12017 =
                          let uu____12018 =
                            FStar_All.pipe_right
                              lb.FStar_Syntax_Syntax.lbname FStar_Util.left
                             in
                          FStar_All.pipe_right uu____12018
                            FStar_Syntax_Syntax.mk_binder
                           in
                        [uu____12017]  in
                      FStar_Syntax_Subst.open_term uu____12016 body  in
                    match uu____12011 with
                    | (bs,body1) ->
                        (log cfg
                           (fun uu____12027  ->
                              FStar_Util.print_string
                                "+++ Normalizing Tm_let -- type");
                         (let ty =
                            norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                          let lbname =
                            let x =
                              let uu____12035 = FStar_List.hd bs  in
                              FStar_Pervasives_Native.fst uu____12035  in
                            FStar_Util.Inl
                              (let uu___154_12045 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___154_12045.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___154_12045.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               })
                             in
                          log cfg
                            (fun uu____12048  ->
                               FStar_Util.print_string
                                 "+++ Normalizing Tm_let -- definiens\n");
                          (let lb1 =
                             let uu___155_12050 = lb  in
                             let uu____12051 =
                               norm cfg env [] lb.FStar_Syntax_Syntax.lbdef
                                in
                             {
                               FStar_Syntax_Syntax.lbname = lbname;
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___155_12050.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp = ty;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___155_12050.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = uu____12051;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___155_12050.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___155_12050.FStar_Syntax_Syntax.lbpos)
                             }  in
                           let env' =
                             FStar_All.pipe_right bs
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12086  -> dummy :: env1) env)
                              in
                           let stack1 = (Cfg cfg) :: stack  in
                           let cfg1 =
                             let uu___156_12109 = cfg  in
                             {
                               steps = (uu___156_12109.steps);
                               tcenv = (uu___156_12109.tcenv);
                               debug = (uu___156_12109.debug);
                               delta_level = (uu___156_12109.delta_level);
                               primitive_steps =
                                 (uu___156_12109.primitive_steps);
                               strong = true;
                               memoize_lazy = (uu___156_12109.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___156_12109.normalize_pure_lets)
                             }  in
                           log cfg1
                             (fun uu____12112  ->
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
               let uu____12129 = FStar_Syntax_Subst.open_let_rec lbs body  in
               (match uu____12129 with
                | (lbs1,body1) ->
                    let lbs2 =
                      FStar_List.map
                        (fun lb  ->
                           let ty =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                           let lbname =
                             let uu____12165 =
                               let uu___157_12166 =
                                 FStar_Util.left
                                   lb.FStar_Syntax_Syntax.lbname
                                  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___157_12166.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___157_12166.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               }  in
                             FStar_Util.Inl uu____12165  in
                           let uu____12167 =
                             FStar_Syntax_Util.abs_formals
                               lb.FStar_Syntax_Syntax.lbdef
                              in
                           match uu____12167 with
                           | (xs,def_body,lopt) ->
                               let xs1 = norm_binders cfg env xs  in
                               let env1 =
                                 let uu____12193 =
                                   FStar_List.map (fun uu____12209  -> dummy)
                                     lbs1
                                    in
                                 let uu____12210 =
                                   let uu____12219 =
                                     FStar_List.map
                                       (fun uu____12239  -> dummy) xs1
                                      in
                                   FStar_List.append uu____12219 env  in
                                 FStar_List.append uu____12193 uu____12210
                                  in
                               let def_body1 = norm cfg env1 [] def_body  in
                               let lopt1 =
                                 match lopt with
                                 | FStar_Pervasives_Native.Some rc ->
                                     let uu____12263 =
                                       let uu___158_12264 = rc  in
                                       let uu____12265 =
                                         FStar_Util.map_opt
                                           rc.FStar_Syntax_Syntax.residual_typ
                                           (norm cfg env1 [])
                                          in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___158_12264.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           uu____12265;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___158_12264.FStar_Syntax_Syntax.residual_flags)
                                       }  in
                                     FStar_Pervasives_Native.Some uu____12263
                                 | uu____12272 -> lopt  in
                               let def =
                                 FStar_Syntax_Util.abs xs1 def_body1 lopt1
                                  in
                               let uu___159_12276 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname = lbname;
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___159_12276.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp = ty;
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___159_12276.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___159_12276.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___159_12276.FStar_Syntax_Syntax.lbpos)
                               }) lbs1
                       in
                    let env' =
                      let uu____12286 =
                        FStar_List.map (fun uu____12302  -> dummy) lbs2  in
                      FStar_List.append uu____12286 env  in
                    let body2 = norm cfg env' [] body1  in
                    let uu____12310 =
                      FStar_Syntax_Subst.close_let_rec lbs2 body2  in
                    (match uu____12310 with
                     | (lbs3,body3) ->
                         let t2 =
                           let uu___160_12326 = t1  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_let
                                  ((true, lbs3), body3));
                             FStar_Syntax_Syntax.pos =
                               (uu___160_12326.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___160_12326.FStar_Syntax_Syntax.vars)
                           }  in
                         rebuild cfg env stack t2))
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               Prims.op_Negation (cfg.steps).zeta ->
               let uu____12353 = closure_as_term cfg env t1  in
               rebuild cfg env stack uu____12353
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____12372 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____12448  ->
                        match uu____12448 with
                        | (rec_env,memos,i) ->
                            let bv =
                              let uu___161_12569 =
                                FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                                 in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___161_12569.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index = i;
                                FStar_Syntax_Syntax.sort =
                                  (uu___161_12569.FStar_Syntax_Syntax.sort)
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
               (match uu____12372 with
                | (rec_env,memos,uu____12782) ->
                    let uu____12835 =
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
                             let uu____13146 =
                               let uu____13153 =
                                 let uu____13154 =
                                   let uu____13185 =
                                     FStar_Util.mk_ref
                                       FStar_Pervasives_Native.None
                                      in
                                   (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                     uu____13185, false)
                                    in
                                 Clos uu____13154  in
                               (FStar_Pervasives_Native.None, uu____13153)
                                in
                             uu____13146 :: env1)
                        (FStar_Pervasives_Native.snd lbs) env
                       in
                    norm cfg body_env stack body)
           | FStar_Syntax_Syntax.Tm_meta (head1,m) ->
               (log cfg
                  (fun uu____13295  ->
                     let uu____13296 =
                       FStar_Syntax_Print.metadata_to_string m  in
                     FStar_Util.print1 ">> metadata = %s\n" uu____13296);
                (match m with
                 | FStar_Syntax_Syntax.Meta_monadic (m1,t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inl m1) t2
                 | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inr (m1, m')) t2
                 | FStar_Syntax_Syntax.Meta_quoted (qt,inf) ->
                     rebuild cfg env stack t1
                 | uu____13324 ->
                     if (cfg.steps).unmeta
                     then norm cfg env stack head1
                     else
                       (match stack with
                        | uu____13326::uu____13327 ->
                            (match m with
                             | FStar_Syntax_Syntax.Meta_labeled
                                 (l,r,uu____13332) ->
                                 norm cfg env ((Meta (m, r)) :: stack) head1
                             | FStar_Syntax_Syntax.Meta_pattern args ->
                                 let args1 = norm_pattern_args cfg env args
                                    in
                                 norm cfg env
                                   ((Meta
                                       ((FStar_Syntax_Syntax.Meta_pattern
                                           args1),
                                         (t1.FStar_Syntax_Syntax.pos))) ::
                                   stack) head1
                             | uu____13355 -> norm cfg env stack head1)
                        | [] ->
                            let head2 = norm cfg env [] head1  in
                            let m1 =
                              match m with
                              | FStar_Syntax_Syntax.Meta_pattern args ->
                                  let uu____13369 =
                                    norm_pattern_args cfg env args  in
                                  FStar_Syntax_Syntax.Meta_pattern
                                    uu____13369
                              | uu____13380 -> m  in
                            let t2 =
                              mk (FStar_Syntax_Syntax.Tm_meta (head2, m1))
                                t1.FStar_Syntax_Syntax.pos
                               in
                            rebuild cfg env stack t2)))
           | FStar_Syntax_Syntax.Tm_delayed uu____13384 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               norm cfg env stack t2
           | FStar_Syntax_Syntax.Tm_uvar uu____13410 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               (match t2.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_uvar uu____13428 ->
                    if (cfg.steps).check_no_uvars
                    then
                      let uu____13445 =
                        let uu____13446 =
                          FStar_Range.string_of_range
                            t2.FStar_Syntax_Syntax.pos
                           in
                        let uu____13447 =
                          FStar_Syntax_Print.term_to_string t2  in
                        FStar_Util.format2
                          "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                          uu____13446 uu____13447
                         in
                      failwith uu____13445
                    else rebuild cfg env stack t2
                | uu____13449 -> norm cfg env stack t2))

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
                let uu____13459 = FStar_Syntax_Syntax.range_of_fv f  in
                FStar_TypeChecker_Env.set_range cfg.tcenv uu____13459  in
              let uu____13460 =
                FStar_TypeChecker_Env.lookup_definition_qninfo
                  cfg.delta_level
                  (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                  qninfo
                 in
              match uu____13460 with
              | FStar_Pervasives_Native.None  ->
                  (log cfg
                     (fun uu____13473  ->
                        FStar_Util.print "Tm_fvar case 2\n" []);
                   rebuild cfg env stack t0)
              | FStar_Pervasives_Native.Some (us,t) ->
                  (log cfg
                     (fun uu____13484  ->
                        let uu____13485 =
                          FStar_Syntax_Print.term_to_string t0  in
                        let uu____13486 = FStar_Syntax_Print.term_to_string t
                           in
                        FStar_Util.print2 ">>> Unfolded %s to %s\n"
                          uu____13485 uu____13486);
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
                      | (UnivArgs (us',uu____13499))::stack1 ->
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
                      | uu____13554 when
                          (cfg.steps).erase_universes ||
                            (cfg.steps).allow_unbound_universes
                          -> norm cfg env stack t1
                      | uu____13557 ->
                          let uu____13560 =
                            let uu____13561 =
                              FStar_Syntax_Print.lid_to_string
                                (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                               in
                            FStar_Util.format1
                              "Impossible: missing universe instantiation on %s"
                              uu____13561
                             in
                          failwith uu____13560
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
                  let uu___162_13585 = cfg  in
                  let uu____13586 =
                    FStar_List.fold_right fstep_add_one new_steps cfg.steps
                     in
                  {
                    steps = uu____13586;
                    tcenv = (uu___162_13585.tcenv);
                    debug = (uu___162_13585.debug);
                    delta_level =
                      [FStar_TypeChecker_Env.Inlining;
                      FStar_TypeChecker_Env.Eager_unfolding_only];
                    primitive_steps = (uu___162_13585.primitive_steps);
                    strong = (uu___162_13585.strong);
                    memoize_lazy = (uu___162_13585.memoize_lazy);
                    normalize_pure_lets =
                      (uu___162_13585.normalize_pure_lets)
                  }
                else
                  (let uu___163_13588 = cfg  in
                   {
                     steps =
                       (let uu___164_13591 = cfg.steps  in
                        {
                          beta = (uu___164_13591.beta);
                          iota = (uu___164_13591.iota);
                          zeta = false;
                          weak = (uu___164_13591.weak);
                          hnf = (uu___164_13591.hnf);
                          primops = (uu___164_13591.primops);
                          no_delta_steps = (uu___164_13591.no_delta_steps);
                          unfold_until = (uu___164_13591.unfold_until);
                          unfold_only = (uu___164_13591.unfold_only);
                          unfold_attr = (uu___164_13591.unfold_attr);
                          unfold_tac = (uu___164_13591.unfold_tac);
                          pure_subterms_within_computations =
                            (uu___164_13591.pure_subterms_within_computations);
                          simplify = (uu___164_13591.simplify);
                          erase_universes = (uu___164_13591.erase_universes);
                          allow_unbound_universes =
                            (uu___164_13591.allow_unbound_universes);
                          reify_ = (uu___164_13591.reify_);
                          compress_uvars = (uu___164_13591.compress_uvars);
                          no_full_norm = (uu___164_13591.no_full_norm);
                          check_no_uvars = (uu___164_13591.check_no_uvars);
                          unmeta = (uu___164_13591.unmeta);
                          unascribe = (uu___164_13591.unascribe)
                        });
                     tcenv = (uu___163_13588.tcenv);
                     debug = (uu___163_13588.debug);
                     delta_level = (uu___163_13588.delta_level);
                     primitive_steps = (uu___163_13588.primitive_steps);
                     strong = (uu___163_13588.strong);
                     memoize_lazy = (uu___163_13588.memoize_lazy);
                     normalize_pure_lets =
                       (uu___163_13588.normalize_pure_lets)
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
                  (fun uu____13621  ->
                     let uu____13622 = FStar_Syntax_Print.tag_of_term head2
                        in
                     let uu____13623 =
                       FStar_Syntax_Print.term_to_string head2  in
                     FStar_Util.print2 "Reifying: (%s) %s\n" uu____13622
                       uu____13623);
                (let head3 = FStar_Syntax_Util.unmeta_safe head2  in
                 let uu____13625 =
                   let uu____13626 = FStar_Syntax_Subst.compress head3  in
                   uu____13626.FStar_Syntax_Syntax.n  in
                 match uu____13625 with
                 | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                     let ed =
                       let uu____13644 =
                         FStar_TypeChecker_Env.norm_eff_name cfg.tcenv m  in
                       FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                         uu____13644
                        in
                     let uu____13645 = ed.FStar_Syntax_Syntax.bind_repr  in
                     (match uu____13645 with
                      | (uu____13646,bind_repr) ->
                          (match lb.FStar_Syntax_Syntax.lbname with
                           | FStar_Util.Inr uu____13652 ->
                               failwith
                                 "Cannot reify a top-level let binding"
                           | FStar_Util.Inl x ->
                               let is_return e =
                                 let uu____13660 =
                                   let uu____13661 =
                                     FStar_Syntax_Subst.compress e  in
                                   uu____13661.FStar_Syntax_Syntax.n  in
                                 match uu____13660 with
                                 | FStar_Syntax_Syntax.Tm_meta
                                     (e1,FStar_Syntax_Syntax.Meta_monadic
                                      (uu____13667,uu____13668))
                                     ->
                                     let uu____13677 =
                                       let uu____13678 =
                                         FStar_Syntax_Subst.compress e1  in
                                       uu____13678.FStar_Syntax_Syntax.n  in
                                     (match uu____13677 with
                                      | FStar_Syntax_Syntax.Tm_meta
                                          (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                           (uu____13684,msrc,uu____13686))
                                          when
                                          FStar_Syntax_Util.is_pure_effect
                                            msrc
                                          ->
                                          let uu____13695 =
                                            FStar_Syntax_Subst.compress e2
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____13695
                                      | uu____13696 ->
                                          FStar_Pervasives_Native.None)
                                 | uu____13697 ->
                                     FStar_Pervasives_Native.None
                                  in
                               let uu____13698 =
                                 is_return lb.FStar_Syntax_Syntax.lbdef  in
                               (match uu____13698 with
                                | FStar_Pervasives_Native.Some e ->
                                    let lb1 =
                                      let uu___165_13703 = lb  in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          (uu___165_13703.FStar_Syntax_Syntax.lbname);
                                        FStar_Syntax_Syntax.lbunivs =
                                          (uu___165_13703.FStar_Syntax_Syntax.lbunivs);
                                        FStar_Syntax_Syntax.lbtyp =
                                          (uu___165_13703.FStar_Syntax_Syntax.lbtyp);
                                        FStar_Syntax_Syntax.lbeff =
                                          FStar_Parser_Const.effect_PURE_lid;
                                        FStar_Syntax_Syntax.lbdef = e;
                                        FStar_Syntax_Syntax.lbattrs =
                                          (uu___165_13703.FStar_Syntax_Syntax.lbattrs);
                                        FStar_Syntax_Syntax.lbpos =
                                          (uu___165_13703.FStar_Syntax_Syntax.lbpos)
                                      }  in
                                    let uu____13704 = FStar_List.tl stack  in
                                    let uu____13705 =
                                      let uu____13706 =
                                        let uu____13709 =
                                          let uu____13710 =
                                            let uu____13723 =
                                              FStar_Syntax_Util.mk_reify body
                                               in
                                            ((false, [lb1]), uu____13723)  in
                                          FStar_Syntax_Syntax.Tm_let
                                            uu____13710
                                           in
                                        FStar_Syntax_Syntax.mk uu____13709
                                         in
                                      uu____13706
                                        FStar_Pervasives_Native.None
                                        head3.FStar_Syntax_Syntax.pos
                                       in
                                    norm cfg env uu____13704 uu____13705
                                | FStar_Pervasives_Native.None  ->
                                    let uu____13739 =
                                      let uu____13740 = is_return body  in
                                      match uu____13740 with
                                      | FStar_Pervasives_Native.Some
                                          {
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_bvar y;
                                            FStar_Syntax_Syntax.pos =
                                              uu____13744;
                                            FStar_Syntax_Syntax.vars =
                                              uu____13745;_}
                                          -> FStar_Syntax_Syntax.bv_eq x y
                                      | uu____13750 -> false  in
                                    if uu____13739
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
                                         let uu____13773 =
                                           let uu____13776 =
                                             let uu____13777 =
                                               let uu____13794 =
                                                 let uu____13797 =
                                                   FStar_Syntax_Syntax.mk_binder
                                                     x
                                                    in
                                                 [uu____13797]  in
                                               (uu____13794, body1,
                                                 (FStar_Pervasives_Native.Some
                                                    body_rc))
                                                in
                                             FStar_Syntax_Syntax.Tm_abs
                                               uu____13777
                                              in
                                           FStar_Syntax_Syntax.mk uu____13776
                                            in
                                         uu____13773
                                           FStar_Pervasives_Native.None
                                           body1.FStar_Syntax_Syntax.pos
                                          in
                                       let close1 = closure_as_term cfg env
                                          in
                                       let bind_inst =
                                         let uu____13813 =
                                           let uu____13814 =
                                             FStar_Syntax_Subst.compress
                                               bind_repr
                                              in
                                           uu____13814.FStar_Syntax_Syntax.n
                                            in
                                         match uu____13813 with
                                         | FStar_Syntax_Syntax.Tm_uinst
                                             (bind1,uu____13820::uu____13821::[])
                                             ->
                                             let uu____13828 =
                                               let uu____13831 =
                                                 let uu____13832 =
                                                   let uu____13839 =
                                                     let uu____13842 =
                                                       let uu____13843 =
                                                         close1
                                                           lb.FStar_Syntax_Syntax.lbtyp
                                                          in
                                                       (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                         cfg.tcenv
                                                         uu____13843
                                                        in
                                                     let uu____13844 =
                                                       let uu____13847 =
                                                         let uu____13848 =
                                                           close1 t  in
                                                         (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                           cfg.tcenv
                                                           uu____13848
                                                          in
                                                       [uu____13847]  in
                                                     uu____13842 ::
                                                       uu____13844
                                                      in
                                                   (bind1, uu____13839)  in
                                                 FStar_Syntax_Syntax.Tm_uinst
                                                   uu____13832
                                                  in
                                               FStar_Syntax_Syntax.mk
                                                 uu____13831
                                                in
                                             uu____13828
                                               FStar_Pervasives_Native.None
                                               rng
                                         | uu____13856 ->
                                             failwith
                                               "NIY : Reification of indexed effects"
                                          in
                                       let maybe_range_arg =
                                         let uu____13862 =
                                           FStar_Util.for_some
                                             (FStar_Syntax_Util.attr_eq
                                                FStar_Syntax_Util.dm4f_bind_range_attr)
                                             ed.FStar_Syntax_Syntax.eff_attrs
                                            in
                                         if uu____13862
                                         then
                                           let uu____13865 =
                                             let uu____13866 =
                                               FStar_Syntax_Embeddings.embed_range
                                                 lb.FStar_Syntax_Syntax.lbpos
                                                 lb.FStar_Syntax_Syntax.lbpos
                                                in
                                             FStar_Syntax_Syntax.as_arg
                                               uu____13866
                                              in
                                           let uu____13867 =
                                             let uu____13870 =
                                               let uu____13871 =
                                                 FStar_Syntax_Embeddings.embed_range
                                                   body2.FStar_Syntax_Syntax.pos
                                                   body2.FStar_Syntax_Syntax.pos
                                                  in
                                               FStar_Syntax_Syntax.as_arg
                                                 uu____13871
                                                in
                                             [uu____13870]  in
                                           uu____13865 :: uu____13867
                                         else []  in
                                       let reified =
                                         let uu____13876 =
                                           let uu____13879 =
                                             let uu____13880 =
                                               let uu____13895 =
                                                 let uu____13898 =
                                                   let uu____13901 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       lb.FStar_Syntax_Syntax.lbtyp
                                                      in
                                                   let uu____13902 =
                                                     let uu____13905 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         t
                                                        in
                                                     [uu____13905]  in
                                                   uu____13901 :: uu____13902
                                                    in
                                                 let uu____13906 =
                                                   let uu____13909 =
                                                     let uu____13912 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         FStar_Syntax_Syntax.tun
                                                        in
                                                     let uu____13913 =
                                                       let uu____13916 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           head4
                                                          in
                                                       let uu____13917 =
                                                         let uu____13920 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             FStar_Syntax_Syntax.tun
                                                            in
                                                         let uu____13921 =
                                                           let uu____13924 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               body2
                                                              in
                                                           [uu____13924]  in
                                                         uu____13920 ::
                                                           uu____13921
                                                          in
                                                       uu____13916 ::
                                                         uu____13917
                                                        in
                                                     uu____13912 ::
                                                       uu____13913
                                                      in
                                                   FStar_List.append
                                                     maybe_range_arg
                                                     uu____13909
                                                    in
                                                 FStar_List.append
                                                   uu____13898 uu____13906
                                                  in
                                               (bind_inst, uu____13895)  in
                                             FStar_Syntax_Syntax.Tm_app
                                               uu____13880
                                              in
                                           FStar_Syntax_Syntax.mk uu____13879
                                            in
                                         uu____13876
                                           FStar_Pervasives_Native.None rng
                                          in
                                       log cfg
                                         (fun uu____13936  ->
                                            let uu____13937 =
                                              FStar_Syntax_Print.term_to_string
                                                head0
                                               in
                                            let uu____13938 =
                                              FStar_Syntax_Print.term_to_string
                                                reified
                                               in
                                            FStar_Util.print2
                                              "Reified (1) <%s> to %s\n"
                                              uu____13937 uu____13938);
                                       (let uu____13939 = FStar_List.tl stack
                                           in
                                        norm cfg env uu____13939 reified)))))
                 | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                     let ed =
                       let uu____13963 =
                         FStar_TypeChecker_Env.norm_eff_name cfg.tcenv m  in
                       FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                         uu____13963
                        in
                     let uu____13964 = ed.FStar_Syntax_Syntax.bind_repr  in
                     (match uu____13964 with
                      | (uu____13965,bind_repr) ->
                          let maybe_unfold_action head4 =
                            let maybe_extract_fv t1 =
                              let t2 =
                                let uu____14000 =
                                  let uu____14001 =
                                    FStar_Syntax_Subst.compress t1  in
                                  uu____14001.FStar_Syntax_Syntax.n  in
                                match uu____14000 with
                                | FStar_Syntax_Syntax.Tm_uinst
                                    (t2,uu____14007) -> t2
                                | uu____14012 -> head4  in
                              let uu____14013 =
                                let uu____14014 =
                                  FStar_Syntax_Subst.compress t2  in
                                uu____14014.FStar_Syntax_Syntax.n  in
                              match uu____14013 with
                              | FStar_Syntax_Syntax.Tm_fvar x ->
                                  FStar_Pervasives_Native.Some x
                              | uu____14020 -> FStar_Pervasives_Native.None
                               in
                            let uu____14021 = maybe_extract_fv head4  in
                            match uu____14021 with
                            | FStar_Pervasives_Native.Some x when
                                let uu____14031 =
                                  FStar_Syntax_Syntax.lid_of_fv x  in
                                FStar_TypeChecker_Env.is_action cfg.tcenv
                                  uu____14031
                                ->
                                let head5 = norm cfg env [] head4  in
                                let action_unfolded =
                                  let uu____14036 = maybe_extract_fv head5
                                     in
                                  match uu____14036 with
                                  | FStar_Pervasives_Native.Some uu____14041
                                      -> FStar_Pervasives_Native.Some true
                                  | uu____14042 ->
                                      FStar_Pervasives_Native.Some false
                                   in
                                (head5, action_unfolded)
                            | uu____14047 ->
                                (head4, FStar_Pervasives_Native.None)
                             in
                          ((let is_arg_impure uu____14062 =
                              match uu____14062 with
                              | (e,q) ->
                                  let uu____14069 =
                                    let uu____14070 =
                                      FStar_Syntax_Subst.compress e  in
                                    uu____14070.FStar_Syntax_Syntax.n  in
                                  (match uu____14069 with
                                   | FStar_Syntax_Syntax.Tm_meta
                                       (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                        (m1,m2,t'))
                                       ->
                                       Prims.op_Negation
                                         (FStar_Syntax_Util.is_pure_effect m1)
                                   | uu____14085 -> false)
                               in
                            let uu____14086 =
                              let uu____14087 =
                                let uu____14094 =
                                  FStar_Syntax_Syntax.as_arg head_app  in
                                uu____14094 :: args  in
                              FStar_Util.for_some is_arg_impure uu____14087
                               in
                            if uu____14086
                            then
                              let uu____14099 =
                                let uu____14100 =
                                  FStar_Syntax_Print.term_to_string head3  in
                                FStar_Util.format1
                                  "Incompability between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                  uu____14100
                                 in
                              failwith uu____14099
                            else ());
                           (let uu____14102 = maybe_unfold_action head_app
                               in
                            match uu____14102 with
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
                                   (fun uu____14143  ->
                                      let uu____14144 =
                                        FStar_Syntax_Print.term_to_string
                                          head0
                                         in
                                      let uu____14145 =
                                        FStar_Syntax_Print.term_to_string
                                          body1
                                         in
                                      FStar_Util.print2
                                        "Reified (2) <%s> to %s\n"
                                        uu____14144 uu____14145);
                                 (let uu____14146 = FStar_List.tl stack  in
                                  norm cfg env uu____14146 body1)))))
                 | FStar_Syntax_Syntax.Tm_meta
                     (e,FStar_Syntax_Syntax.Meta_monadic uu____14148) ->
                     do_reify_monadic fallback cfg env stack e m t
                 | FStar_Syntax_Syntax.Tm_meta
                     (e,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,t'))
                     ->
                     let lifted =
                       let uu____14172 = closure_as_term cfg env t'  in
                       reify_lift cfg e msrc mtgt uu____14172  in
                     (log cfg
                        (fun uu____14176  ->
                           let uu____14177 =
                             FStar_Syntax_Print.term_to_string lifted  in
                           FStar_Util.print1 "Reified lift to (2): %s\n"
                             uu____14177);
                      (let uu____14178 = FStar_List.tl stack  in
                       norm cfg env uu____14178 lifted))
                 | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                     let branches1 =
                       FStar_All.pipe_right branches
                         (FStar_List.map
                            (fun uu____14299  ->
                               match uu____14299 with
                               | (pat,wopt,tm) ->
                                   let uu____14347 =
                                     FStar_Syntax_Util.mk_reify tm  in
                                   (pat, wopt, uu____14347)))
                        in
                     let tm =
                       mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                         head3.FStar_Syntax_Syntax.pos
                        in
                     let uu____14379 = FStar_List.tl stack  in
                     norm cfg env uu____14379 tm
                 | uu____14380 -> fallback ())

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
              (fun uu____14394  ->
                 let uu____14395 = FStar_Ident.string_of_lid msrc  in
                 let uu____14396 = FStar_Ident.string_of_lid mtgt  in
                 let uu____14397 = FStar_Syntax_Print.term_to_string e  in
                 FStar_Util.print3 "Reifying lift %s -> %s: %s\n" uu____14395
                   uu____14396 uu____14397);
            if
              (FStar_Syntax_Util.is_pure_effect msrc) ||
                (FStar_Syntax_Util.is_div_effect msrc)
            then
              (let ed =
                 let uu____14399 =
                   FStar_TypeChecker_Env.norm_eff_name cfg.tcenv mtgt  in
                 FStar_TypeChecker_Env.get_effect_decl env uu____14399  in
               let uu____14400 = ed.FStar_Syntax_Syntax.return_repr  in
               match uu____14400 with
               | (uu____14401,return_repr) ->
                   let return_inst =
                     let uu____14410 =
                       let uu____14411 =
                         FStar_Syntax_Subst.compress return_repr  in
                       uu____14411.FStar_Syntax_Syntax.n  in
                     match uu____14410 with
                     | FStar_Syntax_Syntax.Tm_uinst
                         (return_tm,uu____14417::[]) ->
                         let uu____14424 =
                           let uu____14427 =
                             let uu____14428 =
                               let uu____14435 =
                                 let uu____14438 =
                                   env.FStar_TypeChecker_Env.universe_of env
                                     t
                                    in
                                 [uu____14438]  in
                               (return_tm, uu____14435)  in
                             FStar_Syntax_Syntax.Tm_uinst uu____14428  in
                           FStar_Syntax_Syntax.mk uu____14427  in
                         uu____14424 FStar_Pervasives_Native.None
                           e.FStar_Syntax_Syntax.pos
                     | uu____14446 ->
                         failwith "NIY : Reification of indexed effects"
                      in
                   let uu____14449 =
                     let uu____14452 =
                       let uu____14453 =
                         let uu____14468 =
                           let uu____14471 = FStar_Syntax_Syntax.as_arg t  in
                           let uu____14472 =
                             let uu____14475 = FStar_Syntax_Syntax.as_arg e
                                in
                             [uu____14475]  in
                           uu____14471 :: uu____14472  in
                         (return_inst, uu____14468)  in
                       FStar_Syntax_Syntax.Tm_app uu____14453  in
                     FStar_Syntax_Syntax.mk uu____14452  in
                   uu____14449 FStar_Pervasives_Native.None
                     e.FStar_Syntax_Syntax.pos)
            else
              (let uu____14484 =
                 FStar_TypeChecker_Env.monad_leq env msrc mtgt  in
               match uu____14484 with
               | FStar_Pervasives_Native.None  ->
                   let uu____14487 =
                     FStar_Util.format2
                       "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                       (FStar_Ident.text_of_lid msrc)
                       (FStar_Ident.text_of_lid mtgt)
                      in
                   failwith uu____14487
               | FStar_Pervasives_Native.Some
                   { FStar_TypeChecker_Env.msource = uu____14488;
                     FStar_TypeChecker_Env.mtarget = uu____14489;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____14490;
                         FStar_TypeChecker_Env.mlift_term =
                           FStar_Pervasives_Native.None ;_};_}
                   ->
                   let uu____14505 =
                     FStar_Util.format2
                       "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
                       (FStar_Ident.text_of_lid msrc)
                       (FStar_Ident.text_of_lid mtgt)
                      in
                   failwith uu____14505
               | FStar_Pervasives_Native.Some
                   { FStar_TypeChecker_Env.msource = uu____14506;
                     FStar_TypeChecker_Env.mtarget = uu____14507;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____14508;
                         FStar_TypeChecker_Env.mlift_term =
                           FStar_Pervasives_Native.Some lift;_};_}
                   ->
                   let uu____14532 =
                     env.FStar_TypeChecker_Env.universe_of env t  in
                   let uu____14533 = FStar_Syntax_Util.mk_reify e  in
                   lift uu____14532 t FStar_Syntax_Syntax.tun uu____14533)

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
                (fun uu____14589  ->
                   match uu____14589 with
                   | (a,imp) ->
                       let uu____14600 = norm cfg env [] a  in
                       (uu____14600, imp))))

and (norm_comp :
  cfg -> env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp) =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        match comp.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total (t,uopt) ->
            let uu___166_14614 = comp  in
            let uu____14615 =
              let uu____14616 =
                let uu____14625 = norm cfg env [] t  in
                let uu____14626 =
                  FStar_Option.map (norm_universe cfg env) uopt  in
                (uu____14625, uu____14626)  in
              FStar_Syntax_Syntax.Total uu____14616  in
            {
              FStar_Syntax_Syntax.n = uu____14615;
              FStar_Syntax_Syntax.pos =
                (uu___166_14614.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___166_14614.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
            let uu___167_14641 = comp  in
            let uu____14642 =
              let uu____14643 =
                let uu____14652 = norm cfg env [] t  in
                let uu____14653 =
                  FStar_Option.map (norm_universe cfg env) uopt  in
                (uu____14652, uu____14653)  in
              FStar_Syntax_Syntax.GTotal uu____14643  in
            {
              FStar_Syntax_Syntax.n = uu____14642;
              FStar_Syntax_Syntax.pos =
                (uu___167_14641.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___167_14641.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let norm_args args =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____14705  ->
                      match uu____14705 with
                      | (a,i) ->
                          let uu____14716 = norm cfg env [] a  in
                          (uu____14716, i)))
               in
            let flags1 =
              FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                (FStar_List.map
                   (fun uu___88_14727  ->
                      match uu___88_14727 with
                      | FStar_Syntax_Syntax.DECREASES t ->
                          let uu____14731 = norm cfg env [] t  in
                          FStar_Syntax_Syntax.DECREASES uu____14731
                      | f -> f))
               in
            let uu___168_14735 = comp  in
            let uu____14736 =
              let uu____14737 =
                let uu___169_14738 = ct  in
                let uu____14739 =
                  FStar_List.map (norm_universe cfg env)
                    ct.FStar_Syntax_Syntax.comp_univs
                   in
                let uu____14740 =
                  norm cfg env [] ct.FStar_Syntax_Syntax.result_typ  in
                let uu____14743 =
                  norm_args ct.FStar_Syntax_Syntax.effect_args  in
                {
                  FStar_Syntax_Syntax.comp_univs = uu____14739;
                  FStar_Syntax_Syntax.effect_name =
                    (uu___169_14738.FStar_Syntax_Syntax.effect_name);
                  FStar_Syntax_Syntax.result_typ = uu____14740;
                  FStar_Syntax_Syntax.effect_args = uu____14743;
                  FStar_Syntax_Syntax.flags = flags1
                }  in
              FStar_Syntax_Syntax.Comp uu____14737  in
            {
              FStar_Syntax_Syntax.n = uu____14736;
              FStar_Syntax_Syntax.pos =
                (uu___168_14735.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___168_14735.FStar_Syntax_Syntax.vars)
            }

and (norm_binder :
  cfg -> env -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder) =
  fun cfg  ->
    fun env  ->
      fun uu____14754  ->
        match uu____14754 with
        | (x,imp) ->
            let uu____14757 =
              let uu___170_14758 = x  in
              let uu____14759 = norm cfg env [] x.FStar_Syntax_Syntax.sort
                 in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___170_14758.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___170_14758.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____14759
              }  in
            (uu____14757, imp)

and (norm_binders :
  cfg -> env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders) =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____14765 =
          FStar_List.fold_left
            (fun uu____14783  ->
               fun b  ->
                 match uu____14783 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b  in
                     ((b1 :: nbs'), (dummy :: env1))) ([], env) bs
           in
        match uu____14765 with | (nbs,uu____14823) -> FStar_List.rev nbs

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
            let uu____14839 =
              let uu___171_14840 = rc  in
              let uu____14841 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (norm cfg env [])
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___171_14840.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____14841;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___171_14840.FStar_Syntax_Syntax.residual_flags)
              }  in
            FStar_Pervasives_Native.Some uu____14839
        | uu____14848 -> lopt

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
            (let uu____14869 = FStar_Syntax_Print.term_to_string tm  in
             let uu____14870 = FStar_Syntax_Print.term_to_string tm'  in
             FStar_Util.print3 "%sSimplified\n\t%s to\n\t%s\n"
               (if (cfg.steps).simplify then "" else "NOT ") uu____14869
               uu____14870)
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
          let uu____14890 =
            FStar_All.pipe_left Prims.op_Negation (cfg.steps).simplify  in
          if uu____14890
          then tm1
          else
            (let w t =
               let uu___172_14902 = t  in
               {
                 FStar_Syntax_Syntax.n =
                   (uu___172_14902.FStar_Syntax_Syntax.n);
                 FStar_Syntax_Syntax.pos = (tm1.FStar_Syntax_Syntax.pos);
                 FStar_Syntax_Syntax.vars =
                   (uu___172_14902.FStar_Syntax_Syntax.vars)
               }  in
             let simp_t t =
               let uu____14911 =
                 let uu____14912 = FStar_Syntax_Util.unmeta t  in
                 uu____14912.FStar_Syntax_Syntax.n  in
               match uu____14911 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_Pervasives_Native.Some true
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.false_lid
                   -> FStar_Pervasives_Native.Some false
               | uu____14919 -> FStar_Pervasives_Native.None  in
             let rec args_are_binders args bs =
               match (args, bs) with
               | ((t,uu____14964)::args1,(bv,uu____14967)::bs1) ->
                   let uu____15001 =
                     let uu____15002 = FStar_Syntax_Subst.compress t  in
                     uu____15002.FStar_Syntax_Syntax.n  in
                   (match uu____15001 with
                    | FStar_Syntax_Syntax.Tm_name bv' ->
                        (FStar_Syntax_Syntax.bv_eq bv bv') &&
                          (args_are_binders args1 bs1)
                    | uu____15006 -> false)
               | ([],[]) -> true
               | (uu____15027,uu____15028) -> false  in
             let is_applied bs t =
               let uu____15064 = FStar_Syntax_Util.head_and_args' t  in
               match uu____15064 with
               | (hd1,args) ->
                   let uu____15097 =
                     let uu____15098 = FStar_Syntax_Subst.compress hd1  in
                     uu____15098.FStar_Syntax_Syntax.n  in
                   (match uu____15097 with
                    | FStar_Syntax_Syntax.Tm_name bv when
                        args_are_binders args bs ->
                        FStar_Pervasives_Native.Some bv
                    | uu____15104 -> FStar_Pervasives_Native.None)
                in
             let is_applied_maybe_squashed bs t =
               let uu____15116 = FStar_Syntax_Util.is_squash t  in
               match uu____15116 with
               | FStar_Pervasives_Native.Some (uu____15127,t') ->
                   is_applied bs t'
               | uu____15139 ->
                   let uu____15148 = FStar_Syntax_Util.is_auto_squash t  in
                   (match uu____15148 with
                    | FStar_Pervasives_Native.Some (uu____15159,t') ->
                        is_applied bs t'
                    | uu____15171 -> is_applied bs t)
                in
             let is_quantified_const phi =
               let uu____15188 =
                 FStar_Syntax_Util.destruct_typ_as_formula phi  in
               match uu____15188 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
                   (lid,(p,uu____15195)::(q,uu____15197)::[])) when
                   FStar_Ident.lid_equals lid FStar_Parser_Const.imp_lid ->
                   let uu____15232 =
                     FStar_Syntax_Util.destruct_typ_as_formula p  in
                   (match uu____15232 with
                    | FStar_Pervasives_Native.None  ->
                        let uu____15237 =
                          let uu____15238 = FStar_Syntax_Subst.compress p  in
                          uu____15238.FStar_Syntax_Syntax.n  in
                        (match uu____15237 with
                         | FStar_Syntax_Syntax.Tm_bvar bv ->
                             let uu____15244 =
                               FStar_Syntax_Subst.subst
                                 [FStar_Syntax_Syntax.NT
                                    (bv, FStar_Syntax_Util.t_true)] q
                                in
                             FStar_Pervasives_Native.Some uu____15244
                         | uu____15245 -> FStar_Pervasives_Native.None)
                    | FStar_Pervasives_Native.Some
                        (FStar_Syntax_Util.BaseConn
                        (lid1,(p1,uu____15248)::[])) when
                        FStar_Ident.lid_equals lid1
                          FStar_Parser_Const.not_lid
                        ->
                        let uu____15273 =
                          let uu____15274 = FStar_Syntax_Subst.compress p1
                             in
                          uu____15274.FStar_Syntax_Syntax.n  in
                        (match uu____15273 with
                         | FStar_Syntax_Syntax.Tm_bvar bv ->
                             let uu____15280 =
                               FStar_Syntax_Subst.subst
                                 [FStar_Syntax_Syntax.NT
                                    (bv, FStar_Syntax_Util.t_false)] q
                                in
                             FStar_Pervasives_Native.Some uu____15280
                         | uu____15281 -> FStar_Pervasives_Native.None)
                    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
                        (bs,pats,phi1)) ->
                        let uu____15285 =
                          FStar_Syntax_Util.destruct_typ_as_formula phi1  in
                        (match uu____15285 with
                         | FStar_Pervasives_Native.None  ->
                             let uu____15290 =
                               is_applied_maybe_squashed bs phi1  in
                             (match uu____15290 with
                              | FStar_Pervasives_Native.Some bv ->
                                  let ftrue =
                                    FStar_Syntax_Util.abs bs
                                      FStar_Syntax_Util.t_true
                                      (FStar_Pervasives_Native.Some
                                         (FStar_Syntax_Util.residual_tot
                                            FStar_Syntax_Util.ktype0))
                                     in
                                  let uu____15297 =
                                    FStar_Syntax_Subst.subst
                                      [FStar_Syntax_Syntax.NT (bv, ftrue)] q
                                     in
                                  FStar_Pervasives_Native.Some uu____15297
                              | FStar_Pervasives_Native.None  ->
                                  FStar_Pervasives_Native.None)
                         | FStar_Pervasives_Native.Some
                             (FStar_Syntax_Util.BaseConn
                             (lid1,(p1,uu____15300)::[])) when
                             FStar_Ident.lid_equals lid1
                               FStar_Parser_Const.not_lid
                             ->
                             let uu____15325 =
                               is_applied_maybe_squashed bs p1  in
                             (match uu____15325 with
                              | FStar_Pervasives_Native.Some bv ->
                                  let ffalse =
                                    FStar_Syntax_Util.abs bs
                                      FStar_Syntax_Util.t_false
                                      (FStar_Pervasives_Native.Some
                                         (FStar_Syntax_Util.residual_tot
                                            FStar_Syntax_Util.ktype0))
                                     in
                                  let uu____15332 =
                                    FStar_Syntax_Subst.subst
                                      [FStar_Syntax_Syntax.NT (bv, ffalse)] q
                                     in
                                  FStar_Pervasives_Native.Some uu____15332
                              | uu____15333 -> FStar_Pervasives_Native.None)
                         | uu____15336 -> FStar_Pervasives_Native.None)
                    | uu____15339 -> FStar_Pervasives_Native.None)
               | uu____15342 -> FStar_Pervasives_Native.None  in
             let is_const_match phi =
               let uu____15353 =
                 let uu____15354 = FStar_Syntax_Subst.compress phi  in
                 uu____15354.FStar_Syntax_Syntax.n  in
               match uu____15353 with
               | FStar_Syntax_Syntax.Tm_match (uu____15359,br::brs) ->
                   let uu____15426 = br  in
                   (match uu____15426 with
                    | (uu____15443,uu____15444,e) ->
                        let r =
                          let uu____15465 = simp_t e  in
                          match uu____15465 with
                          | FStar_Pervasives_Native.None  ->
                              FStar_Pervasives_Native.None
                          | FStar_Pervasives_Native.Some b ->
                              let uu____15471 =
                                FStar_List.for_all
                                  (fun uu____15489  ->
                                     match uu____15489 with
                                     | (uu____15502,uu____15503,e') ->
                                         let uu____15517 = simp_t e'  in
                                         uu____15517 =
                                           (FStar_Pervasives_Native.Some b))
                                  brs
                                 in
                              if uu____15471
                              then FStar_Pervasives_Native.Some b
                              else FStar_Pervasives_Native.None
                           in
                        r)
               | uu____15525 -> FStar_Pervasives_Native.None  in
             let maybe_auto_squash t =
               let uu____15530 = FStar_Syntax_Util.is_sub_singleton t  in
               if uu____15530
               then t
               else
                 FStar_Syntax_Util.mk_auto_squash FStar_Syntax_Syntax.U_zero
                   t
                in
             let squashed_head_un_auto_squash_args t =
               let maybe_un_auto_squash_arg uu____15551 =
                 match uu____15551 with
                 | (t1,q) ->
                     let uu____15564 = FStar_Syntax_Util.is_auto_squash t1
                        in
                     (match uu____15564 with
                      | FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.U_zero ,t2) -> (t2, q)
                      | uu____15592 -> (t1, q))
                  in
               let uu____15601 = FStar_Syntax_Util.head_and_args t  in
               match uu____15601 with
               | (head1,args) ->
                   let args1 = FStar_List.map maybe_un_auto_squash_arg args
                      in
                   FStar_Syntax_Syntax.mk_Tm_app head1 args1
                     FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
                in
             let rec clearly_inhabited ty =
               let uu____15663 =
                 let uu____15664 = FStar_Syntax_Util.unmeta ty  in
                 uu____15664.FStar_Syntax_Syntax.n  in
               match uu____15663 with
               | FStar_Syntax_Syntax.Tm_uinst (t,uu____15668) ->
                   clearly_inhabited t
               | FStar_Syntax_Syntax.Tm_arrow (uu____15673,c) ->
                   clearly_inhabited (FStar_Syntax_Util.comp_result c)
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   let l = FStar_Syntax_Syntax.lid_of_fv fv  in
                   (((FStar_Ident.lid_equals l FStar_Parser_Const.int_lid) ||
                       (FStar_Ident.lid_equals l FStar_Parser_Const.bool_lid))
                      ||
                      (FStar_Ident.lid_equals l FStar_Parser_Const.string_lid))
                     || (FStar_Ident.lid_equals l FStar_Parser_Const.exn_lid)
               | uu____15693 -> false  in
             let simplify1 arg =
               let uu____15716 = simp_t (FStar_Pervasives_Native.fst arg)  in
               (uu____15716, arg)  in
             let uu____15725 = is_quantified_const tm1  in
             match uu____15725 with
             | FStar_Pervasives_Native.Some tm2 ->
                 let uu____15729 = norm cfg env [] tm2  in
                 maybe_simplify_aux cfg env stack uu____15729
             | FStar_Pervasives_Native.None  ->
                 let uu____15730 =
                   let uu____15731 = FStar_Syntax_Subst.compress tm1  in
                   uu____15731.FStar_Syntax_Syntax.n  in
                 (match uu____15730 with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                           ({
                              FStar_Syntax_Syntax.n =
                                FStar_Syntax_Syntax.Tm_fvar fv;
                              FStar_Syntax_Syntax.pos = uu____15735;
                              FStar_Syntax_Syntax.vars = uu____15736;_},uu____15737);
                         FStar_Syntax_Syntax.pos = uu____15738;
                         FStar_Syntax_Syntax.vars = uu____15739;_},args)
                      ->
                      let uu____15765 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid
                         in
                      if uu____15765
                      then
                        let uu____15766 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        (match uu____15766 with
                         | (FStar_Pervasives_Native.Some (true ),uu____15813)::
                             (uu____15814,(arg,uu____15816))::[] ->
                             maybe_auto_squash arg
                         | (uu____15865,(arg,uu____15867))::(FStar_Pervasives_Native.Some
                                                             (true
                                                             ),uu____15868)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____15917)::uu____15918::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____15969::(FStar_Pervasives_Native.Some (false
                                         ),uu____15970)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____16021 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____16035 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid
                            in
                         if uu____16035
                         then
                           let uu____16036 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify1)
                              in
                           match uu____16036 with
                           | (FStar_Pervasives_Native.Some (true
                              ),uu____16083)::uu____16084::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____16135::(FStar_Pervasives_Native.Some (true
                                           ),uu____16136)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false
                              ),uu____16187)::(uu____16188,(arg,uu____16190))::[]
                               -> maybe_auto_squash arg
                           | (uu____16239,(arg,uu____16241))::(FStar_Pervasives_Native.Some
                                                               (false
                                                               ),uu____16242)::[]
                               -> maybe_auto_squash arg
                           | uu____16291 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____16305 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid
                               in
                            if uu____16305
                            then
                              let uu____16306 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify1)
                                 in
                              match uu____16306 with
                              | uu____16353::(FStar_Pervasives_Native.Some
                                              (true ),uu____16354)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false
                                 ),uu____16405)::uu____16406::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true
                                 ),uu____16457)::(uu____16458,(arg,uu____16460))::[]
                                  -> maybe_auto_squash arg
                              | (uu____16509,(p,uu____16511))::(uu____16512,
                                                                (q,uu____16514))::[]
                                  ->
                                  let uu____16561 =
                                    FStar_Syntax_Util.term_eq p q  in
                                  (if uu____16561
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____16563 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____16577 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid
                                  in
                               if uu____16577
                               then
                                 let uu____16578 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify1)
                                    in
                                 match uu____16578 with
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____16625)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____16626)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____16677)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____16678)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____16729)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____16730)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____16781)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____16782)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____16833,(arg,uu____16835))::(FStar_Pervasives_Native.Some
                                                                    (true
                                                                    ),uu____16836)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____16885)::(uu____16886,(arg,uu____16888))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____16937,(arg,uu____16939))::(FStar_Pervasives_Native.Some
                                                                    (false
                                                                    ),uu____16940)::[]
                                     ->
                                     let uu____16989 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____16989
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____16990)::(uu____16991,(arg,uu____16993))::[]
                                     ->
                                     let uu____17042 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____17042
                                 | (uu____17043,(p,uu____17045))::(uu____17046,
                                                                   (q,uu____17048))::[]
                                     ->
                                     let uu____17095 =
                                       FStar_Syntax_Util.term_eq p q  in
                                     (if uu____17095
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____17097 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____17111 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid
                                     in
                                  if uu____17111
                                  then
                                    let uu____17112 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify1)
                                       in
                                    match uu____17112 with
                                    | (FStar_Pervasives_Native.Some (true
                                       ),uu____17159)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false
                                       ),uu____17190)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____17221 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____17235 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid
                                        in
                                     if uu____17235
                                     then
                                       match args with
                                       | (t,uu____17237)::[] ->
                                           let uu____17254 =
                                             let uu____17255 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____17255.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____17254 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____17258::[],body,uu____17260)
                                                ->
                                                let uu____17287 = simp_t body
                                                   in
                                                (match uu____17287 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____17290 -> tm1)
                                            | uu____17293 -> tm1)
                                       | (ty,FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____17295))::(t,uu____17297)::[]
                                           ->
                                           let uu____17336 =
                                             let uu____17337 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____17337.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____17336 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____17340::[],body,uu____17342)
                                                ->
                                                let uu____17369 = simp_t body
                                                   in
                                                (match uu____17369 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false ) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____17372 -> tm1)
                                            | uu____17375 -> tm1)
                                       | uu____17376 -> tm1
                                     else
                                       (let uu____17386 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid
                                           in
                                        if uu____17386
                                        then
                                          match args with
                                          | (t,uu____17388)::[] ->
                                              let uu____17405 =
                                                let uu____17406 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____17406.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____17405 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____17409::[],body,uu____17411)
                                                   ->
                                                   let uu____17438 =
                                                     simp_t body  in
                                                   (match uu____17438 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____17441 -> tm1)
                                               | uu____17444 -> tm1)
                                          | (ty,FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____17446))::(t,uu____17448)::[]
                                              ->
                                              let uu____17487 =
                                                let uu____17488 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____17488.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____17487 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____17491::[],body,uu____17493)
                                                   ->
                                                   let uu____17520 =
                                                     simp_t body  in
                                                   (match uu____17520 with
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
                                                    | uu____17523 -> tm1)
                                               | uu____17526 -> tm1)
                                          | uu____17527 -> tm1
                                        else
                                          (let uu____17537 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid
                                              in
                                           if uu____17537
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____17538;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____17539;_},uu____17540)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____17557;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____17558;_},uu____17559)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____17576 -> tm1
                                           else
                                             (let uu____17586 =
                                                FStar_Syntax_Util.is_auto_squash
                                                  tm1
                                                 in
                                              match uu____17586 with
                                              | FStar_Pervasives_Native.Some
                                                  (FStar_Syntax_Syntax.U_zero
                                                   ,t)
                                                  when
                                                  FStar_Syntax_Util.is_sub_singleton
                                                    t
                                                  -> t
                                              | uu____17606 ->
                                                  reduce_equality cfg env
                                                    stack tm1))))))))
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____17616;
                         FStar_Syntax_Syntax.vars = uu____17617;_},args)
                      ->
                      let uu____17639 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid
                         in
                      if uu____17639
                      then
                        let uu____17640 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        (match uu____17640 with
                         | (FStar_Pervasives_Native.Some (true ),uu____17687)::
                             (uu____17688,(arg,uu____17690))::[] ->
                             maybe_auto_squash arg
                         | (uu____17739,(arg,uu____17741))::(FStar_Pervasives_Native.Some
                                                             (true
                                                             ),uu____17742)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____17791)::uu____17792::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____17843::(FStar_Pervasives_Native.Some (false
                                         ),uu____17844)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____17895 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____17909 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid
                            in
                         if uu____17909
                         then
                           let uu____17910 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify1)
                              in
                           match uu____17910 with
                           | (FStar_Pervasives_Native.Some (true
                              ),uu____17957)::uu____17958::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____18009::(FStar_Pervasives_Native.Some (true
                                           ),uu____18010)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false
                              ),uu____18061)::(uu____18062,(arg,uu____18064))::[]
                               -> maybe_auto_squash arg
                           | (uu____18113,(arg,uu____18115))::(FStar_Pervasives_Native.Some
                                                               (false
                                                               ),uu____18116)::[]
                               -> maybe_auto_squash arg
                           | uu____18165 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____18179 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid
                               in
                            if uu____18179
                            then
                              let uu____18180 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify1)
                                 in
                              match uu____18180 with
                              | uu____18227::(FStar_Pervasives_Native.Some
                                              (true ),uu____18228)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false
                                 ),uu____18279)::uu____18280::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true
                                 ),uu____18331)::(uu____18332,(arg,uu____18334))::[]
                                  -> maybe_auto_squash arg
                              | (uu____18383,(p,uu____18385))::(uu____18386,
                                                                (q,uu____18388))::[]
                                  ->
                                  let uu____18435 =
                                    FStar_Syntax_Util.term_eq p q  in
                                  (if uu____18435
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____18437 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____18451 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid
                                  in
                               if uu____18451
                               then
                                 let uu____18452 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify1)
                                    in
                                 match uu____18452 with
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____18499)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____18500)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____18551)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____18552)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____18603)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____18604)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____18655)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____18656)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____18707,(arg,uu____18709))::(FStar_Pervasives_Native.Some
                                                                    (true
                                                                    ),uu____18710)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____18759)::(uu____18760,(arg,uu____18762))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____18811,(arg,uu____18813))::(FStar_Pervasives_Native.Some
                                                                    (false
                                                                    ),uu____18814)::[]
                                     ->
                                     let uu____18863 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____18863
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____18864)::(uu____18865,(arg,uu____18867))::[]
                                     ->
                                     let uu____18916 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____18916
                                 | (uu____18917,(p,uu____18919))::(uu____18920,
                                                                   (q,uu____18922))::[]
                                     ->
                                     let uu____18969 =
                                       FStar_Syntax_Util.term_eq p q  in
                                     (if uu____18969
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____18971 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____18985 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid
                                     in
                                  if uu____18985
                                  then
                                    let uu____18986 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify1)
                                       in
                                    match uu____18986 with
                                    | (FStar_Pervasives_Native.Some (true
                                       ),uu____19033)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false
                                       ),uu____19064)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____19095 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____19109 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid
                                        in
                                     if uu____19109
                                     then
                                       match args with
                                       | (t,uu____19111)::[] ->
                                           let uu____19128 =
                                             let uu____19129 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____19129.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____19128 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____19132::[],body,uu____19134)
                                                ->
                                                let uu____19161 = simp_t body
                                                   in
                                                (match uu____19161 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____19164 -> tm1)
                                            | uu____19167 -> tm1)
                                       | (ty,FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____19169))::(t,uu____19171)::[]
                                           ->
                                           let uu____19210 =
                                             let uu____19211 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____19211.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____19210 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____19214::[],body,uu____19216)
                                                ->
                                                let uu____19243 = simp_t body
                                                   in
                                                (match uu____19243 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false ) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____19246 -> tm1)
                                            | uu____19249 -> tm1)
                                       | uu____19250 -> tm1
                                     else
                                       (let uu____19260 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid
                                           in
                                        if uu____19260
                                        then
                                          match args with
                                          | (t,uu____19262)::[] ->
                                              let uu____19279 =
                                                let uu____19280 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____19280.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____19279 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____19283::[],body,uu____19285)
                                                   ->
                                                   let uu____19312 =
                                                     simp_t body  in
                                                   (match uu____19312 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____19315 -> tm1)
                                               | uu____19318 -> tm1)
                                          | (ty,FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____19320))::(t,uu____19322)::[]
                                              ->
                                              let uu____19361 =
                                                let uu____19362 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____19362.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____19361 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____19365::[],body,uu____19367)
                                                   ->
                                                   let uu____19394 =
                                                     simp_t body  in
                                                   (match uu____19394 with
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
                                                    | uu____19397 -> tm1)
                                               | uu____19400 -> tm1)
                                          | uu____19401 -> tm1
                                        else
                                          (let uu____19411 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid
                                              in
                                           if uu____19411
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____19412;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____19413;_},uu____19414)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____19431;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____19432;_},uu____19433)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____19450 -> tm1
                                           else
                                             (let uu____19460 =
                                                FStar_Syntax_Util.is_auto_squash
                                                  tm1
                                                 in
                                              match uu____19460 with
                                              | FStar_Pervasives_Native.Some
                                                  (FStar_Syntax_Syntax.U_zero
                                                   ,t)
                                                  when
                                                  FStar_Syntax_Util.is_sub_singleton
                                                    t
                                                  -> t
                                              | uu____19480 ->
                                                  reduce_equality cfg env
                                                    stack tm1))))))))
                  | FStar_Syntax_Syntax.Tm_refine (bv,t) ->
                      let uu____19495 = simp_t t  in
                      (match uu____19495 with
                       | FStar_Pervasives_Native.Some (true ) ->
                           bv.FStar_Syntax_Syntax.sort
                       | FStar_Pervasives_Native.Some (false ) -> tm1
                       | FStar_Pervasives_Native.None  -> tm1)
                  | FStar_Syntax_Syntax.Tm_match uu____19498 ->
                      let uu____19521 = is_const_match tm1  in
                      (match uu____19521 with
                       | FStar_Pervasives_Native.Some (true ) ->
                           w FStar_Syntax_Util.t_true
                       | FStar_Pervasives_Native.Some (false ) ->
                           w FStar_Syntax_Util.t_false
                       | FStar_Pervasives_Native.None  -> tm1)
                  | uu____19524 -> tm1))

and (rebuild :
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          log cfg
            (fun uu____19535  ->
               let uu____19536 = FStar_Syntax_Print.tag_of_term t  in
               let uu____19537 = FStar_Syntax_Print.term_to_string t  in
               let uu____19538 =
                 FStar_Util.string_of_int (FStar_List.length env)  in
               let uu____19545 =
                 let uu____19546 =
                   let uu____19549 = firstn (Prims.parse_int "4") stack  in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____19549
                    in
                 stack_to_string uu____19546  in
               FStar_Util.print4
                 ">>> %s\nRebuild %s with %s env elements and top of the stack %s \n"
                 uu____19536 uu____19537 uu____19538 uu____19545);
          (let t1 = maybe_simplify cfg env stack t  in
           match stack with
           | [] -> t1
           | (Debug (tm,time_then))::stack1 ->
               (if (cfg.debug).print_normalized
                then
                  (let time_now = FStar_Util.now ()  in
                   let uu____19580 =
                     let uu____19581 =
                       let uu____19582 =
                         FStar_Util.time_diff time_then time_now  in
                       FStar_Pervasives_Native.snd uu____19582  in
                     FStar_Util.string_of_int uu____19581  in
                   let uu____19587 = FStar_Syntax_Print.term_to_string tm  in
                   let uu____19588 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.print3 "Normalized (%s ms) %s\n\tto %s\n"
                     uu____19580 uu____19587 uu____19588)
                else ();
                rebuild cfg env stack1 t1)
           | (Cfg cfg1)::stack1 -> rebuild cfg1 env stack1 t1
           | (Meta (m,r))::stack1 ->
               let t2 = mk (FStar_Syntax_Syntax.Tm_meta (t1, m)) r  in
               rebuild cfg env stack1 t2
           | (MemoLazy r)::stack1 ->
               (set_memo cfg r (env, t1);
                log cfg
                  (fun uu____19642  ->
                     let uu____19643 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 "\tSet memo %s\n" uu____19643);
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
               let uu____19679 =
                 let uu___173_19680 = FStar_Syntax_Util.abs bs1 t1 lopt1  in
                 {
                   FStar_Syntax_Syntax.n =
                     (uu___173_19680.FStar_Syntax_Syntax.n);
                   FStar_Syntax_Syntax.pos = r;
                   FStar_Syntax_Syntax.vars =
                     (uu___173_19680.FStar_Syntax_Syntax.vars)
                 }  in
               rebuild cfg env stack1 uu____19679
           | (Arg (Univ uu____19681,uu____19682,uu____19683))::uu____19684 ->
               failwith "Impossible"
           | (Arg (Dummy ,uu____19687,uu____19688))::uu____19689 ->
               failwith "Impossible"
           | (UnivArgs (us,r))::stack1 ->
               let t2 = FStar_Syntax_Syntax.mk_Tm_uinst t1 us  in
               rebuild cfg env stack1 t2
           | (Arg (Clos (env_arg,tm,uu____19704,uu____19705),aq,r))::stack1
               when
               let uu____19755 = head_of t1  in
               FStar_Syntax_Util.is_fstar_tactics_by_tactic uu____19755 ->
               let t2 =
                 let uu____19759 =
                   let uu____19760 =
                     let uu____19761 = closure_as_term cfg env_arg tm  in
                     (uu____19761, aq)  in
                   FStar_Syntax_Syntax.extend_app t1 uu____19760  in
                 uu____19759 FStar_Pervasives_Native.None r  in
               rebuild cfg env stack1 t2
           | (Arg (Clos (env_arg,tm,m,uu____19767),aq,r))::stack1 ->
               (log cfg
                  (fun uu____19820  ->
                     let uu____19821 = FStar_Syntax_Print.term_to_string tm
                        in
                     FStar_Util.print1 "Rebuilding with arg %s\n" uu____19821);
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
                  (let uu____19831 = FStar_ST.op_Bang m  in
                   match uu____19831 with
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
                   | FStar_Pervasives_Native.Some (uu____19968,a) ->
                       let t2 =
                         FStar_Syntax_Syntax.extend_app t1 (a, aq)
                           FStar_Pervasives_Native.None r
                          in
                       rebuild cfg env_arg stack1 t2))
           | (App (env1,head1,aq,r))::stack' when should_reify cfg stack ->
               let t0 = t1  in
               let fallback msg uu____20015 =
                 log cfg
                   (fun uu____20019  ->
                      let uu____20020 = FStar_Syntax_Print.term_to_string t1
                         in
                      FStar_Util.print2 "Not reifying%s: %s\n" msg
                        uu____20020);
                 (let t2 =
                    FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                      FStar_Pervasives_Native.None r
                     in
                  rebuild cfg env1 stack' t2)
                  in
               let uu____20024 =
                 let uu____20025 = FStar_Syntax_Subst.compress t1  in
                 uu____20025.FStar_Syntax_Syntax.n  in
               (match uu____20024 with
                | FStar_Syntax_Syntax.Tm_meta
                    (t2,FStar_Syntax_Syntax.Meta_monadic (m,ty)) ->
                    do_reify_monadic (fallback " (1)") cfg env1 stack t2 m ty
                | FStar_Syntax_Syntax.Tm_meta
                    (t2,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,ty))
                    ->
                    let lifted =
                      let uu____20052 = closure_as_term cfg env1 ty  in
                      reify_lift cfg t2 msrc mtgt uu____20052  in
                    (log cfg
                       (fun uu____20056  ->
                          let uu____20057 =
                            FStar_Syntax_Print.term_to_string lifted  in
                          FStar_Util.print1 "Reified lift to (1): %s\n"
                            uu____20057);
                     (let uu____20058 = FStar_List.tl stack  in
                      norm cfg env1 uu____20058 lifted))
                | FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reflect uu____20059);
                       FStar_Syntax_Syntax.pos = uu____20060;
                       FStar_Syntax_Syntax.vars = uu____20061;_},(e,uu____20063)::[])
                    -> norm cfg env1 stack' e
                | FStar_Syntax_Syntax.Tm_app uu____20092 when
                    (cfg.steps).primops ->
                    let uu____20107 = FStar_Syntax_Util.head_and_args t1  in
                    (match uu____20107 with
                     | (hd1,args) ->
                         let uu____20144 =
                           let uu____20145 = FStar_Syntax_Util.un_uinst hd1
                              in
                           uu____20145.FStar_Syntax_Syntax.n  in
                         (match uu____20144 with
                          | FStar_Syntax_Syntax.Tm_fvar fv ->
                              let uu____20149 = find_prim_step cfg fv  in
                              (match uu____20149 with
                               | FStar_Pervasives_Native.Some
                                   { name = uu____20152; arity = uu____20153;
                                     auto_reflect =
                                       FStar_Pervasives_Native.Some n1;
                                     strong_reduction_ok = uu____20155;
                                     requires_binder_substitution =
                                       uu____20156;
                                     interpretation = uu____20157;_}
                                   when (FStar_List.length args) = n1 ->
                                   norm cfg env1 stack' t1
                               | uu____20170 -> fallback " (3)" ())
                          | uu____20173 -> fallback " (4)" ()))
                | uu____20174 -> fallback " (2)" ())
           | (App (env1,head1,aq,r))::stack1 ->
               let t2 =
                 FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                   FStar_Pervasives_Native.None r
                  in
               rebuild cfg env1 stack1 t2
           | (Match (env1,branches,r))::stack1 ->
               (log cfg
                  (fun uu____20194  ->
                     let uu____20195 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1
                       "Rebuilding with match, scrutinee is %s ...\n"
                       uu____20195);
                (let scrutinee = t1  in
                 let norm_and_rebuild_match uu____20200 =
                   log cfg
                     (fun uu____20205  ->
                        let uu____20206 =
                          FStar_Syntax_Print.term_to_string scrutinee  in
                        let uu____20207 =
                          let uu____20208 =
                            FStar_All.pipe_right branches
                              (FStar_List.map
                                 (fun uu____20225  ->
                                    match uu____20225 with
                                    | (p,uu____20235,uu____20236) ->
                                        FStar_Syntax_Print.pat_to_string p))
                             in
                          FStar_All.pipe_right uu____20208
                            (FStar_String.concat "\n\t")
                           in
                        FStar_Util.print2
                          "match is irreducible: scrutinee=%s\nbranches=%s\n"
                          uu____20206 uu____20207);
                   (let whnf = (cfg.steps).weak || (cfg.steps).hnf  in
                    let cfg_exclude_iota_zeta =
                      let new_delta =
                        FStar_All.pipe_right cfg.delta_level
                          (FStar_List.filter
                             (fun uu___89_20253  ->
                                match uu___89_20253 with
                                | FStar_TypeChecker_Env.Inlining  -> true
                                | FStar_TypeChecker_Env.Eager_unfolding_only 
                                    -> true
                                | uu____20254 -> false))
                         in
                      let uu___174_20255 = cfg  in
                      {
                        steps =
                          (let uu___175_20258 = cfg.steps  in
                           {
                             beta = (uu___175_20258.beta);
                             iota = (uu___175_20258.iota);
                             zeta = false;
                             weak = (uu___175_20258.weak);
                             hnf = (uu___175_20258.hnf);
                             primops = (uu___175_20258.primops);
                             no_delta_steps = (uu___175_20258.no_delta_steps);
                             unfold_until = (uu___175_20258.unfold_until);
                             unfold_only = (uu___175_20258.unfold_only);
                             unfold_attr = (uu___175_20258.unfold_attr);
                             unfold_tac = (uu___175_20258.unfold_tac);
                             pure_subterms_within_computations =
                               (uu___175_20258.pure_subterms_within_computations);
                             simplify = (uu___175_20258.simplify);
                             erase_universes =
                               (uu___175_20258.erase_universes);
                             allow_unbound_universes =
                               (uu___175_20258.allow_unbound_universes);
                             reify_ = (uu___175_20258.reify_);
                             compress_uvars = (uu___175_20258.compress_uvars);
                             no_full_norm = (uu___175_20258.no_full_norm);
                             check_no_uvars = (uu___175_20258.check_no_uvars);
                             unmeta = (uu___175_20258.unmeta);
                             unascribe = (uu___175_20258.unascribe)
                           });
                        tcenv = (uu___174_20255.tcenv);
                        debug = (uu___174_20255.debug);
                        delta_level = new_delta;
                        primitive_steps = (uu___174_20255.primitive_steps);
                        strong = true;
                        memoize_lazy = (uu___174_20255.memoize_lazy);
                        normalize_pure_lets =
                          (uu___174_20255.normalize_pure_lets)
                      }  in
                    let norm_or_whnf env2 t2 =
                      if whnf
                      then closure_as_term cfg_exclude_iota_zeta env2 t2
                      else norm cfg_exclude_iota_zeta env2 [] t2  in
                    let rec norm_pat env2 p =
                      match p.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_constant uu____20290 ->
                          (p, env2)
                      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                          let uu____20311 =
                            FStar_All.pipe_right pats
                              (FStar_List.fold_left
                                 (fun uu____20371  ->
                                    fun uu____20372  ->
                                      match (uu____20371, uu____20372) with
                                      | ((pats1,env3),(p1,b)) ->
                                          let uu____20463 = norm_pat env3 p1
                                             in
                                          (match uu____20463 with
                                           | (p2,env4) ->
                                               (((p2, b) :: pats1), env4)))
                                 ([], env2))
                             in
                          (match uu____20311 with
                           | (pats1,env3) ->
                               ((let uu___176_20545 = p  in
                                 {
                                   FStar_Syntax_Syntax.v =
                                     (FStar_Syntax_Syntax.Pat_cons
                                        (fv, (FStar_List.rev pats1)));
                                   FStar_Syntax_Syntax.p =
                                     (uu___176_20545.FStar_Syntax_Syntax.p)
                                 }), env3))
                      | FStar_Syntax_Syntax.Pat_var x ->
                          let x1 =
                            let uu___177_20564 = x  in
                            let uu____20565 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___177_20564.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___177_20564.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____20565
                            }  in
                          ((let uu___178_20579 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_var x1);
                              FStar_Syntax_Syntax.p =
                                (uu___178_20579.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_wild x ->
                          let x1 =
                            let uu___179_20590 = x  in
                            let uu____20591 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___179_20590.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___179_20590.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____20591
                            }  in
                          ((let uu___180_20605 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_wild x1);
                              FStar_Syntax_Syntax.p =
                                (uu___180_20605.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                          let x1 =
                            let uu___181_20621 = x  in
                            let uu____20622 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___181_20621.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___181_20621.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____20622
                            }  in
                          let t3 = norm_or_whnf env2 t2  in
                          ((let uu___182_20629 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_dot_term (x1, t3));
                              FStar_Syntax_Syntax.p =
                                (uu___182_20629.FStar_Syntax_Syntax.p)
                            }), env2)
                       in
                    let branches1 =
                      match env1 with
                      | [] when whnf -> branches
                      | uu____20639 ->
                          FStar_All.pipe_right branches
                            (FStar_List.map
                               (fun branch1  ->
                                  let uu____20653 =
                                    FStar_Syntax_Subst.open_branch branch1
                                     in
                                  match uu____20653 with
                                  | (p,wopt,e) ->
                                      let uu____20673 = norm_pat env1 p  in
                                      (match uu____20673 with
                                       | (p1,env2) ->
                                           let wopt1 =
                                             match wopt with
                                             | FStar_Pervasives_Native.None 
                                                 ->
                                                 FStar_Pervasives_Native.None
                                             | FStar_Pervasives_Native.Some w
                                                 ->
                                                 let uu____20698 =
                                                   norm_or_whnf env2 w  in
                                                 FStar_Pervasives_Native.Some
                                                   uu____20698
                                              in
                                           let e1 = norm_or_whnf env2 e  in
                                           FStar_Syntax_Util.branch
                                             (p1, wopt1, e1))))
                       in
                    let uu____20704 =
                      mk
                        (FStar_Syntax_Syntax.Tm_match (scrutinee, branches1))
                        r
                       in
                    rebuild cfg env1 stack1 uu____20704)
                    in
                 let rec is_cons head1 =
                   let uu____20709 =
                     let uu____20710 = FStar_Syntax_Subst.compress head1  in
                     uu____20710.FStar_Syntax_Syntax.n  in
                   match uu____20709 with
                   | FStar_Syntax_Syntax.Tm_uinst (h,uu____20714) ->
                       is_cons h
                   | FStar_Syntax_Syntax.Tm_constant uu____20719 -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____20720;
                         FStar_Syntax_Syntax.fv_delta = uu____20721;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Data_ctor );_}
                       -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____20722;
                         FStar_Syntax_Syntax.fv_delta = uu____20723;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Record_ctor uu____20724);_}
                       -> true
                   | uu____20731 -> false  in
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
                   let uu____20876 =
                     FStar_Syntax_Util.head_and_args scrutinee1  in
                   match uu____20876 with
                   | (head1,args) ->
                       (match p.FStar_Syntax_Syntax.v with
                        | FStar_Syntax_Syntax.Pat_var bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_wild bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_dot_term uu____20963 ->
                            FStar_Util.Inl []
                        | FStar_Syntax_Syntax.Pat_constant s ->
                            (match scrutinee1.FStar_Syntax_Syntax.n with
                             | FStar_Syntax_Syntax.Tm_constant s' when
                                 FStar_Const.eq_const s s' ->
                                 FStar_Util.Inl []
                             | uu____21002 ->
                                 let uu____21003 =
                                   let uu____21004 = is_cons head1  in
                                   Prims.op_Negation uu____21004  in
                                 FStar_Util.Inr uu____21003)
                        | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                            let uu____21029 =
                              let uu____21030 =
                                FStar_Syntax_Util.un_uinst head1  in
                              uu____21030.FStar_Syntax_Syntax.n  in
                            (match uu____21029 with
                             | FStar_Syntax_Syntax.Tm_fvar fv' when
                                 FStar_Syntax_Syntax.fv_eq fv fv' ->
                                 matches_args [] args arg_pats
                             | uu____21048 ->
                                 let uu____21049 =
                                   let uu____21050 = is_cons head1  in
                                   Prims.op_Negation uu____21050  in
                                 FStar_Util.Inr uu____21049))
                 
                 and matches_args out a p =
                   match (a, p) with
                   | ([],[]) -> FStar_Util.Inl out
                   | ((t2,uu____21119)::rest_a,(p1,uu____21122)::rest_p) ->
                       let uu____21166 = matches_pat t2 p1  in
                       (match uu____21166 with
                        | FStar_Util.Inl s ->
                            matches_args (FStar_List.append out s) rest_a
                              rest_p
                        | m -> m)
                   | uu____21215 -> FStar_Util.Inr false
                  in
                 let rec matches scrutinee1 p =
                   match p with
                   | [] -> norm_and_rebuild_match ()
                   | (p1,wopt,b)::rest ->
                       let uu____21321 = matches_pat scrutinee1 p1  in
                       (match uu____21321 with
                        | FStar_Util.Inr (false ) -> matches scrutinee1 rest
                        | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                        | FStar_Util.Inl s ->
                            (log cfg
                               (fun uu____21361  ->
                                  let uu____21362 =
                                    FStar_Syntax_Print.pat_to_string p1  in
                                  let uu____21363 =
                                    let uu____21364 =
                                      FStar_List.map
                                        (fun uu____21374  ->
                                           match uu____21374 with
                                           | (uu____21379,t2) ->
                                               FStar_Syntax_Print.term_to_string
                                                 t2) s
                                       in
                                    FStar_All.pipe_right uu____21364
                                      (FStar_String.concat "; ")
                                     in
                                  FStar_Util.print2
                                    "Matches pattern %s with subst = %s\n"
                                    uu____21362 uu____21363);
                             (let env2 =
                                FStar_List.fold_left
                                  (fun env2  ->
                                     fun uu____21410  ->
                                       match uu____21410 with
                                       | (bv,t2) ->
                                           let uu____21433 =
                                             let uu____21440 =
                                               let uu____21443 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   bv
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 uu____21443
                                                in
                                             let uu____21444 =
                                               let uu____21445 =
                                                 let uu____21476 =
                                                   FStar_Util.mk_ref
                                                     (FStar_Pervasives_Native.Some
                                                        ([], t2))
                                                    in
                                                 ([], t2, uu____21476, false)
                                                  in
                                               Clos uu____21445  in
                                             (uu____21440, uu____21444)  in
                                           uu____21433 :: env2) env1 s
                                 in
                              let uu____21593 = guard_when_clause wopt b rest
                                 in
                              norm cfg env2 stack1 uu____21593)))
                    in
                 if (cfg.steps).iota
                 then matches scrutinee branches
                 else norm_and_rebuild_match ())))

let (plugins :
  (primitive_step -> Prims.unit,Prims.unit -> primitive_step Prims.list)
    FStar_Pervasives_Native.tuple2)
  =
  let plugins = FStar_Util.mk_ref []  in
  let register p =
    let uu____21616 =
      let uu____21619 = FStar_ST.op_Bang plugins  in p :: uu____21619  in
    FStar_ST.op_Colon_Equals plugins uu____21616  in
  let retrieve uu____21717 = FStar_ST.op_Bang plugins  in
  (register, retrieve) 
let (register_plugin : primitive_step -> Prims.unit) =
  fun p  -> FStar_Pervasives_Native.fst plugins p 
let (retrieve_plugins : Prims.unit -> primitive_step Prims.list) =
  fun uu____21782  -> FStar_Pervasives_Native.snd plugins () 
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
               (fun uu___90_21815  ->
                  match uu___90_21815 with
                  | UnfoldUntil k -> [FStar_TypeChecker_Env.Unfold k]
                  | Eager_unfolding  ->
                      [FStar_TypeChecker_Env.Eager_unfolding_only]
                  | Inlining  -> [FStar_TypeChecker_Env.Inlining]
                  | UnfoldTac  -> [FStar_TypeChecker_Env.UnfoldTac]
                  | uu____21819 -> []))
           in
        let d1 =
          match d with
          | [] -> [FStar_TypeChecker_Env.NoDelta]
          | uu____21825 -> d  in
        let uu____21828 = to_fsteps s  in
        let uu____21829 =
          let uu____21830 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Norm")  in
          let uu____21831 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Primops")  in
          let uu____21832 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "380")  in
          let uu____21833 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "NormDelayed")
             in
          let uu____21834 =
            FStar_TypeChecker_Env.debug e
              (FStar_Options.Other "print_normalized_terms")
             in
          {
            gen = uu____21830;
            primop = uu____21831;
            b380 = uu____21832;
            norm_delayed = uu____21833;
            print_normalized = uu____21834
          }  in
        let uu____21835 =
          let uu____21838 =
            let uu____21841 = retrieve_plugins ()  in
            FStar_List.append uu____21841 psteps  in
          add_steps built_in_primitive_steps uu____21838  in
        let uu____21844 =
          (FStar_Options.normalize_pure_terms_for_extraction ()) ||
            (let uu____21846 =
               FStar_All.pipe_right s
                 (FStar_List.contains PureSubtermsWithinComputations)
                in
             Prims.op_Negation uu____21846)
           in
        {
          steps = uu____21828;
          tcenv = e;
          debug = uu____21829;
          delta_level = d1;
          primitive_steps = uu____21835;
          strong = false;
          memoize_lazy = true;
          normalize_pure_lets = uu____21844
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
      fun t  -> let uu____21904 = config s e  in norm_comp uu____21904 [] t
  
let (normalize_universe :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun u  ->
      let uu____21917 = config [] env  in norm_universe uu____21917 [] u
  
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
        let uu____21935 = norm cfg [] [] t  in
        FStar_Syntax_Util.non_informative uu____21935  in
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____21942 -> c
      | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
          let uu___183_21961 = c  in
          {
            FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
            FStar_Syntax_Syntax.pos =
              (uu___183_21961.FStar_Syntax_Syntax.pos);
            FStar_Syntax_Syntax.vars =
              (uu___183_21961.FStar_Syntax_Syntax.vars)
          }
      | FStar_Syntax_Syntax.Comp ct ->
          let l =
            FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
              ct.FStar_Syntax_Syntax.effect_name
             in
          let uu____21968 =
            (FStar_Syntax_Util.is_ghost_effect l) &&
              (non_info ct.FStar_Syntax_Syntax.result_typ)
             in
          if uu____21968
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
                  let uu___184_21977 = ct  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___184_21977.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name = pure_eff;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___184_21977.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___184_21977.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags = flags1
                  }
              | FStar_Pervasives_Native.None  ->
                  let ct1 =
                    FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c
                     in
                  let uu___185_21979 = ct1  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___185_21979.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name =
                      FStar_Parser_Const.effect_PURE_lid;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___185_21979.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___185_21979.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags =
                      (uu___185_21979.FStar_Syntax_Syntax.flags)
                  }
               in
            let uu___186_21980 = c  in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
              FStar_Syntax_Syntax.pos =
                (uu___186_21980.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___186_21980.FStar_Syntax_Syntax.vars)
            }
          else c
      | uu____21982 -> c
  
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
        let uu____21994 = norm cfg [] [] t  in
        FStar_Syntax_Util.non_informative uu____21994  in
      let uu____22001 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ)
         in
      if uu____22001
      then
        match downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name
        with
        | FStar_Pervasives_Native.Some pure_eff ->
            FStar_Syntax_Syntax.mk_lcomp pure_eff
              lc.FStar_Syntax_Syntax.res_typ lc.FStar_Syntax_Syntax.cflags
              (fun uu____22005  ->
                 let uu____22006 = FStar_Syntax_Syntax.lcomp_comp lc  in
                 ghost_to_pure env uu____22006)
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
            ((let uu____22023 =
                let uu____22028 =
                  let uu____22029 = FStar_Util.message_of_exn e  in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____22029
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____22028)  in
              FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____22023);
             t)
         in
      FStar_Syntax_Print.term_to_string' env.FStar_TypeChecker_Env.dsenv t1
  
let (comp_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string) =
  fun env  ->
    fun c  ->
      let c1 =
        try
          let uu____22040 = config [AllowUnboundUniverses] env  in
          norm_comp uu____22040 [] c
        with
        | e ->
            ((let uu____22053 =
                let uu____22058 =
                  let uu____22059 = FStar_Util.message_of_exn e  in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____22059
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____22058)  in
              FStar_Errors.log_issue c.FStar_Syntax_Syntax.pos uu____22053);
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
                   let uu____22096 =
                     let uu____22097 =
                       let uu____22104 = FStar_Syntax_Util.mk_conj phi1 phi
                          in
                       (y, uu____22104)  in
                     FStar_Syntax_Syntax.Tm_refine uu____22097  in
                   mk uu____22096 t01.FStar_Syntax_Syntax.pos
               | uu____22109 -> t2)
          | uu____22110 -> t2  in
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
        let uu____22150 = FStar_Syntax_Util.arrow_formals_comp t_e  in
        match uu____22150 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____22179 ->
                 let uu____22186 = FStar_Syntax_Util.abs_formals e  in
                 (match uu____22186 with
                  | (actuals,uu____22196,uu____22197) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____22211 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders
                            in
                         match uu____22211 with
                         | (binders,args) ->
                             let uu____22228 =
                               FStar_Syntax_Syntax.mk_Tm_app e args
                                 FStar_Pervasives_Native.None
                                 e.FStar_Syntax_Syntax.pos
                                in
                             FStar_Syntax_Util.abs binders uu____22228
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
      | uu____22236 ->
          let uu____22237 = FStar_Syntax_Util.head_and_args t  in
          (match uu____22237 with
           | (head1,args) ->
               let uu____22274 =
                 let uu____22275 = FStar_Syntax_Subst.compress head1  in
                 uu____22275.FStar_Syntax_Syntax.n  in
               (match uu____22274 with
                | FStar_Syntax_Syntax.Tm_uvar (uu____22278,thead) ->
                    let uu____22304 = FStar_Syntax_Util.arrow_formals thead
                       in
                    (match uu____22304 with
                     | (formals,tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____22346 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___191_22354 = env  in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___191_22354.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___191_22354.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___191_22354.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___191_22354.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___191_22354.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___191_22354.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___191_22354.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___191_22354.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___191_22354.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___191_22354.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___191_22354.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___191_22354.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___191_22354.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___191_22354.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___191_22354.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___191_22354.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___191_22354.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___191_22354.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___191_22354.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___191_22354.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___191_22354.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___191_22354.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___191_22354.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___191_22354.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                     =
                                     (uu___191_22354.FStar_TypeChecker_Env.qtbl_name_and_index);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___191_22354.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth_hook =
                                     (uu___191_22354.FStar_TypeChecker_Env.synth_hook);
                                   FStar_TypeChecker_Env.splice =
                                     (uu___191_22354.FStar_TypeChecker_Env.splice);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___191_22354.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___191_22354.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___191_22354.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___191_22354.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.dep_graph =
                                     (uu___191_22354.FStar_TypeChecker_Env.dep_graph)
                                 }) t
                               in
                            match uu____22346 with
                            | (uu____22355,ty,uu____22357) ->
                                eta_expand_with_type env t ty))
                | uu____22358 ->
                    let uu____22359 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___192_22367 = env  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___192_22367.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___192_22367.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___192_22367.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___192_22367.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___192_22367.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___192_22367.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___192_22367.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___192_22367.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___192_22367.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___192_22367.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___192_22367.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___192_22367.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___192_22367.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___192_22367.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___192_22367.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___192_22367.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___192_22367.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___192_22367.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.failhard =
                             (uu___192_22367.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___192_22367.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___192_22367.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___192_22367.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___192_22367.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___192_22367.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qtbl_name_and_index =
                             (uu___192_22367.FStar_TypeChecker_Env.qtbl_name_and_index);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___192_22367.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth_hook =
                             (uu___192_22367.FStar_TypeChecker_Env.synth_hook);
                           FStar_TypeChecker_Env.splice =
                             (uu___192_22367.FStar_TypeChecker_Env.splice);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___192_22367.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___192_22367.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___192_22367.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___192_22367.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.dep_graph =
                             (uu___192_22367.FStar_TypeChecker_Env.dep_graph)
                         }) t
                       in
                    (match uu____22359 with
                     | (uu____22368,ty,uu____22370) ->
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
      let uu___193_22427 = x  in
      let uu____22428 = elim_delayed_subst_term x.FStar_Syntax_Syntax.sort
         in
      {
        FStar_Syntax_Syntax.ppname =
          (uu___193_22427.FStar_Syntax_Syntax.ppname);
        FStar_Syntax_Syntax.index =
          (uu___193_22427.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = uu____22428
      }  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____22431 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_bvar uu____22456 -> t1
    | FStar_Syntax_Syntax.Tm_name uu____22457 -> t1
    | FStar_Syntax_Syntax.Tm_fvar uu____22458 -> t1
    | FStar_Syntax_Syntax.Tm_uinst uu____22459 -> t1
    | FStar_Syntax_Syntax.Tm_constant uu____22466 -> t1
    | FStar_Syntax_Syntax.Tm_type uu____22467 -> t1
    | FStar_Syntax_Syntax.Tm_lazy uu____22468 -> t1
    | FStar_Syntax_Syntax.Tm_unknown  -> t1
    | FStar_Syntax_Syntax.Tm_abs (bs,t2,rc_opt) ->
        let elim_rc rc =
          let uu___194_22496 = rc  in
          let uu____22497 =
            FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
              elim_delayed_subst_term
             in
          let uu____22504 =
            elim_delayed_subst_cflags rc.FStar_Syntax_Syntax.residual_flags
             in
          {
            FStar_Syntax_Syntax.residual_effect =
              (uu___194_22496.FStar_Syntax_Syntax.residual_effect);
            FStar_Syntax_Syntax.residual_typ = uu____22497;
            FStar_Syntax_Syntax.residual_flags = uu____22504
          }  in
        let uu____22507 =
          let uu____22508 =
            let uu____22525 = elim_delayed_subst_binders bs  in
            let uu____22532 = elim_delayed_subst_term t2  in
            let uu____22533 = FStar_Util.map_opt rc_opt elim_rc  in
            (uu____22525, uu____22532, uu____22533)  in
          FStar_Syntax_Syntax.Tm_abs uu____22508  in
        mk1 uu____22507
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____22562 =
          let uu____22563 =
            let uu____22576 = elim_delayed_subst_binders bs  in
            let uu____22583 = elim_delayed_subst_comp c  in
            (uu____22576, uu____22583)  in
          FStar_Syntax_Syntax.Tm_arrow uu____22563  in
        mk1 uu____22562
    | FStar_Syntax_Syntax.Tm_refine (bv,phi) ->
        let uu____22596 =
          let uu____22597 =
            let uu____22604 = elim_bv bv  in
            let uu____22605 = elim_delayed_subst_term phi  in
            (uu____22604, uu____22605)  in
          FStar_Syntax_Syntax.Tm_refine uu____22597  in
        mk1 uu____22596
    | FStar_Syntax_Syntax.Tm_app (t2,args) ->
        let uu____22628 =
          let uu____22629 =
            let uu____22644 = elim_delayed_subst_term t2  in
            let uu____22645 = elim_delayed_subst_args args  in
            (uu____22644, uu____22645)  in
          FStar_Syntax_Syntax.Tm_app uu____22629  in
        mk1 uu____22628
    | FStar_Syntax_Syntax.Tm_match (t2,branches) ->
        let rec elim_pat p =
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_var x ->
              let uu___195_22709 = p  in
              let uu____22710 =
                let uu____22711 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_var uu____22711  in
              {
                FStar_Syntax_Syntax.v = uu____22710;
                FStar_Syntax_Syntax.p =
                  (uu___195_22709.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_wild x ->
              let uu___196_22713 = p  in
              let uu____22714 =
                let uu____22715 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_wild uu____22715  in
              {
                FStar_Syntax_Syntax.v = uu____22714;
                FStar_Syntax_Syntax.p =
                  (uu___196_22713.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
              let uu___197_22722 = p  in
              let uu____22723 =
                let uu____22724 =
                  let uu____22731 = elim_bv x  in
                  let uu____22732 = elim_delayed_subst_term t0  in
                  (uu____22731, uu____22732)  in
                FStar_Syntax_Syntax.Pat_dot_term uu____22724  in
              {
                FStar_Syntax_Syntax.v = uu____22723;
                FStar_Syntax_Syntax.p =
                  (uu___197_22722.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
              let uu___198_22751 = p  in
              let uu____22752 =
                let uu____22753 =
                  let uu____22766 =
                    FStar_List.map
                      (fun uu____22789  ->
                         match uu____22789 with
                         | (x,b) ->
                             let uu____22802 = elim_pat x  in
                             (uu____22802, b)) pats
                     in
                  (fv, uu____22766)  in
                FStar_Syntax_Syntax.Pat_cons uu____22753  in
              {
                FStar_Syntax_Syntax.v = uu____22752;
                FStar_Syntax_Syntax.p =
                  (uu___198_22751.FStar_Syntax_Syntax.p)
              }
          | uu____22815 -> p  in
        let elim_branch uu____22837 =
          match uu____22837 with
          | (pat,wopt,t3) ->
              let uu____22863 = elim_pat pat  in
              let uu____22866 =
                FStar_Util.map_opt wopt elim_delayed_subst_term  in
              let uu____22869 = elim_delayed_subst_term t3  in
              (uu____22863, uu____22866, uu____22869)
           in
        let uu____22874 =
          let uu____22875 =
            let uu____22898 = elim_delayed_subst_term t2  in
            let uu____22899 = FStar_List.map elim_branch branches  in
            (uu____22898, uu____22899)  in
          FStar_Syntax_Syntax.Tm_match uu____22875  in
        mk1 uu____22874
    | FStar_Syntax_Syntax.Tm_ascribed (t2,a,lopt) ->
        let elim_ascription uu____23008 =
          match uu____23008 with
          | (tc,topt) ->
              let uu____23043 =
                match tc with
                | FStar_Util.Inl t3 ->
                    let uu____23053 = elim_delayed_subst_term t3  in
                    FStar_Util.Inl uu____23053
                | FStar_Util.Inr c ->
                    let uu____23055 = elim_delayed_subst_comp c  in
                    FStar_Util.Inr uu____23055
                 in
              let uu____23056 =
                FStar_Util.map_opt topt elim_delayed_subst_term  in
              (uu____23043, uu____23056)
           in
        let uu____23065 =
          let uu____23066 =
            let uu____23093 = elim_delayed_subst_term t2  in
            let uu____23094 = elim_ascription a  in
            (uu____23093, uu____23094, lopt)  in
          FStar_Syntax_Syntax.Tm_ascribed uu____23066  in
        mk1 uu____23065
    | FStar_Syntax_Syntax.Tm_let (lbs,t2) ->
        let elim_lb lb =
          let uu___199_23139 = lb  in
          let uu____23140 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbtyp  in
          let uu____23143 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbdef  in
          {
            FStar_Syntax_Syntax.lbname =
              (uu___199_23139.FStar_Syntax_Syntax.lbname);
            FStar_Syntax_Syntax.lbunivs =
              (uu___199_23139.FStar_Syntax_Syntax.lbunivs);
            FStar_Syntax_Syntax.lbtyp = uu____23140;
            FStar_Syntax_Syntax.lbeff =
              (uu___199_23139.FStar_Syntax_Syntax.lbeff);
            FStar_Syntax_Syntax.lbdef = uu____23143;
            FStar_Syntax_Syntax.lbattrs =
              (uu___199_23139.FStar_Syntax_Syntax.lbattrs);
            FStar_Syntax_Syntax.lbpos =
              (uu___199_23139.FStar_Syntax_Syntax.lbpos)
          }  in
        let uu____23146 =
          let uu____23147 =
            let uu____23160 =
              let uu____23167 =
                FStar_List.map elim_lb (FStar_Pervasives_Native.snd lbs)  in
              ((FStar_Pervasives_Native.fst lbs), uu____23167)  in
            let uu____23176 = elim_delayed_subst_term t2  in
            (uu____23160, uu____23176)  in
          FStar_Syntax_Syntax.Tm_let uu____23147  in
        mk1 uu____23146
    | FStar_Syntax_Syntax.Tm_uvar (uv,t2) ->
        let uu____23209 =
          let uu____23210 =
            let uu____23227 = elim_delayed_subst_term t2  in
            (uv, uu____23227)  in
          FStar_Syntax_Syntax.Tm_uvar uu____23210  in
        mk1 uu____23209
    | FStar_Syntax_Syntax.Tm_meta (t2,md) ->
        let uu____23244 =
          let uu____23245 =
            let uu____23252 = elim_delayed_subst_term t2  in
            let uu____23253 = elim_delayed_subst_meta md  in
            (uu____23252, uu____23253)  in
          FStar_Syntax_Syntax.Tm_meta uu____23245  in
        mk1 uu____23244

and (elim_delayed_subst_cflags :
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun flags1  ->
    FStar_List.map
      (fun uu___91_23260  ->
         match uu___91_23260 with
         | FStar_Syntax_Syntax.DECREASES t ->
             let uu____23264 = elim_delayed_subst_term t  in
             FStar_Syntax_Syntax.DECREASES uu____23264
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
        let uu____23285 =
          let uu____23286 =
            let uu____23295 = elim_delayed_subst_term t  in
            (uu____23295, uopt)  in
          FStar_Syntax_Syntax.Total uu____23286  in
        mk1 uu____23285
    | FStar_Syntax_Syntax.GTotal (t,uopt) ->
        let uu____23308 =
          let uu____23309 =
            let uu____23318 = elim_delayed_subst_term t  in
            (uu____23318, uopt)  in
          FStar_Syntax_Syntax.GTotal uu____23309  in
        mk1 uu____23308
    | FStar_Syntax_Syntax.Comp ct ->
        let ct1 =
          let uu___200_23323 = ct  in
          let uu____23324 =
            elim_delayed_subst_term ct.FStar_Syntax_Syntax.result_typ  in
          let uu____23327 =
            elim_delayed_subst_args ct.FStar_Syntax_Syntax.effect_args  in
          let uu____23336 =
            elim_delayed_subst_cflags ct.FStar_Syntax_Syntax.flags  in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___200_23323.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___200_23323.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ = uu____23324;
            FStar_Syntax_Syntax.effect_args = uu____23327;
            FStar_Syntax_Syntax.flags = uu____23336
          }  in
        mk1 (FStar_Syntax_Syntax.Comp ct1)

and (elim_delayed_subst_meta :
  FStar_Syntax_Syntax.metadata -> FStar_Syntax_Syntax.metadata) =
  fun uu___92_23339  ->
    match uu___92_23339 with
    | FStar_Syntax_Syntax.Meta_pattern args ->
        let uu____23351 = FStar_List.map elim_delayed_subst_args args  in
        FStar_Syntax_Syntax.Meta_pattern uu____23351
    | FStar_Syntax_Syntax.Meta_monadic (m,t) ->
        let uu____23384 =
          let uu____23391 = elim_delayed_subst_term t  in (m, uu____23391)
           in
        FStar_Syntax_Syntax.Meta_monadic uu____23384
    | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,t) ->
        let uu____23399 =
          let uu____23408 = elim_delayed_subst_term t  in
          (m1, m2, uu____23408)  in
        FStar_Syntax_Syntax.Meta_monadic_lift uu____23399
    | m -> m

and (elim_delayed_subst_args :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun args  ->
    FStar_List.map
      (fun uu____23431  ->
         match uu____23431 with
         | (t,q) ->
             let uu____23442 = elim_delayed_subst_term t  in (uu____23442, q))
      args

and (elim_delayed_subst_binders :
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun bs  ->
    FStar_List.map
      (fun uu____23462  ->
         match uu____23462 with
         | (x,q) ->
             let uu____23473 =
               let uu___201_23474 = x  in
               let uu____23475 =
                 elim_delayed_subst_term x.FStar_Syntax_Syntax.sort  in
               {
                 FStar_Syntax_Syntax.ppname =
                   (uu___201_23474.FStar_Syntax_Syntax.ppname);
                 FStar_Syntax_Syntax.index =
                   (uu___201_23474.FStar_Syntax_Syntax.index);
                 FStar_Syntax_Syntax.sort = uu____23475
               }  in
             (uu____23473, q)) bs

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
            | (uu____23551,FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c))
                  FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
            | (uu____23557,FStar_Util.Inl t) ->
                let uu____23563 =
                  let uu____23566 =
                    let uu____23567 =
                      let uu____23580 = FStar_Syntax_Syntax.mk_Total t  in
                      (binders, uu____23580)  in
                    FStar_Syntax_Syntax.Tm_arrow uu____23567  in
                  FStar_Syntax_Syntax.mk uu____23566  in
                uu____23563 FStar_Pervasives_Native.None
                  t.FStar_Syntax_Syntax.pos
             in
          let uu____23584 = FStar_Syntax_Subst.open_univ_vars univ_names t
             in
          match uu____23584 with
          | (univ_names1,t1) ->
              let t2 = remove_uvar_solutions env t1  in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2  in
              let t4 = elim_delayed_subst_term t3  in
              let uu____23612 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t4))
                | uu____23667 ->
                    let uu____23668 =
                      let uu____23677 =
                        let uu____23678 = FStar_Syntax_Subst.compress t4  in
                        uu____23678.FStar_Syntax_Syntax.n  in
                      (uu____23677, tc)  in
                    (match uu____23668 with
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inr uu____23703) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inl uu____23740) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____23779,FStar_Util.Inl uu____23780) ->
                         ([], (FStar_Util.Inl t4))
                     | uu____23803 -> failwith "Impossible")
                 in
              (match uu____23612 with
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
          let uu____23908 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl t)  in
          match uu____23908 with
          | (univ_names1,binders1,tc) ->
              let uu____23966 = FStar_Util.left tc  in
              (univ_names1, binders1, uu____23966)
  
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
          let uu____24001 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr c)  in
          match uu____24001 with
          | (univ_names1,binders1,tc) ->
              let uu____24061 = FStar_Util.right tc  in
              (univ_names1, binders1, uu____24061)
  
let rec (elim_uvars :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt)
  =
  fun env  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univ_names,binders,typ,lids,lids') ->
          let uu____24094 = elim_uvars_aux_t env univ_names binders typ  in
          (match uu____24094 with
           | (univ_names1,binders1,typ1) ->
               let uu___202_24122 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___202_24122.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___202_24122.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___202_24122.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___202_24122.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
          let uu___203_24143 = s  in
          let uu____24144 =
            let uu____24145 =
              let uu____24154 = FStar_List.map (elim_uvars env) sigs  in
              (uu____24154, lids)  in
            FStar_Syntax_Syntax.Sig_bundle uu____24145  in
          {
            FStar_Syntax_Syntax.sigel = uu____24144;
            FStar_Syntax_Syntax.sigrng =
              (uu___203_24143.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___203_24143.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___203_24143.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___203_24143.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_datacon (lid,univ_names,typ,lident,i,lids) ->
          let uu____24171 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____24171 with
           | (univ_names1,uu____24189,typ1) ->
               let uu___204_24203 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___204_24203.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___204_24203.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___204_24203.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___204_24203.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univ_names,typ) ->
          let uu____24209 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____24209 with
           | (univ_names1,uu____24227,typ1) ->
               let uu___205_24241 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___205_24241.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___205_24241.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___205_24241.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___205_24241.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____24275 =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs
                       in
                    match uu____24275 with
                    | (opening,lbunivs) ->
                        let elim t =
                          let uu____24298 =
                            let uu____24299 =
                              let uu____24300 =
                                FStar_Syntax_Subst.subst opening t  in
                              remove_uvar_solutions env uu____24300  in
                            FStar_Syntax_Subst.close_univ_vars lbunivs
                              uu____24299
                             in
                          elim_delayed_subst_term uu____24298  in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp  in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef  in
                        let uu___206_24303 = lb  in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___206_24303.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___206_24303.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___206_24303.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___206_24303.FStar_Syntax_Syntax.lbpos)
                        }))
             in
          let uu___207_24304 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids));
            FStar_Syntax_Syntax.sigrng =
              (uu___207_24304.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___207_24304.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___207_24304.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___207_24304.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_main t ->
          let uu___208_24316 = s  in
          let uu____24317 =
            let uu____24318 = remove_uvar_solutions env t  in
            FStar_Syntax_Syntax.Sig_main uu____24318  in
          {
            FStar_Syntax_Syntax.sigel = uu____24317;
            FStar_Syntax_Syntax.sigrng =
              (uu___208_24316.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___208_24316.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___208_24316.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___208_24316.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_assume (l,us,t) ->
          let uu____24322 = elim_uvars_aux_t env us [] t  in
          (match uu____24322 with
           | (us1,uu____24340,t1) ->
               let uu___209_24354 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___209_24354.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___209_24354.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___209_24354.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___209_24354.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____24355 ->
          failwith "Impossible: should have been desugared already"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____24357 =
            elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature
             in
          (match uu____24357 with
           | (univs1,binders,signature) ->
               let uu____24385 =
                 let uu____24394 = FStar_Syntax_Subst.univ_var_opening univs1
                    in
                 match uu____24394 with
                 | (univs_opening,univs2) ->
                     let uu____24421 =
                       FStar_Syntax_Subst.univ_var_closing univs2  in
                     (univs_opening, uu____24421)
                  in
               (match uu____24385 with
                | (univs_opening,univs_closing) ->
                    let uu____24438 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders
                         in
                      let uu____24444 =
                        FStar_Syntax_Subst.opening_of_binders binders1  in
                      let uu____24445 =
                        FStar_Syntax_Subst.closing_of_binders binders1  in
                      (uu____24444, uu____24445)  in
                    (match uu____24438 with
                     | (b_opening,b_closing) ->
                         let n1 = FStar_List.length univs1  in
                         let n_binders = FStar_List.length binders  in
                         let elim_tscheme uu____24467 =
                           match uu____24467 with
                           | (us,t) ->
                               let n_us = FStar_List.length us  in
                               let uu____24485 =
                                 FStar_Syntax_Subst.open_univ_vars us t  in
                               (match uu____24485 with
                                | (us1,t1) ->
                                    let uu____24496 =
                                      let uu____24501 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      let uu____24508 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      (uu____24501, uu____24508)  in
                                    (match uu____24496 with
                                     | (b_opening1,b_closing1) ->
                                         let uu____24521 =
                                           let uu____24526 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us)
                                              in
                                           let uu____24535 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us)
                                              in
                                           (uu____24526, uu____24535)  in
                                         (match uu____24521 with
                                          | (univs_opening1,univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____24551 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1
                                                   in
                                                FStar_Syntax_Subst.subst
                                                  univs_opening1 uu____24551
                                                 in
                                              let uu____24552 =
                                                elim_uvars_aux_t env [] [] t2
                                                 in
                                              (match uu____24552 with
                                               | (uu____24573,uu____24574,t3)
                                                   ->
                                                   let t4 =
                                                     let uu____24589 =
                                                       let uu____24590 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3
                                                          in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
                                                         uu____24590
                                                        in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____24589
                                                      in
                                                   (us1, t4)))))
                            in
                         let elim_term t =
                           let uu____24595 =
                             elim_uvars_aux_t env univs1 binders t  in
                           match uu____24595 with
                           | (uu____24608,uu____24609,t1) -> t1  in
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
                             | uu____24669 ->
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_abs
                                      ((a.FStar_Syntax_Syntax.action_params),
                                        body, FStar_Pervasives_Native.None))
                                   FStar_Pervasives_Native.None
                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                              in
                           let destruct_action_body body =
                             let uu____24686 =
                               let uu____24687 =
                                 FStar_Syntax_Subst.compress body  in
                               uu____24687.FStar_Syntax_Syntax.n  in
                             match uu____24686 with
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,(FStar_Util.Inl
                                        typ,FStar_Pervasives_Native.None ),FStar_Pervasives_Native.None
                                  )
                                 -> (defn, typ)
                             | uu____24746 -> failwith "Impossible"  in
                           let destruct_action_typ_templ t =
                             let uu____24775 =
                               let uu____24776 =
                                 FStar_Syntax_Subst.compress t  in
                               uu____24776.FStar_Syntax_Syntax.n  in
                             match uu____24775 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (pars,body,uu____24797) ->
                                 let uu____24818 = destruct_action_body body
                                    in
                                 (match uu____24818 with
                                  | (defn,typ) -> (pars, defn, typ))
                             | uu____24863 ->
                                 let uu____24864 = destruct_action_body t  in
                                 (match uu____24864 with
                                  | (defn,typ) -> ([], defn, typ))
                              in
                           let uu____24913 =
                             elim_tscheme
                               ((a.FStar_Syntax_Syntax.action_univs),
                                 action_typ_templ)
                              in
                           match uu____24913 with
                           | (action_univs,t) ->
                               let uu____24922 = destruct_action_typ_templ t
                                  in
                               (match uu____24922 with
                                | (action_params,action_defn,action_typ) ->
                                    let a' =
                                      let uu___210_24963 = a  in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___210_24963.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___210_24963.FStar_Syntax_Syntax.action_unqualified_name);
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
                           let uu___211_24965 = ed  in
                           let uu____24966 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ret_wp  in
                           let uu____24967 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_wp  in
                           let uu____24968 =
                             elim_tscheme ed.FStar_Syntax_Syntax.if_then_else
                              in
                           let uu____24969 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ite_wp  in
                           let uu____24970 =
                             elim_tscheme ed.FStar_Syntax_Syntax.stronger  in
                           let uu____24971 =
                             elim_tscheme ed.FStar_Syntax_Syntax.close_wp  in
                           let uu____24972 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assert_p  in
                           let uu____24973 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assume_p  in
                           let uu____24974 =
                             elim_tscheme ed.FStar_Syntax_Syntax.null_wp  in
                           let uu____24975 =
                             elim_tscheme ed.FStar_Syntax_Syntax.trivial  in
                           let uu____24976 =
                             elim_term ed.FStar_Syntax_Syntax.repr  in
                           let uu____24977 =
                             elim_tscheme ed.FStar_Syntax_Syntax.return_repr
                              in
                           let uu____24978 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_repr
                              in
                           let uu____24979 =
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions
                              in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___211_24965.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___211_24965.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs = univs1;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp = uu____24966;
                             FStar_Syntax_Syntax.bind_wp = uu____24967;
                             FStar_Syntax_Syntax.if_then_else = uu____24968;
                             FStar_Syntax_Syntax.ite_wp = uu____24969;
                             FStar_Syntax_Syntax.stronger = uu____24970;
                             FStar_Syntax_Syntax.close_wp = uu____24971;
                             FStar_Syntax_Syntax.assert_p = uu____24972;
                             FStar_Syntax_Syntax.assume_p = uu____24973;
                             FStar_Syntax_Syntax.null_wp = uu____24974;
                             FStar_Syntax_Syntax.trivial = uu____24975;
                             FStar_Syntax_Syntax.repr = uu____24976;
                             FStar_Syntax_Syntax.return_repr = uu____24977;
                             FStar_Syntax_Syntax.bind_repr = uu____24978;
                             FStar_Syntax_Syntax.actions = uu____24979;
                             FStar_Syntax_Syntax.eff_attrs =
                               (uu___211_24965.FStar_Syntax_Syntax.eff_attrs)
                           }  in
                         let uu___212_24982 = s  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___212_24982.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___212_24982.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___212_24982.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___212_24982.FStar_Syntax_Syntax.sigattrs)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___93_24999 =
            match uu___93_24999 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (us,t) ->
                let uu____25026 = elim_uvars_aux_t env us [] t  in
                (match uu____25026 with
                 | (us1,uu____25050,t1) ->
                     FStar_Pervasives_Native.Some (us1, t1))
             in
          let sub_eff1 =
            let uu___213_25069 = sub_eff  in
            let uu____25070 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp  in
            let uu____25073 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift  in
            {
              FStar_Syntax_Syntax.source =
                (uu___213_25069.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___213_25069.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____25070;
              FStar_Syntax_Syntax.lift = uu____25073
            }  in
          let uu___214_25076 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___214_25076.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___214_25076.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___214_25076.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___214_25076.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,univ_names,binders,comp,flags1) ->
          let uu____25086 = elim_uvars_aux_c env univ_names binders comp  in
          (match uu____25086 with
           | (univ_names1,binders1,comp1) ->
               let uu___215_25120 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___215_25120.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___215_25120.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___215_25120.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___215_25120.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____25131 -> s
      | FStar_Syntax_Syntax.Sig_splice uu____25132 -> s
  
let (erase_universes :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  -> normalize [EraseUniverses; AllowUnboundUniverses] env t
  