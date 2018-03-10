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
    match projectee with | Clos _0 -> true | uu____1329 -> false
  
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
    match projectee with | Univ _0 -> true | uu____1431 -> false
  
let (__proj__Univ__item___0 : closure -> FStar_Syntax_Syntax.universe) =
  fun projectee  -> match projectee with | Univ _0 -> _0 
let (uu___is_Dummy : closure -> Prims.bool) =
  fun projectee  ->
    match projectee with | Dummy  -> true | uu____1442 -> false
  
type env =
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
    FStar_Pervasives_Native.tuple2 Prims.list[@@deriving show]
let (dummy :
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
    FStar_Pervasives_Native.tuple2)
  = (FStar_Pervasives_Native.None, Dummy) 
let (closure_to_string : closure -> Prims.string) =
  fun uu___77_1461  ->
    match uu___77_1461 with
    | Clos (uu____1462,t,uu____1464,uu____1465) ->
        FStar_Syntax_Print.term_to_string t
    | Univ uu____1510 -> "Univ"
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
    let uu____1772 = FStar_Util.psmap_empty ()  in add_steps uu____1772 l
  
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
    match projectee with | Arg _0 -> true | uu____1916 -> false
  
let (__proj__Arg__item___0 :
  stack_elt ->
    (closure,FStar_Syntax_Syntax.aqual,FStar_Range.range)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | Arg _0 -> _0 
let (uu___is_UnivArgs : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnivArgs _0 -> true | uu____1952 -> false
  
let (__proj__UnivArgs__item___0 :
  stack_elt ->
    (FStar_Syntax_Syntax.universe Prims.list,FStar_Range.range)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | UnivArgs _0 -> _0 
let (uu___is_MemoLazy : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | MemoLazy _0 -> true | uu____1988 -> false
  
let (__proj__MemoLazy__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.term) FStar_Pervasives_Native.tuple2
      FStar_Syntax_Syntax.memo)
  = fun projectee  -> match projectee with | MemoLazy _0 -> _0 
let (uu___is_Match : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____2057 -> false
  
let (__proj__Match__item___0 :
  stack_elt ->
    (env,branches,FStar_Range.range) FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | Match _0 -> _0 
let (uu___is_Abs : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Abs _0 -> true | uu____2099 -> false
  
let (__proj__Abs__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.binders,env,FStar_Syntax_Syntax.residual_comp
                                           FStar_Pervasives_Native.option,
      FStar_Range.range) FStar_Pervasives_Native.tuple5)
  = fun projectee  -> match projectee with | Abs _0 -> _0 
let (uu___is_App : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____2155 -> false
  
let (__proj__App__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual,FStar_Range.range)
      FStar_Pervasives_Native.tuple4)
  = fun projectee  -> match projectee with | App _0 -> _0 
let (uu___is_Meta : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Meta _0 -> true | uu____2195 -> false
  
let (__proj__Meta__item___0 :
  stack_elt ->
    (FStar_Syntax_Syntax.metadata,FStar_Range.range)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Meta _0 -> _0 
let (uu___is_Let : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Let _0 -> true | uu____2227 -> false
  
let (__proj__Let__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.letbinding,FStar_Range.range)
      FStar_Pervasives_Native.tuple4)
  = fun projectee  -> match projectee with | Let _0 -> _0 
let (uu___is_Cfg : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Cfg _0 -> true | uu____2263 -> false
  
let (__proj__Cfg__item___0 : stack_elt -> cfg) =
  fun projectee  -> match projectee with | Cfg _0 -> _0 
let (uu___is_Debug : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Debug _0 -> true | uu____2279 -> false
  
let (__proj__Debug__item___0 :
  stack_elt ->
    (FStar_Syntax_Syntax.term,FStar_Util.time) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Debug _0 -> _0 
type stack = stack_elt Prims.list[@@deriving show]
let (head_of : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____2304 = FStar_Syntax_Util.head_and_args' t  in
    match uu____2304 with | (hd1,uu____2318) -> hd1
  
let mk :
  'Auu____2338 .
    'Auu____2338 ->
      FStar_Range.range -> 'Auu____2338 FStar_Syntax_Syntax.syntax
  =
  fun t  -> fun r  -> FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None r 
let set_memo : 'a . cfg -> 'a FStar_Syntax_Syntax.memo -> 'a -> Prims.unit =
  fun cfg  ->
    fun r  ->
      fun t  ->
        if cfg.memoize_lazy
        then
          let uu____2392 = FStar_ST.op_Bang r  in
          match uu____2392 with
          | FStar_Pervasives_Native.Some uu____2440 ->
              failwith "Unexpected set_memo: thunk already evaluated"
          | FStar_Pervasives_Native.None  ->
              FStar_ST.op_Colon_Equals r (FStar_Pervasives_Native.Some t)
        else ()
  
let (env_to_string : closure Prims.list -> Prims.string) =
  fun env  ->
    let uu____2494 = FStar_List.map closure_to_string env  in
    FStar_All.pipe_right uu____2494 (FStar_String.concat "; ")
  
let (stack_elt_to_string : stack_elt -> Prims.string) =
  fun uu___78_2501  ->
    match uu___78_2501 with
    | Arg (c,uu____2503,uu____2504) ->
        let uu____2505 = closure_to_string c  in
        FStar_Util.format1 "Closure %s" uu____2505
    | MemoLazy uu____2506 -> "MemoLazy"
    | Abs (uu____2513,bs,uu____2515,uu____2516,uu____2517) ->
        let uu____2522 =
          FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs)
           in
        FStar_Util.format1 "Abs %s" uu____2522
    | UnivArgs uu____2527 -> "UnivArgs"
    | Match uu____2534 -> "Match"
    | App (uu____2541,t,uu____2543,uu____2544) ->
        let uu____2545 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "App %s" uu____2545
    | Meta (m,uu____2547) -> "Meta"
    | Let uu____2548 -> "Let"
    | Cfg uu____2557 -> "Cfg"
    | Debug (t,uu____2559) ->
        let uu____2560 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "Debug %s" uu____2560
  
let (stack_to_string : stack_elt Prims.list -> Prims.string) =
  fun s  ->
    let uu____2568 = FStar_List.map stack_elt_to_string s  in
    FStar_All.pipe_right uu____2568 (FStar_String.concat "; ")
  
let (log : cfg -> (Prims.unit -> Prims.unit) -> Prims.unit) =
  fun cfg  -> fun f  -> if (cfg.debug).gen then f () else () 
let (log_primops : cfg -> (Prims.unit -> Prims.unit) -> Prims.unit) =
  fun cfg  -> fun f  -> if (cfg.debug).primop then f () else () 
let is_empty : 'Auu____2599 . 'Auu____2599 Prims.list -> Prims.bool =
  fun uu___79_2605  ->
    match uu___79_2605 with | [] -> true | uu____2608 -> false
  
let lookup_bvar :
  'Auu____2615 'Auu____2616 .
    ('Auu____2615,'Auu____2616) FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Syntax_Syntax.bv -> 'Auu____2616
  =
  fun env  ->
    fun x  ->
      try
        let uu____2640 = FStar_List.nth env x.FStar_Syntax_Syntax.index  in
        FStar_Pervasives_Native.snd uu____2640
      with
      | uu____2653 ->
          let uu____2654 =
            let uu____2655 = FStar_Syntax_Print.db_to_string x  in
            FStar_Util.format1 "Failed to find %s\n" uu____2655  in
          failwith uu____2654
  
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
          let uu____2692 =
            FStar_List.fold_left
              (fun uu____2718  ->
                 fun u1  ->
                   match uu____2718 with
                   | (cur_kernel,cur_max,out) ->
                       let uu____2743 = FStar_Syntax_Util.univ_kernel u1  in
                       (match uu____2743 with
                        | (k_u,n1) ->
                            let uu____2758 =
                              FStar_Syntax_Util.eq_univs cur_kernel k_u  in
                            if uu____2758
                            then (cur_kernel, u1, out)
                            else (k_u, u1, (cur_max :: out))))
              (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero, [])
              us1
             in
          match uu____2692 with
          | (uu____2776,u1,out) -> FStar_List.rev (u1 :: out)  in
        let rec aux u1 =
          let u2 = FStar_Syntax_Subst.compress_univ u1  in
          match u2 with
          | FStar_Syntax_Syntax.U_bvar x ->
              (try
                 let uu____2801 =
                   let uu____2802 = FStar_List.nth env x  in
                   FStar_Pervasives_Native.snd uu____2802  in
                 match uu____2801 with
                 | Univ u3 -> aux u3
                 | Dummy  -> [u2]
                 | uu____2820 ->
                     failwith "Impossible: universe variable bound to a term"
               with
               | uu____2828 ->
                   if (cfg.steps).allow_unbound_universes
                   then [FStar_Syntax_Syntax.U_unknown]
                   else failwith "Universe variable not found")
          | FStar_Syntax_Syntax.U_unif uu____2834 when
              (cfg.steps).check_no_uvars -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_zero  -> [u2]
          | FStar_Syntax_Syntax.U_unif uu____2843 -> [u2]
          | FStar_Syntax_Syntax.U_name uu____2852 -> [u2]
          | FStar_Syntax_Syntax.U_unknown  -> [u2]
          | FStar_Syntax_Syntax.U_max [] -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_max us ->
              let us1 =
                let uu____2859 = FStar_List.collect aux us  in
                FStar_All.pipe_right uu____2859 norm_univs  in
              (match us1 with
               | u_k::hd1::rest ->
                   let rest1 = hd1 :: rest  in
                   let uu____2876 = FStar_Syntax_Util.univ_kernel u_k  in
                   (match uu____2876 with
                    | (FStar_Syntax_Syntax.U_zero ,n1) ->
                        let uu____2884 =
                          FStar_All.pipe_right rest1
                            (FStar_List.for_all
                               (fun u3  ->
                                  let uu____2892 =
                                    FStar_Syntax_Util.univ_kernel u3  in
                                  match uu____2892 with
                                  | (uu____2897,m) -> n1 <= m))
                           in
                        if uu____2884 then rest1 else us1
                    | uu____2902 -> us1)
               | uu____2907 -> us1)
          | FStar_Syntax_Syntax.U_succ u3 ->
              let uu____2911 = aux u3  in
              FStar_List.map (fun _0_40  -> FStar_Syntax_Syntax.U_succ _0_40)
                uu____2911
           in
        if (cfg.steps).erase_universes
        then FStar_Syntax_Syntax.U_unknown
        else
          (let uu____2915 = aux u  in
           match uu____2915 with
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
          (fun uu____3019  ->
             let uu____3020 = FStar_Syntax_Print.tag_of_term t  in
             let uu____3021 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.print2 ">>> %s Closure_as_term %s\n" uu____3020
               uu____3021);
        (match env with
         | [] when
             FStar_All.pipe_left Prims.op_Negation (cfg.steps).compress_uvars
             -> t
         | uu____3028 ->
             let t1 = FStar_Syntax_Subst.compress t  in
             (match t1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_delayed uu____3030 ->
                  failwith "Impossible"
              | FStar_Syntax_Syntax.Tm_unknown  -> t1
              | FStar_Syntax_Syntax.Tm_constant uu____3055 -> t1
              | FStar_Syntax_Syntax.Tm_name uu____3056 -> t1
              | FStar_Syntax_Syntax.Tm_lazy uu____3057 -> t1
              | FStar_Syntax_Syntax.Tm_fvar uu____3058 -> t1
              | FStar_Syntax_Syntax.Tm_uvar uu____3059 ->
                  if (cfg.steps).check_no_uvars
                  then
                    let uu____3076 =
                      let uu____3077 =
                        FStar_Range.string_of_range
                          t1.FStar_Syntax_Syntax.pos
                         in
                      let uu____3078 = FStar_Syntax_Print.term_to_string t1
                         in
                      FStar_Util.format2
                        "(%s): CheckNoUvars: Unexpected unification variable remains: %s"
                        uu____3077 uu____3078
                       in
                    failwith uu____3076
                  else t1
              | FStar_Syntax_Syntax.Tm_type u ->
                  let uu____3081 =
                    let uu____3082 = norm_universe cfg env u  in
                    FStar_Syntax_Syntax.Tm_type uu____3082  in
                  mk uu____3081 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
                  let uu____3089 = FStar_List.map (norm_universe cfg env) us
                     in
                  FStar_Syntax_Syntax.mk_Tm_uinst t' uu____3089
              | FStar_Syntax_Syntax.Tm_bvar x ->
                  let uu____3091 = lookup_bvar env x  in
                  (match uu____3091 with
                   | Univ uu____3094 ->
                       failwith
                         "Impossible: term variable is bound to a universe"
                   | Dummy  -> t1
                   | Clos (env1,t0,uu____3097,uu____3098) ->
                       closure_as_term cfg env1 t0)
              | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                  let head2 = closure_as_term_delayed cfg env head1  in
                  let args1 = closures_as_args_delayed cfg env args  in
                  mk (FStar_Syntax_Syntax.Tm_app (head2, args1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
                  let uu____3210 = closures_as_binders_delayed cfg env bs  in
                  (match uu____3210 with
                   | (bs1,env1) ->
                       let body1 = closure_as_term_delayed cfg env1 body  in
                       let uu____3238 =
                         let uu____3239 =
                           let uu____3256 = close_lcomp_opt cfg env1 lopt  in
                           (bs1, body1, uu____3256)  in
                         FStar_Syntax_Syntax.Tm_abs uu____3239  in
                       mk uu____3238 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                  let uu____3287 = closures_as_binders_delayed cfg env bs  in
                  (match uu____3287 with
                   | (bs1,env1) ->
                       let c1 = close_comp cfg env1 c  in
                       mk (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
                         t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
                  let uu____3329 =
                    let uu____3340 =
                      let uu____3347 = FStar_Syntax_Syntax.mk_binder x  in
                      [uu____3347]  in
                    closures_as_binders_delayed cfg env uu____3340  in
                  (match uu____3329 with
                   | (x1,env1) ->
                       let phi1 = closure_as_term_delayed cfg env1 phi  in
                       let uu____3365 =
                         let uu____3366 =
                           let uu____3373 =
                             let uu____3374 = FStar_List.hd x1  in
                             FStar_All.pipe_right uu____3374
                               FStar_Pervasives_Native.fst
                              in
                           (uu____3373, phi1)  in
                         FStar_Syntax_Syntax.Tm_refine uu____3366  in
                       mk uu____3365 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_ascribed (t11,(annot,tacopt),lopt) ->
                  let annot1 =
                    match annot with
                    | FStar_Util.Inl t2 ->
                        let uu____3465 = closure_as_term_delayed cfg env t2
                           in
                        FStar_Util.Inl uu____3465
                    | FStar_Util.Inr c ->
                        let uu____3479 = close_comp cfg env c  in
                        FStar_Util.Inr uu____3479
                     in
                  let tacopt1 =
                    FStar_Util.map_opt tacopt
                      (closure_as_term_delayed cfg env)
                     in
                  let uu____3495 =
                    let uu____3496 =
                      let uu____3523 = closure_as_term_delayed cfg env t11
                         in
                      (uu____3523, (annot1, tacopt1), lopt)  in
                    FStar_Syntax_Syntax.Tm_ascribed uu____3496  in
                  mk uu____3495 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_pattern args) ->
                  let uu____3574 =
                    let uu____3575 =
                      let uu____3582 = closure_as_term_delayed cfg env t'  in
                      let uu____3585 =
                        let uu____3586 =
                          FStar_All.pipe_right args
                            (FStar_List.map
                               (closures_as_args_delayed cfg env))
                           in
                        FStar_Syntax_Syntax.Meta_pattern uu____3586  in
                      (uu____3582, uu____3585)  in
                    FStar_Syntax_Syntax.Tm_meta uu____3575  in
                  mk uu____3574 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic (m,tbody)) ->
                  let uu____3646 =
                    let uu____3647 =
                      let uu____3654 = closure_as_term_delayed cfg env t'  in
                      let uu____3657 =
                        let uu____3658 =
                          let uu____3665 =
                            closure_as_term_delayed cfg env tbody  in
                          (m, uu____3665)  in
                        FStar_Syntax_Syntax.Meta_monadic uu____3658  in
                      (uu____3654, uu____3657)  in
                    FStar_Syntax_Syntax.Tm_meta uu____3647  in
                  mk uu____3646 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,tbody)) ->
                  let uu____3684 =
                    let uu____3685 =
                      let uu____3692 = closure_as_term_delayed cfg env t'  in
                      let uu____3695 =
                        let uu____3696 =
                          let uu____3705 =
                            closure_as_term_delayed cfg env tbody  in
                          (m1, m2, uu____3705)  in
                        FStar_Syntax_Syntax.Meta_monadic_lift uu____3696  in
                      (uu____3692, uu____3695)  in
                    FStar_Syntax_Syntax.Tm_meta uu____3685  in
                  mk uu____3684 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_quoted (t'',qi)) ->
                  if qi.FStar_Syntax_Syntax.qopen
                  then
                    let uu____3723 =
                      let uu____3724 =
                        let uu____3731 = closure_as_term_delayed cfg env t'
                           in
                        let uu____3734 =
                          let uu____3735 =
                            let uu____3742 =
                              closure_as_term_delayed cfg env t''  in
                            (uu____3742, qi)  in
                          FStar_Syntax_Syntax.Meta_quoted uu____3735  in
                        (uu____3731, uu____3734)  in
                      FStar_Syntax_Syntax.Tm_meta uu____3724  in
                    mk uu____3723 t1.FStar_Syntax_Syntax.pos
                  else
                    (let uu____3750 =
                       let uu____3751 =
                         let uu____3758 = closure_as_term_delayed cfg env t'
                            in
                         (uu____3758,
                           (FStar_Syntax_Syntax.Meta_quoted (t'', qi)))
                          in
                       FStar_Syntax_Syntax.Tm_meta uu____3751  in
                     mk uu____3750 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_meta (t',m) ->
                  let uu____3771 =
                    let uu____3772 =
                      let uu____3779 = closure_as_term_delayed cfg env t'  in
                      (uu____3779, m)  in
                    FStar_Syntax_Syntax.Tm_meta uu____3772  in
                  mk uu____3771 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                  let env0 = env  in
                  let env1 =
                    FStar_List.fold_left
                      (fun env1  -> fun uu____3819  -> dummy :: env1) env
                      lb.FStar_Syntax_Syntax.lbunivs
                     in
                  let typ =
                    closure_as_term_delayed cfg env1
                      lb.FStar_Syntax_Syntax.lbtyp
                     in
                  let def =
                    closure_as_term cfg env1 lb.FStar_Syntax_Syntax.lbdef  in
                  let uu____3838 =
                    let uu____3849 = FStar_Syntax_Syntax.is_top_level [lb]
                       in
                    if uu____3849
                    then ((lb.FStar_Syntax_Syntax.lbname), body)
                    else
                      (let x = FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                          in
                       let uu____3868 =
                         closure_as_term cfg (dummy :: env0) body  in
                       ((FStar_Util.Inl
                           (let uu___122_3880 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___122_3880.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___122_3880.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = typ
                            })), uu____3868))
                     in
                  (match uu____3838 with
                   | (nm,body1) ->
                       let lb1 =
                         let uu___123_3896 = lb  in
                         {
                           FStar_Syntax_Syntax.lbname = nm;
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___123_3896.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp = typ;
                           FStar_Syntax_Syntax.lbeff =
                             (uu___123_3896.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef = def;
                           FStar_Syntax_Syntax.lbattrs =
                             (uu___123_3896.FStar_Syntax_Syntax.lbattrs);
                           FStar_Syntax_Syntax.lbpos =
                             (uu___123_3896.FStar_Syntax_Syntax.lbpos)
                         }  in
                       mk
                         (FStar_Syntax_Syntax.Tm_let ((false, [lb1]), body1))
                         t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_let ((uu____3907,lbs),body) ->
                  let norm_one_lb env1 lb =
                    let env_univs =
                      FStar_List.fold_right
                        (fun uu____3966  -> fun env2  -> dummy :: env2)
                        lb.FStar_Syntax_Syntax.lbunivs env1
                       in
                    let env2 =
                      let uu____3991 = FStar_Syntax_Syntax.is_top_level lbs
                         in
                      if uu____3991
                      then env_univs
                      else
                        FStar_List.fold_right
                          (fun uu____4011  -> fun env2  -> dummy :: env2) lbs
                          env_univs
                       in
                    let ty =
                      closure_as_term cfg env_univs
                        lb.FStar_Syntax_Syntax.lbtyp
                       in
                    let nm =
                      let uu____4033 = FStar_Syntax_Syntax.is_top_level lbs
                         in
                      if uu____4033
                      then lb.FStar_Syntax_Syntax.lbname
                      else
                        (let x =
                           FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                         FStar_All.pipe_right
                           (let uu___124_4045 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___124_4045.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___124_4045.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = ty
                            }) (fun _0_41  -> FStar_Util.Inl _0_41))
                       in
                    let uu___125_4046 = lb  in
                    let uu____4047 =
                      closure_as_term cfg env2 lb.FStar_Syntax_Syntax.lbdef
                       in
                    {
                      FStar_Syntax_Syntax.lbname = nm;
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___125_4046.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = ty;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___125_4046.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = uu____4047;
                      FStar_Syntax_Syntax.lbattrs =
                        (uu___125_4046.FStar_Syntax_Syntax.lbattrs);
                      FStar_Syntax_Syntax.lbpos =
                        (uu___125_4046.FStar_Syntax_Syntax.lbpos)
                    }  in
                  let lbs1 =
                    FStar_All.pipe_right lbs
                      (FStar_List.map (norm_one_lb env))
                     in
                  let body1 =
                    let body_env =
                      FStar_List.fold_right
                        (fun uu____4077  -> fun env1  -> dummy :: env1) lbs1
                        env
                       in
                    closure_as_term cfg body_env body  in
                  mk (FStar_Syntax_Syntax.Tm_let ((true, lbs1), body1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
                  let head2 = closure_as_term cfg env head1  in
                  let norm_one_branch env1 uu____4166 =
                    match uu____4166 with
                    | (pat,w_opt,tm) ->
                        let rec norm_pat env2 p =
                          match p.FStar_Syntax_Syntax.v with
                          | FStar_Syntax_Syntax.Pat_constant uu____4221 ->
                              (p, env2)
                          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                              let uu____4242 =
                                FStar_All.pipe_right pats
                                  (FStar_List.fold_left
                                     (fun uu____4302  ->
                                        fun uu____4303  ->
                                          match (uu____4302, uu____4303) with
                                          | ((pats1,env3),(p1,b)) ->
                                              let uu____4394 =
                                                norm_pat env3 p1  in
                                              (match uu____4394 with
                                               | (p2,env4) ->
                                                   (((p2, b) :: pats1), env4)))
                                     ([], env2))
                                 in
                              (match uu____4242 with
                               | (pats1,env3) ->
                                   ((let uu___126_4476 = p  in
                                     {
                                       FStar_Syntax_Syntax.v =
                                         (FStar_Syntax_Syntax.Pat_cons
                                            (fv, (FStar_List.rev pats1)));
                                       FStar_Syntax_Syntax.p =
                                         (uu___126_4476.FStar_Syntax_Syntax.p)
                                     }), env3))
                          | FStar_Syntax_Syntax.Pat_var x ->
                              let x1 =
                                let uu___127_4495 = x  in
                                let uu____4496 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort
                                   in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___127_4495.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___127_4495.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____4496
                                }  in
                              ((let uu___128_4510 = p  in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_var x1);
                                  FStar_Syntax_Syntax.p =
                                    (uu___128_4510.FStar_Syntax_Syntax.p)
                                }), (dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_wild x ->
                              let x1 =
                                let uu___129_4521 = x  in
                                let uu____4522 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort
                                   in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___129_4521.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___129_4521.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____4522
                                }  in
                              ((let uu___130_4536 = p  in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_wild x1);
                                  FStar_Syntax_Syntax.p =
                                    (uu___130_4536.FStar_Syntax_Syntax.p)
                                }), (dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                              let x1 =
                                let uu___131_4552 = x  in
                                let uu____4553 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort
                                   in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___131_4552.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___131_4552.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____4553
                                }  in
                              let t3 = closure_as_term cfg env2 t2  in
                              ((let uu___132_4560 = p  in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_dot_term
                                       (x1, t3));
                                  FStar_Syntax_Syntax.p =
                                    (uu___132_4560.FStar_Syntax_Syntax.p)
                                }), env2)
                           in
                        let uu____4563 = norm_pat env1 pat  in
                        (match uu____4563 with
                         | (pat1,env2) ->
                             let w_opt1 =
                               match w_opt with
                               | FStar_Pervasives_Native.None  ->
                                   FStar_Pervasives_Native.None
                               | FStar_Pervasives_Native.Some w ->
                                   let uu____4592 =
                                     closure_as_term cfg env2 w  in
                                   FStar_Pervasives_Native.Some uu____4592
                                in
                             let tm1 = closure_as_term cfg env2 tm  in
                             (pat1, w_opt1, tm1))
                     in
                  let uu____4598 =
                    let uu____4599 =
                      let uu____4622 =
                        FStar_All.pipe_right branches
                          (FStar_List.map (norm_one_branch env))
                         in
                      (head2, uu____4622)  in
                    FStar_Syntax_Syntax.Tm_match uu____4599  in
                  mk uu____4598 t1.FStar_Syntax_Syntax.pos))

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
        | uu____4708 -> closure_as_term cfg env t

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
        | uu____4734 ->
            FStar_List.map
              (fun uu____4751  ->
                 match uu____4751 with
                 | (x,imp) ->
                     let uu____4770 = closure_as_term_delayed cfg env x  in
                     (uu____4770, imp)) args

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
        let uu____4784 =
          FStar_All.pipe_right bs
            (FStar_List.fold_left
               (fun uu____4833  ->
                  fun uu____4834  ->
                    match (uu____4833, uu____4834) with
                    | ((env1,out),(b,imp)) ->
                        let b1 =
                          let uu___133_4904 = b  in
                          let uu____4905 =
                            closure_as_term_delayed cfg env1
                              b.FStar_Syntax_Syntax.sort
                             in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___133_4904.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___133_4904.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = uu____4905
                          }  in
                        let env2 = dummy :: env1  in
                        (env2, ((b1, imp) :: out))) (env, []))
           in
        match uu____4784 with | (env1,bs1) -> ((FStar_List.rev bs1), env1)

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
        | uu____4998 ->
            (match c.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Total (t,uopt) ->
                 let uu____5011 = closure_as_term_delayed cfg env t  in
                 let uu____5012 =
                   FStar_Option.map (norm_universe cfg env) uopt  in
                 FStar_Syntax_Syntax.mk_Total' uu____5011 uu____5012
             | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                 let uu____5025 = closure_as_term_delayed cfg env t  in
                 let uu____5026 =
                   FStar_Option.map (norm_universe cfg env) uopt  in
                 FStar_Syntax_Syntax.mk_GTotal' uu____5025 uu____5026
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
                        (fun uu___80_5052  ->
                           match uu___80_5052 with
                           | FStar_Syntax_Syntax.DECREASES t ->
                               let uu____5056 =
                                 closure_as_term_delayed cfg env t  in
                               FStar_Syntax_Syntax.DECREASES uu____5056
                           | f -> f))
                    in
                 let uu____5060 =
                   let uu___134_5061 = c1  in
                   let uu____5062 =
                     FStar_List.map (norm_universe cfg env)
                       c1.FStar_Syntax_Syntax.comp_univs
                      in
                   {
                     FStar_Syntax_Syntax.comp_univs = uu____5062;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___134_5061.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ = rt;
                     FStar_Syntax_Syntax.effect_args = args;
                     FStar_Syntax_Syntax.flags = flags1
                   }  in
                 FStar_Syntax_Syntax.mk_Comp uu____5060)

and (filter_out_lcomp_cflags :
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun flags1  ->
    FStar_All.pipe_right flags1
      (FStar_List.filter
         (fun uu___81_5072  ->
            match uu___81_5072 with
            | FStar_Syntax_Syntax.DECREASES uu____5073 -> false
            | uu____5076 -> true))

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
                   (fun uu___82_5094  ->
                      match uu___82_5094 with
                      | FStar_Syntax_Syntax.DECREASES uu____5095 -> false
                      | uu____5098 -> true))
               in
            let rc1 =
              let uu___135_5100 = rc  in
              let uu____5101 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (closure_as_term cfg env)
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___135_5100.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____5101;
                FStar_Syntax_Syntax.residual_flags = flags1
              }  in
            FStar_Pervasives_Native.Some rc1
        | uu____5108 -> lopt

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
    let uu____5193 = FStar_Syntax_Embeddings.unembed_list_safe u  in
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a) uu____5193  in
  let arg_as_bounded_int uu____5221 =
    match uu____5221 with
    | (a,uu____5233) ->
        let uu____5240 =
          let uu____5241 = FStar_Syntax_Subst.compress a  in
          uu____5241.FStar_Syntax_Syntax.n  in
        (match uu____5240 with
         | FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv1;
                FStar_Syntax_Syntax.pos = uu____5251;
                FStar_Syntax_Syntax.vars = uu____5252;_},({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_constant
                                                              (FStar_Const.Const_int
                                                              (i,FStar_Pervasives_Native.None
                                                               ));
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____5254;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____5255;_},uu____5256)::[])
             when
             FStar_Util.ends_with
               (FStar_Ident.text_of_lid
                  (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
               "int_to_t"
             ->
             let uu____5295 =
               let uu____5300 = FStar_BigInt.big_int_of_string i  in
               (fv1, uu____5300)  in
             FStar_Pervasives_Native.Some uu____5295
         | uu____5305 -> FStar_Pervasives_Native.None)
     in
  let lift_unary a b f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a)::[] ->
        let uu____5345 = f a  in FStar_Pervasives_Native.Some uu____5345
    | uu____5346 -> FStar_Pervasives_Native.None  in
  let lift_binary a b f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a0)::(FStar_Pervasives_Native.Some
        a1)::[] ->
        let uu____5394 = f a0 a1  in FStar_Pervasives_Native.Some uu____5394
    | uu____5395 -> FStar_Pervasives_Native.None  in
  let unary_op a416 a417 a418 a419 a420 =
    (Obj.magic
       (fun a  ->
          fun as_a  ->
            fun f  ->
              fun res  ->
                fun args  ->
                  let uu____5437 = FStar_List.map as_a args  in
                  lift_unary () ()
                    (fun a415  -> (Obj.magic (f res.psc_range)) a415)
                    uu____5437)) a416 a417 a418 a419 a420
     in
  let binary_op a423 a424 a425 a426 a427 =
    (Obj.magic
       (fun a  ->
          fun as_a  ->
            fun f  ->
              fun res  ->
                fun args  ->
                  let uu____5486 = FStar_List.map as_a args  in
                  lift_binary () ()
                    (fun a421  ->
                       fun a422  -> (Obj.magic (f res.psc_range)) a421 a422)
                    uu____5486)) a423 a424 a425 a426 a427
     in
  let as_primitive_step is_strong uu____5513 =
    match uu____5513 with
    | (l,arity,f) ->
        {
          name = l;
          arity;
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
                   let uu____5561 = f x  in
                   FStar_Syntax_Embeddings.embed_int r uu____5561)) a429 a430)
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
                       let uu____5589 = f x y  in
                       FStar_Syntax_Embeddings.embed_int r uu____5589)) a432
               a433 a434)
     in
  let unary_bool_op f =
    unary_op () (fun a435  -> (Obj.magic arg_as_bool) a435)
      (fun a436  ->
         fun a437  ->
           (Obj.magic
              (fun r  ->
                 fun x  ->
                   let uu____5610 = f x  in
                   FStar_Syntax_Embeddings.embed_bool r uu____5610)) a436
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
                       let uu____5638 = f x y  in
                       FStar_Syntax_Embeddings.embed_bool r uu____5638)) a439
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
                       let uu____5666 = f x y  in
                       FStar_Syntax_Embeddings.embed_string r uu____5666))
               a443 a444 a445)
     in
  let mixed_binary_op a b c as_a as_b embed_c f res args =
    match args with
    | a::b::[] ->
        let uu____5774 =
          let uu____5783 = as_a a  in
          let uu____5786 = as_b b  in (uu____5783, uu____5786)  in
        (match uu____5774 with
         | (FStar_Pervasives_Native.Some a1,FStar_Pervasives_Native.Some b1)
             ->
             let uu____5801 =
               let uu____5802 = f res.psc_range a1 b1  in
               embed_c res.psc_range uu____5802  in
             FStar_Pervasives_Native.Some uu____5801
         | uu____5803 -> FStar_Pervasives_Native.None)
    | uu____5812 -> FStar_Pervasives_Native.None  in
  let list_of_string' rng s =
    let name l =
      let uu____5826 =
        let uu____5827 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant
            FStar_Pervasives_Native.None
           in
        FStar_Syntax_Syntax.Tm_fvar uu____5827  in
      mk uu____5826 rng  in
    let char_t = name FStar_Parser_Const.char_lid  in
    let charterm c =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c)) rng  in
    let uu____5837 =
      let uu____5840 = FStar_String.list_of_string s  in
      FStar_List.map charterm uu____5840  in
    FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu____5837  in
  let string_of_list' rng l =
    let s = FStar_String.string_of_list l  in FStar_Syntax_Util.exp_string s
     in
  let string_compare' rng s1 s2 =
    let r = FStar_String.compare s1 s2  in
    let uu____5872 =
      let uu____5873 = FStar_Util.string_of_int r  in
      FStar_BigInt.big_int_of_string uu____5873  in
    FStar_Syntax_Embeddings.embed_int rng uu____5872  in
  let string_concat' psc args =
    match args with
    | a1::a2::[] ->
        let uu____5891 = arg_as_string a1  in
        (match uu____5891 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____5897 =
               Obj.magic
                 (arg_as_list ()
                    (Obj.magic FStar_Syntax_Embeddings.unembed_string_safe)
                    a2)
                in
             (match uu____5897 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2  in
                  let uu____5910 =
                    FStar_Syntax_Embeddings.embed_string psc.psc_range r  in
                  FStar_Pervasives_Native.Some uu____5910
              | uu____5911 -> FStar_Pervasives_Native.None)
         | uu____5916 -> FStar_Pervasives_Native.None)
    | uu____5919 -> FStar_Pervasives_Native.None  in
  let string_of_int1 rng i =
    let uu____5929 = FStar_BigInt.string_of_big_int i  in
    FStar_Syntax_Embeddings.embed_string rng uu____5929  in
  let string_of_bool1 rng b =
    FStar_Syntax_Embeddings.embed_string rng (if b then "true" else "false")
     in
  let term_of_range r =
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range r))
      FStar_Pervasives_Native.None r
     in
  let mk_range1 uu____5953 args =
    match args with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____5964 =
          let uu____5985 = arg_as_string fn  in
          let uu____5988 = arg_as_int from_line  in
          let uu____5991 = arg_as_int from_col  in
          let uu____5994 = arg_as_int to_line  in
          let uu____5997 = arg_as_int to_col  in
          (uu____5985, uu____5988, uu____5991, uu____5994, uu____5997)  in
        (match uu____5964 with
         | (FStar_Pervasives_Native.Some fn1,FStar_Pervasives_Native.Some
            from_l,FStar_Pervasives_Native.Some
            from_c,FStar_Pervasives_Native.Some
            to_l,FStar_Pervasives_Native.Some to_c) ->
             let r =
               let uu____6028 =
                 let uu____6029 = FStar_BigInt.to_int_fs from_l  in
                 let uu____6030 = FStar_BigInt.to_int_fs from_c  in
                 FStar_Range.mk_pos uu____6029 uu____6030  in
               let uu____6031 =
                 let uu____6032 = FStar_BigInt.to_int_fs to_l  in
                 let uu____6033 = FStar_BigInt.to_int_fs to_c  in
                 FStar_Range.mk_pos uu____6032 uu____6033  in
               FStar_Range.mk_range fn1 uu____6028 uu____6031  in
             let uu____6034 = term_of_range r  in
             FStar_Pervasives_Native.Some uu____6034
         | uu____6039 -> FStar_Pervasives_Native.None)
    | uu____6060 -> FStar_Pervasives_Native.None  in
  let decidable_eq neg psc args =
    let r = psc.psc_range  in
    let tru =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool true)) r
       in
    let fal =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool false)) r
       in
    match args with
    | (_typ,uu____6087)::(a1,uu____6089)::(a2,uu____6091)::[] ->
        let uu____6128 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____6128 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some (if neg then fal else tru)
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some (if neg then tru else fal)
         | uu____6141 -> FStar_Pervasives_Native.None)
    | uu____6142 -> failwith "Unexpected number of arguments"  in
  let idstep psc args =
    match args with
    | (a1,uu____6169)::[] -> FStar_Pervasives_Native.Some a1
    | uu____6178 -> failwith "Unexpected number of arguments"  in
  let basic_ops =
    let uu____6202 =
      let uu____6217 =
        let uu____6232 =
          let uu____6247 =
            let uu____6262 =
              let uu____6277 =
                let uu____6292 =
                  let uu____6307 =
                    let uu____6322 =
                      let uu____6337 =
                        let uu____6352 =
                          let uu____6367 =
                            let uu____6382 =
                              let uu____6397 =
                                let uu____6412 =
                                  let uu____6427 =
                                    let uu____6442 =
                                      let uu____6457 =
                                        let uu____6472 =
                                          let uu____6487 =
                                            let uu____6502 =
                                              let uu____6517 =
                                                let uu____6530 =
                                                  FStar_Parser_Const.p2l
                                                    ["FStar";
                                                    "String";
                                                    "list_of_string"]
                                                   in
                                                (uu____6530,
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
                                              let uu____6537 =
                                                let uu____6552 =
                                                  let uu____6565 =
                                                    FStar_Parser_Const.p2l
                                                      ["FStar";
                                                      "String";
                                                      "string_of_list"]
                                                     in
                                                  (uu____6565,
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
                                                let uu____6572 =
                                                  let uu____6587 =
                                                    let uu____6602 =
                                                      FStar_Parser_Const.p2l
                                                        ["FStar";
                                                        "String";
                                                        "concat"]
                                                       in
                                                    (uu____6602,
                                                      (Prims.parse_int "2"),
                                                      string_concat')
                                                     in
                                                  let uu____6611 =
                                                    let uu____6628 =
                                                      let uu____6643 =
                                                        FStar_Parser_Const.p2l
                                                          ["Prims";
                                                          "mk_range"]
                                                         in
                                                      (uu____6643,
                                                        (Prims.parse_int "5"),
                                                        mk_range1)
                                                       in
                                                    [uu____6628]  in
                                                  uu____6587 :: uu____6611
                                                   in
                                                uu____6552 :: uu____6572  in
                                              uu____6517 :: uu____6537  in
                                            (FStar_Parser_Const.op_notEq,
                                              (Prims.parse_int "3"),
                                              (decidable_eq true)) ::
                                              uu____6502
                                             in
                                          (FStar_Parser_Const.op_Eq,
                                            (Prims.parse_int "3"),
                                            (decidable_eq false)) ::
                                            uu____6487
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
                                          :: uu____6472
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
                                        :: uu____6457
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
                                      :: uu____6442
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
                                                        let uu____6834 =
                                                          FStar_BigInt.to_int_fs
                                                            x
                                                           in
                                                        FStar_String.make
                                                          uu____6834 y)) a466
                                                a467 a468)))
                                    :: uu____6427
                                   in
                                (FStar_Parser_Const.strcat_lid',
                                  (Prims.parse_int "2"),
                                  (binary_string_op
                                     (fun x  -> fun y  -> Prims.strcat x y)))
                                  :: uu____6412
                                 in
                              (FStar_Parser_Const.strcat_lid,
                                (Prims.parse_int "2"),
                                (binary_string_op
                                   (fun x  -> fun y  -> Prims.strcat x y)))
                                :: uu____6397
                               in
                            (FStar_Parser_Const.op_Or, (Prims.parse_int "2"),
                              (binary_bool_op (fun x  -> fun y  -> x || y)))
                              :: uu____6382
                             in
                          (FStar_Parser_Const.op_And, (Prims.parse_int "2"),
                            (binary_bool_op (fun x  -> fun y  -> x && y))) ::
                            uu____6367
                           in
                        (FStar_Parser_Const.op_Negation,
                          (Prims.parse_int "1"),
                          (unary_bool_op (fun x  -> Prims.op_Negation x))) ::
                          uu____6352
                         in
                      (FStar_Parser_Const.op_Modulus, (Prims.parse_int "2"),
                        (binary_int_op
                           (fun x  -> fun y  -> FStar_BigInt.mod_big_int x y)))
                        :: uu____6337
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
                                          let uu____7001 =
                                            FStar_BigInt.ge_big_int x y  in
                                          FStar_Syntax_Embeddings.embed_bool
                                            r uu____7001)) a470 a471 a472)))
                      :: uu____6322
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
                                        let uu____7027 =
                                          FStar_BigInt.gt_big_int x y  in
                                        FStar_Syntax_Embeddings.embed_bool r
                                          uu____7027)) a474 a475 a476)))
                    :: uu____6307
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
                                      let uu____7053 =
                                        FStar_BigInt.le_big_int x y  in
                                      FStar_Syntax_Embeddings.embed_bool r
                                        uu____7053)) a478 a479 a480)))
                  :: uu____6292
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
                                    let uu____7079 =
                                      FStar_BigInt.lt_big_int x y  in
                                    FStar_Syntax_Embeddings.embed_bool r
                                      uu____7079)) a482 a483 a484)))
                :: uu____6277
               in
            (FStar_Parser_Const.op_Division, (Prims.parse_int "2"),
              (binary_int_op
                 (fun x  -> fun y  -> FStar_BigInt.div_big_int x y)))
              :: uu____6262
             in
          (FStar_Parser_Const.op_Multiply, (Prims.parse_int "2"),
            (binary_int_op
               (fun x  -> fun y  -> FStar_BigInt.mult_big_int x y)))
            :: uu____6247
           in
        (FStar_Parser_Const.op_Subtraction, (Prims.parse_int "2"),
          (binary_int_op (fun x  -> fun y  -> FStar_BigInt.sub_big_int x y)))
          :: uu____6232
         in
      (FStar_Parser_Const.op_Addition, (Prims.parse_int "2"),
        (binary_int_op (fun x  -> fun y  -> FStar_BigInt.add_big_int x y)))
        :: uu____6217
       in
    (FStar_Parser_Const.op_Minus, (Prims.parse_int "1"),
      (unary_int_op (fun x  -> FStar_BigInt.minus_big_int x))) :: uu____6202
     in
  let weak_ops =
    let uu____7218 =
      let uu____7237 =
        FStar_Parser_Const.p2l ["FStar"; "Range"; "prims_to_fstar_range"]  in
      (uu____7237, (Prims.parse_int "1"), idstep)  in
    [uu____7218]  in
  let bounded_arith_ops =
    let bounded_signed_int_types = ["Int8"; "Int16"; "Int32"; "Int64"]  in
    let bounded_unsigned_int_types =
      ["UInt8"; "UInt16"; "UInt32"; "UInt64"; "UInt128"]  in
    let int_as_bounded r int_to_t1 n1 =
      let c = FStar_Syntax_Embeddings.embed_int r n1  in
      let int_to_t2 = FStar_Syntax_Syntax.fv_to_tm int_to_t1  in
      let uu____7321 =
        let uu____7322 =
          let uu____7323 = FStar_Syntax_Syntax.as_arg c  in [uu____7323]  in
        FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____7322  in
      uu____7321 FStar_Pervasives_Native.None r  in
    let add_sub_mul_v =
      FStar_All.pipe_right
        (FStar_List.append bounded_signed_int_types
           bounded_unsigned_int_types)
        (FStar_List.collect
           (fun m  ->
              let uu____7373 =
                let uu____7386 = FStar_Parser_Const.p2l ["FStar"; m; "add"]
                   in
                (uu____7386, (Prims.parse_int "2"),
                  (binary_op ()
                     (fun a485  -> (Obj.magic arg_as_bounded_int) a485)
                     (fun a486  ->
                        fun a487  ->
                          fun a488  ->
                            (Obj.magic
                               (fun r  ->
                                  fun uu____7402  ->
                                    fun uu____7403  ->
                                      match (uu____7402, uu____7403) with
                                      | ((int_to_t1,x),(uu____7422,y)) ->
                                          let uu____7432 =
                                            FStar_BigInt.add_big_int x y  in
                                          int_as_bounded r int_to_t1
                                            uu____7432)) a486 a487 a488)))
                 in
              let uu____7433 =
                let uu____7448 =
                  let uu____7461 = FStar_Parser_Const.p2l ["FStar"; m; "sub"]
                     in
                  (uu____7461, (Prims.parse_int "2"),
                    (binary_op ()
                       (fun a489  -> (Obj.magic arg_as_bounded_int) a489)
                       (fun a490  ->
                          fun a491  ->
                            fun a492  ->
                              (Obj.magic
                                 (fun r  ->
                                    fun uu____7477  ->
                                      fun uu____7478  ->
                                        match (uu____7477, uu____7478) with
                                        | ((int_to_t1,x),(uu____7497,y)) ->
                                            let uu____7507 =
                                              FStar_BigInt.sub_big_int x y
                                               in
                                            int_as_bounded r int_to_t1
                                              uu____7507)) a490 a491 a492)))
                   in
                let uu____7508 =
                  let uu____7523 =
                    let uu____7536 =
                      FStar_Parser_Const.p2l ["FStar"; m; "mul"]  in
                    (uu____7536, (Prims.parse_int "2"),
                      (binary_op ()
                         (fun a493  -> (Obj.magic arg_as_bounded_int) a493)
                         (fun a494  ->
                            fun a495  ->
                              fun a496  ->
                                (Obj.magic
                                   (fun r  ->
                                      fun uu____7552  ->
                                        fun uu____7553  ->
                                          match (uu____7552, uu____7553) with
                                          | ((int_to_t1,x),(uu____7572,y)) ->
                                              let uu____7582 =
                                                FStar_BigInt.mult_big_int x y
                                                 in
                                              int_as_bounded r int_to_t1
                                                uu____7582)) a494 a495 a496)))
                     in
                  let uu____7583 =
                    let uu____7598 =
                      let uu____7611 =
                        FStar_Parser_Const.p2l ["FStar"; m; "v"]  in
                      (uu____7611, (Prims.parse_int "1"),
                        (unary_op ()
                           (fun a497  -> (Obj.magic arg_as_bounded_int) a497)
                           (fun a498  ->
                              fun a499  ->
                                (Obj.magic
                                   (fun r  ->
                                      fun uu____7623  ->
                                        match uu____7623 with
                                        | (int_to_t1,x) ->
                                            FStar_Syntax_Embeddings.embed_int
                                              r x)) a498 a499)))
                       in
                    [uu____7598]  in
                  uu____7523 :: uu____7583  in
                uu____7448 :: uu____7508  in
              uu____7373 :: uu____7433))
       in
    let div_mod_unsigned =
      FStar_All.pipe_right bounded_unsigned_int_types
        (FStar_List.collect
           (fun m  ->
              let uu____7737 =
                let uu____7750 = FStar_Parser_Const.p2l ["FStar"; m; "div"]
                   in
                (uu____7750, (Prims.parse_int "2"),
                  (binary_op ()
                     (fun a500  -> (Obj.magic arg_as_bounded_int) a500)
                     (fun a501  ->
                        fun a502  ->
                          fun a503  ->
                            (Obj.magic
                               (fun r  ->
                                  fun uu____7766  ->
                                    fun uu____7767  ->
                                      match (uu____7766, uu____7767) with
                                      | ((int_to_t1,x),(uu____7786,y)) ->
                                          let uu____7796 =
                                            FStar_BigInt.div_big_int x y  in
                                          int_as_bounded r int_to_t1
                                            uu____7796)) a501 a502 a503)))
                 in
              let uu____7797 =
                let uu____7812 =
                  let uu____7825 = FStar_Parser_Const.p2l ["FStar"; m; "rem"]
                     in
                  (uu____7825, (Prims.parse_int "2"),
                    (binary_op ()
                       (fun a504  -> (Obj.magic arg_as_bounded_int) a504)
                       (fun a505  ->
                          fun a506  ->
                            fun a507  ->
                              (Obj.magic
                                 (fun r  ->
                                    fun uu____7841  ->
                                      fun uu____7842  ->
                                        match (uu____7841, uu____7842) with
                                        | ((int_to_t1,x),(uu____7861,y)) ->
                                            let uu____7871 =
                                              FStar_BigInt.mod_big_int x y
                                               in
                                            int_as_bounded r int_to_t1
                                              uu____7871)) a505 a506 a507)))
                   in
                [uu____7812]  in
              uu____7737 :: uu____7797))
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
    | (_typ,uu____7983)::(a1,uu____7985)::(a2,uu____7987)::[] ->
        let uu____8024 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____8024 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___136_8030 = FStar_Syntax_Util.t_true  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___136_8030.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___136_8030.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___137_8034 = FStar_Syntax_Util.t_false  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___137_8034.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___137_8034.FStar_Syntax_Syntax.vars)
                })
         | uu____8035 -> FStar_Pervasives_Native.None)
    | (_typ,uu____8037)::uu____8038::(a1,uu____8040)::(a2,uu____8042)::[] ->
        let uu____8091 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____8091 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___136_8097 = FStar_Syntax_Util.t_true  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___136_8097.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___136_8097.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___137_8101 = FStar_Syntax_Util.t_false  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___137_8101.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___137_8101.FStar_Syntax_Syntax.vars)
                })
         | uu____8102 -> FStar_Pervasives_Native.None)
    | uu____8103 -> failwith "Unexpected number of arguments"  in
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
let (unembed_binder_knot :
  FStar_Syntax_Syntax.binder FStar_Syntax_Embeddings.unembedder
    FStar_Pervasives_Native.option FStar_ST.ref)
  = FStar_Util.mk_ref FStar_Pervasives_Native.None 
let (unembed_binder :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____8155 = FStar_ST.op_Bang unembed_binder_knot  in
    match uu____8155 with
    | FStar_Pervasives_Native.Some f -> f t
    | FStar_Pervasives_Native.None  ->
        (FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos
           (FStar_Errors.Warning_UnembedBinderKnot,
             "unembed_binder_knot is unset!");
         FStar_Pervasives_Native.None)
  
let mk_psc_subst :
  'Auu____8202 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____8202) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_Syntax_Syntax.subst_elt Prims.list
  =
  fun cfg  ->
    fun env  ->
      FStar_List.fold_right
        (fun uu____8262  ->
           fun subst1  ->
             match uu____8262 with
             | (binder_opt,closure) ->
                 (match (binder_opt, closure) with
                  | (FStar_Pervasives_Native.Some b,Clos
                     (env1,term,uu____8303,uu____8304)) ->
                      let uu____8363 = b  in
                      (match uu____8363 with
                       | (bv,uu____8371) ->
                           let uu____8372 =
                             let uu____8373 =
                               FStar_Syntax_Util.is_constructed_typ
                                 bv.FStar_Syntax_Syntax.sort
                                 FStar_Parser_Const.binder_lid
                                in
                             Prims.op_Negation uu____8373  in
                           if uu____8372
                           then subst1
                           else
                             (let term1 = closure_as_term cfg env1 term  in
                              let uu____8378 = unembed_binder term1  in
                              match uu____8378 with
                              | FStar_Pervasives_Native.None  -> subst1
                              | FStar_Pervasives_Native.Some x ->
                                  let b1 =
                                    let uu____8385 =
                                      let uu___138_8386 = bv  in
                                      let uu____8387 =
                                        FStar_Syntax_Subst.subst subst1
                                          (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort
                                         in
                                      {
                                        FStar_Syntax_Syntax.ppname =
                                          (uu___138_8386.FStar_Syntax_Syntax.ppname);
                                        FStar_Syntax_Syntax.index =
                                          (uu___138_8386.FStar_Syntax_Syntax.index);
                                        FStar_Syntax_Syntax.sort = uu____8387
                                      }  in
                                    FStar_Syntax_Syntax.freshen_bv uu____8385
                                     in
                                  let b_for_x =
                                    let uu____8391 =
                                      let uu____8398 =
                                        FStar_Syntax_Syntax.bv_to_name b1  in
                                      ((FStar_Pervasives_Native.fst x),
                                        uu____8398)
                                       in
                                    FStar_Syntax_Syntax.NT uu____8391  in
                                  let subst2 =
                                    FStar_List.filter
                                      (fun uu___83_8407  ->
                                         match uu___83_8407 with
                                         | FStar_Syntax_Syntax.NT
                                             (uu____8408,{
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_name
                                                             b';
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____8410;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____8411;_})
                                             ->
                                             Prims.op_Negation
                                               (FStar_Ident.ident_equals
                                                  b1.FStar_Syntax_Syntax.ppname
                                                  b'.FStar_Syntax_Syntax.ppname)
                                         | uu____8416 -> true) subst1
                                     in
                                  b_for_x :: subst2))
                  | uu____8417 -> subst1)) env []
  
let reduce_primops :
  'Auu____8434 'Auu____8435 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____8434) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____8435 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          if Prims.op_Negation (cfg.steps).primops
          then tm
          else
            (let uu____8477 = FStar_Syntax_Util.head_and_args tm  in
             match uu____8477 with
             | (head1,args) ->
                 let uu____8514 =
                   let uu____8515 = FStar_Syntax_Util.un_uinst head1  in
                   uu____8515.FStar_Syntax_Syntax.n  in
                 (match uu____8514 with
                  | FStar_Syntax_Syntax.Tm_fvar fv ->
                      let uu____8519 =
                        FStar_Util.psmap_try_find cfg.primitive_steps
                          (FStar_Ident.text_of_lid
                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                         in
                      (match uu____8519 with
                       | FStar_Pervasives_Native.Some prim_step when
                           prim_step.strong_reduction_ok ||
                             (Prims.op_Negation cfg.strong)
                           ->
                           if (FStar_List.length args) < prim_step.arity
                           then
                             (log_primops cfg
                                (fun uu____8534  ->
                                   let uu____8535 =
                                     FStar_Syntax_Print.lid_to_string
                                       prim_step.name
                                      in
                                   let uu____8536 =
                                     FStar_Util.string_of_int
                                       (FStar_List.length args)
                                      in
                                   let uu____8543 =
                                     FStar_Util.string_of_int prim_step.arity
                                      in
                                   FStar_Util.print3
                                     "primop: found partially applied %s (%s/%s args)\n"
                                     uu____8535 uu____8536 uu____8543);
                              tm)
                           else
                             (log_primops cfg
                                (fun uu____8548  ->
                                   let uu____8549 =
                                     FStar_Syntax_Print.term_to_string tm  in
                                   FStar_Util.print1
                                     "primop: trying to reduce <%s>\n"
                                     uu____8549);
                              (let psc =
                                 {
                                   psc_range =
                                     (head1.FStar_Syntax_Syntax.pos);
                                   psc_subst =
                                     (fun uu____8552  ->
                                        if
                                          prim_step.requires_binder_substitution
                                        then mk_psc_subst cfg env
                                        else [])
                                 }  in
                               let uu____8554 =
                                 prim_step.interpretation psc args  in
                               match uu____8554 with
                               | FStar_Pervasives_Native.None  ->
                                   (log_primops cfg
                                      (fun uu____8560  ->
                                         let uu____8561 =
                                           FStar_Syntax_Print.term_to_string
                                             tm
                                            in
                                         FStar_Util.print1
                                           "primop: <%s> did not reduce\n"
                                           uu____8561);
                                    tm)
                               | FStar_Pervasives_Native.Some reduced ->
                                   (log_primops cfg
                                      (fun uu____8567  ->
                                         let uu____8568 =
                                           FStar_Syntax_Print.term_to_string
                                             tm
                                            in
                                         let uu____8569 =
                                           FStar_Syntax_Print.term_to_string
                                             reduced
                                            in
                                         FStar_Util.print2
                                           "primop: <%s> reduced to <%s>\n"
                                           uu____8568 uu____8569);
                                    reduced)))
                       | FStar_Pervasives_Native.Some uu____8570 ->
                           (log_primops cfg
                              (fun uu____8574  ->
                                 let uu____8575 =
                                   FStar_Syntax_Print.term_to_string tm  in
                                 FStar_Util.print1
                                   "primop: not reducing <%s> since we're doing strong reduction\n"
                                   uu____8575);
                            tm)
                       | FStar_Pervasives_Native.None  -> tm)
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_range_of ) when
                      Prims.op_Negation cfg.strong ->
                      (log_primops cfg
                         (fun uu____8579  ->
                            let uu____8580 =
                              FStar_Syntax_Print.term_to_string tm  in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____8580);
                       (match args with
                        | (a1,uu____8582)::[] ->
                            FStar_Syntax_Embeddings.embed_range
                              tm.FStar_Syntax_Syntax.pos
                              a1.FStar_Syntax_Syntax.pos
                        | uu____8599 -> tm))
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_set_range_of ) when
                      Prims.op_Negation cfg.strong ->
                      (log_primops cfg
                         (fun uu____8611  ->
                            let uu____8612 =
                              FStar_Syntax_Print.term_to_string tm  in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____8612);
                       (match args with
                        | (t,uu____8614)::(r,uu____8616)::[] ->
                            let uu____8643 =
                              FStar_Syntax_Embeddings.unembed_range r  in
                            (match uu____8643 with
                             | FStar_Pervasives_Native.Some rng ->
                                 let uu___139_8647 = t  in
                                 {
                                   FStar_Syntax_Syntax.n =
                                     (uu___139_8647.FStar_Syntax_Syntax.n);
                                   FStar_Syntax_Syntax.pos = rng;
                                   FStar_Syntax_Syntax.vars =
                                     (uu___139_8647.FStar_Syntax_Syntax.vars)
                                 }
                             | FStar_Pervasives_Native.None  -> tm)
                        | uu____8650 -> tm))
                  | uu____8659 -> tm))
  
let reduce_equality :
  'Auu____8664 'Auu____8665 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____8664) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____8665 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun tm  ->
      reduce_primops
        (let uu___140_8703 = cfg  in
         {
           steps =
             (let uu___141_8706 = default_steps  in
              {
                beta = (uu___141_8706.beta);
                iota = (uu___141_8706.iota);
                zeta = (uu___141_8706.zeta);
                weak = (uu___141_8706.weak);
                hnf = (uu___141_8706.hnf);
                primops = true;
                no_delta_steps = (uu___141_8706.no_delta_steps);
                unfold_until = (uu___141_8706.unfold_until);
                unfold_only = (uu___141_8706.unfold_only);
                unfold_attr = (uu___141_8706.unfold_attr);
                unfold_tac = (uu___141_8706.unfold_tac);
                pure_subterms_within_computations =
                  (uu___141_8706.pure_subterms_within_computations);
                simplify = (uu___141_8706.simplify);
                erase_universes = (uu___141_8706.erase_universes);
                allow_unbound_universes =
                  (uu___141_8706.allow_unbound_universes);
                reify_ = (uu___141_8706.reify_);
                compress_uvars = (uu___141_8706.compress_uvars);
                no_full_norm = (uu___141_8706.no_full_norm);
                check_no_uvars = (uu___141_8706.check_no_uvars);
                unmeta = (uu___141_8706.unmeta);
                unascribe = (uu___141_8706.unascribe)
              });
           tcenv = (uu___140_8703.tcenv);
           debug = (uu___140_8703.debug);
           delta_level = (uu___140_8703.delta_level);
           primitive_steps = equality_ops;
           strong = (uu___140_8703.strong);
           memoize_lazy = (uu___140_8703.memoize_lazy);
           normalize_pure_lets = (uu___140_8703.normalize_pure_lets)
         }) tm
  
let maybe_simplify_aux :
  'Auu____8713 'Auu____8714 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____8713) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____8714 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          let tm1 = reduce_primops cfg env stack tm  in
          let uu____8756 =
            FStar_All.pipe_left Prims.op_Negation (cfg.steps).simplify  in
          if uu____8756
          then tm1
          else
            (let w t =
               let uu___142_8768 = t  in
               {
                 FStar_Syntax_Syntax.n =
                   (uu___142_8768.FStar_Syntax_Syntax.n);
                 FStar_Syntax_Syntax.pos = (tm1.FStar_Syntax_Syntax.pos);
                 FStar_Syntax_Syntax.vars =
                   (uu___142_8768.FStar_Syntax_Syntax.vars)
               }  in
             let simp_t t =
               match t.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_meta
                   ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                      FStar_Syntax_Syntax.pos = uu____8784;
                      FStar_Syntax_Syntax.vars = uu____8785;_},uu____8786)
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
                      FStar_Syntax_Syntax.pos = uu____8793;
                      FStar_Syntax_Syntax.vars = uu____8794;_},uu____8795)
                   when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.false_lid
                   -> FStar_Pervasives_Native.Some false
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.false_lid
                   -> FStar_Pervasives_Native.Some false
               | uu____8801 -> FStar_Pervasives_Native.None  in
             let maybe_auto_squash t =
               let uu____8806 = FStar_Syntax_Util.is_sub_singleton t  in
               if uu____8806
               then t
               else
                 FStar_Syntax_Util.mk_auto_squash FStar_Syntax_Syntax.U_zero
                   t
                in
             let squashed_head_un_auto_squash_args t =
               let maybe_un_auto_squash_arg uu____8827 =
                 match uu____8827 with
                 | (t1,q) ->
                     let uu____8840 = FStar_Syntax_Util.is_auto_squash t1  in
                     (match uu____8840 with
                      | FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.U_zero ,t2) -> (t2, q)
                      | uu____8868 -> (t1, q))
                  in
               let uu____8877 = FStar_Syntax_Util.head_and_args t  in
               match uu____8877 with
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
                         FStar_Syntax_Syntax.pos = uu____8974;
                         FStar_Syntax_Syntax.vars = uu____8975;_},uu____8976);
                    FStar_Syntax_Syntax.pos = uu____8977;
                    FStar_Syntax_Syntax.vars = uu____8978;_},args)
                 ->
                 let uu____9004 =
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.and_lid
                    in
                 if uu____9004
                 then
                   let uu____9005 =
                     FStar_All.pipe_right args (FStar_List.map simplify1)  in
                   (match uu____9005 with
                    | (FStar_Pervasives_Native.Some (true ),uu____9060)::
                        (uu____9061,(arg,uu____9063))::[] ->
                        maybe_auto_squash arg
                    | (uu____9128,(arg,uu____9130))::(FStar_Pervasives_Native.Some
                                                      (true ),uu____9131)::[]
                        -> maybe_auto_squash arg
                    | (FStar_Pervasives_Native.Some (false ),uu____9196)::uu____9197::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____9260::(FStar_Pervasives_Native.Some (false
                                   ),uu____9261)::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____9324 -> squashed_head_un_auto_squash_args tm1)
                 else
                   (let uu____9340 =
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.or_lid
                       in
                    if uu____9340
                    then
                      let uu____9341 =
                        FStar_All.pipe_right args (FStar_List.map simplify1)
                         in
                      match uu____9341 with
                      | (FStar_Pervasives_Native.Some (true ),uu____9396)::uu____9397::[]
                          -> w FStar_Syntax_Util.t_true
                      | uu____9460::(FStar_Pervasives_Native.Some (true
                                     ),uu____9461)::[]
                          -> w FStar_Syntax_Util.t_true
                      | (FStar_Pervasives_Native.Some (false ),uu____9524)::
                          (uu____9525,(arg,uu____9527))::[] ->
                          maybe_auto_squash arg
                      | (uu____9592,(arg,uu____9594))::(FStar_Pervasives_Native.Some
                                                        (false ),uu____9595)::[]
                          -> maybe_auto_squash arg
                      | uu____9660 -> squashed_head_un_auto_squash_args tm1
                    else
                      (let uu____9676 =
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.imp_lid
                          in
                       if uu____9676
                       then
                         let uu____9677 =
                           FStar_All.pipe_right args
                             (FStar_List.map simplify1)
                            in
                         match uu____9677 with
                         | uu____9732::(FStar_Pervasives_Native.Some (true
                                        ),uu____9733)::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (false ),uu____9796)::uu____9797::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (true ),uu____9860)::
                             (uu____9861,(arg,uu____9863))::[] ->
                             maybe_auto_squash arg
                         | (uu____9928,(p,uu____9930))::(uu____9931,(q,uu____9933))::[]
                             ->
                             let uu____9998 = FStar_Syntax_Util.term_eq p q
                                in
                             (if uu____9998
                              then w FStar_Syntax_Util.t_true
                              else squashed_head_un_auto_squash_args tm1)
                         | uu____10000 ->
                             squashed_head_un_auto_squash_args tm1
                       else
                         (let uu____10016 =
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.iff_lid
                             in
                          if uu____10016
                          then
                            let uu____10017 =
                              FStar_All.pipe_right args
                                (FStar_List.map simplify1)
                               in
                            match uu____10017 with
                            | (FStar_Pervasives_Native.Some (true
                               ),uu____10072)::(FStar_Pervasives_Native.Some
                                                (true ),uu____10073)::[]
                                -> w FStar_Syntax_Util.t_true
                            | (FStar_Pervasives_Native.Some (false
                               ),uu____10138)::(FStar_Pervasives_Native.Some
                                                (false ),uu____10139)::[]
                                -> w FStar_Syntax_Util.t_true
                            | (FStar_Pervasives_Native.Some (true
                               ),uu____10204)::(FStar_Pervasives_Native.Some
                                                (false ),uu____10205)::[]
                                -> w FStar_Syntax_Util.t_false
                            | (FStar_Pervasives_Native.Some (false
                               ),uu____10270)::(FStar_Pervasives_Native.Some
                                                (true ),uu____10271)::[]
                                -> w FStar_Syntax_Util.t_false
                            | (uu____10336,(arg,uu____10338))::(FStar_Pervasives_Native.Some
                                                                (true
                                                                ),uu____10339)::[]
                                -> maybe_auto_squash arg
                            | (FStar_Pervasives_Native.Some (true
                               ),uu____10404)::(uu____10405,(arg,uu____10407))::[]
                                -> maybe_auto_squash arg
                            | (uu____10472,(p,uu____10474))::(uu____10475,
                                                              (q,uu____10477))::[]
                                ->
                                let uu____10542 =
                                  FStar_Syntax_Util.term_eq p q  in
                                (if uu____10542
                                 then w FStar_Syntax_Util.t_true
                                 else squashed_head_un_auto_squash_args tm1)
                            | uu____10544 ->
                                squashed_head_un_auto_squash_args tm1
                          else
                            (let uu____10560 =
                               FStar_Syntax_Syntax.fv_eq_lid fv
                                 FStar_Parser_Const.not_lid
                                in
                             if uu____10560
                             then
                               let uu____10561 =
                                 FStar_All.pipe_right args
                                   (FStar_List.map simplify1)
                                  in
                               match uu____10561 with
                               | (FStar_Pervasives_Native.Some (true
                                  ),uu____10616)::[] ->
                                   w FStar_Syntax_Util.t_false
                               | (FStar_Pervasives_Native.Some (false
                                  ),uu____10655)::[] ->
                                   w FStar_Syntax_Util.t_true
                               | uu____10694 ->
                                   squashed_head_un_auto_squash_args tm1
                             else
                               (let uu____10710 =
                                  FStar_Syntax_Syntax.fv_eq_lid fv
                                    FStar_Parser_Const.forall_lid
                                   in
                                if uu____10710
                                then
                                  match args with
                                  | (t,uu____10712)::[] ->
                                      let uu____10729 =
                                        let uu____10730 =
                                          FStar_Syntax_Subst.compress t  in
                                        uu____10730.FStar_Syntax_Syntax.n  in
                                      (match uu____10729 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____10733::[],body,uu____10735)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (true ) ->
                                                w FStar_Syntax_Util.t_true
                                            | uu____10762 -> tm1)
                                       | uu____10765 -> tm1)
                                  | (uu____10766,FStar_Pervasives_Native.Some
                                     (FStar_Syntax_Syntax.Implicit
                                     uu____10767))::(t,uu____10769)::[] ->
                                      let uu____10808 =
                                        let uu____10809 =
                                          FStar_Syntax_Subst.compress t  in
                                        uu____10809.FStar_Syntax_Syntax.n  in
                                      (match uu____10808 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____10812::[],body,uu____10814)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (true ) ->
                                                w FStar_Syntax_Util.t_true
                                            | uu____10841 -> tm1)
                                       | uu____10844 -> tm1)
                                  | uu____10845 -> tm1
                                else
                                  (let uu____10855 =
                                     FStar_Syntax_Syntax.fv_eq_lid fv
                                       FStar_Parser_Const.exists_lid
                                      in
                                   if uu____10855
                                   then
                                     match args with
                                     | (t,uu____10857)::[] ->
                                         let uu____10874 =
                                           let uu____10875 =
                                             FStar_Syntax_Subst.compress t
                                              in
                                           uu____10875.FStar_Syntax_Syntax.n
                                            in
                                         (match uu____10874 with
                                          | FStar_Syntax_Syntax.Tm_abs
                                              (uu____10878::[],body,uu____10880)
                                              ->
                                              (match simp_t body with
                                               | FStar_Pervasives_Native.Some
                                                   (false ) ->
                                                   w
                                                     FStar_Syntax_Util.t_false
                                               | uu____10907 -> tm1)
                                          | uu____10910 -> tm1)
                                     | (uu____10911,FStar_Pervasives_Native.Some
                                        (FStar_Syntax_Syntax.Implicit
                                        uu____10912))::(t,uu____10914)::[] ->
                                         let uu____10953 =
                                           let uu____10954 =
                                             FStar_Syntax_Subst.compress t
                                              in
                                           uu____10954.FStar_Syntax_Syntax.n
                                            in
                                         (match uu____10953 with
                                          | FStar_Syntax_Syntax.Tm_abs
                                              (uu____10957::[],body,uu____10959)
                                              ->
                                              (match simp_t body with
                                               | FStar_Pervasives_Native.Some
                                                   (false ) ->
                                                   w
                                                     FStar_Syntax_Util.t_false
                                               | uu____10986 -> tm1)
                                          | uu____10989 -> tm1)
                                     | uu____10990 -> tm1
                                   else
                                     (let uu____11000 =
                                        FStar_Syntax_Syntax.fv_eq_lid fv
                                          FStar_Parser_Const.b2t_lid
                                         in
                                      if uu____11000
                                      then
                                        match args with
                                        | ({
                                             FStar_Syntax_Syntax.n =
                                               FStar_Syntax_Syntax.Tm_constant
                                               (FStar_Const.Const_bool (true
                                               ));
                                             FStar_Syntax_Syntax.pos =
                                               uu____11001;
                                             FStar_Syntax_Syntax.vars =
                                               uu____11002;_},uu____11003)::[]
                                            -> w FStar_Syntax_Util.t_true
                                        | ({
                                             FStar_Syntax_Syntax.n =
                                               FStar_Syntax_Syntax.Tm_constant
                                               (FStar_Const.Const_bool (false
                                               ));
                                             FStar_Syntax_Syntax.pos =
                                               uu____11020;
                                             FStar_Syntax_Syntax.vars =
                                               uu____11021;_},uu____11022)::[]
                                            -> w FStar_Syntax_Util.t_false
                                        | uu____11039 -> tm1
                                      else
                                        (let uu____11049 =
                                           FStar_Syntax_Util.is_auto_squash
                                             tm1
                                            in
                                         match uu____11049 with
                                         | FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.U_zero ,t)
                                             when
                                             FStar_Syntax_Util.is_sub_singleton
                                               t
                                             -> t
                                         | uu____11069 ->
                                             reduce_equality cfg env stack
                                               tm1))))))))
             | FStar_Syntax_Syntax.Tm_app
                 ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                    FStar_Syntax_Syntax.pos = uu____11079;
                    FStar_Syntax_Syntax.vars = uu____11080;_},args)
                 ->
                 let uu____11102 =
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.and_lid
                    in
                 if uu____11102
                 then
                   let uu____11103 =
                     FStar_All.pipe_right args (FStar_List.map simplify1)  in
                   (match uu____11103 with
                    | (FStar_Pervasives_Native.Some (true ),uu____11158)::
                        (uu____11159,(arg,uu____11161))::[] ->
                        maybe_auto_squash arg
                    | (uu____11226,(arg,uu____11228))::(FStar_Pervasives_Native.Some
                                                        (true ),uu____11229)::[]
                        -> maybe_auto_squash arg
                    | (FStar_Pervasives_Native.Some (false ),uu____11294)::uu____11295::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____11358::(FStar_Pervasives_Native.Some (false
                                    ),uu____11359)::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____11422 -> squashed_head_un_auto_squash_args tm1)
                 else
                   (let uu____11438 =
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.or_lid
                       in
                    if uu____11438
                    then
                      let uu____11439 =
                        FStar_All.pipe_right args (FStar_List.map simplify1)
                         in
                      match uu____11439 with
                      | (FStar_Pervasives_Native.Some (true ),uu____11494)::uu____11495::[]
                          -> w FStar_Syntax_Util.t_true
                      | uu____11558::(FStar_Pervasives_Native.Some (true
                                      ),uu____11559)::[]
                          -> w FStar_Syntax_Util.t_true
                      | (FStar_Pervasives_Native.Some (false ),uu____11622)::
                          (uu____11623,(arg,uu____11625))::[] ->
                          maybe_auto_squash arg
                      | (uu____11690,(arg,uu____11692))::(FStar_Pervasives_Native.Some
                                                          (false
                                                          ),uu____11693)::[]
                          -> maybe_auto_squash arg
                      | uu____11758 -> squashed_head_un_auto_squash_args tm1
                    else
                      (let uu____11774 =
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.imp_lid
                          in
                       if uu____11774
                       then
                         let uu____11775 =
                           FStar_All.pipe_right args
                             (FStar_List.map simplify1)
                            in
                         match uu____11775 with
                         | uu____11830::(FStar_Pervasives_Native.Some (true
                                         ),uu____11831)::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____11894)::uu____11895::[] ->
                             w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (true ),uu____11958)::
                             (uu____11959,(arg,uu____11961))::[] ->
                             maybe_auto_squash arg
                         | (uu____12026,(p,uu____12028))::(uu____12029,
                                                           (q,uu____12031))::[]
                             ->
                             let uu____12096 = FStar_Syntax_Util.term_eq p q
                                in
                             (if uu____12096
                              then w FStar_Syntax_Util.t_true
                              else squashed_head_un_auto_squash_args tm1)
                         | uu____12098 ->
                             squashed_head_un_auto_squash_args tm1
                       else
                         (let uu____12114 =
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.iff_lid
                             in
                          if uu____12114
                          then
                            let uu____12115 =
                              FStar_All.pipe_right args
                                (FStar_List.map simplify1)
                               in
                            match uu____12115 with
                            | (FStar_Pervasives_Native.Some (true
                               ),uu____12170)::(FStar_Pervasives_Native.Some
                                                (true ),uu____12171)::[]
                                -> w FStar_Syntax_Util.t_true
                            | (FStar_Pervasives_Native.Some (false
                               ),uu____12236)::(FStar_Pervasives_Native.Some
                                                (false ),uu____12237)::[]
                                -> w FStar_Syntax_Util.t_true
                            | (FStar_Pervasives_Native.Some (true
                               ),uu____12302)::(FStar_Pervasives_Native.Some
                                                (false ),uu____12303)::[]
                                -> w FStar_Syntax_Util.t_false
                            | (FStar_Pervasives_Native.Some (false
                               ),uu____12368)::(FStar_Pervasives_Native.Some
                                                (true ),uu____12369)::[]
                                -> w FStar_Syntax_Util.t_false
                            | (uu____12434,(arg,uu____12436))::(FStar_Pervasives_Native.Some
                                                                (true
                                                                ),uu____12437)::[]
                                -> maybe_auto_squash arg
                            | (FStar_Pervasives_Native.Some (true
                               ),uu____12502)::(uu____12503,(arg,uu____12505))::[]
                                -> maybe_auto_squash arg
                            | (uu____12570,(p,uu____12572))::(uu____12573,
                                                              (q,uu____12575))::[]
                                ->
                                let uu____12640 =
                                  FStar_Syntax_Util.term_eq p q  in
                                (if uu____12640
                                 then w FStar_Syntax_Util.t_true
                                 else squashed_head_un_auto_squash_args tm1)
                            | uu____12642 ->
                                squashed_head_un_auto_squash_args tm1
                          else
                            (let uu____12658 =
                               FStar_Syntax_Syntax.fv_eq_lid fv
                                 FStar_Parser_Const.not_lid
                                in
                             if uu____12658
                             then
                               let uu____12659 =
                                 FStar_All.pipe_right args
                                   (FStar_List.map simplify1)
                                  in
                               match uu____12659 with
                               | (FStar_Pervasives_Native.Some (true
                                  ),uu____12714)::[] ->
                                   w FStar_Syntax_Util.t_false
                               | (FStar_Pervasives_Native.Some (false
                                  ),uu____12753)::[] ->
                                   w FStar_Syntax_Util.t_true
                               | uu____12792 ->
                                   squashed_head_un_auto_squash_args tm1
                             else
                               (let uu____12808 =
                                  FStar_Syntax_Syntax.fv_eq_lid fv
                                    FStar_Parser_Const.forall_lid
                                   in
                                if uu____12808
                                then
                                  match args with
                                  | (t,uu____12810)::[] ->
                                      let uu____12827 =
                                        let uu____12828 =
                                          FStar_Syntax_Subst.compress t  in
                                        uu____12828.FStar_Syntax_Syntax.n  in
                                      (match uu____12827 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____12831::[],body,uu____12833)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (true ) ->
                                                w FStar_Syntax_Util.t_true
                                            | uu____12860 -> tm1)
                                       | uu____12863 -> tm1)
                                  | (uu____12864,FStar_Pervasives_Native.Some
                                     (FStar_Syntax_Syntax.Implicit
                                     uu____12865))::(t,uu____12867)::[] ->
                                      let uu____12906 =
                                        let uu____12907 =
                                          FStar_Syntax_Subst.compress t  in
                                        uu____12907.FStar_Syntax_Syntax.n  in
                                      (match uu____12906 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____12910::[],body,uu____12912)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (true ) ->
                                                w FStar_Syntax_Util.t_true
                                            | uu____12939 -> tm1)
                                       | uu____12942 -> tm1)
                                  | uu____12943 -> tm1
                                else
                                  (let uu____12953 =
                                     FStar_Syntax_Syntax.fv_eq_lid fv
                                       FStar_Parser_Const.exists_lid
                                      in
                                   if uu____12953
                                   then
                                     match args with
                                     | (t,uu____12955)::[] ->
                                         let uu____12972 =
                                           let uu____12973 =
                                             FStar_Syntax_Subst.compress t
                                              in
                                           uu____12973.FStar_Syntax_Syntax.n
                                            in
                                         (match uu____12972 with
                                          | FStar_Syntax_Syntax.Tm_abs
                                              (uu____12976::[],body,uu____12978)
                                              ->
                                              (match simp_t body with
                                               | FStar_Pervasives_Native.Some
                                                   (false ) ->
                                                   w
                                                     FStar_Syntax_Util.t_false
                                               | uu____13005 -> tm1)
                                          | uu____13008 -> tm1)
                                     | (uu____13009,FStar_Pervasives_Native.Some
                                        (FStar_Syntax_Syntax.Implicit
                                        uu____13010))::(t,uu____13012)::[] ->
                                         let uu____13051 =
                                           let uu____13052 =
                                             FStar_Syntax_Subst.compress t
                                              in
                                           uu____13052.FStar_Syntax_Syntax.n
                                            in
                                         (match uu____13051 with
                                          | FStar_Syntax_Syntax.Tm_abs
                                              (uu____13055::[],body,uu____13057)
                                              ->
                                              (match simp_t body with
                                               | FStar_Pervasives_Native.Some
                                                   (false ) ->
                                                   w
                                                     FStar_Syntax_Util.t_false
                                               | uu____13084 -> tm1)
                                          | uu____13087 -> tm1)
                                     | uu____13088 -> tm1
                                   else
                                     (let uu____13098 =
                                        FStar_Syntax_Syntax.fv_eq_lid fv
                                          FStar_Parser_Const.b2t_lid
                                         in
                                      if uu____13098
                                      then
                                        match args with
                                        | ({
                                             FStar_Syntax_Syntax.n =
                                               FStar_Syntax_Syntax.Tm_constant
                                               (FStar_Const.Const_bool (true
                                               ));
                                             FStar_Syntax_Syntax.pos =
                                               uu____13099;
                                             FStar_Syntax_Syntax.vars =
                                               uu____13100;_},uu____13101)::[]
                                            -> w FStar_Syntax_Util.t_true
                                        | ({
                                             FStar_Syntax_Syntax.n =
                                               FStar_Syntax_Syntax.Tm_constant
                                               (FStar_Const.Const_bool (false
                                               ));
                                             FStar_Syntax_Syntax.pos =
                                               uu____13118;
                                             FStar_Syntax_Syntax.vars =
                                               uu____13119;_},uu____13120)::[]
                                            -> w FStar_Syntax_Util.t_false
                                        | uu____13137 -> tm1
                                      else
                                        (let uu____13147 =
                                           FStar_Syntax_Util.is_auto_squash
                                             tm1
                                            in
                                         match uu____13147 with
                                         | FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.U_zero ,t)
                                             when
                                             FStar_Syntax_Util.is_sub_singleton
                                               t
                                             -> t
                                         | uu____13167 ->
                                             reduce_equality cfg env stack
                                               tm1))))))))
             | FStar_Syntax_Syntax.Tm_refine (bv,t) ->
                 (match simp_t t with
                  | FStar_Pervasives_Native.Some (true ) ->
                      bv.FStar_Syntax_Syntax.sort
                  | FStar_Pervasives_Native.Some (false ) -> tm1
                  | FStar_Pervasives_Native.None  -> tm1)
             | uu____13182 -> tm1)
  
let maybe_simplify :
  'Auu____13189 'Auu____13190 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____13189) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____13190 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          let tm' = maybe_simplify_aux cfg env stack tm  in
          if (cfg.debug).b380
          then
            (let uu____13233 = FStar_Syntax_Print.term_to_string tm  in
             let uu____13234 = FStar_Syntax_Print.term_to_string tm'  in
             FStar_Util.print3 "%sSimplified\n\t%s to\n\t%s\n"
               (if (cfg.steps).simplify then "" else "NOT ") uu____13233
               uu____13234)
          else ();
          tm'
  
let is_norm_request :
  'Auu____13240 .
    FStar_Syntax_Syntax.term -> 'Auu____13240 Prims.list -> Prims.bool
  =
  fun hd1  ->
    fun args  ->
      let uu____13253 =
        let uu____13260 =
          let uu____13261 = FStar_Syntax_Util.un_uinst hd1  in
          uu____13261.FStar_Syntax_Syntax.n  in
        (uu____13260, args)  in
      match uu____13253 with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____13267::uu____13268::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____13272::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize
      | (FStar_Syntax_Syntax.Tm_fvar fv,steps::uu____13277::uu____13278::[])
          -> FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm
      | uu____13281 -> false
  
let (tr_norm_step : FStar_Syntax_Embeddings.norm_step -> step Prims.list) =
  fun uu___84_13292  ->
    match uu___84_13292 with
    | FStar_Syntax_Embeddings.Zeta  -> [Zeta]
    | FStar_Syntax_Embeddings.Iota  -> [Iota]
    | FStar_Syntax_Embeddings.Delta  ->
        [UnfoldUntil FStar_Syntax_Syntax.Delta_constant]
    | FStar_Syntax_Embeddings.Simpl  -> [Simplify]
    | FStar_Syntax_Embeddings.Weak  -> [Weak]
    | FStar_Syntax_Embeddings.HNF  -> [HNF]
    | FStar_Syntax_Embeddings.Primops  -> [Primops]
    | FStar_Syntax_Embeddings.UnfoldOnly names1 ->
        let uu____13298 =
          let uu____13301 =
            let uu____13302 = FStar_List.map FStar_Ident.lid_of_str names1
               in
            UnfoldOnly uu____13302  in
          [uu____13301]  in
        (UnfoldUntil FStar_Syntax_Syntax.Delta_constant) :: uu____13298
    | FStar_Syntax_Embeddings.UnfoldAttr t ->
        [UnfoldUntil FStar_Syntax_Syntax.Delta_constant; UnfoldAttr t]
  
let (tr_norm_steps :
  FStar_Syntax_Embeddings.norm_step Prims.list -> step Prims.list) =
  fun s  -> FStar_List.concatMap tr_norm_step s 
let get_norm_request :
  'Auu____13318 .
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
      (FStar_Syntax_Syntax.term,'Auu____13318) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (step Prims.list,FStar_Syntax_Syntax.term)
          FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun full_norm  ->
    fun args  ->
      let parse_steps s =
        try
          let uu____13371 =
            let uu____13374 =
              let uu____13377 =
                let uu____13382 =
                  FStar_Syntax_Embeddings.unembed_list_safe
                    FStar_Syntax_Embeddings.unembed_norm_step
                   in
                uu____13382 s  in
              FStar_All.pipe_right uu____13377 FStar_Util.must  in
            FStar_All.pipe_right uu____13374 tr_norm_steps  in
          FStar_Pervasives_Native.Some uu____13371
        with | uu____13410 -> FStar_Pervasives_Native.None  in
      match args with
      | uu____13421::(tm,uu____13423)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify]  in
          FStar_Pervasives_Native.Some (s, tm)
      | (tm,uu____13452)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify]  in
          FStar_Pervasives_Native.Some (s, tm)
      | (steps,uu____13473)::uu____13474::(tm,uu____13476)::[] ->
          let add_exclude s z =
            if FStar_List.contains z s then s else (Exclude z) :: s  in
          let uu____13513 =
            let uu____13518 = full_norm steps  in parse_steps uu____13518  in
          (match uu____13513 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some s ->
               let s1 = Beta :: s  in
               let s2 = add_exclude s1 Zeta  in
               let s3 = add_exclude s2 Iota  in
               FStar_Pervasives_Native.Some (s3, tm))
      | uu____13557 -> FStar_Pervasives_Native.None
  
let (is_reify_head : stack_elt Prims.list -> Prims.bool) =
  fun uu___85_13574  ->
    match uu___85_13574 with
    | (App
        (uu____13577,{
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reify );
                       FStar_Syntax_Syntax.pos = uu____13578;
                       FStar_Syntax_Syntax.vars = uu____13579;_},uu____13580,uu____13581))::uu____13582
        -> true
    | uu____13589 -> false
  
let firstn :
  'Auu____13595 .
    Prims.int ->
      'Auu____13595 Prims.list ->
        ('Auu____13595 Prims.list,'Auu____13595 Prims.list)
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
          (uu____13631,{
                         FStar_Syntax_Syntax.n =
                           FStar_Syntax_Syntax.Tm_constant
                           (FStar_Const.Const_reify );
                         FStar_Syntax_Syntax.pos = uu____13632;
                         FStar_Syntax_Syntax.vars = uu____13633;_},uu____13634,uu____13635))::uu____13636
          -> (cfg.steps).reify_
      | uu____13643 -> false
  
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
               | FStar_Syntax_Syntax.Tm_delayed uu____13787 ->
                   let uu____13812 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print1 "NORM delayed: %s\n" uu____13812
               | uu____13813 -> ())
            else ();
            FStar_Syntax_Subst.compress t  in
          log cfg
            (fun uu____13821  ->
               let uu____13822 = FStar_Syntax_Print.tag_of_term t1  in
               let uu____13823 = FStar_Syntax_Print.term_to_string t1  in
               let uu____13824 =
                 FStar_Util.string_of_int (FStar_List.length env)  in
               let uu____13831 =
                 let uu____13832 =
                   let uu____13835 = firstn (Prims.parse_int "4") stack  in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____13835
                    in
                 stack_to_string uu____13832  in
               FStar_Util.print4
                 ">>> %s\nNorm %s with with %s env elements top of the stack %s \n"
                 uu____13822 uu____13823 uu____13824 uu____13831);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_constant uu____13858 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_name uu____13859 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_lazy uu____13860 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____13861;
                 FStar_Syntax_Syntax.fv_delta =
                   FStar_Syntax_Syntax.Delta_constant ;
                 FStar_Syntax_Syntax.fv_qual = uu____13862;_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____13865;
                 FStar_Syntax_Syntax.fv_delta = uu____13866;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Data_ctor );_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____13867;
                 FStar_Syntax_Syntax.fv_delta = uu____13868;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor uu____13869);_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_meta
               (t0,FStar_Syntax_Syntax.Meta_quoted (t11,qi)) ->
               let t01 = closure_as_term cfg env t0  in
               let t12 =
                 if qi.FStar_Syntax_Syntax.qopen
                 then closure_as_term cfg env t11
                 else t11  in
               let t2 =
                 let uu___145_13893 = t1  in
                 {
                   FStar_Syntax_Syntax.n =
                     (FStar_Syntax_Syntax.Tm_meta
                        (t01, (FStar_Syntax_Syntax.Meta_quoted (t12, qi))));
                   FStar_Syntax_Syntax.pos =
                     (uu___145_13893.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___145_13893.FStar_Syntax_Syntax.vars)
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
                 let uu___146_13923 = cfg  in
                 {
                   steps =
                     (let uu___147_13926 = cfg.steps  in
                      {
                        beta = (uu___147_13926.beta);
                        iota = (uu___147_13926.iota);
                        zeta = (uu___147_13926.zeta);
                        weak = (uu___147_13926.weak);
                        hnf = (uu___147_13926.hnf);
                        primops = (uu___147_13926.primops);
                        no_delta_steps = false;
                        unfold_until = (uu___147_13926.unfold_until);
                        unfold_only = FStar_Pervasives_Native.None;
                        unfold_attr = (uu___147_13926.unfold_attr);
                        unfold_tac = (uu___147_13926.unfold_tac);
                        pure_subterms_within_computations =
                          (uu___147_13926.pure_subterms_within_computations);
                        simplify = (uu___147_13926.simplify);
                        erase_universes = (uu___147_13926.erase_universes);
                        allow_unbound_universes =
                          (uu___147_13926.allow_unbound_universes);
                        reify_ = (uu___147_13926.reify_);
                        compress_uvars = (uu___147_13926.compress_uvars);
                        no_full_norm = (uu___147_13926.no_full_norm);
                        check_no_uvars = (uu___147_13926.check_no_uvars);
                        unmeta = (uu___147_13926.unmeta);
                        unascribe = (uu___147_13926.unascribe)
                      });
                   tcenv = (uu___146_13923.tcenv);
                   debug = (uu___146_13923.debug);
                   delta_level =
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.Delta_constant];
                   primitive_steps = (uu___146_13923.primitive_steps);
                   strong = (uu___146_13923.strong);
                   memoize_lazy = (uu___146_13923.memoize_lazy);
                   normalize_pure_lets = true
                 }  in
               let uu____13929 = get_norm_request (norm cfg' env []) args  in
               (match uu____13929 with
                | FStar_Pervasives_Native.None  ->
                    let stack1 =
                      FStar_All.pipe_right stack
                        (FStar_List.fold_right
                           (fun uu____13960  ->
                              fun stack1  ->
                                match uu____13960 with
                                | (a,aq) ->
                                    let uu____13972 =
                                      let uu____13973 =
                                        let uu____13980 =
                                          let uu____13981 =
                                            let uu____14012 =
                                              FStar_Util.mk_ref
                                                FStar_Pervasives_Native.None
                                               in
                                            (env, a, uu____14012, false)  in
                                          Clos uu____13981  in
                                        (uu____13980, aq,
                                          (t1.FStar_Syntax_Syntax.pos))
                                         in
                                      Arg uu____13973  in
                                    uu____13972 :: stack1) args)
                       in
                    (log cfg
                       (fun uu____14096  ->
                          let uu____14097 =
                            FStar_All.pipe_left FStar_Util.string_of_int
                              (FStar_List.length args)
                             in
                          FStar_Util.print1 "\tPushed %s arguments\n"
                            uu____14097);
                     norm cfg env stack1 hd1)
                | FStar_Pervasives_Native.Some (s,tm) ->
                    let delta_level =
                      let uu____14119 =
                        FStar_All.pipe_right s
                          (FStar_Util.for_some
                             (fun uu___86_14124  ->
                                match uu___86_14124 with
                                | UnfoldUntil uu____14125 -> true
                                | UnfoldOnly uu____14126 -> true
                                | uu____14129 -> false))
                         in
                      if uu____14119
                      then
                        [FStar_TypeChecker_Env.Unfold
                           FStar_Syntax_Syntax.Delta_constant]
                      else [FStar_TypeChecker_Env.NoDelta]  in
                    let cfg'1 =
                      let uu___148_14134 = cfg  in
                      let uu____14135 = to_fsteps s  in
                      {
                        steps = uu____14135;
                        tcenv = (uu___148_14134.tcenv);
                        debug = (uu___148_14134.debug);
                        delta_level;
                        primitive_steps = (uu___148_14134.primitive_steps);
                        strong = (uu___148_14134.strong);
                        memoize_lazy = (uu___148_14134.memoize_lazy);
                        normalize_pure_lets = true
                      }  in
                    let stack' =
                      let tail1 = (Cfg cfg) :: stack  in
                      if (cfg.debug).print_normalized
                      then
                        let uu____14144 =
                          let uu____14145 =
                            let uu____14150 = FStar_Util.now ()  in
                            (t1, uu____14150)  in
                          Debug uu____14145  in
                        uu____14144 :: tail1
                      else tail1  in
                    norm cfg'1 env stack' tm)
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u  in
               let uu____14154 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack uu____14154
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               if (cfg.steps).erase_universes
               then norm cfg env stack t'
               else
                 (let us1 =
                    let uu____14163 =
                      let uu____14170 =
                        FStar_List.map (norm_universe cfg env) us  in
                      (uu____14170, (t1.FStar_Syntax_Syntax.pos))  in
                    UnivArgs uu____14163  in
                  let stack1 = us1 :: stack  in norm cfg env stack1 t')
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let qninfo =
                 let uu____14180 = FStar_Syntax_Syntax.lid_of_fv fv  in
                 FStar_TypeChecker_Env.lookup_qname cfg.tcenv uu____14180  in
               let uu____14181 =
                 FStar_TypeChecker_Env.qninfo_is_action qninfo  in
               if uu____14181
               then
                 let b = should_reify cfg stack  in
                 (log cfg
                    (fun uu____14187  ->
                       let uu____14188 = FStar_Syntax_Print.term_to_string t1
                          in
                       let uu____14189 = FStar_Util.string_of_bool b  in
                       FStar_Util.print2
                         ">>> For DM4F action %s, should_reify = %s\n"
                         uu____14188 uu____14189);
                  if b
                  then
                    (let uu____14190 = FStar_List.tl stack  in
                     do_unfold_fv cfg env uu____14190 t1 qninfo fv)
                  else rebuild cfg env stack t1)
               else
                 (let should_delta =
                    FStar_All.pipe_right cfg.delta_level
                      (FStar_Util.for_some
                         (fun uu___87_14199  ->
                            match uu___87_14199 with
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
                      (let attrs =
                         FStar_TypeChecker_Env.attrs_of_qninfo qninfo  in
                       ((Prims.op_Negation (cfg.steps).unfold_tac) ||
                          (let uu____14209 =
                             cases
                               (FStar_Util.for_some
                                  (FStar_Syntax_Util.attr_eq
                                     FStar_Syntax_Util.tac_opaque_attr))
                               false attrs
                              in
                           Prims.op_Negation uu____14209))
                         &&
                         ((match (cfg.steps).unfold_only with
                           | FStar_Pervasives_Native.None  -> true
                           | FStar_Pervasives_Native.Some lids ->
                               FStar_Util.for_some
                                 (FStar_Syntax_Syntax.fv_eq_lid fv) lids)
                            ||
                            (match (attrs, ((cfg.steps).unfold_attr)) with
                             | (FStar_Pervasives_Native.None
                                ,FStar_Pervasives_Native.Some uu____14228) ->
                                 false
                             | (FStar_Pervasives_Native.Some
                                ats,FStar_Pervasives_Native.Some ats') ->
                                 FStar_Util.for_some
                                   (fun at  ->
                                      FStar_Util.for_some
                                        (FStar_Syntax_Util.attr_eq at) ats')
                                   ats
                             | (uu____14263,uu____14264) -> false)))
                     in
                  log cfg
                    (fun uu____14286  ->
                       let uu____14287 = FStar_Syntax_Print.term_to_string t1
                          in
                       let uu____14288 =
                         FStar_Range.string_of_range
                           t1.FStar_Syntax_Syntax.pos
                          in
                       let uu____14289 =
                         FStar_Util.string_of_bool should_delta1  in
                       FStar_Util.print3
                         ">>> For %s (%s), should_delta = %s\n" uu____14287
                         uu____14288 uu____14289);
                  if should_delta1
                  then do_unfold_fv cfg env stack t1 qninfo fv
                  else rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____14292 = lookup_bvar env x  in
               (match uu____14292 with
                | Univ uu____14295 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if (Prims.op_Negation fix) || (cfg.steps).zeta
                    then
                      let uu____14344 = FStar_ST.op_Bang r  in
                      (match uu____14344 with
                       | FStar_Pervasives_Native.Some (env2,t') ->
                           (log cfg
                              (fun uu____14462  ->
                                 let uu____14463 =
                                   FStar_Syntax_Print.term_to_string t1  in
                                 let uu____14464 =
                                   FStar_Syntax_Print.term_to_string t'  in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____14463
                                   uu____14464);
                            (let uu____14465 =
                               let uu____14466 =
                                 FStar_Syntax_Subst.compress t'  in
                               uu____14466.FStar_Syntax_Syntax.n  in
                             match uu____14465 with
                             | FStar_Syntax_Syntax.Tm_abs uu____14469 ->
                                 norm cfg env2 stack t'
                             | uu____14486 -> rebuild cfg env2 stack t'))
                       | FStar_Pervasives_Native.None  ->
                           norm cfg env1 ((MemoLazy r) :: stack) t0)
                    else norm cfg env1 stack t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack with
                | (UnivArgs uu____14556)::uu____14557 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Match uu____14566)::uu____14567 ->
                    failwith
                      "Ill-typed term: cannot pattern match an abstraction"
                | (Arg (c,uu____14577,uu____14578))::stack_rest ->
                    (match c with
                     | Univ uu____14582 ->
                         norm cfg ((FStar_Pervasives_Native.None, c) :: env)
                           stack_rest t1
                     | uu____14591 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | b::[] ->
                              (log cfg
                                 (fun uu____14612  ->
                                    let uu____14613 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____14613);
                               norm cfg
                                 (((FStar_Pervasives_Native.Some b), c) ::
                                 env) stack_rest body)
                          | b::tl1 ->
                              (log cfg
                                 (fun uu____14653  ->
                                    let uu____14654 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____14654);
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
                       (fun uu____14732  ->
                          let uu____14733 =
                            FStar_Syntax_Print.term_to_string t1  in
                          FStar_Util.print1 "\tSet memo %s\n" uu____14733);
                     norm cfg env stack1 t1)
                | (Debug uu____14734)::uu____14735 ->
                    if (cfg.steps).weak
                    then
                      let uu____14742 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____14742
                    else
                      (let uu____14744 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____14744 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____14786  -> dummy :: env1) env)
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
                                          let uu____14823 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____14823)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___149_14828 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___149_14828.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___149_14828.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____14829 -> lopt  in
                           (log cfg
                              (fun uu____14835  ->
                                 let uu____14836 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____14836);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___150_14845 = cfg  in
                               {
                                 steps = (uu___150_14845.steps);
                                 tcenv = (uu___150_14845.tcenv);
                                 debug = (uu___150_14845.debug);
                                 delta_level = (uu___150_14845.delta_level);
                                 primitive_steps =
                                   (uu___150_14845.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___150_14845.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___150_14845.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Meta uu____14856)::uu____14857 ->
                    if (cfg.steps).weak
                    then
                      let uu____14864 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____14864
                    else
                      (let uu____14866 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____14866 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____14908  -> dummy :: env1) env)
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
                                          let uu____14945 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____14945)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___149_14950 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___149_14950.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___149_14950.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____14951 -> lopt  in
                           (log cfg
                              (fun uu____14957  ->
                                 let uu____14958 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____14958);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___150_14967 = cfg  in
                               {
                                 steps = (uu___150_14967.steps);
                                 tcenv = (uu___150_14967.tcenv);
                                 debug = (uu___150_14967.debug);
                                 delta_level = (uu___150_14967.delta_level);
                                 primitive_steps =
                                   (uu___150_14967.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___150_14967.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___150_14967.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Let uu____14978)::uu____14979 ->
                    if (cfg.steps).weak
                    then
                      let uu____14990 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____14990
                    else
                      (let uu____14992 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____14992 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____15034  -> dummy :: env1) env)
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
                                          let uu____15071 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____15071)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___149_15076 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___149_15076.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___149_15076.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____15077 -> lopt  in
                           (log cfg
                              (fun uu____15083  ->
                                 let uu____15084 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____15084);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___150_15093 = cfg  in
                               {
                                 steps = (uu___150_15093.steps);
                                 tcenv = (uu___150_15093.tcenv);
                                 debug = (uu___150_15093.debug);
                                 delta_level = (uu___150_15093.delta_level);
                                 primitive_steps =
                                   (uu___150_15093.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___150_15093.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___150_15093.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (App uu____15104)::uu____15105 ->
                    if (cfg.steps).weak
                    then
                      let uu____15116 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____15116
                    else
                      (let uu____15118 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____15118 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____15160  -> dummy :: env1) env)
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
                                          let uu____15197 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____15197)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___149_15202 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___149_15202.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___149_15202.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____15203 -> lopt  in
                           (log cfg
                              (fun uu____15209  ->
                                 let uu____15210 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____15210);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___150_15219 = cfg  in
                               {
                                 steps = (uu___150_15219.steps);
                                 tcenv = (uu___150_15219.tcenv);
                                 debug = (uu___150_15219.debug);
                                 delta_level = (uu___150_15219.delta_level);
                                 primitive_steps =
                                   (uu___150_15219.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___150_15219.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___150_15219.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Abs uu____15230)::uu____15231 ->
                    if (cfg.steps).weak
                    then
                      let uu____15246 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____15246
                    else
                      (let uu____15248 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____15248 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____15290  -> dummy :: env1) env)
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
                                          let uu____15327 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____15327)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___149_15332 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___149_15332.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___149_15332.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____15333 -> lopt  in
                           (log cfg
                              (fun uu____15339  ->
                                 let uu____15340 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____15340);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___150_15349 = cfg  in
                               {
                                 steps = (uu___150_15349.steps);
                                 tcenv = (uu___150_15349.tcenv);
                                 debug = (uu___150_15349.debug);
                                 delta_level = (uu___150_15349.delta_level);
                                 primitive_steps =
                                   (uu___150_15349.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___150_15349.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___150_15349.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | [] ->
                    if (cfg.steps).weak
                    then
                      let uu____15360 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____15360
                    else
                      (let uu____15362 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____15362 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____15404  -> dummy :: env1) env)
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
                                          let uu____15441 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____15441)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___149_15446 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___149_15446.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___149_15446.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____15447 -> lopt  in
                           (log cfg
                              (fun uu____15453  ->
                                 let uu____15454 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____15454);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___150_15463 = cfg  in
                               {
                                 steps = (uu___150_15463.steps);
                                 tcenv = (uu___150_15463.tcenv);
                                 debug = (uu___150_15463.debug);
                                 delta_level = (uu___150_15463.delta_level);
                                 primitive_steps =
                                   (uu___150_15463.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___150_15463.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___150_15463.normalize_pure_lets)
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
                      (fun uu____15512  ->
                         fun stack1  ->
                           match uu____15512 with
                           | (a,aq) ->
                               let uu____15524 =
                                 let uu____15525 =
                                   let uu____15532 =
                                     let uu____15533 =
                                       let uu____15564 =
                                         FStar_Util.mk_ref
                                           FStar_Pervasives_Native.None
                                          in
                                       (env, a, uu____15564, false)  in
                                     Clos uu____15533  in
                                   (uu____15532, aq,
                                     (t1.FStar_Syntax_Syntax.pos))
                                    in
                                 Arg uu____15525  in
                               uu____15524 :: stack1) args)
                  in
               (log cfg
                  (fun uu____15648  ->
                     let uu____15649 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args)
                        in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____15649);
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
                             ((let uu___151_15685 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___151_15685.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___151_15685.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos
                         in
                      rebuild cfg env stack t2
                  | uu____15686 ->
                      let uu____15691 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____15691)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort  in
                  let uu____15694 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] f
                     in
                  match uu____15694 with
                  | (closing,f1) ->
                      let f2 = norm cfg (dummy :: env) [] f1  in
                      let t2 =
                        let uu____15725 =
                          let uu____15726 =
                            let uu____15733 =
                              FStar_Syntax_Subst.close closing f2  in
                            ((let uu___152_15735 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___152_15735.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___152_15735.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____15733)
                             in
                          FStar_Syntax_Syntax.Tm_refine uu____15726  in
                        mk uu____15725 t1.FStar_Syntax_Syntax.pos  in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if (cfg.steps).weak
               then
                 let uu____15754 = closure_as_term cfg env t1  in
                 rebuild cfg env stack uu____15754
               else
                 (let uu____15756 = FStar_Syntax_Subst.open_comp bs c  in
                  match uu____15756 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____15764 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun uu____15788  -> dummy :: env1) env)
                           in
                        norm_comp cfg uu____15764 c1  in
                      let t2 =
                        let uu____15810 = norm_binders cfg env bs1  in
                        FStar_Syntax_Util.arrow uu____15810 c2  in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) when
               (cfg.steps).unascribe -> norm cfg env stack t11
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack with
                | (Match uu____15921)::uu____15922 ->
                    (log cfg
                       (fun uu____15933  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (Arg uu____15934)::uu____15935 ->
                    (log cfg
                       (fun uu____15946  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (App
                    (uu____15947,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_constant
                                     (FStar_Const.Const_reify );
                                   FStar_Syntax_Syntax.pos = uu____15948;
                                   FStar_Syntax_Syntax.vars = uu____15949;_},uu____15950,uu____15951))::uu____15952
                    ->
                    (log cfg
                       (fun uu____15961  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (MemoLazy uu____15962)::uu____15963 ->
                    (log cfg
                       (fun uu____15974  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | uu____15975 ->
                    (log cfg
                       (fun uu____15978  ->
                          FStar_Util.print_string "+++ Keeping ascription \n");
                     (let t12 = norm cfg env [] t11  in
                      log cfg
                        (fun uu____15982  ->
                           FStar_Util.print_string
                             "+++ Normalizing ascription \n");
                      (let tc1 =
                         match tc with
                         | FStar_Util.Inl t2 ->
                             let uu____15999 = norm cfg env [] t2  in
                             FStar_Util.Inl uu____15999
                         | FStar_Util.Inr c ->
                             let uu____16007 = norm_comp cfg env c  in
                             FStar_Util.Inr uu____16007
                          in
                       let tacopt1 =
                         FStar_Util.map_opt tacopt (norm cfg env [])  in
                       match stack with
                       | (Cfg cfg1)::stack1 ->
                           let t2 =
                             let uu____16020 =
                               let uu____16021 =
                                 let uu____16048 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____16048, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____16021
                                in
                             mk uu____16020 t1.FStar_Syntax_Syntax.pos  in
                           norm cfg1 env stack1 t2
                       | uu____16067 ->
                           let uu____16068 =
                             let uu____16069 =
                               let uu____16070 =
                                 let uu____16097 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____16097, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____16070
                                in
                             mk uu____16069 t1.FStar_Syntax_Syntax.pos  in
                           rebuild cfg env stack uu____16068))))
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
                         let uu____16207 =
                           FStar_Syntax_Subst.univ_var_opening
                             lb.FStar_Syntax_Syntax.lbunivs
                            in
                         match uu____16207 with
                         | (openings,lbunivs) ->
                             let cfg1 =
                               let uu___153_16227 = cfg  in
                               let uu____16228 =
                                 FStar_TypeChecker_Env.push_univ_vars
                                   cfg.tcenv lbunivs
                                  in
                               {
                                 steps = (uu___153_16227.steps);
                                 tcenv = uu____16228;
                                 debug = (uu___153_16227.debug);
                                 delta_level = (uu___153_16227.delta_level);
                                 primitive_steps =
                                   (uu___153_16227.primitive_steps);
                                 strong = (uu___153_16227.strong);
                                 memoize_lazy = (uu___153_16227.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___153_16227.normalize_pure_lets)
                               }  in
                             let norm1 t2 =
                               let uu____16233 =
                                 let uu____16234 =
                                   FStar_Syntax_Subst.subst openings t2  in
                                 norm cfg1 env [] uu____16234  in
                               FStar_Syntax_Subst.close_univ_vars lbunivs
                                 uu____16233
                                in
                             let lbtyp = norm1 lb.FStar_Syntax_Syntax.lbtyp
                                in
                             let lbdef = norm1 lb.FStar_Syntax_Syntax.lbdef
                                in
                             let uu___154_16237 = lb  in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___154_16237.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs = lbunivs;
                               FStar_Syntax_Syntax.lbtyp = lbtyp;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___154_16237.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = lbdef;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___154_16237.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___154_16237.FStar_Syntax_Syntax.lbpos)
                             }))
                  in
               let uu____16238 =
                 mk (FStar_Syntax_Syntax.Tm_let ((b, lbs1), lbody))
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack uu____16238
           | FStar_Syntax_Syntax.Tm_let
               ((uu____16249,{
                               FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                 uu____16250;
                               FStar_Syntax_Syntax.lbunivs = uu____16251;
                               FStar_Syntax_Syntax.lbtyp = uu____16252;
                               FStar_Syntax_Syntax.lbeff = uu____16253;
                               FStar_Syntax_Syntax.lbdef = uu____16254;
                               FStar_Syntax_Syntax.lbattrs = uu____16255;
                               FStar_Syntax_Syntax.lbpos = uu____16256;_}::uu____16257),uu____16258)
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff
                  in
               let uu____16298 =
                 (Prims.op_Negation (cfg.steps).no_delta_steps) &&
                   ((((cfg.steps).pure_subterms_within_computations &&
                        (FStar_Util.for_some
                           (FStar_Syntax_Util.is_fvar
                              FStar_Parser_Const.inline_let_attr)
                           lb.FStar_Syntax_Syntax.lbattrs))
                       ||
                       ((FStar_Syntax_Util.is_pure_effect n1) &&
                          (cfg.normalize_pure_lets ||
                             (FStar_Util.for_some
                                (FStar_Syntax_Util.is_fvar
                                   FStar_Parser_Const.inline_let_attr)
                                lb.FStar_Syntax_Syntax.lbattrs))))
                      ||
                      ((FStar_Syntax_Util.is_ghost_effect n1) &&
                         (Prims.op_Negation
                            (cfg.steps).pure_subterms_within_computations)))
                  in
               if uu____16298
               then
                 let binder =
                   let uu____16300 =
                     FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                   FStar_Syntax_Syntax.mk_binder uu____16300  in
                 let env1 =
                   let uu____16310 =
                     let uu____16317 =
                       let uu____16318 =
                         let uu____16349 =
                           FStar_Util.mk_ref FStar_Pervasives_Native.None  in
                         (env, (lb.FStar_Syntax_Syntax.lbdef), uu____16349,
                           false)
                          in
                       Clos uu____16318  in
                     ((FStar_Pervasives_Native.Some binder), uu____16317)  in
                   uu____16310 :: env  in
                 (log cfg
                    (fun uu____16442  ->
                       FStar_Util.print_string "+++ Reducing Tm_let\n");
                  norm cfg env1 stack body)
               else
                 if (cfg.steps).weak
                 then
                   (log cfg
                      (fun uu____16446  ->
                         FStar_Util.print_string "+++ Not touching Tm_let\n");
                    (let uu____16447 = closure_as_term cfg env t1  in
                     rebuild cfg env stack uu____16447))
                 else
                   (let uu____16449 =
                      let uu____16454 =
                        let uu____16455 =
                          let uu____16456 =
                            FStar_All.pipe_right
                              lb.FStar_Syntax_Syntax.lbname FStar_Util.left
                             in
                          FStar_All.pipe_right uu____16456
                            FStar_Syntax_Syntax.mk_binder
                           in
                        [uu____16455]  in
                      FStar_Syntax_Subst.open_term uu____16454 body  in
                    match uu____16449 with
                    | (bs,body1) ->
                        (log cfg
                           (fun uu____16465  ->
                              FStar_Util.print_string
                                "+++ Normalizing Tm_let -- type");
                         (let ty =
                            norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                          let lbname =
                            let x =
                              let uu____16473 = FStar_List.hd bs  in
                              FStar_Pervasives_Native.fst uu____16473  in
                            FStar_Util.Inl
                              (let uu___155_16483 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___155_16483.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___155_16483.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               })
                             in
                          log cfg
                            (fun uu____16486  ->
                               FStar_Util.print_string
                                 "+++ Normalizing Tm_let -- definiens\n");
                          (let lb1 =
                             let uu___156_16488 = lb  in
                             let uu____16489 =
                               norm cfg env [] lb.FStar_Syntax_Syntax.lbdef
                                in
                             {
                               FStar_Syntax_Syntax.lbname = lbname;
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___156_16488.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp = ty;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___156_16488.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = uu____16489;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___156_16488.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___156_16488.FStar_Syntax_Syntax.lbpos)
                             }  in
                           let env' =
                             FStar_All.pipe_right bs
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____16524  -> dummy :: env1) env)
                              in
                           let stack1 = (Cfg cfg) :: stack  in
                           let cfg1 =
                             let uu___157_16547 = cfg  in
                             {
                               steps = (uu___157_16547.steps);
                               tcenv = (uu___157_16547.tcenv);
                               debug = (uu___157_16547.debug);
                               delta_level = (uu___157_16547.delta_level);
                               primitive_steps =
                                 (uu___157_16547.primitive_steps);
                               strong = true;
                               memoize_lazy = (uu___157_16547.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___157_16547.normalize_pure_lets)
                             }  in
                           log cfg1
                             (fun uu____16550  ->
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
               let uu____16567 = FStar_Syntax_Subst.open_let_rec lbs body  in
               (match uu____16567 with
                | (lbs1,body1) ->
                    let lbs2 =
                      FStar_List.map
                        (fun lb  ->
                           let ty =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                           let lbname =
                             let uu____16603 =
                               let uu___158_16604 =
                                 FStar_Util.left
                                   lb.FStar_Syntax_Syntax.lbname
                                  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___158_16604.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___158_16604.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               }  in
                             FStar_Util.Inl uu____16603  in
                           let uu____16605 =
                             FStar_Syntax_Util.abs_formals
                               lb.FStar_Syntax_Syntax.lbdef
                              in
                           match uu____16605 with
                           | (xs,def_body,lopt) ->
                               let xs1 = norm_binders cfg env xs  in
                               let env1 =
                                 let uu____16631 =
                                   FStar_List.map (fun uu____16647  -> dummy)
                                     lbs1
                                    in
                                 let uu____16648 =
                                   let uu____16657 =
                                     FStar_List.map
                                       (fun uu____16677  -> dummy) xs1
                                      in
                                   FStar_List.append uu____16657 env  in
                                 FStar_List.append uu____16631 uu____16648
                                  in
                               let def_body1 = norm cfg env1 [] def_body  in
                               let lopt1 =
                                 match lopt with
                                 | FStar_Pervasives_Native.Some rc ->
                                     let uu____16701 =
                                       let uu___159_16702 = rc  in
                                       let uu____16703 =
                                         FStar_Util.map_opt
                                           rc.FStar_Syntax_Syntax.residual_typ
                                           (norm cfg env1 [])
                                          in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___159_16702.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           uu____16703;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___159_16702.FStar_Syntax_Syntax.residual_flags)
                                       }  in
                                     FStar_Pervasives_Native.Some uu____16701
                                 | uu____16710 -> lopt  in
                               let def =
                                 FStar_Syntax_Util.abs xs1 def_body1 lopt1
                                  in
                               let uu___160_16714 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname = lbname;
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___160_16714.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp = ty;
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___160_16714.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___160_16714.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___160_16714.FStar_Syntax_Syntax.lbpos)
                               }) lbs1
                       in
                    let env' =
                      let uu____16724 =
                        FStar_List.map (fun uu____16740  -> dummy) lbs2  in
                      FStar_List.append uu____16724 env  in
                    let body2 = norm cfg env' [] body1  in
                    let uu____16748 =
                      FStar_Syntax_Subst.close_let_rec lbs2 body2  in
                    (match uu____16748 with
                     | (lbs3,body3) ->
                         let t2 =
                           let uu___161_16764 = t1  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_let
                                  ((true, lbs3), body3));
                             FStar_Syntax_Syntax.pos =
                               (uu___161_16764.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___161_16764.FStar_Syntax_Syntax.vars)
                           }  in
                         rebuild cfg env stack t2))
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               Prims.op_Negation (cfg.steps).zeta ->
               let uu____16791 = closure_as_term cfg env t1  in
               rebuild cfg env stack uu____16791
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____16810 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____16886  ->
                        match uu____16886 with
                        | (rec_env,memos,i) ->
                            let bv =
                              let uu___162_17007 =
                                FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                                 in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___162_17007.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index = i;
                                FStar_Syntax_Syntax.sort =
                                  (uu___162_17007.FStar_Syntax_Syntax.sort)
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
               (match uu____16810 with
                | (rec_env,memos,uu____17220) ->
                    let uu____17273 =
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
                             let uu____17584 =
                               let uu____17591 =
                                 let uu____17592 =
                                   let uu____17623 =
                                     FStar_Util.mk_ref
                                       FStar_Pervasives_Native.None
                                      in
                                   (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                     uu____17623, false)
                                    in
                                 Clos uu____17592  in
                               (FStar_Pervasives_Native.None, uu____17591)
                                in
                             uu____17584 :: env1)
                        (FStar_Pervasives_Native.snd lbs) env
                       in
                    norm cfg body_env stack body)
           | FStar_Syntax_Syntax.Tm_meta (head1,m) ->
               (log cfg
                  (fun uu____17733  ->
                     let uu____17734 =
                       FStar_Syntax_Print.metadata_to_string m  in
                     FStar_Util.print1 ">> metadata = %s\n" uu____17734);
                (match m with
                 | FStar_Syntax_Syntax.Meta_monadic (m1,t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inl m1) t2
                 | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inr (m1, m')) t2
                 | FStar_Syntax_Syntax.Meta_quoted (qt,inf) ->
                     rebuild cfg env stack t1
                 | uu____17762 ->
                     if (cfg.steps).unmeta
                     then norm cfg env stack head1
                     else
                       (match stack with
                        | uu____17764::uu____17765 ->
                            (match m with
                             | FStar_Syntax_Syntax.Meta_labeled
                                 (l,r,uu____17770) ->
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
                             | uu____17793 -> norm cfg env stack head1)
                        | [] ->
                            let head2 = norm cfg env [] head1  in
                            let m1 =
                              match m with
                              | FStar_Syntax_Syntax.Meta_pattern args ->
                                  let uu____17807 =
                                    norm_pattern_args cfg env args  in
                                  FStar_Syntax_Syntax.Meta_pattern
                                    uu____17807
                              | uu____17818 -> m  in
                            let t2 =
                              mk (FStar_Syntax_Syntax.Tm_meta (head2, m1))
                                t1.FStar_Syntax_Syntax.pos
                               in
                            rebuild cfg env stack t2)))
           | FStar_Syntax_Syntax.Tm_delayed uu____17822 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               norm cfg env stack t2
           | FStar_Syntax_Syntax.Tm_uvar uu____17848 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               (match t2.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_uvar uu____17866 ->
                    if (cfg.steps).check_no_uvars
                    then
                      let uu____17883 =
                        let uu____17884 =
                          FStar_Range.string_of_range
                            t2.FStar_Syntax_Syntax.pos
                           in
                        let uu____17885 =
                          FStar_Syntax_Print.term_to_string t2  in
                        FStar_Util.format2
                          "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                          uu____17884 uu____17885
                         in
                      failwith uu____17883
                    else rebuild cfg env stack t2
                | uu____17887 -> norm cfg env stack t2))

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
                let uu____17897 = FStar_Syntax_Syntax.range_of_fv f  in
                FStar_TypeChecker_Env.set_range cfg.tcenv uu____17897  in
              let uu____17898 =
                FStar_TypeChecker_Env.lookup_definition_qninfo
                  cfg.delta_level
                  (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                  qninfo
                 in
              match uu____17898 with
              | FStar_Pervasives_Native.None  ->
                  (log cfg
                     (fun uu____17911  ->
                        FStar_Util.print "Tm_fvar case 2\n" []);
                   rebuild cfg env stack t0)
              | FStar_Pervasives_Native.Some (us,t) ->
                  (log cfg
                     (fun uu____17922  ->
                        let uu____17923 =
                          FStar_Syntax_Print.term_to_string t0  in
                        let uu____17924 = FStar_Syntax_Print.term_to_string t
                           in
                        FStar_Util.print2 ">>> Unfolded %s to %s\n"
                          uu____17923 uu____17924);
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
                      | (UnivArgs (us',uu____17937))::stack1 ->
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
                      | uu____17992 when (cfg.steps).erase_universes ->
                          norm cfg env stack t1
                      | uu____17995 ->
                          let uu____17998 =
                            let uu____17999 =
                              FStar_Syntax_Print.lid_to_string
                                (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                               in
                            FStar_Util.format1
                              "Impossible: missing universe instantiation on %s"
                              uu____17999
                             in
                          failwith uu____17998
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
                  let uu___163_18023 = cfg  in
                  let uu____18024 =
                    FStar_List.fold_right fstep_add_one new_steps cfg.steps
                     in
                  {
                    steps = uu____18024;
                    tcenv = (uu___163_18023.tcenv);
                    debug = (uu___163_18023.debug);
                    delta_level =
                      [FStar_TypeChecker_Env.Inlining;
                      FStar_TypeChecker_Env.Eager_unfolding_only];
                    primitive_steps = (uu___163_18023.primitive_steps);
                    strong = (uu___163_18023.strong);
                    memoize_lazy = (uu___163_18023.memoize_lazy);
                    normalize_pure_lets =
                      (uu___163_18023.normalize_pure_lets)
                  }
                else
                  (let uu___164_18026 = cfg  in
                   {
                     steps =
                       (let uu___165_18029 = cfg.steps  in
                        {
                          beta = (uu___165_18029.beta);
                          iota = (uu___165_18029.iota);
                          zeta = false;
                          weak = (uu___165_18029.weak);
                          hnf = (uu___165_18029.hnf);
                          primops = (uu___165_18029.primops);
                          no_delta_steps = (uu___165_18029.no_delta_steps);
                          unfold_until = (uu___165_18029.unfold_until);
                          unfold_only = (uu___165_18029.unfold_only);
                          unfold_attr = (uu___165_18029.unfold_attr);
                          unfold_tac = (uu___165_18029.unfold_tac);
                          pure_subterms_within_computations =
                            (uu___165_18029.pure_subterms_within_computations);
                          simplify = (uu___165_18029.simplify);
                          erase_universes = (uu___165_18029.erase_universes);
                          allow_unbound_universes =
                            (uu___165_18029.allow_unbound_universes);
                          reify_ = (uu___165_18029.reify_);
                          compress_uvars = (uu___165_18029.compress_uvars);
                          no_full_norm = (uu___165_18029.no_full_norm);
                          check_no_uvars = (uu___165_18029.check_no_uvars);
                          unmeta = (uu___165_18029.unmeta);
                          unascribe = (uu___165_18029.unascribe)
                        });
                     tcenv = (uu___164_18026.tcenv);
                     debug = (uu___164_18026.debug);
                     delta_level = (uu___164_18026.delta_level);
                     primitive_steps = (uu___164_18026.primitive_steps);
                     strong = (uu___164_18026.strong);
                     memoize_lazy = (uu___164_18026.memoize_lazy);
                     normalize_pure_lets =
                       (uu___164_18026.normalize_pure_lets)
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
                  (fun uu____18059  ->
                     let uu____18060 = FStar_Syntax_Print.tag_of_term head2
                        in
                     let uu____18061 =
                       FStar_Syntax_Print.term_to_string head2  in
                     FStar_Util.print2 "Reifying: (%s) %s\n" uu____18060
                       uu____18061);
                (let head3 = FStar_Syntax_Util.unmeta_safe head2  in
                 let uu____18063 =
                   let uu____18064 = FStar_Syntax_Subst.compress head3  in
                   uu____18064.FStar_Syntax_Syntax.n  in
                 match uu____18063 with
                 | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                     let ed =
                       let uu____18082 =
                         FStar_TypeChecker_Env.norm_eff_name cfg.tcenv m  in
                       FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                         uu____18082
                        in
                     let uu____18083 = ed.FStar_Syntax_Syntax.bind_repr  in
                     (match uu____18083 with
                      | (uu____18084,bind_repr) ->
                          (match lb.FStar_Syntax_Syntax.lbname with
                           | FStar_Util.Inr uu____18090 ->
                               failwith
                                 "Cannot reify a top-level let binding"
                           | FStar_Util.Inl x ->
                               let is_return e =
                                 let uu____18098 =
                                   let uu____18099 =
                                     FStar_Syntax_Subst.compress e  in
                                   uu____18099.FStar_Syntax_Syntax.n  in
                                 match uu____18098 with
                                 | FStar_Syntax_Syntax.Tm_meta
                                     (e1,FStar_Syntax_Syntax.Meta_monadic
                                      (uu____18105,uu____18106))
                                     ->
                                     let uu____18115 =
                                       let uu____18116 =
                                         FStar_Syntax_Subst.compress e1  in
                                       uu____18116.FStar_Syntax_Syntax.n  in
                                     (match uu____18115 with
                                      | FStar_Syntax_Syntax.Tm_meta
                                          (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                           (uu____18122,msrc,uu____18124))
                                          when
                                          FStar_Syntax_Util.is_pure_effect
                                            msrc
                                          ->
                                          let uu____18133 =
                                            FStar_Syntax_Subst.compress e2
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____18133
                                      | uu____18134 ->
                                          FStar_Pervasives_Native.None)
                                 | uu____18135 ->
                                     FStar_Pervasives_Native.None
                                  in
                               let uu____18136 =
                                 is_return lb.FStar_Syntax_Syntax.lbdef  in
                               (match uu____18136 with
                                | FStar_Pervasives_Native.Some e ->
                                    let lb1 =
                                      let uu___166_18141 = lb  in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          (uu___166_18141.FStar_Syntax_Syntax.lbname);
                                        FStar_Syntax_Syntax.lbunivs =
                                          (uu___166_18141.FStar_Syntax_Syntax.lbunivs);
                                        FStar_Syntax_Syntax.lbtyp =
                                          (uu___166_18141.FStar_Syntax_Syntax.lbtyp);
                                        FStar_Syntax_Syntax.lbeff =
                                          FStar_Parser_Const.effect_PURE_lid;
                                        FStar_Syntax_Syntax.lbdef = e;
                                        FStar_Syntax_Syntax.lbattrs =
                                          (uu___166_18141.FStar_Syntax_Syntax.lbattrs);
                                        FStar_Syntax_Syntax.lbpos =
                                          (uu___166_18141.FStar_Syntax_Syntax.lbpos)
                                      }  in
                                    let uu____18142 = FStar_List.tl stack  in
                                    let uu____18143 =
                                      let uu____18144 =
                                        let uu____18147 =
                                          let uu____18148 =
                                            let uu____18161 =
                                              FStar_Syntax_Util.mk_reify body
                                               in
                                            ((false, [lb1]), uu____18161)  in
                                          FStar_Syntax_Syntax.Tm_let
                                            uu____18148
                                           in
                                        FStar_Syntax_Syntax.mk uu____18147
                                         in
                                      uu____18144
                                        FStar_Pervasives_Native.None
                                        head3.FStar_Syntax_Syntax.pos
                                       in
                                    norm cfg env uu____18142 uu____18143
                                | FStar_Pervasives_Native.None  ->
                                    let uu____18177 =
                                      let uu____18178 = is_return body  in
                                      match uu____18178 with
                                      | FStar_Pervasives_Native.Some
                                          {
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_bvar y;
                                            FStar_Syntax_Syntax.pos =
                                              uu____18182;
                                            FStar_Syntax_Syntax.vars =
                                              uu____18183;_}
                                          -> FStar_Syntax_Syntax.bv_eq x y
                                      | uu____18188 -> false  in
                                    if uu____18177
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
                                         let uu____18211 =
                                           let uu____18214 =
                                             let uu____18215 =
                                               let uu____18232 =
                                                 let uu____18235 =
                                                   FStar_Syntax_Syntax.mk_binder
                                                     x
                                                    in
                                                 [uu____18235]  in
                                               (uu____18232, body1,
                                                 (FStar_Pervasives_Native.Some
                                                    body_rc))
                                                in
                                             FStar_Syntax_Syntax.Tm_abs
                                               uu____18215
                                              in
                                           FStar_Syntax_Syntax.mk uu____18214
                                            in
                                         uu____18211
                                           FStar_Pervasives_Native.None
                                           body1.FStar_Syntax_Syntax.pos
                                          in
                                       let close1 = closure_as_term cfg env
                                          in
                                       let bind_inst =
                                         let uu____18251 =
                                           let uu____18252 =
                                             FStar_Syntax_Subst.compress
                                               bind_repr
                                              in
                                           uu____18252.FStar_Syntax_Syntax.n
                                            in
                                         match uu____18251 with
                                         | FStar_Syntax_Syntax.Tm_uinst
                                             (bind1,uu____18258::uu____18259::[])
                                             ->
                                             let uu____18266 =
                                               let uu____18269 =
                                                 let uu____18270 =
                                                   let uu____18277 =
                                                     let uu____18280 =
                                                       let uu____18281 =
                                                         close1
                                                           lb.FStar_Syntax_Syntax.lbtyp
                                                          in
                                                       (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                         cfg.tcenv
                                                         uu____18281
                                                        in
                                                     let uu____18282 =
                                                       let uu____18285 =
                                                         let uu____18286 =
                                                           close1 t  in
                                                         (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                           cfg.tcenv
                                                           uu____18286
                                                          in
                                                       [uu____18285]  in
                                                     uu____18280 ::
                                                       uu____18282
                                                      in
                                                   (bind1, uu____18277)  in
                                                 FStar_Syntax_Syntax.Tm_uinst
                                                   uu____18270
                                                  in
                                               FStar_Syntax_Syntax.mk
                                                 uu____18269
                                                in
                                             uu____18266
                                               FStar_Pervasives_Native.None
                                               rng
                                         | uu____18294 ->
                                             failwith
                                               "NIY : Reification of indexed effects"
                                          in
                                       let maybe_range_arg =
                                         let uu____18300 =
                                           FStar_Util.for_some
                                             (FStar_Syntax_Util.attr_eq
                                                FStar_Syntax_Util.dm4f_bind_range_attr)
                                             ed.FStar_Syntax_Syntax.eff_attrs
                                            in
                                         if uu____18300
                                         then
                                           let uu____18303 =
                                             let uu____18304 =
                                               FStar_Syntax_Embeddings.embed_range
                                                 lb.FStar_Syntax_Syntax.lbpos
                                                 lb.FStar_Syntax_Syntax.lbpos
                                                in
                                             FStar_Syntax_Syntax.as_arg
                                               uu____18304
                                              in
                                           let uu____18305 =
                                             let uu____18308 =
                                               let uu____18309 =
                                                 FStar_Syntax_Embeddings.embed_range
                                                   body2.FStar_Syntax_Syntax.pos
                                                   body2.FStar_Syntax_Syntax.pos
                                                  in
                                               FStar_Syntax_Syntax.as_arg
                                                 uu____18309
                                                in
                                             [uu____18308]  in
                                           uu____18303 :: uu____18305
                                         else []  in
                                       let reified =
                                         let uu____18314 =
                                           let uu____18317 =
                                             let uu____18318 =
                                               let uu____18333 =
                                                 let uu____18336 =
                                                   let uu____18339 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       lb.FStar_Syntax_Syntax.lbtyp
                                                      in
                                                   let uu____18340 =
                                                     let uu____18343 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         t
                                                        in
                                                     [uu____18343]  in
                                                   uu____18339 :: uu____18340
                                                    in
                                                 let uu____18344 =
                                                   let uu____18347 =
                                                     let uu____18350 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         FStar_Syntax_Syntax.tun
                                                        in
                                                     let uu____18351 =
                                                       let uu____18354 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           head4
                                                          in
                                                       let uu____18355 =
                                                         let uu____18358 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             FStar_Syntax_Syntax.tun
                                                            in
                                                         let uu____18359 =
                                                           let uu____18362 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               body2
                                                              in
                                                           [uu____18362]  in
                                                         uu____18358 ::
                                                           uu____18359
                                                          in
                                                       uu____18354 ::
                                                         uu____18355
                                                        in
                                                     uu____18350 ::
                                                       uu____18351
                                                      in
                                                   FStar_List.append
                                                     maybe_range_arg
                                                     uu____18347
                                                    in
                                                 FStar_List.append
                                                   uu____18336 uu____18344
                                                  in
                                               (bind_inst, uu____18333)  in
                                             FStar_Syntax_Syntax.Tm_app
                                               uu____18318
                                              in
                                           FStar_Syntax_Syntax.mk uu____18317
                                            in
                                         uu____18314
                                           FStar_Pervasives_Native.None rng
                                          in
                                       log cfg
                                         (fun uu____18374  ->
                                            let uu____18375 =
                                              FStar_Syntax_Print.term_to_string
                                                head0
                                               in
                                            let uu____18376 =
                                              FStar_Syntax_Print.term_to_string
                                                reified
                                               in
                                            FStar_Util.print2
                                              "Reified (1) <%s> to %s\n"
                                              uu____18375 uu____18376);
                                       (let uu____18377 = FStar_List.tl stack
                                           in
                                        norm cfg env uu____18377 reified)))))
                 | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                     let ed =
                       let uu____18401 =
                         FStar_TypeChecker_Env.norm_eff_name cfg.tcenv m  in
                       FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                         uu____18401
                        in
                     let uu____18402 = ed.FStar_Syntax_Syntax.bind_repr  in
                     (match uu____18402 with
                      | (uu____18403,bind_repr) ->
                          let maybe_unfold_action head4 =
                            let maybe_extract_fv t1 =
                              let t2 =
                                let uu____18438 =
                                  let uu____18439 =
                                    FStar_Syntax_Subst.compress t1  in
                                  uu____18439.FStar_Syntax_Syntax.n  in
                                match uu____18438 with
                                | FStar_Syntax_Syntax.Tm_uinst
                                    (t2,uu____18445) -> t2
                                | uu____18450 -> head4  in
                              let uu____18451 =
                                let uu____18452 =
                                  FStar_Syntax_Subst.compress t2  in
                                uu____18452.FStar_Syntax_Syntax.n  in
                              match uu____18451 with
                              | FStar_Syntax_Syntax.Tm_fvar x ->
                                  FStar_Pervasives_Native.Some x
                              | uu____18458 -> FStar_Pervasives_Native.None
                               in
                            let uu____18459 = maybe_extract_fv head4  in
                            match uu____18459 with
                            | FStar_Pervasives_Native.Some x when
                                let uu____18469 =
                                  FStar_Syntax_Syntax.lid_of_fv x  in
                                FStar_TypeChecker_Env.is_action cfg.tcenv
                                  uu____18469
                                ->
                                let head5 = norm cfg env [] head4  in
                                let action_unfolded =
                                  let uu____18474 = maybe_extract_fv head5
                                     in
                                  match uu____18474 with
                                  | FStar_Pervasives_Native.Some uu____18479
                                      -> FStar_Pervasives_Native.Some true
                                  | uu____18480 ->
                                      FStar_Pervasives_Native.Some false
                                   in
                                (head5, action_unfolded)
                            | uu____18485 ->
                                (head4, FStar_Pervasives_Native.None)
                             in
                          ((let is_arg_impure uu____18500 =
                              match uu____18500 with
                              | (e,q) ->
                                  let uu____18507 =
                                    let uu____18508 =
                                      FStar_Syntax_Subst.compress e  in
                                    uu____18508.FStar_Syntax_Syntax.n  in
                                  (match uu____18507 with
                                   | FStar_Syntax_Syntax.Tm_meta
                                       (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                        (m1,m2,t'))
                                       ->
                                       Prims.op_Negation
                                         (FStar_Syntax_Util.is_pure_effect m1)
                                   | uu____18523 -> false)
                               in
                            let uu____18524 =
                              let uu____18525 =
                                let uu____18532 =
                                  FStar_Syntax_Syntax.as_arg head_app  in
                                uu____18532 :: args  in
                              FStar_Util.for_some is_arg_impure uu____18525
                               in
                            if uu____18524
                            then
                              let uu____18537 =
                                let uu____18538 =
                                  FStar_Syntax_Print.term_to_string head3  in
                                FStar_Util.format1
                                  "Incompability between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                  uu____18538
                                 in
                              failwith uu____18537
                            else ());
                           (let uu____18540 = maybe_unfold_action head_app
                               in
                            match uu____18540 with
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
                                   (fun uu____18581  ->
                                      let uu____18582 =
                                        FStar_Syntax_Print.term_to_string
                                          head0
                                         in
                                      let uu____18583 =
                                        FStar_Syntax_Print.term_to_string
                                          body1
                                         in
                                      FStar_Util.print2
                                        "Reified (2) <%s> to %s\n"
                                        uu____18582 uu____18583);
                                 (let uu____18584 = FStar_List.tl stack  in
                                  norm cfg env uu____18584 body1)))))
                 | FStar_Syntax_Syntax.Tm_meta
                     (e,FStar_Syntax_Syntax.Meta_monadic uu____18586) ->
                     do_reify_monadic fallback cfg env stack e m t
                 | FStar_Syntax_Syntax.Tm_meta
                     (e,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,t'))
                     ->
                     let lifted =
                       let uu____18610 = closure_as_term cfg env t'  in
                       reify_lift cfg e msrc mtgt uu____18610  in
                     (log cfg
                        (fun uu____18614  ->
                           let uu____18615 =
                             FStar_Syntax_Print.term_to_string lifted  in
                           FStar_Util.print1 "Reified lift to (2): %s\n"
                             uu____18615);
                      (let uu____18616 = FStar_List.tl stack  in
                       norm cfg env uu____18616 lifted))
                 | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                     let branches1 =
                       FStar_All.pipe_right branches
                         (FStar_List.map
                            (fun uu____18737  ->
                               match uu____18737 with
                               | (pat,wopt,tm) ->
                                   let uu____18785 =
                                     FStar_Syntax_Util.mk_reify tm  in
                                   (pat, wopt, uu____18785)))
                        in
                     let tm =
                       mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                         head3.FStar_Syntax_Syntax.pos
                        in
                     let uu____18817 = FStar_List.tl stack  in
                     norm cfg env uu____18817 tm
                 | uu____18818 -> fallback ())

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
              (fun uu____18832  ->
                 let uu____18833 = FStar_Ident.string_of_lid msrc  in
                 let uu____18834 = FStar_Ident.string_of_lid mtgt  in
                 let uu____18835 = FStar_Syntax_Print.term_to_string e  in
                 FStar_Util.print3 "Reifying lift %s -> %s: %s\n" uu____18833
                   uu____18834 uu____18835);
            if FStar_Syntax_Util.is_pure_effect msrc
            then
              (let ed =
                 let uu____18837 =
                   FStar_TypeChecker_Env.norm_eff_name cfg.tcenv mtgt  in
                 FStar_TypeChecker_Env.get_effect_decl env uu____18837  in
               let uu____18838 = ed.FStar_Syntax_Syntax.return_repr  in
               match uu____18838 with
               | (uu____18839,return_repr) ->
                   let return_inst =
                     let uu____18848 =
                       let uu____18849 =
                         FStar_Syntax_Subst.compress return_repr  in
                       uu____18849.FStar_Syntax_Syntax.n  in
                     match uu____18848 with
                     | FStar_Syntax_Syntax.Tm_uinst
                         (return_tm,uu____18855::[]) ->
                         let uu____18862 =
                           let uu____18865 =
                             let uu____18866 =
                               let uu____18873 =
                                 let uu____18876 =
                                   env.FStar_TypeChecker_Env.universe_of env
                                     t
                                    in
                                 [uu____18876]  in
                               (return_tm, uu____18873)  in
                             FStar_Syntax_Syntax.Tm_uinst uu____18866  in
                           FStar_Syntax_Syntax.mk uu____18865  in
                         uu____18862 FStar_Pervasives_Native.None
                           e.FStar_Syntax_Syntax.pos
                     | uu____18884 ->
                         failwith "NIY : Reification of indexed effects"
                      in
                   let uu____18887 =
                     let uu____18890 =
                       let uu____18891 =
                         let uu____18906 =
                           let uu____18909 = FStar_Syntax_Syntax.as_arg t  in
                           let uu____18910 =
                             let uu____18913 = FStar_Syntax_Syntax.as_arg e
                                in
                             [uu____18913]  in
                           uu____18909 :: uu____18910  in
                         (return_inst, uu____18906)  in
                       FStar_Syntax_Syntax.Tm_app uu____18891  in
                     FStar_Syntax_Syntax.mk uu____18890  in
                   uu____18887 FStar_Pervasives_Native.None
                     e.FStar_Syntax_Syntax.pos)
            else
              (let uu____18922 =
                 FStar_TypeChecker_Env.monad_leq env msrc mtgt  in
               match uu____18922 with
               | FStar_Pervasives_Native.None  ->
                   let uu____18925 =
                     FStar_Util.format2
                       "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                       (FStar_Ident.text_of_lid msrc)
                       (FStar_Ident.text_of_lid mtgt)
                      in
                   failwith uu____18925
               | FStar_Pervasives_Native.Some
                   { FStar_TypeChecker_Env.msource = uu____18926;
                     FStar_TypeChecker_Env.mtarget = uu____18927;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____18928;
                         FStar_TypeChecker_Env.mlift_term =
                           FStar_Pervasives_Native.None ;_};_}
                   ->
                   let uu____18943 =
                     FStar_Util.format2
                       "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
                       (FStar_Ident.text_of_lid msrc)
                       (FStar_Ident.text_of_lid mtgt)
                      in
                   failwith uu____18943
               | FStar_Pervasives_Native.Some
                   { FStar_TypeChecker_Env.msource = uu____18944;
                     FStar_TypeChecker_Env.mtarget = uu____18945;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____18946;
                         FStar_TypeChecker_Env.mlift_term =
                           FStar_Pervasives_Native.Some lift;_};_}
                   ->
                   let uu____18970 =
                     env.FStar_TypeChecker_Env.universe_of env t  in
                   let uu____18971 = FStar_Syntax_Util.mk_reify e  in
                   lift uu____18970 t FStar_Syntax_Syntax.tun uu____18971)

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
                (fun uu____19027  ->
                   match uu____19027 with
                   | (a,imp) ->
                       let uu____19038 = norm cfg env [] a  in
                       (uu____19038, imp))))

and (norm_comp :
  cfg -> env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp) =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        match comp.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total (t,uopt) ->
            let uu___167_19052 = comp  in
            let uu____19053 =
              let uu____19054 =
                let uu____19063 = norm cfg env [] t  in
                let uu____19064 =
                  FStar_Option.map (norm_universe cfg env) uopt  in
                (uu____19063, uu____19064)  in
              FStar_Syntax_Syntax.Total uu____19054  in
            {
              FStar_Syntax_Syntax.n = uu____19053;
              FStar_Syntax_Syntax.pos =
                (uu___167_19052.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___167_19052.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
            let uu___168_19079 = comp  in
            let uu____19080 =
              let uu____19081 =
                let uu____19090 = norm cfg env [] t  in
                let uu____19091 =
                  FStar_Option.map (norm_universe cfg env) uopt  in
                (uu____19090, uu____19091)  in
              FStar_Syntax_Syntax.GTotal uu____19081  in
            {
              FStar_Syntax_Syntax.n = uu____19080;
              FStar_Syntax_Syntax.pos =
                (uu___168_19079.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___168_19079.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let norm_args args =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____19143  ->
                      match uu____19143 with
                      | (a,i) ->
                          let uu____19154 = norm cfg env [] a  in
                          (uu____19154, i)))
               in
            let flags1 =
              FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                (FStar_List.map
                   (fun uu___88_19165  ->
                      match uu___88_19165 with
                      | FStar_Syntax_Syntax.DECREASES t ->
                          let uu____19169 = norm cfg env [] t  in
                          FStar_Syntax_Syntax.DECREASES uu____19169
                      | f -> f))
               in
            let uu___169_19173 = comp  in
            let uu____19174 =
              let uu____19175 =
                let uu___170_19176 = ct  in
                let uu____19177 =
                  FStar_List.map (norm_universe cfg env)
                    ct.FStar_Syntax_Syntax.comp_univs
                   in
                let uu____19178 =
                  norm cfg env [] ct.FStar_Syntax_Syntax.result_typ  in
                let uu____19181 =
                  norm_args ct.FStar_Syntax_Syntax.effect_args  in
                {
                  FStar_Syntax_Syntax.comp_univs = uu____19177;
                  FStar_Syntax_Syntax.effect_name =
                    (uu___170_19176.FStar_Syntax_Syntax.effect_name);
                  FStar_Syntax_Syntax.result_typ = uu____19178;
                  FStar_Syntax_Syntax.effect_args = uu____19181;
                  FStar_Syntax_Syntax.flags = flags1
                }  in
              FStar_Syntax_Syntax.Comp uu____19175  in
            {
              FStar_Syntax_Syntax.n = uu____19174;
              FStar_Syntax_Syntax.pos =
                (uu___169_19173.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___169_19173.FStar_Syntax_Syntax.vars)
            }

and (norm_binder :
  cfg -> env -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder) =
  fun cfg  ->
    fun env  ->
      fun uu____19192  ->
        match uu____19192 with
        | (x,imp) ->
            let uu____19195 =
              let uu___171_19196 = x  in
              let uu____19197 = norm cfg env [] x.FStar_Syntax_Syntax.sort
                 in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___171_19196.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___171_19196.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____19197
              }  in
            (uu____19195, imp)

and (norm_binders :
  cfg -> env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders) =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____19203 =
          FStar_List.fold_left
            (fun uu____19221  ->
               fun b  ->
                 match uu____19221 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b  in
                     ((b1 :: nbs'), (dummy :: env1))) ([], env) bs
           in
        match uu____19203 with | (nbs,uu____19261) -> FStar_List.rev nbs

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
            let uu____19277 =
              let uu___172_19278 = rc  in
              let uu____19279 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (norm cfg env [])
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___172_19278.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____19279;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___172_19278.FStar_Syntax_Syntax.residual_flags)
              }  in
            FStar_Pervasives_Native.Some uu____19277
        | uu____19286 -> lopt

and (rebuild :
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          log cfg
            (fun uu____19299  ->
               let uu____19300 = FStar_Syntax_Print.tag_of_term t  in
               let uu____19301 = FStar_Syntax_Print.term_to_string t  in
               let uu____19302 =
                 FStar_Util.string_of_int (FStar_List.length env)  in
               let uu____19309 =
                 let uu____19310 =
                   let uu____19313 = firstn (Prims.parse_int "4") stack  in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____19313
                    in
                 stack_to_string uu____19310  in
               FStar_Util.print4
                 ">>> %s\nRebuild %s with %s env elements and top of the stack %s \n"
                 uu____19300 uu____19301 uu____19302 uu____19309);
          (let t1 = maybe_simplify cfg env stack t  in
           match stack with
           | [] -> t1
           | (Debug (tm,time_then))::stack1 ->
               (if (cfg.debug).print_normalized
                then
                  (let time_now = FStar_Util.now ()  in
                   let uu____19344 =
                     let uu____19345 =
                       let uu____19346 =
                         FStar_Util.time_diff time_then time_now  in
                       FStar_Pervasives_Native.snd uu____19346  in
                     FStar_Util.string_of_int uu____19345  in
                   let uu____19351 = FStar_Syntax_Print.term_to_string tm  in
                   let uu____19352 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.print3 "Normalized (%s ms) %s\n\tto %s\n"
                     uu____19344 uu____19351 uu____19352)
                else ();
                rebuild cfg env stack1 t1)
           | (Cfg cfg1)::stack1 -> rebuild cfg1 env stack1 t1
           | (Meta (m,r))::stack1 ->
               let t2 = mk (FStar_Syntax_Syntax.Tm_meta (t1, m)) r  in
               rebuild cfg env stack1 t2
           | (MemoLazy r)::stack1 ->
               (set_memo cfg r (env, t1);
                log cfg
                  (fun uu____19406  ->
                     let uu____19407 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 "\tSet memo %s\n" uu____19407);
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
               let uu____19443 =
                 let uu___173_19444 = FStar_Syntax_Util.abs bs1 t1 lopt1  in
                 {
                   FStar_Syntax_Syntax.n =
                     (uu___173_19444.FStar_Syntax_Syntax.n);
                   FStar_Syntax_Syntax.pos = r;
                   FStar_Syntax_Syntax.vars =
                     (uu___173_19444.FStar_Syntax_Syntax.vars)
                 }  in
               rebuild cfg env stack1 uu____19443
           | (Arg (Univ uu____19445,uu____19446,uu____19447))::uu____19448 ->
               failwith "Impossible"
           | (Arg (Dummy ,uu____19451,uu____19452))::uu____19453 ->
               failwith "Impossible"
           | (UnivArgs (us,r))::stack1 ->
               let t2 = FStar_Syntax_Syntax.mk_Tm_uinst t1 us  in
               rebuild cfg env stack1 t2
           | (Arg (Clos (env_arg,tm,uu____19468,uu____19469),aq,r))::stack1
               when
               let uu____19519 = head_of t1  in
               FStar_Syntax_Util.is_fstar_tactics_by_tactic uu____19519 ->
               let t2 =
                 let uu____19523 =
                   let uu____19524 =
                     let uu____19525 = closure_as_term cfg env_arg tm  in
                     (uu____19525, aq)  in
                   FStar_Syntax_Syntax.extend_app t1 uu____19524  in
                 uu____19523 FStar_Pervasives_Native.None r  in
               rebuild cfg env stack1 t2
           | (Arg (Clos (env_arg,tm,m,uu____19531),aq,r))::stack1 ->
               (log cfg
                  (fun uu____19584  ->
                     let uu____19585 = FStar_Syntax_Print.term_to_string tm
                        in
                     FStar_Util.print1 "Rebuilding with arg %s\n" uu____19585);
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
                  (let uu____19595 = FStar_ST.op_Bang m  in
                   match uu____19595 with
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
                   | FStar_Pervasives_Native.Some (uu____19732,a) ->
                       let t2 =
                         FStar_Syntax_Syntax.extend_app t1 (a, aq)
                           FStar_Pervasives_Native.None r
                          in
                       rebuild cfg env_arg stack1 t2))
           | (App (env1,head1,aq,r))::stack' when should_reify cfg stack ->
               let t0 = t1  in
               let fallback msg uu____19779 =
                 log cfg
                   (fun uu____19783  ->
                      let uu____19784 = FStar_Syntax_Print.term_to_string t1
                         in
                      FStar_Util.print2 "Not reifying%s: %s\n" msg
                        uu____19784);
                 (let t2 =
                    FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                      FStar_Pervasives_Native.None r
                     in
                  rebuild cfg env1 stack' t2)
                  in
               let uu____19788 =
                 let uu____19789 = FStar_Syntax_Subst.compress t1  in
                 uu____19789.FStar_Syntax_Syntax.n  in
               (match uu____19788 with
                | FStar_Syntax_Syntax.Tm_meta
                    (t2,FStar_Syntax_Syntax.Meta_monadic (m,ty)) ->
                    do_reify_monadic (fallback " (1)") cfg env1 stack t2 m ty
                | FStar_Syntax_Syntax.Tm_meta
                    (t2,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,ty))
                    ->
                    let lifted =
                      let uu____19816 = closure_as_term cfg env1 ty  in
                      reify_lift cfg t2 msrc mtgt uu____19816  in
                    (log cfg
                       (fun uu____19820  ->
                          let uu____19821 =
                            FStar_Syntax_Print.term_to_string lifted  in
                          FStar_Util.print1 "Reified lift to (1): %s\n"
                            uu____19821);
                     (let uu____19822 = FStar_List.tl stack  in
                      norm cfg env1 uu____19822 lifted))
                | FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reflect uu____19823);
                       FStar_Syntax_Syntax.pos = uu____19824;
                       FStar_Syntax_Syntax.vars = uu____19825;_},(e,uu____19827)::[])
                    -> norm cfg env1 stack' e
                | uu____19856 -> fallback " (2)" ())
           | (App (env1,head1,aq,r))::stack1 ->
               let t2 =
                 FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                   FStar_Pervasives_Native.None r
                  in
               rebuild cfg env1 stack1 t2
           | (Match (env1,branches,r))::stack1 ->
               (log cfg
                  (fun uu____19876  ->
                     let uu____19877 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1
                       "Rebuilding with match, scrutinee is %s ...\n"
                       uu____19877);
                (let scrutinee = t1  in
                 let norm_and_rebuild_match uu____19882 =
                   log cfg
                     (fun uu____19887  ->
                        let uu____19888 =
                          FStar_Syntax_Print.term_to_string scrutinee  in
                        let uu____19889 =
                          let uu____19890 =
                            FStar_All.pipe_right branches
                              (FStar_List.map
                                 (fun uu____19907  ->
                                    match uu____19907 with
                                    | (p,uu____19917,uu____19918) ->
                                        FStar_Syntax_Print.pat_to_string p))
                             in
                          FStar_All.pipe_right uu____19890
                            (FStar_String.concat "\n\t")
                           in
                        FStar_Util.print2
                          "match is irreducible: scrutinee=%s\nbranches=%s\n"
                          uu____19888 uu____19889);
                   (let whnf = (cfg.steps).weak || (cfg.steps).hnf  in
                    let cfg_exclude_iota_zeta =
                      let new_delta =
                        FStar_All.pipe_right cfg.delta_level
                          (FStar_List.filter
                             (fun uu___89_19935  ->
                                match uu___89_19935 with
                                | FStar_TypeChecker_Env.Inlining  -> true
                                | FStar_TypeChecker_Env.Eager_unfolding_only 
                                    -> true
                                | uu____19936 -> false))
                         in
                      let uu___174_19937 = cfg  in
                      {
                        steps =
                          (let uu___175_19940 = cfg.steps  in
                           {
                             beta = (uu___175_19940.beta);
                             iota = (uu___175_19940.iota);
                             zeta = false;
                             weak = (uu___175_19940.weak);
                             hnf = (uu___175_19940.hnf);
                             primops = (uu___175_19940.primops);
                             no_delta_steps = (uu___175_19940.no_delta_steps);
                             unfold_until = (uu___175_19940.unfold_until);
                             unfold_only = (uu___175_19940.unfold_only);
                             unfold_attr = (uu___175_19940.unfold_attr);
                             unfold_tac = (uu___175_19940.unfold_tac);
                             pure_subterms_within_computations =
                               (uu___175_19940.pure_subterms_within_computations);
                             simplify = (uu___175_19940.simplify);
                             erase_universes =
                               (uu___175_19940.erase_universes);
                             allow_unbound_universes =
                               (uu___175_19940.allow_unbound_universes);
                             reify_ = (uu___175_19940.reify_);
                             compress_uvars = (uu___175_19940.compress_uvars);
                             no_full_norm = (uu___175_19940.no_full_norm);
                             check_no_uvars = (uu___175_19940.check_no_uvars);
                             unmeta = (uu___175_19940.unmeta);
                             unascribe = (uu___175_19940.unascribe)
                           });
                        tcenv = (uu___174_19937.tcenv);
                        debug = (uu___174_19937.debug);
                        delta_level = new_delta;
                        primitive_steps = (uu___174_19937.primitive_steps);
                        strong = true;
                        memoize_lazy = (uu___174_19937.memoize_lazy);
                        normalize_pure_lets =
                          (uu___174_19937.normalize_pure_lets)
                      }  in
                    let norm_or_whnf env2 t2 =
                      if whnf
                      then closure_as_term cfg_exclude_iota_zeta env2 t2
                      else norm cfg_exclude_iota_zeta env2 [] t2  in
                    let rec norm_pat env2 p =
                      match p.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_constant uu____19972 ->
                          (p, env2)
                      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                          let uu____19993 =
                            FStar_All.pipe_right pats
                              (FStar_List.fold_left
                                 (fun uu____20053  ->
                                    fun uu____20054  ->
                                      match (uu____20053, uu____20054) with
                                      | ((pats1,env3),(p1,b)) ->
                                          let uu____20145 = norm_pat env3 p1
                                             in
                                          (match uu____20145 with
                                           | (p2,env4) ->
                                               (((p2, b) :: pats1), env4)))
                                 ([], env2))
                             in
                          (match uu____19993 with
                           | (pats1,env3) ->
                               ((let uu___176_20227 = p  in
                                 {
                                   FStar_Syntax_Syntax.v =
                                     (FStar_Syntax_Syntax.Pat_cons
                                        (fv, (FStar_List.rev pats1)));
                                   FStar_Syntax_Syntax.p =
                                     (uu___176_20227.FStar_Syntax_Syntax.p)
                                 }), env3))
                      | FStar_Syntax_Syntax.Pat_var x ->
                          let x1 =
                            let uu___177_20246 = x  in
                            let uu____20247 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___177_20246.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___177_20246.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____20247
                            }  in
                          ((let uu___178_20261 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_var x1);
                              FStar_Syntax_Syntax.p =
                                (uu___178_20261.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_wild x ->
                          let x1 =
                            let uu___179_20272 = x  in
                            let uu____20273 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___179_20272.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___179_20272.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____20273
                            }  in
                          ((let uu___180_20287 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_wild x1);
                              FStar_Syntax_Syntax.p =
                                (uu___180_20287.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                          let x1 =
                            let uu___181_20303 = x  in
                            let uu____20304 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___181_20303.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___181_20303.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____20304
                            }  in
                          let t3 = norm_or_whnf env2 t2  in
                          ((let uu___182_20311 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_dot_term (x1, t3));
                              FStar_Syntax_Syntax.p =
                                (uu___182_20311.FStar_Syntax_Syntax.p)
                            }), env2)
                       in
                    let branches1 =
                      match env1 with
                      | [] when whnf -> branches
                      | uu____20321 ->
                          FStar_All.pipe_right branches
                            (FStar_List.map
                               (fun branch1  ->
                                  let uu____20335 =
                                    FStar_Syntax_Subst.open_branch branch1
                                     in
                                  match uu____20335 with
                                  | (p,wopt,e) ->
                                      let uu____20355 = norm_pat env1 p  in
                                      (match uu____20355 with
                                       | (p1,env2) ->
                                           let wopt1 =
                                             match wopt with
                                             | FStar_Pervasives_Native.None 
                                                 ->
                                                 FStar_Pervasives_Native.None
                                             | FStar_Pervasives_Native.Some w
                                                 ->
                                                 let uu____20380 =
                                                   norm_or_whnf env2 w  in
                                                 FStar_Pervasives_Native.Some
                                                   uu____20380
                                              in
                                           let e1 = norm_or_whnf env2 e  in
                                           FStar_Syntax_Util.branch
                                             (p1, wopt1, e1))))
                       in
                    let uu____20386 =
                      mk
                        (FStar_Syntax_Syntax.Tm_match (scrutinee, branches1))
                        r
                       in
                    rebuild cfg env1 stack1 uu____20386)
                    in
                 let rec is_cons head1 =
                   let uu____20391 =
                     let uu____20392 = FStar_Syntax_Subst.compress head1  in
                     uu____20392.FStar_Syntax_Syntax.n  in
                   match uu____20391 with
                   | FStar_Syntax_Syntax.Tm_uinst (h,uu____20396) ->
                       is_cons h
                   | FStar_Syntax_Syntax.Tm_constant uu____20401 -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____20402;
                         FStar_Syntax_Syntax.fv_delta = uu____20403;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Data_ctor );_}
                       -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____20404;
                         FStar_Syntax_Syntax.fv_delta = uu____20405;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Record_ctor uu____20406);_}
                       -> true
                   | uu____20413 -> false  in
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
                   let uu____20558 =
                     FStar_Syntax_Util.head_and_args scrutinee1  in
                   match uu____20558 with
                   | (head1,args) ->
                       (match p.FStar_Syntax_Syntax.v with
                        | FStar_Syntax_Syntax.Pat_var bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_wild bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_dot_term uu____20645 ->
                            FStar_Util.Inl []
                        | FStar_Syntax_Syntax.Pat_constant s ->
                            (match scrutinee1.FStar_Syntax_Syntax.n with
                             | FStar_Syntax_Syntax.Tm_constant s' when
                                 FStar_Const.eq_const s s' ->
                                 FStar_Util.Inl []
                             | uu____20684 ->
                                 let uu____20685 =
                                   let uu____20686 = is_cons head1  in
                                   Prims.op_Negation uu____20686  in
                                 FStar_Util.Inr uu____20685)
                        | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                            let uu____20711 =
                              let uu____20712 =
                                FStar_Syntax_Util.un_uinst head1  in
                              uu____20712.FStar_Syntax_Syntax.n  in
                            (match uu____20711 with
                             | FStar_Syntax_Syntax.Tm_fvar fv' when
                                 FStar_Syntax_Syntax.fv_eq fv fv' ->
                                 matches_args [] args arg_pats
                             | uu____20730 ->
                                 let uu____20731 =
                                   let uu____20732 = is_cons head1  in
                                   Prims.op_Negation uu____20732  in
                                 FStar_Util.Inr uu____20731))
                 
                 and matches_args out a p =
                   match (a, p) with
                   | ([],[]) -> FStar_Util.Inl out
                   | ((t2,uu____20801)::rest_a,(p1,uu____20804)::rest_p) ->
                       let uu____20848 = matches_pat t2 p1  in
                       (match uu____20848 with
                        | FStar_Util.Inl s ->
                            matches_args (FStar_List.append out s) rest_a
                              rest_p
                        | m -> m)
                   | uu____20897 -> FStar_Util.Inr false
                  in
                 let rec matches scrutinee1 p =
                   match p with
                   | [] -> norm_and_rebuild_match ()
                   | (p1,wopt,b)::rest ->
                       let uu____21003 = matches_pat scrutinee1 p1  in
                       (match uu____21003 with
                        | FStar_Util.Inr (false ) -> matches scrutinee1 rest
                        | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                        | FStar_Util.Inl s ->
                            (log cfg
                               (fun uu____21043  ->
                                  let uu____21044 =
                                    FStar_Syntax_Print.pat_to_string p1  in
                                  let uu____21045 =
                                    let uu____21046 =
                                      FStar_List.map
                                        (fun uu____21056  ->
                                           match uu____21056 with
                                           | (uu____21061,t2) ->
                                               FStar_Syntax_Print.term_to_string
                                                 t2) s
                                       in
                                    FStar_All.pipe_right uu____21046
                                      (FStar_String.concat "; ")
                                     in
                                  FStar_Util.print2
                                    "Matches pattern %s with subst = %s\n"
                                    uu____21044 uu____21045);
                             (let env2 =
                                FStar_List.fold_left
                                  (fun env2  ->
                                     fun uu____21092  ->
                                       match uu____21092 with
                                       | (bv,t2) ->
                                           let uu____21115 =
                                             let uu____21122 =
                                               let uu____21125 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   bv
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 uu____21125
                                                in
                                             let uu____21126 =
                                               let uu____21127 =
                                                 let uu____21158 =
                                                   FStar_Util.mk_ref
                                                     (FStar_Pervasives_Native.Some
                                                        ([], t2))
                                                    in
                                                 ([], t2, uu____21158, false)
                                                  in
                                               Clos uu____21127  in
                                             (uu____21122, uu____21126)  in
                                           uu____21115 :: env2) env1 s
                                 in
                              let uu____21275 = guard_when_clause wopt b rest
                                 in
                              norm cfg env2 stack1 uu____21275)))
                    in
                 if (cfg.steps).iota
                 then matches scrutinee branches
                 else norm_and_rebuild_match ())))

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
               (fun uu___90_21303  ->
                  match uu___90_21303 with
                  | UnfoldUntil k -> [FStar_TypeChecker_Env.Unfold k]
                  | Eager_unfolding  ->
                      [FStar_TypeChecker_Env.Eager_unfolding_only]
                  | Inlining  -> [FStar_TypeChecker_Env.Inlining]
                  | UnfoldTac  -> [FStar_TypeChecker_Env.UnfoldTac]
                  | uu____21307 -> []))
           in
        let d1 =
          match d with
          | [] -> [FStar_TypeChecker_Env.NoDelta]
          | uu____21313 -> d  in
        let uu____21316 = to_fsteps s  in
        let uu____21317 =
          let uu____21318 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Norm")  in
          let uu____21319 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Primops")  in
          let uu____21320 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "380")  in
          let uu____21321 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "NormDelayed")
             in
          let uu____21322 =
            FStar_TypeChecker_Env.debug e
              (FStar_Options.Other "print_normalized_terms")
             in
          {
            gen = uu____21318;
            primop = uu____21319;
            b380 = uu____21320;
            norm_delayed = uu____21321;
            print_normalized = uu____21322
          }  in
        let uu____21323 = add_steps built_in_primitive_steps psteps  in
        let uu____21326 =
          (FStar_Options.normalize_pure_terms_for_extraction ()) ||
            (let uu____21328 =
               FStar_All.pipe_right s
                 (FStar_List.contains PureSubtermsWithinComputations)
                in
             Prims.op_Negation uu____21328)
           in
        {
          steps = uu____21316;
          tcenv = e;
          debug = uu____21317;
          delta_level = d1;
          primitive_steps = uu____21323;
          strong = false;
          memoize_lazy = true;
          normalize_pure_lets = uu____21326
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
      fun t  -> let uu____21386 = config s e  in norm_comp uu____21386 [] t
  
let (normalize_universe :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun u  ->
      let uu____21399 = config [] env  in norm_universe uu____21399 [] u
  
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
        let uu____21417 = norm cfg [] [] t  in
        FStar_Syntax_Util.non_informative uu____21417  in
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____21424 -> c
      | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
          let uu___183_21443 = c  in
          {
            FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
            FStar_Syntax_Syntax.pos =
              (uu___183_21443.FStar_Syntax_Syntax.pos);
            FStar_Syntax_Syntax.vars =
              (uu___183_21443.FStar_Syntax_Syntax.vars)
          }
      | FStar_Syntax_Syntax.Comp ct ->
          let l =
            FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
              ct.FStar_Syntax_Syntax.effect_name
             in
          let uu____21450 =
            (FStar_Syntax_Util.is_ghost_effect l) &&
              (non_info ct.FStar_Syntax_Syntax.result_typ)
             in
          if uu____21450
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
                  let uu___184_21459 = ct  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___184_21459.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name = pure_eff;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___184_21459.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___184_21459.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags = flags1
                  }
              | FStar_Pervasives_Native.None  ->
                  let ct1 =
                    FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c
                     in
                  let uu___185_21461 = ct1  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___185_21461.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name =
                      FStar_Parser_Const.effect_PURE_lid;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___185_21461.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___185_21461.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags =
                      (uu___185_21461.FStar_Syntax_Syntax.flags)
                  }
               in
            let uu___186_21462 = c  in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
              FStar_Syntax_Syntax.pos =
                (uu___186_21462.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___186_21462.FStar_Syntax_Syntax.vars)
            }
          else c
      | uu____21464 -> c
  
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
        let uu____21476 = norm cfg [] [] t  in
        FStar_Syntax_Util.non_informative uu____21476  in
      let uu____21483 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ)
         in
      if uu____21483
      then
        match downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name
        with
        | FStar_Pervasives_Native.Some pure_eff ->
            FStar_Syntax_Syntax.mk_lcomp pure_eff
              lc.FStar_Syntax_Syntax.res_typ lc.FStar_Syntax_Syntax.cflags
              (fun uu____21487  ->
                 let uu____21488 = FStar_Syntax_Syntax.lcomp_comp lc  in
                 ghost_to_pure env uu____21488)
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
            ((let uu____21505 =
                let uu____21510 =
                  let uu____21511 = FStar_Util.message_of_exn e  in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____21511
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____21510)  in
              FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____21505);
             t)
         in
      FStar_Syntax_Print.term_to_string' env.FStar_TypeChecker_Env.dsenv t1
  
let (comp_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string) =
  fun env  ->
    fun c  ->
      let c1 =
        try
          let uu____21522 = config [AllowUnboundUniverses] env  in
          norm_comp uu____21522 [] c
        with
        | e ->
            ((let uu____21535 =
                let uu____21540 =
                  let uu____21541 = FStar_Util.message_of_exn e  in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____21541
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____21540)  in
              FStar_Errors.log_issue c.FStar_Syntax_Syntax.pos uu____21535);
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
                   let uu____21578 =
                     let uu____21579 =
                       let uu____21586 = FStar_Syntax_Util.mk_conj phi1 phi
                          in
                       (y, uu____21586)  in
                     FStar_Syntax_Syntax.Tm_refine uu____21579  in
                   mk uu____21578 t01.FStar_Syntax_Syntax.pos
               | uu____21591 -> t2)
          | uu____21592 -> t2  in
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
        let uu____21632 = FStar_Syntax_Util.arrow_formals_comp t_e  in
        match uu____21632 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____21661 ->
                 let uu____21668 = FStar_Syntax_Util.abs_formals e  in
                 (match uu____21668 with
                  | (actuals,uu____21678,uu____21679) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____21693 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders
                            in
                         match uu____21693 with
                         | (binders,args) ->
                             let uu____21710 =
                               FStar_Syntax_Syntax.mk_Tm_app e args
                                 FStar_Pervasives_Native.None
                                 e.FStar_Syntax_Syntax.pos
                                in
                             FStar_Syntax_Util.abs binders uu____21710
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
      | uu____21718 ->
          let uu____21719 = FStar_Syntax_Util.head_and_args t  in
          (match uu____21719 with
           | (head1,args) ->
               let uu____21756 =
                 let uu____21757 = FStar_Syntax_Subst.compress head1  in
                 uu____21757.FStar_Syntax_Syntax.n  in
               (match uu____21756 with
                | FStar_Syntax_Syntax.Tm_uvar (uu____21760,thead) ->
                    let uu____21786 = FStar_Syntax_Util.arrow_formals thead
                       in
                    (match uu____21786 with
                     | (formals,tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____21828 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___191_21836 = env  in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___191_21836.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___191_21836.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___191_21836.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___191_21836.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___191_21836.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___191_21836.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___191_21836.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___191_21836.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___191_21836.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___191_21836.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___191_21836.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___191_21836.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___191_21836.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___191_21836.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___191_21836.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___191_21836.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___191_21836.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___191_21836.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___191_21836.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___191_21836.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___191_21836.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___191_21836.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___191_21836.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___191_21836.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                     =
                                     (uu___191_21836.FStar_TypeChecker_Env.qtbl_name_and_index);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___191_21836.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth =
                                     (uu___191_21836.FStar_TypeChecker_Env.synth);
                                   FStar_TypeChecker_Env.splice =
                                     (uu___191_21836.FStar_TypeChecker_Env.splice);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___191_21836.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___191_21836.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___191_21836.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___191_21836.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.dep_graph =
                                     (uu___191_21836.FStar_TypeChecker_Env.dep_graph)
                                 }) t
                               in
                            match uu____21828 with
                            | (uu____21837,ty,uu____21839) ->
                                eta_expand_with_type env t ty))
                | uu____21840 ->
                    let uu____21841 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___192_21849 = env  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___192_21849.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___192_21849.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___192_21849.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___192_21849.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___192_21849.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___192_21849.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___192_21849.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___192_21849.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___192_21849.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___192_21849.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___192_21849.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___192_21849.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___192_21849.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___192_21849.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___192_21849.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___192_21849.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___192_21849.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___192_21849.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.failhard =
                             (uu___192_21849.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___192_21849.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___192_21849.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___192_21849.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___192_21849.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___192_21849.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qtbl_name_and_index =
                             (uu___192_21849.FStar_TypeChecker_Env.qtbl_name_and_index);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___192_21849.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth =
                             (uu___192_21849.FStar_TypeChecker_Env.synth);
                           FStar_TypeChecker_Env.splice =
                             (uu___192_21849.FStar_TypeChecker_Env.splice);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___192_21849.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___192_21849.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___192_21849.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___192_21849.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.dep_graph =
                             (uu___192_21849.FStar_TypeChecker_Env.dep_graph)
                         }) t
                       in
                    (match uu____21841 with
                     | (uu____21850,ty,uu____21852) ->
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
      let uu___193_21909 = x  in
      let uu____21910 = elim_delayed_subst_term x.FStar_Syntax_Syntax.sort
         in
      {
        FStar_Syntax_Syntax.ppname =
          (uu___193_21909.FStar_Syntax_Syntax.ppname);
        FStar_Syntax_Syntax.index =
          (uu___193_21909.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = uu____21910
      }  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____21913 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_bvar uu____21938 -> t1
    | FStar_Syntax_Syntax.Tm_name uu____21939 -> t1
    | FStar_Syntax_Syntax.Tm_fvar uu____21940 -> t1
    | FStar_Syntax_Syntax.Tm_uinst uu____21941 -> t1
    | FStar_Syntax_Syntax.Tm_constant uu____21948 -> t1
    | FStar_Syntax_Syntax.Tm_type uu____21949 -> t1
    | FStar_Syntax_Syntax.Tm_lazy uu____21950 -> t1
    | FStar_Syntax_Syntax.Tm_unknown  -> t1
    | FStar_Syntax_Syntax.Tm_abs (bs,t2,rc_opt) ->
        let elim_rc rc =
          let uu___194_21978 = rc  in
          let uu____21979 =
            FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
              elim_delayed_subst_term
             in
          let uu____21986 =
            elim_delayed_subst_cflags rc.FStar_Syntax_Syntax.residual_flags
             in
          {
            FStar_Syntax_Syntax.residual_effect =
              (uu___194_21978.FStar_Syntax_Syntax.residual_effect);
            FStar_Syntax_Syntax.residual_typ = uu____21979;
            FStar_Syntax_Syntax.residual_flags = uu____21986
          }  in
        let uu____21989 =
          let uu____21990 =
            let uu____22007 = elim_delayed_subst_binders bs  in
            let uu____22014 = elim_delayed_subst_term t2  in
            let uu____22015 = FStar_Util.map_opt rc_opt elim_rc  in
            (uu____22007, uu____22014, uu____22015)  in
          FStar_Syntax_Syntax.Tm_abs uu____21990  in
        mk1 uu____21989
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____22044 =
          let uu____22045 =
            let uu____22058 = elim_delayed_subst_binders bs  in
            let uu____22065 = elim_delayed_subst_comp c  in
            (uu____22058, uu____22065)  in
          FStar_Syntax_Syntax.Tm_arrow uu____22045  in
        mk1 uu____22044
    | FStar_Syntax_Syntax.Tm_refine (bv,phi) ->
        let uu____22078 =
          let uu____22079 =
            let uu____22086 = elim_bv bv  in
            let uu____22087 = elim_delayed_subst_term phi  in
            (uu____22086, uu____22087)  in
          FStar_Syntax_Syntax.Tm_refine uu____22079  in
        mk1 uu____22078
    | FStar_Syntax_Syntax.Tm_app (t2,args) ->
        let uu____22110 =
          let uu____22111 =
            let uu____22126 = elim_delayed_subst_term t2  in
            let uu____22127 = elim_delayed_subst_args args  in
            (uu____22126, uu____22127)  in
          FStar_Syntax_Syntax.Tm_app uu____22111  in
        mk1 uu____22110
    | FStar_Syntax_Syntax.Tm_match (t2,branches) ->
        let rec elim_pat p =
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_var x ->
              let uu___195_22191 = p  in
              let uu____22192 =
                let uu____22193 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_var uu____22193  in
              {
                FStar_Syntax_Syntax.v = uu____22192;
                FStar_Syntax_Syntax.p =
                  (uu___195_22191.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_wild x ->
              let uu___196_22195 = p  in
              let uu____22196 =
                let uu____22197 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_wild uu____22197  in
              {
                FStar_Syntax_Syntax.v = uu____22196;
                FStar_Syntax_Syntax.p =
                  (uu___196_22195.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
              let uu___197_22204 = p  in
              let uu____22205 =
                let uu____22206 =
                  let uu____22213 = elim_bv x  in
                  let uu____22214 = elim_delayed_subst_term t0  in
                  (uu____22213, uu____22214)  in
                FStar_Syntax_Syntax.Pat_dot_term uu____22206  in
              {
                FStar_Syntax_Syntax.v = uu____22205;
                FStar_Syntax_Syntax.p =
                  (uu___197_22204.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
              let uu___198_22233 = p  in
              let uu____22234 =
                let uu____22235 =
                  let uu____22248 =
                    FStar_List.map
                      (fun uu____22271  ->
                         match uu____22271 with
                         | (x,b) ->
                             let uu____22284 = elim_pat x  in
                             (uu____22284, b)) pats
                     in
                  (fv, uu____22248)  in
                FStar_Syntax_Syntax.Pat_cons uu____22235  in
              {
                FStar_Syntax_Syntax.v = uu____22234;
                FStar_Syntax_Syntax.p =
                  (uu___198_22233.FStar_Syntax_Syntax.p)
              }
          | uu____22297 -> p  in
        let elim_branch uu____22319 =
          match uu____22319 with
          | (pat,wopt,t3) ->
              let uu____22345 = elim_pat pat  in
              let uu____22348 =
                FStar_Util.map_opt wopt elim_delayed_subst_term  in
              let uu____22351 = elim_delayed_subst_term t3  in
              (uu____22345, uu____22348, uu____22351)
           in
        let uu____22356 =
          let uu____22357 =
            let uu____22380 = elim_delayed_subst_term t2  in
            let uu____22381 = FStar_List.map elim_branch branches  in
            (uu____22380, uu____22381)  in
          FStar_Syntax_Syntax.Tm_match uu____22357  in
        mk1 uu____22356
    | FStar_Syntax_Syntax.Tm_ascribed (t2,a,lopt) ->
        let elim_ascription uu____22490 =
          match uu____22490 with
          | (tc,topt) ->
              let uu____22525 =
                match tc with
                | FStar_Util.Inl t3 ->
                    let uu____22535 = elim_delayed_subst_term t3  in
                    FStar_Util.Inl uu____22535
                | FStar_Util.Inr c ->
                    let uu____22537 = elim_delayed_subst_comp c  in
                    FStar_Util.Inr uu____22537
                 in
              let uu____22538 =
                FStar_Util.map_opt topt elim_delayed_subst_term  in
              (uu____22525, uu____22538)
           in
        let uu____22547 =
          let uu____22548 =
            let uu____22575 = elim_delayed_subst_term t2  in
            let uu____22576 = elim_ascription a  in
            (uu____22575, uu____22576, lopt)  in
          FStar_Syntax_Syntax.Tm_ascribed uu____22548  in
        mk1 uu____22547
    | FStar_Syntax_Syntax.Tm_let (lbs,t2) ->
        let elim_lb lb =
          let uu___199_22621 = lb  in
          let uu____22622 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbtyp  in
          let uu____22625 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbdef  in
          {
            FStar_Syntax_Syntax.lbname =
              (uu___199_22621.FStar_Syntax_Syntax.lbname);
            FStar_Syntax_Syntax.lbunivs =
              (uu___199_22621.FStar_Syntax_Syntax.lbunivs);
            FStar_Syntax_Syntax.lbtyp = uu____22622;
            FStar_Syntax_Syntax.lbeff =
              (uu___199_22621.FStar_Syntax_Syntax.lbeff);
            FStar_Syntax_Syntax.lbdef = uu____22625;
            FStar_Syntax_Syntax.lbattrs =
              (uu___199_22621.FStar_Syntax_Syntax.lbattrs);
            FStar_Syntax_Syntax.lbpos =
              (uu___199_22621.FStar_Syntax_Syntax.lbpos)
          }  in
        let uu____22628 =
          let uu____22629 =
            let uu____22642 =
              let uu____22649 =
                FStar_List.map elim_lb (FStar_Pervasives_Native.snd lbs)  in
              ((FStar_Pervasives_Native.fst lbs), uu____22649)  in
            let uu____22658 = elim_delayed_subst_term t2  in
            (uu____22642, uu____22658)  in
          FStar_Syntax_Syntax.Tm_let uu____22629  in
        mk1 uu____22628
    | FStar_Syntax_Syntax.Tm_uvar (uv,t2) ->
        let uu____22691 =
          let uu____22692 =
            let uu____22709 = elim_delayed_subst_term t2  in
            (uv, uu____22709)  in
          FStar_Syntax_Syntax.Tm_uvar uu____22692  in
        mk1 uu____22691
    | FStar_Syntax_Syntax.Tm_meta (t2,md) ->
        let uu____22726 =
          let uu____22727 =
            let uu____22734 = elim_delayed_subst_term t2  in
            let uu____22735 = elim_delayed_subst_meta md  in
            (uu____22734, uu____22735)  in
          FStar_Syntax_Syntax.Tm_meta uu____22727  in
        mk1 uu____22726

and (elim_delayed_subst_cflags :
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun flags1  ->
    FStar_List.map
      (fun uu___91_22742  ->
         match uu___91_22742 with
         | FStar_Syntax_Syntax.DECREASES t ->
             let uu____22746 = elim_delayed_subst_term t  in
             FStar_Syntax_Syntax.DECREASES uu____22746
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
        let uu____22767 =
          let uu____22768 =
            let uu____22777 = elim_delayed_subst_term t  in
            (uu____22777, uopt)  in
          FStar_Syntax_Syntax.Total uu____22768  in
        mk1 uu____22767
    | FStar_Syntax_Syntax.GTotal (t,uopt) ->
        let uu____22790 =
          let uu____22791 =
            let uu____22800 = elim_delayed_subst_term t  in
            (uu____22800, uopt)  in
          FStar_Syntax_Syntax.GTotal uu____22791  in
        mk1 uu____22790
    | FStar_Syntax_Syntax.Comp ct ->
        let ct1 =
          let uu___200_22805 = ct  in
          let uu____22806 =
            elim_delayed_subst_term ct.FStar_Syntax_Syntax.result_typ  in
          let uu____22809 =
            elim_delayed_subst_args ct.FStar_Syntax_Syntax.effect_args  in
          let uu____22818 =
            elim_delayed_subst_cflags ct.FStar_Syntax_Syntax.flags  in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___200_22805.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___200_22805.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ = uu____22806;
            FStar_Syntax_Syntax.effect_args = uu____22809;
            FStar_Syntax_Syntax.flags = uu____22818
          }  in
        mk1 (FStar_Syntax_Syntax.Comp ct1)

and (elim_delayed_subst_meta :
  FStar_Syntax_Syntax.metadata -> FStar_Syntax_Syntax.metadata) =
  fun uu___92_22821  ->
    match uu___92_22821 with
    | FStar_Syntax_Syntax.Meta_pattern args ->
        let uu____22833 = FStar_List.map elim_delayed_subst_args args  in
        FStar_Syntax_Syntax.Meta_pattern uu____22833
    | FStar_Syntax_Syntax.Meta_monadic (m,t) ->
        let uu____22866 =
          let uu____22873 = elim_delayed_subst_term t  in (m, uu____22873)
           in
        FStar_Syntax_Syntax.Meta_monadic uu____22866
    | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,t) ->
        let uu____22881 =
          let uu____22890 = elim_delayed_subst_term t  in
          (m1, m2, uu____22890)  in
        FStar_Syntax_Syntax.Meta_monadic_lift uu____22881
    | m -> m

and (elim_delayed_subst_args :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun args  ->
    FStar_List.map
      (fun uu____22913  ->
         match uu____22913 with
         | (t,q) ->
             let uu____22924 = elim_delayed_subst_term t  in (uu____22924, q))
      args

and (elim_delayed_subst_binders :
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun bs  ->
    FStar_List.map
      (fun uu____22944  ->
         match uu____22944 with
         | (x,q) ->
             let uu____22955 =
               let uu___201_22956 = x  in
               let uu____22957 =
                 elim_delayed_subst_term x.FStar_Syntax_Syntax.sort  in
               {
                 FStar_Syntax_Syntax.ppname =
                   (uu___201_22956.FStar_Syntax_Syntax.ppname);
                 FStar_Syntax_Syntax.index =
                   (uu___201_22956.FStar_Syntax_Syntax.index);
                 FStar_Syntax_Syntax.sort = uu____22957
               }  in
             (uu____22955, q)) bs

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
            | (uu____23033,FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c))
                  FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
            | (uu____23039,FStar_Util.Inl t) ->
                let uu____23045 =
                  let uu____23048 =
                    let uu____23049 =
                      let uu____23062 = FStar_Syntax_Syntax.mk_Total t  in
                      (binders, uu____23062)  in
                    FStar_Syntax_Syntax.Tm_arrow uu____23049  in
                  FStar_Syntax_Syntax.mk uu____23048  in
                uu____23045 FStar_Pervasives_Native.None
                  t.FStar_Syntax_Syntax.pos
             in
          let uu____23066 = FStar_Syntax_Subst.open_univ_vars univ_names t
             in
          match uu____23066 with
          | (univ_names1,t1) ->
              let t2 = remove_uvar_solutions env t1  in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2  in
              let t4 = elim_delayed_subst_term t3  in
              let uu____23094 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t4))
                | uu____23149 ->
                    let uu____23150 =
                      let uu____23159 =
                        let uu____23160 = FStar_Syntax_Subst.compress t4  in
                        uu____23160.FStar_Syntax_Syntax.n  in
                      (uu____23159, tc)  in
                    (match uu____23150 with
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inr uu____23185) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inl uu____23222) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____23261,FStar_Util.Inl uu____23262) ->
                         ([], (FStar_Util.Inl t4))
                     | uu____23285 -> failwith "Impossible")
                 in
              (match uu____23094 with
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
          let uu____23390 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl t)  in
          match uu____23390 with
          | (univ_names1,binders1,tc) ->
              let uu____23448 = FStar_Util.left tc  in
              (univ_names1, binders1, uu____23448)
  
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
          let uu____23483 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr c)  in
          match uu____23483 with
          | (univ_names1,binders1,tc) ->
              let uu____23543 = FStar_Util.right tc  in
              (univ_names1, binders1, uu____23543)
  
let rec (elim_uvars :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt)
  =
  fun env  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univ_names,binders,typ,lids,lids') ->
          let uu____23576 = elim_uvars_aux_t env univ_names binders typ  in
          (match uu____23576 with
           | (univ_names1,binders1,typ1) ->
               let uu___202_23604 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___202_23604.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___202_23604.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___202_23604.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___202_23604.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
          let uu___203_23625 = s  in
          let uu____23626 =
            let uu____23627 =
              let uu____23636 = FStar_List.map (elim_uvars env) sigs  in
              (uu____23636, lids)  in
            FStar_Syntax_Syntax.Sig_bundle uu____23627  in
          {
            FStar_Syntax_Syntax.sigel = uu____23626;
            FStar_Syntax_Syntax.sigrng =
              (uu___203_23625.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___203_23625.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___203_23625.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___203_23625.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_datacon (lid,univ_names,typ,lident,i,lids) ->
          let uu____23653 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____23653 with
           | (univ_names1,uu____23671,typ1) ->
               let uu___204_23685 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___204_23685.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___204_23685.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___204_23685.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___204_23685.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univ_names,typ) ->
          let uu____23691 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____23691 with
           | (univ_names1,uu____23709,typ1) ->
               let uu___205_23723 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___205_23723.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___205_23723.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___205_23723.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___205_23723.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____23757 =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs
                       in
                    match uu____23757 with
                    | (opening,lbunivs) ->
                        let elim t =
                          let uu____23780 =
                            let uu____23781 =
                              let uu____23782 =
                                FStar_Syntax_Subst.subst opening t  in
                              remove_uvar_solutions env uu____23782  in
                            FStar_Syntax_Subst.close_univ_vars lbunivs
                              uu____23781
                             in
                          elim_delayed_subst_term uu____23780  in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp  in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef  in
                        let uu___206_23785 = lb  in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___206_23785.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___206_23785.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___206_23785.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___206_23785.FStar_Syntax_Syntax.lbpos)
                        }))
             in
          let uu___207_23786 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids));
            FStar_Syntax_Syntax.sigrng =
              (uu___207_23786.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___207_23786.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___207_23786.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___207_23786.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_main t ->
          let uu___208_23798 = s  in
          let uu____23799 =
            let uu____23800 = remove_uvar_solutions env t  in
            FStar_Syntax_Syntax.Sig_main uu____23800  in
          {
            FStar_Syntax_Syntax.sigel = uu____23799;
            FStar_Syntax_Syntax.sigrng =
              (uu___208_23798.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___208_23798.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___208_23798.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___208_23798.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_assume (l,us,t) ->
          let uu____23804 = elim_uvars_aux_t env us [] t  in
          (match uu____23804 with
           | (us1,uu____23822,t1) ->
               let uu___209_23836 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___209_23836.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___209_23836.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___209_23836.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___209_23836.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____23837 ->
          failwith "Impossible: should have been desugared already"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____23839 =
            elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature
             in
          (match uu____23839 with
           | (univs1,binders,signature) ->
               let uu____23867 =
                 let uu____23876 = FStar_Syntax_Subst.univ_var_opening univs1
                    in
                 match uu____23876 with
                 | (univs_opening,univs2) ->
                     let uu____23903 =
                       FStar_Syntax_Subst.univ_var_closing univs2  in
                     (univs_opening, uu____23903)
                  in
               (match uu____23867 with
                | (univs_opening,univs_closing) ->
                    let uu____23920 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders
                         in
                      let uu____23926 =
                        FStar_Syntax_Subst.opening_of_binders binders1  in
                      let uu____23927 =
                        FStar_Syntax_Subst.closing_of_binders binders1  in
                      (uu____23926, uu____23927)  in
                    (match uu____23920 with
                     | (b_opening,b_closing) ->
                         let n1 = FStar_List.length univs1  in
                         let n_binders = FStar_List.length binders  in
                         let elim_tscheme uu____23949 =
                           match uu____23949 with
                           | (us,t) ->
                               let n_us = FStar_List.length us  in
                               let uu____23967 =
                                 FStar_Syntax_Subst.open_univ_vars us t  in
                               (match uu____23967 with
                                | (us1,t1) ->
                                    let uu____23978 =
                                      let uu____23983 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      let uu____23990 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      (uu____23983, uu____23990)  in
                                    (match uu____23978 with
                                     | (b_opening1,b_closing1) ->
                                         let uu____24003 =
                                           let uu____24008 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us)
                                              in
                                           let uu____24017 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us)
                                              in
                                           (uu____24008, uu____24017)  in
                                         (match uu____24003 with
                                          | (univs_opening1,univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____24033 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1
                                                   in
                                                FStar_Syntax_Subst.subst
                                                  univs_opening1 uu____24033
                                                 in
                                              let uu____24034 =
                                                elim_uvars_aux_t env [] [] t2
                                                 in
                                              (match uu____24034 with
                                               | (uu____24055,uu____24056,t3)
                                                   ->
                                                   let t4 =
                                                     let uu____24071 =
                                                       let uu____24072 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3
                                                          in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
                                                         uu____24072
                                                        in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____24071
                                                      in
                                                   (us1, t4)))))
                            in
                         let elim_term t =
                           let uu____24077 =
                             elim_uvars_aux_t env univs1 binders t  in
                           match uu____24077 with
                           | (uu____24090,uu____24091,t1) -> t1  in
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
                             | uu____24151 ->
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_abs
                                      ((a.FStar_Syntax_Syntax.action_params),
                                        body, FStar_Pervasives_Native.None))
                                   FStar_Pervasives_Native.None
                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                              in
                           let destruct_action_body body =
                             let uu____24168 =
                               let uu____24169 =
                                 FStar_Syntax_Subst.compress body  in
                               uu____24169.FStar_Syntax_Syntax.n  in
                             match uu____24168 with
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,(FStar_Util.Inl
                                        typ,FStar_Pervasives_Native.None ),FStar_Pervasives_Native.None
                                  )
                                 -> (defn, typ)
                             | uu____24228 -> failwith "Impossible"  in
                           let destruct_action_typ_templ t =
                             let uu____24257 =
                               let uu____24258 =
                                 FStar_Syntax_Subst.compress t  in
                               uu____24258.FStar_Syntax_Syntax.n  in
                             match uu____24257 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (pars,body,uu____24279) ->
                                 let uu____24300 = destruct_action_body body
                                    in
                                 (match uu____24300 with
                                  | (defn,typ) -> (pars, defn, typ))
                             | uu____24345 ->
                                 let uu____24346 = destruct_action_body t  in
                                 (match uu____24346 with
                                  | (defn,typ) -> ([], defn, typ))
                              in
                           let uu____24395 =
                             elim_tscheme
                               ((a.FStar_Syntax_Syntax.action_univs),
                                 action_typ_templ)
                              in
                           match uu____24395 with
                           | (action_univs,t) ->
                               let uu____24404 = destruct_action_typ_templ t
                                  in
                               (match uu____24404 with
                                | (action_params,action_defn,action_typ) ->
                                    let a' =
                                      let uu___210_24445 = a  in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___210_24445.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___210_24445.FStar_Syntax_Syntax.action_unqualified_name);
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
                           let uu___211_24447 = ed  in
                           let uu____24448 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ret_wp  in
                           let uu____24449 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_wp  in
                           let uu____24450 =
                             elim_tscheme ed.FStar_Syntax_Syntax.if_then_else
                              in
                           let uu____24451 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ite_wp  in
                           let uu____24452 =
                             elim_tscheme ed.FStar_Syntax_Syntax.stronger  in
                           let uu____24453 =
                             elim_tscheme ed.FStar_Syntax_Syntax.close_wp  in
                           let uu____24454 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assert_p  in
                           let uu____24455 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assume_p  in
                           let uu____24456 =
                             elim_tscheme ed.FStar_Syntax_Syntax.null_wp  in
                           let uu____24457 =
                             elim_tscheme ed.FStar_Syntax_Syntax.trivial  in
                           let uu____24458 =
                             elim_term ed.FStar_Syntax_Syntax.repr  in
                           let uu____24459 =
                             elim_tscheme ed.FStar_Syntax_Syntax.return_repr
                              in
                           let uu____24460 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_repr
                              in
                           let uu____24461 =
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions
                              in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___211_24447.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___211_24447.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs = univs1;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp = uu____24448;
                             FStar_Syntax_Syntax.bind_wp = uu____24449;
                             FStar_Syntax_Syntax.if_then_else = uu____24450;
                             FStar_Syntax_Syntax.ite_wp = uu____24451;
                             FStar_Syntax_Syntax.stronger = uu____24452;
                             FStar_Syntax_Syntax.close_wp = uu____24453;
                             FStar_Syntax_Syntax.assert_p = uu____24454;
                             FStar_Syntax_Syntax.assume_p = uu____24455;
                             FStar_Syntax_Syntax.null_wp = uu____24456;
                             FStar_Syntax_Syntax.trivial = uu____24457;
                             FStar_Syntax_Syntax.repr = uu____24458;
                             FStar_Syntax_Syntax.return_repr = uu____24459;
                             FStar_Syntax_Syntax.bind_repr = uu____24460;
                             FStar_Syntax_Syntax.actions = uu____24461;
                             FStar_Syntax_Syntax.eff_attrs =
                               (uu___211_24447.FStar_Syntax_Syntax.eff_attrs)
                           }  in
                         let uu___212_24464 = s  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___212_24464.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___212_24464.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___212_24464.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___212_24464.FStar_Syntax_Syntax.sigattrs)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___93_24481 =
            match uu___93_24481 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (us,t) ->
                let uu____24508 = elim_uvars_aux_t env us [] t  in
                (match uu____24508 with
                 | (us1,uu____24532,t1) ->
                     FStar_Pervasives_Native.Some (us1, t1))
             in
          let sub_eff1 =
            let uu___213_24551 = sub_eff  in
            let uu____24552 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp  in
            let uu____24555 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift  in
            {
              FStar_Syntax_Syntax.source =
                (uu___213_24551.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___213_24551.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____24552;
              FStar_Syntax_Syntax.lift = uu____24555
            }  in
          let uu___214_24558 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___214_24558.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___214_24558.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___214_24558.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___214_24558.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,univ_names,binders,comp,flags1) ->
          let uu____24568 = elim_uvars_aux_c env univ_names binders comp  in
          (match uu____24568 with
           | (univ_names1,binders1,comp1) ->
               let uu___215_24602 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___215_24602.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___215_24602.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___215_24602.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___215_24602.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____24613 -> s
      | FStar_Syntax_Syntax.Sig_splice uu____24614 -> s
  
let (erase_universes :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  -> normalize [EraseUniverses; AllowUnboundUniverses] env t
  