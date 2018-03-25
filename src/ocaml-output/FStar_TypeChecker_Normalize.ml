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
      fun uu___77_180  ->
        match uu___77_180 with
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
      let add_opt x uu___78_1038 =
        match uu___78_1038 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.Some [x]
        | FStar_Pervasives_Native.Some xs ->
            FStar_Pervasives_Native.Some (x :: xs)
         in
      match s with
      | Beta  ->
          let uu___96_1058 = fs  in
          {
            beta = true;
            iota = (uu___96_1058.iota);
            zeta = (uu___96_1058.zeta);
            weak = (uu___96_1058.weak);
            hnf = (uu___96_1058.hnf);
            primops = (uu___96_1058.primops);
            no_delta_steps = (uu___96_1058.no_delta_steps);
            unfold_until = (uu___96_1058.unfold_until);
            unfold_only = (uu___96_1058.unfold_only);
            unfold_attr = (uu___96_1058.unfold_attr);
            unfold_tac = (uu___96_1058.unfold_tac);
            pure_subterms_within_computations =
              (uu___96_1058.pure_subterms_within_computations);
            simplify = (uu___96_1058.simplify);
            erase_universes = (uu___96_1058.erase_universes);
            allow_unbound_universes = (uu___96_1058.allow_unbound_universes);
            reify_ = (uu___96_1058.reify_);
            compress_uvars = (uu___96_1058.compress_uvars);
            no_full_norm = (uu___96_1058.no_full_norm);
            check_no_uvars = (uu___96_1058.check_no_uvars);
            unmeta = (uu___96_1058.unmeta);
            unascribe = (uu___96_1058.unascribe)
          }
      | Iota  ->
          let uu___97_1059 = fs  in
          {
            beta = (uu___97_1059.beta);
            iota = true;
            zeta = (uu___97_1059.zeta);
            weak = (uu___97_1059.weak);
            hnf = (uu___97_1059.hnf);
            primops = (uu___97_1059.primops);
            no_delta_steps = (uu___97_1059.no_delta_steps);
            unfold_until = (uu___97_1059.unfold_until);
            unfold_only = (uu___97_1059.unfold_only);
            unfold_attr = (uu___97_1059.unfold_attr);
            unfold_tac = (uu___97_1059.unfold_tac);
            pure_subterms_within_computations =
              (uu___97_1059.pure_subterms_within_computations);
            simplify = (uu___97_1059.simplify);
            erase_universes = (uu___97_1059.erase_universes);
            allow_unbound_universes = (uu___97_1059.allow_unbound_universes);
            reify_ = (uu___97_1059.reify_);
            compress_uvars = (uu___97_1059.compress_uvars);
            no_full_norm = (uu___97_1059.no_full_norm);
            check_no_uvars = (uu___97_1059.check_no_uvars);
            unmeta = (uu___97_1059.unmeta);
            unascribe = (uu___97_1059.unascribe)
          }
      | Zeta  ->
          let uu___98_1060 = fs  in
          {
            beta = (uu___98_1060.beta);
            iota = (uu___98_1060.iota);
            zeta = true;
            weak = (uu___98_1060.weak);
            hnf = (uu___98_1060.hnf);
            primops = (uu___98_1060.primops);
            no_delta_steps = (uu___98_1060.no_delta_steps);
            unfold_until = (uu___98_1060.unfold_until);
            unfold_only = (uu___98_1060.unfold_only);
            unfold_attr = (uu___98_1060.unfold_attr);
            unfold_tac = (uu___98_1060.unfold_tac);
            pure_subterms_within_computations =
              (uu___98_1060.pure_subterms_within_computations);
            simplify = (uu___98_1060.simplify);
            erase_universes = (uu___98_1060.erase_universes);
            allow_unbound_universes = (uu___98_1060.allow_unbound_universes);
            reify_ = (uu___98_1060.reify_);
            compress_uvars = (uu___98_1060.compress_uvars);
            no_full_norm = (uu___98_1060.no_full_norm);
            check_no_uvars = (uu___98_1060.check_no_uvars);
            unmeta = (uu___98_1060.unmeta);
            unascribe = (uu___98_1060.unascribe)
          }
      | Exclude (Beta ) ->
          let uu___99_1061 = fs  in
          {
            beta = false;
            iota = (uu___99_1061.iota);
            zeta = (uu___99_1061.zeta);
            weak = (uu___99_1061.weak);
            hnf = (uu___99_1061.hnf);
            primops = (uu___99_1061.primops);
            no_delta_steps = (uu___99_1061.no_delta_steps);
            unfold_until = (uu___99_1061.unfold_until);
            unfold_only = (uu___99_1061.unfold_only);
            unfold_attr = (uu___99_1061.unfold_attr);
            unfold_tac = (uu___99_1061.unfold_tac);
            pure_subterms_within_computations =
              (uu___99_1061.pure_subterms_within_computations);
            simplify = (uu___99_1061.simplify);
            erase_universes = (uu___99_1061.erase_universes);
            allow_unbound_universes = (uu___99_1061.allow_unbound_universes);
            reify_ = (uu___99_1061.reify_);
            compress_uvars = (uu___99_1061.compress_uvars);
            no_full_norm = (uu___99_1061.no_full_norm);
            check_no_uvars = (uu___99_1061.check_no_uvars);
            unmeta = (uu___99_1061.unmeta);
            unascribe = (uu___99_1061.unascribe)
          }
      | Exclude (Iota ) ->
          let uu___100_1062 = fs  in
          {
            beta = (uu___100_1062.beta);
            iota = false;
            zeta = (uu___100_1062.zeta);
            weak = (uu___100_1062.weak);
            hnf = (uu___100_1062.hnf);
            primops = (uu___100_1062.primops);
            no_delta_steps = (uu___100_1062.no_delta_steps);
            unfold_until = (uu___100_1062.unfold_until);
            unfold_only = (uu___100_1062.unfold_only);
            unfold_attr = (uu___100_1062.unfold_attr);
            unfold_tac = (uu___100_1062.unfold_tac);
            pure_subterms_within_computations =
              (uu___100_1062.pure_subterms_within_computations);
            simplify = (uu___100_1062.simplify);
            erase_universes = (uu___100_1062.erase_universes);
            allow_unbound_universes = (uu___100_1062.allow_unbound_universes);
            reify_ = (uu___100_1062.reify_);
            compress_uvars = (uu___100_1062.compress_uvars);
            no_full_norm = (uu___100_1062.no_full_norm);
            check_no_uvars = (uu___100_1062.check_no_uvars);
            unmeta = (uu___100_1062.unmeta);
            unascribe = (uu___100_1062.unascribe)
          }
      | Exclude (Zeta ) ->
          let uu___101_1063 = fs  in
          {
            beta = (uu___101_1063.beta);
            iota = (uu___101_1063.iota);
            zeta = false;
            weak = (uu___101_1063.weak);
            hnf = (uu___101_1063.hnf);
            primops = (uu___101_1063.primops);
            no_delta_steps = (uu___101_1063.no_delta_steps);
            unfold_until = (uu___101_1063.unfold_until);
            unfold_only = (uu___101_1063.unfold_only);
            unfold_attr = (uu___101_1063.unfold_attr);
            unfold_tac = (uu___101_1063.unfold_tac);
            pure_subterms_within_computations =
              (uu___101_1063.pure_subterms_within_computations);
            simplify = (uu___101_1063.simplify);
            erase_universes = (uu___101_1063.erase_universes);
            allow_unbound_universes = (uu___101_1063.allow_unbound_universes);
            reify_ = (uu___101_1063.reify_);
            compress_uvars = (uu___101_1063.compress_uvars);
            no_full_norm = (uu___101_1063.no_full_norm);
            check_no_uvars = (uu___101_1063.check_no_uvars);
            unmeta = (uu___101_1063.unmeta);
            unascribe = (uu___101_1063.unascribe)
          }
      | Exclude uu____1064 -> failwith "Bad exclude"
      | Weak  ->
          let uu___102_1065 = fs  in
          {
            beta = (uu___102_1065.beta);
            iota = (uu___102_1065.iota);
            zeta = (uu___102_1065.zeta);
            weak = true;
            hnf = (uu___102_1065.hnf);
            primops = (uu___102_1065.primops);
            no_delta_steps = (uu___102_1065.no_delta_steps);
            unfold_until = (uu___102_1065.unfold_until);
            unfold_only = (uu___102_1065.unfold_only);
            unfold_attr = (uu___102_1065.unfold_attr);
            unfold_tac = (uu___102_1065.unfold_tac);
            pure_subterms_within_computations =
              (uu___102_1065.pure_subterms_within_computations);
            simplify = (uu___102_1065.simplify);
            erase_universes = (uu___102_1065.erase_universes);
            allow_unbound_universes = (uu___102_1065.allow_unbound_universes);
            reify_ = (uu___102_1065.reify_);
            compress_uvars = (uu___102_1065.compress_uvars);
            no_full_norm = (uu___102_1065.no_full_norm);
            check_no_uvars = (uu___102_1065.check_no_uvars);
            unmeta = (uu___102_1065.unmeta);
            unascribe = (uu___102_1065.unascribe)
          }
      | HNF  ->
          let uu___103_1066 = fs  in
          {
            beta = (uu___103_1066.beta);
            iota = (uu___103_1066.iota);
            zeta = (uu___103_1066.zeta);
            weak = (uu___103_1066.weak);
            hnf = true;
            primops = (uu___103_1066.primops);
            no_delta_steps = (uu___103_1066.no_delta_steps);
            unfold_until = (uu___103_1066.unfold_until);
            unfold_only = (uu___103_1066.unfold_only);
            unfold_attr = (uu___103_1066.unfold_attr);
            unfold_tac = (uu___103_1066.unfold_tac);
            pure_subterms_within_computations =
              (uu___103_1066.pure_subterms_within_computations);
            simplify = (uu___103_1066.simplify);
            erase_universes = (uu___103_1066.erase_universes);
            allow_unbound_universes = (uu___103_1066.allow_unbound_universes);
            reify_ = (uu___103_1066.reify_);
            compress_uvars = (uu___103_1066.compress_uvars);
            no_full_norm = (uu___103_1066.no_full_norm);
            check_no_uvars = (uu___103_1066.check_no_uvars);
            unmeta = (uu___103_1066.unmeta);
            unascribe = (uu___103_1066.unascribe)
          }
      | Primops  ->
          let uu___104_1067 = fs  in
          {
            beta = (uu___104_1067.beta);
            iota = (uu___104_1067.iota);
            zeta = (uu___104_1067.zeta);
            weak = (uu___104_1067.weak);
            hnf = (uu___104_1067.hnf);
            primops = true;
            no_delta_steps = (uu___104_1067.no_delta_steps);
            unfold_until = (uu___104_1067.unfold_until);
            unfold_only = (uu___104_1067.unfold_only);
            unfold_attr = (uu___104_1067.unfold_attr);
            unfold_tac = (uu___104_1067.unfold_tac);
            pure_subterms_within_computations =
              (uu___104_1067.pure_subterms_within_computations);
            simplify = (uu___104_1067.simplify);
            erase_universes = (uu___104_1067.erase_universes);
            allow_unbound_universes = (uu___104_1067.allow_unbound_universes);
            reify_ = (uu___104_1067.reify_);
            compress_uvars = (uu___104_1067.compress_uvars);
            no_full_norm = (uu___104_1067.no_full_norm);
            check_no_uvars = (uu___104_1067.check_no_uvars);
            unmeta = (uu___104_1067.unmeta);
            unascribe = (uu___104_1067.unascribe)
          }
      | Eager_unfolding  -> fs
      | Inlining  -> fs
      | NoDeltaSteps  ->
          let uu___105_1068 = fs  in
          {
            beta = (uu___105_1068.beta);
            iota = (uu___105_1068.iota);
            zeta = (uu___105_1068.zeta);
            weak = (uu___105_1068.weak);
            hnf = (uu___105_1068.hnf);
            primops = (uu___105_1068.primops);
            no_delta_steps = true;
            unfold_until = (uu___105_1068.unfold_until);
            unfold_only = (uu___105_1068.unfold_only);
            unfold_attr = (uu___105_1068.unfold_attr);
            unfold_tac = (uu___105_1068.unfold_tac);
            pure_subterms_within_computations =
              (uu___105_1068.pure_subterms_within_computations);
            simplify = (uu___105_1068.simplify);
            erase_universes = (uu___105_1068.erase_universes);
            allow_unbound_universes = (uu___105_1068.allow_unbound_universes);
            reify_ = (uu___105_1068.reify_);
            compress_uvars = (uu___105_1068.compress_uvars);
            no_full_norm = (uu___105_1068.no_full_norm);
            check_no_uvars = (uu___105_1068.check_no_uvars);
            unmeta = (uu___105_1068.unmeta);
            unascribe = (uu___105_1068.unascribe)
          }
      | UnfoldUntil d ->
          let uu___106_1070 = fs  in
          {
            beta = (uu___106_1070.beta);
            iota = (uu___106_1070.iota);
            zeta = (uu___106_1070.zeta);
            weak = (uu___106_1070.weak);
            hnf = (uu___106_1070.hnf);
            primops = (uu___106_1070.primops);
            no_delta_steps = (uu___106_1070.no_delta_steps);
            unfold_until = (FStar_Pervasives_Native.Some d);
            unfold_only = (uu___106_1070.unfold_only);
            unfold_attr = (uu___106_1070.unfold_attr);
            unfold_tac = (uu___106_1070.unfold_tac);
            pure_subterms_within_computations =
              (uu___106_1070.pure_subterms_within_computations);
            simplify = (uu___106_1070.simplify);
            erase_universes = (uu___106_1070.erase_universes);
            allow_unbound_universes = (uu___106_1070.allow_unbound_universes);
            reify_ = (uu___106_1070.reify_);
            compress_uvars = (uu___106_1070.compress_uvars);
            no_full_norm = (uu___106_1070.no_full_norm);
            check_no_uvars = (uu___106_1070.check_no_uvars);
            unmeta = (uu___106_1070.unmeta);
            unascribe = (uu___106_1070.unascribe)
          }
      | UnfoldOnly lids ->
          let uu___107_1074 = fs  in
          {
            beta = (uu___107_1074.beta);
            iota = (uu___107_1074.iota);
            zeta = (uu___107_1074.zeta);
            weak = (uu___107_1074.weak);
            hnf = (uu___107_1074.hnf);
            primops = (uu___107_1074.primops);
            no_delta_steps = (uu___107_1074.no_delta_steps);
            unfold_until = (uu___107_1074.unfold_until);
            unfold_only = (FStar_Pervasives_Native.Some lids);
            unfold_attr = (uu___107_1074.unfold_attr);
            unfold_tac = (uu___107_1074.unfold_tac);
            pure_subterms_within_computations =
              (uu___107_1074.pure_subterms_within_computations);
            simplify = (uu___107_1074.simplify);
            erase_universes = (uu___107_1074.erase_universes);
            allow_unbound_universes = (uu___107_1074.allow_unbound_universes);
            reify_ = (uu___107_1074.reify_);
            compress_uvars = (uu___107_1074.compress_uvars);
            no_full_norm = (uu___107_1074.no_full_norm);
            check_no_uvars = (uu___107_1074.check_no_uvars);
            unmeta = (uu___107_1074.unmeta);
            unascribe = (uu___107_1074.unascribe)
          }
      | UnfoldAttr attr ->
          let uu___108_1078 = fs  in
          {
            beta = (uu___108_1078.beta);
            iota = (uu___108_1078.iota);
            zeta = (uu___108_1078.zeta);
            weak = (uu___108_1078.weak);
            hnf = (uu___108_1078.hnf);
            primops = (uu___108_1078.primops);
            no_delta_steps = (uu___108_1078.no_delta_steps);
            unfold_until = (uu___108_1078.unfold_until);
            unfold_only = (uu___108_1078.unfold_only);
            unfold_attr = (add_opt attr fs.unfold_attr);
            unfold_tac = (uu___108_1078.unfold_tac);
            pure_subterms_within_computations =
              (uu___108_1078.pure_subterms_within_computations);
            simplify = (uu___108_1078.simplify);
            erase_universes = (uu___108_1078.erase_universes);
            allow_unbound_universes = (uu___108_1078.allow_unbound_universes);
            reify_ = (uu___108_1078.reify_);
            compress_uvars = (uu___108_1078.compress_uvars);
            no_full_norm = (uu___108_1078.no_full_norm);
            check_no_uvars = (uu___108_1078.check_no_uvars);
            unmeta = (uu___108_1078.unmeta);
            unascribe = (uu___108_1078.unascribe)
          }
      | UnfoldTac  ->
          let uu___109_1079 = fs  in
          {
            beta = (uu___109_1079.beta);
            iota = (uu___109_1079.iota);
            zeta = (uu___109_1079.zeta);
            weak = (uu___109_1079.weak);
            hnf = (uu___109_1079.hnf);
            primops = (uu___109_1079.primops);
            no_delta_steps = (uu___109_1079.no_delta_steps);
            unfold_until = (uu___109_1079.unfold_until);
            unfold_only = (uu___109_1079.unfold_only);
            unfold_attr = (uu___109_1079.unfold_attr);
            unfold_tac = true;
            pure_subterms_within_computations =
              (uu___109_1079.pure_subterms_within_computations);
            simplify = (uu___109_1079.simplify);
            erase_universes = (uu___109_1079.erase_universes);
            allow_unbound_universes = (uu___109_1079.allow_unbound_universes);
            reify_ = (uu___109_1079.reify_);
            compress_uvars = (uu___109_1079.compress_uvars);
            no_full_norm = (uu___109_1079.no_full_norm);
            check_no_uvars = (uu___109_1079.check_no_uvars);
            unmeta = (uu___109_1079.unmeta);
            unascribe = (uu___109_1079.unascribe)
          }
      | PureSubtermsWithinComputations  ->
          let uu___110_1080 = fs  in
          {
            beta = (uu___110_1080.beta);
            iota = (uu___110_1080.iota);
            zeta = (uu___110_1080.zeta);
            weak = (uu___110_1080.weak);
            hnf = (uu___110_1080.hnf);
            primops = (uu___110_1080.primops);
            no_delta_steps = (uu___110_1080.no_delta_steps);
            unfold_until = (uu___110_1080.unfold_until);
            unfold_only = (uu___110_1080.unfold_only);
            unfold_attr = (uu___110_1080.unfold_attr);
            unfold_tac = (uu___110_1080.unfold_tac);
            pure_subterms_within_computations = true;
            simplify = (uu___110_1080.simplify);
            erase_universes = (uu___110_1080.erase_universes);
            allow_unbound_universes = (uu___110_1080.allow_unbound_universes);
            reify_ = (uu___110_1080.reify_);
            compress_uvars = (uu___110_1080.compress_uvars);
            no_full_norm = (uu___110_1080.no_full_norm);
            check_no_uvars = (uu___110_1080.check_no_uvars);
            unmeta = (uu___110_1080.unmeta);
            unascribe = (uu___110_1080.unascribe)
          }
      | Simplify  ->
          let uu___111_1081 = fs  in
          {
            beta = (uu___111_1081.beta);
            iota = (uu___111_1081.iota);
            zeta = (uu___111_1081.zeta);
            weak = (uu___111_1081.weak);
            hnf = (uu___111_1081.hnf);
            primops = (uu___111_1081.primops);
            no_delta_steps = (uu___111_1081.no_delta_steps);
            unfold_until = (uu___111_1081.unfold_until);
            unfold_only = (uu___111_1081.unfold_only);
            unfold_attr = (uu___111_1081.unfold_attr);
            unfold_tac = (uu___111_1081.unfold_tac);
            pure_subterms_within_computations =
              (uu___111_1081.pure_subterms_within_computations);
            simplify = true;
            erase_universes = (uu___111_1081.erase_universes);
            allow_unbound_universes = (uu___111_1081.allow_unbound_universes);
            reify_ = (uu___111_1081.reify_);
            compress_uvars = (uu___111_1081.compress_uvars);
            no_full_norm = (uu___111_1081.no_full_norm);
            check_no_uvars = (uu___111_1081.check_no_uvars);
            unmeta = (uu___111_1081.unmeta);
            unascribe = (uu___111_1081.unascribe)
          }
      | EraseUniverses  ->
          let uu___112_1082 = fs  in
          {
            beta = (uu___112_1082.beta);
            iota = (uu___112_1082.iota);
            zeta = (uu___112_1082.zeta);
            weak = (uu___112_1082.weak);
            hnf = (uu___112_1082.hnf);
            primops = (uu___112_1082.primops);
            no_delta_steps = (uu___112_1082.no_delta_steps);
            unfold_until = (uu___112_1082.unfold_until);
            unfold_only = (uu___112_1082.unfold_only);
            unfold_attr = (uu___112_1082.unfold_attr);
            unfold_tac = (uu___112_1082.unfold_tac);
            pure_subterms_within_computations =
              (uu___112_1082.pure_subterms_within_computations);
            simplify = (uu___112_1082.simplify);
            erase_universes = true;
            allow_unbound_universes = (uu___112_1082.allow_unbound_universes);
            reify_ = (uu___112_1082.reify_);
            compress_uvars = (uu___112_1082.compress_uvars);
            no_full_norm = (uu___112_1082.no_full_norm);
            check_no_uvars = (uu___112_1082.check_no_uvars);
            unmeta = (uu___112_1082.unmeta);
            unascribe = (uu___112_1082.unascribe)
          }
      | AllowUnboundUniverses  ->
          let uu___113_1083 = fs  in
          {
            beta = (uu___113_1083.beta);
            iota = (uu___113_1083.iota);
            zeta = (uu___113_1083.zeta);
            weak = (uu___113_1083.weak);
            hnf = (uu___113_1083.hnf);
            primops = (uu___113_1083.primops);
            no_delta_steps = (uu___113_1083.no_delta_steps);
            unfold_until = (uu___113_1083.unfold_until);
            unfold_only = (uu___113_1083.unfold_only);
            unfold_attr = (uu___113_1083.unfold_attr);
            unfold_tac = (uu___113_1083.unfold_tac);
            pure_subterms_within_computations =
              (uu___113_1083.pure_subterms_within_computations);
            simplify = (uu___113_1083.simplify);
            erase_universes = (uu___113_1083.erase_universes);
            allow_unbound_universes = true;
            reify_ = (uu___113_1083.reify_);
            compress_uvars = (uu___113_1083.compress_uvars);
            no_full_norm = (uu___113_1083.no_full_norm);
            check_no_uvars = (uu___113_1083.check_no_uvars);
            unmeta = (uu___113_1083.unmeta);
            unascribe = (uu___113_1083.unascribe)
          }
      | Reify  ->
          let uu___114_1084 = fs  in
          {
            beta = (uu___114_1084.beta);
            iota = (uu___114_1084.iota);
            zeta = (uu___114_1084.zeta);
            weak = (uu___114_1084.weak);
            hnf = (uu___114_1084.hnf);
            primops = (uu___114_1084.primops);
            no_delta_steps = (uu___114_1084.no_delta_steps);
            unfold_until = (uu___114_1084.unfold_until);
            unfold_only = (uu___114_1084.unfold_only);
            unfold_attr = (uu___114_1084.unfold_attr);
            unfold_tac = (uu___114_1084.unfold_tac);
            pure_subterms_within_computations =
              (uu___114_1084.pure_subterms_within_computations);
            simplify = (uu___114_1084.simplify);
            erase_universes = (uu___114_1084.erase_universes);
            allow_unbound_universes = (uu___114_1084.allow_unbound_universes);
            reify_ = true;
            compress_uvars = (uu___114_1084.compress_uvars);
            no_full_norm = (uu___114_1084.no_full_norm);
            check_no_uvars = (uu___114_1084.check_no_uvars);
            unmeta = (uu___114_1084.unmeta);
            unascribe = (uu___114_1084.unascribe)
          }
      | CompressUvars  ->
          let uu___115_1085 = fs  in
          {
            beta = (uu___115_1085.beta);
            iota = (uu___115_1085.iota);
            zeta = (uu___115_1085.zeta);
            weak = (uu___115_1085.weak);
            hnf = (uu___115_1085.hnf);
            primops = (uu___115_1085.primops);
            no_delta_steps = (uu___115_1085.no_delta_steps);
            unfold_until = (uu___115_1085.unfold_until);
            unfold_only = (uu___115_1085.unfold_only);
            unfold_attr = (uu___115_1085.unfold_attr);
            unfold_tac = (uu___115_1085.unfold_tac);
            pure_subterms_within_computations =
              (uu___115_1085.pure_subterms_within_computations);
            simplify = (uu___115_1085.simplify);
            erase_universes = (uu___115_1085.erase_universes);
            allow_unbound_universes = (uu___115_1085.allow_unbound_universes);
            reify_ = (uu___115_1085.reify_);
            compress_uvars = true;
            no_full_norm = (uu___115_1085.no_full_norm);
            check_no_uvars = (uu___115_1085.check_no_uvars);
            unmeta = (uu___115_1085.unmeta);
            unascribe = (uu___115_1085.unascribe)
          }
      | NoFullNorm  ->
          let uu___116_1086 = fs  in
          {
            beta = (uu___116_1086.beta);
            iota = (uu___116_1086.iota);
            zeta = (uu___116_1086.zeta);
            weak = (uu___116_1086.weak);
            hnf = (uu___116_1086.hnf);
            primops = (uu___116_1086.primops);
            no_delta_steps = (uu___116_1086.no_delta_steps);
            unfold_until = (uu___116_1086.unfold_until);
            unfold_only = (uu___116_1086.unfold_only);
            unfold_attr = (uu___116_1086.unfold_attr);
            unfold_tac = (uu___116_1086.unfold_tac);
            pure_subterms_within_computations =
              (uu___116_1086.pure_subterms_within_computations);
            simplify = (uu___116_1086.simplify);
            erase_universes = (uu___116_1086.erase_universes);
            allow_unbound_universes = (uu___116_1086.allow_unbound_universes);
            reify_ = (uu___116_1086.reify_);
            compress_uvars = (uu___116_1086.compress_uvars);
            no_full_norm = true;
            check_no_uvars = (uu___116_1086.check_no_uvars);
            unmeta = (uu___116_1086.unmeta);
            unascribe = (uu___116_1086.unascribe)
          }
      | CheckNoUvars  ->
          let uu___117_1087 = fs  in
          {
            beta = (uu___117_1087.beta);
            iota = (uu___117_1087.iota);
            zeta = (uu___117_1087.zeta);
            weak = (uu___117_1087.weak);
            hnf = (uu___117_1087.hnf);
            primops = (uu___117_1087.primops);
            no_delta_steps = (uu___117_1087.no_delta_steps);
            unfold_until = (uu___117_1087.unfold_until);
            unfold_only = (uu___117_1087.unfold_only);
            unfold_attr = (uu___117_1087.unfold_attr);
            unfold_tac = (uu___117_1087.unfold_tac);
            pure_subterms_within_computations =
              (uu___117_1087.pure_subterms_within_computations);
            simplify = (uu___117_1087.simplify);
            erase_universes = (uu___117_1087.erase_universes);
            allow_unbound_universes = (uu___117_1087.allow_unbound_universes);
            reify_ = (uu___117_1087.reify_);
            compress_uvars = (uu___117_1087.compress_uvars);
            no_full_norm = (uu___117_1087.no_full_norm);
            check_no_uvars = true;
            unmeta = (uu___117_1087.unmeta);
            unascribe = (uu___117_1087.unascribe)
          }
      | Unmeta  ->
          let uu___118_1088 = fs  in
          {
            beta = (uu___118_1088.beta);
            iota = (uu___118_1088.iota);
            zeta = (uu___118_1088.zeta);
            weak = (uu___118_1088.weak);
            hnf = (uu___118_1088.hnf);
            primops = (uu___118_1088.primops);
            no_delta_steps = (uu___118_1088.no_delta_steps);
            unfold_until = (uu___118_1088.unfold_until);
            unfold_only = (uu___118_1088.unfold_only);
            unfold_attr = (uu___118_1088.unfold_attr);
            unfold_tac = (uu___118_1088.unfold_tac);
            pure_subterms_within_computations =
              (uu___118_1088.pure_subterms_within_computations);
            simplify = (uu___118_1088.simplify);
            erase_universes = (uu___118_1088.erase_universes);
            allow_unbound_universes = (uu___118_1088.allow_unbound_universes);
            reify_ = (uu___118_1088.reify_);
            compress_uvars = (uu___118_1088.compress_uvars);
            no_full_norm = (uu___118_1088.no_full_norm);
            check_no_uvars = (uu___118_1088.check_no_uvars);
            unmeta = true;
            unascribe = (uu___118_1088.unascribe)
          }
      | Unascribe  ->
          let uu___119_1089 = fs  in
          {
            beta = (uu___119_1089.beta);
            iota = (uu___119_1089.iota);
            zeta = (uu___119_1089.zeta);
            weak = (uu___119_1089.weak);
            hnf = (uu___119_1089.hnf);
            primops = (uu___119_1089.primops);
            no_delta_steps = (uu___119_1089.no_delta_steps);
            unfold_until = (uu___119_1089.unfold_until);
            unfold_only = (uu___119_1089.unfold_only);
            unfold_attr = (uu___119_1089.unfold_attr);
            unfold_tac = (uu___119_1089.unfold_tac);
            pure_subterms_within_computations =
              (uu___119_1089.pure_subterms_within_computations);
            simplify = (uu___119_1089.simplify);
            erase_universes = (uu___119_1089.erase_universes);
            allow_unbound_universes = (uu___119_1089.allow_unbound_universes);
            reify_ = (uu___119_1089.reify_);
            compress_uvars = (uu___119_1089.compress_uvars);
            no_full_norm = (uu___119_1089.no_full_norm);
            check_no_uvars = (uu___119_1089.check_no_uvars);
            unmeta = (uu___119_1089.unmeta);
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
  fun uu___79_1503  ->
    match uu___79_1503 with
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
             let uu____1804 = FStar_Ident.text_of_lid p.name  in
             FStar_Util.psmap_add m1 uu____1804 p) l m
  
let (prim_from_list :
  primitive_step Prims.list -> primitive_step FStar_Util.psmap) =
  fun l  ->
    let uu____1816 = FStar_Util.psmap_empty ()  in add_steps uu____1816 l
  
let (find_prim_step :
  cfg ->
    FStar_Syntax_Syntax.fv -> primitive_step FStar_Pervasives_Native.option)
  =
  fun cfg  ->
    fun fv  ->
      let uu____1827 =
        FStar_Ident.text_of_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
         in
      FStar_Util.psmap_try_find cfg.primitive_steps uu____1827
  
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
    match projectee with | Arg _0 -> true | uu____1969 -> false
  
let (__proj__Arg__item___0 :
  stack_elt ->
    (closure,FStar_Syntax_Syntax.aqual,FStar_Range.range)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | Arg _0 -> _0 
let (uu___is_UnivArgs : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnivArgs _0 -> true | uu____2005 -> false
  
let (__proj__UnivArgs__item___0 :
  stack_elt ->
    (FStar_Syntax_Syntax.universe Prims.list,FStar_Range.range)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | UnivArgs _0 -> _0 
let (uu___is_MemoLazy : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | MemoLazy _0 -> true | uu____2041 -> false
  
let (__proj__MemoLazy__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.term) FStar_Pervasives_Native.tuple2
      FStar_Syntax_Syntax.memo)
  = fun projectee  -> match projectee with | MemoLazy _0 -> _0 
let (uu___is_Match : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____2110 -> false
  
let (__proj__Match__item___0 :
  stack_elt ->
    (env,branches,FStar_Range.range) FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | Match _0 -> _0 
let (uu___is_Abs : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Abs _0 -> true | uu____2152 -> false
  
let (__proj__Abs__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.binders,env,FStar_Syntax_Syntax.residual_comp
                                           FStar_Pervasives_Native.option,
      FStar_Range.range) FStar_Pervasives_Native.tuple5)
  = fun projectee  -> match projectee with | Abs _0 -> _0 
let (uu___is_App : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____2208 -> false
  
let (__proj__App__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual,FStar_Range.range)
      FStar_Pervasives_Native.tuple4)
  = fun projectee  -> match projectee with | App _0 -> _0 
let (uu___is_Meta : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Meta _0 -> true | uu____2248 -> false
  
let (__proj__Meta__item___0 :
  stack_elt ->
    (FStar_Syntax_Syntax.metadata,FStar_Range.range)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Meta _0 -> _0 
let (uu___is_Let : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Let _0 -> true | uu____2280 -> false
  
let (__proj__Let__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.letbinding,FStar_Range.range)
      FStar_Pervasives_Native.tuple4)
  = fun projectee  -> match projectee with | Let _0 -> _0 
let (uu___is_Cfg : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Cfg _0 -> true | uu____2316 -> false
  
let (__proj__Cfg__item___0 : stack_elt -> cfg) =
  fun projectee  -> match projectee with | Cfg _0 -> _0 
let (uu___is_Debug : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Debug _0 -> true | uu____2332 -> false
  
let (__proj__Debug__item___0 :
  stack_elt ->
    (FStar_Syntax_Syntax.term,FStar_Util.time) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Debug _0 -> _0 
type stack = stack_elt Prims.list[@@deriving show]
let (head_of : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____2357 = FStar_Syntax_Util.head_and_args' t  in
    match uu____2357 with | (hd1,uu____2371) -> hd1
  
let mk :
  'Auu____2391 .
    'Auu____2391 ->
      FStar_Range.range -> 'Auu____2391 FStar_Syntax_Syntax.syntax
  =
  fun t  -> fun r  -> FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None r 
let set_memo : 'a . cfg -> 'a FStar_Syntax_Syntax.memo -> 'a -> Prims.unit =
  fun cfg  ->
    fun r  ->
      fun t  ->
        if cfg.memoize_lazy
        then
          let uu____2445 = FStar_ST.op_Bang r  in
          match uu____2445 with
          | FStar_Pervasives_Native.Some uu____2493 ->
              failwith "Unexpected set_memo: thunk already evaluated"
          | FStar_Pervasives_Native.None  ->
              FStar_ST.op_Colon_Equals r (FStar_Pervasives_Native.Some t)
        else ()
  
let (env_to_string : closure Prims.list -> Prims.string) =
  fun env  ->
    let uu____2547 = FStar_List.map closure_to_string env  in
    FStar_All.pipe_right uu____2547 (FStar_String.concat "; ")
  
let (stack_elt_to_string : stack_elt -> Prims.string) =
  fun uu___80_2554  ->
    match uu___80_2554 with
    | Arg (c,uu____2556,uu____2557) ->
        let uu____2558 = closure_to_string c  in
        FStar_Util.format1 "Closure %s" uu____2558
    | MemoLazy uu____2559 -> "MemoLazy"
    | Abs (uu____2566,bs,uu____2568,uu____2569,uu____2570) ->
        let uu____2575 =
          FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs)
           in
        FStar_Util.format1 "Abs %s" uu____2575
    | UnivArgs uu____2580 -> "UnivArgs"
    | Match uu____2587 -> "Match"
    | App (uu____2594,t,uu____2596,uu____2597) ->
        let uu____2598 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "App %s" uu____2598
    | Meta (m,uu____2600) -> "Meta"
    | Let uu____2601 -> "Let"
    | Cfg uu____2610 -> "Cfg"
    | Debug (t,uu____2612) ->
        let uu____2613 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "Debug %s" uu____2613
  
let (stack_to_string : stack_elt Prims.list -> Prims.string) =
  fun s  ->
    let uu____2621 = FStar_List.map stack_elt_to_string s  in
    FStar_All.pipe_right uu____2621 (FStar_String.concat "; ")
  
let (log : cfg -> (Prims.unit -> Prims.unit) -> Prims.unit) =
  fun cfg  -> fun f  -> if (cfg.debug).gen then f () else () 
let (log_primops : cfg -> (Prims.unit -> Prims.unit) -> Prims.unit) =
  fun cfg  -> fun f  -> if (cfg.debug).primop then f () else () 
let is_empty : 'Auu____2652 . 'Auu____2652 Prims.list -> Prims.bool =
  fun uu___81_2658  ->
    match uu___81_2658 with | [] -> true | uu____2661 -> false
  
let lookup_bvar :
  'Auu____2668 'Auu____2669 .
    ('Auu____2668,'Auu____2669) FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Syntax_Syntax.bv -> 'Auu____2669
  =
  fun env  ->
    fun x  ->
      try
        let uu____2693 = FStar_List.nth env x.FStar_Syntax_Syntax.index  in
        FStar_Pervasives_Native.snd uu____2693
      with
      | uu____2706 ->
          let uu____2707 =
            let uu____2708 = FStar_Syntax_Print.db_to_string x  in
            FStar_Util.format1 "Failed to find %s\n" uu____2708  in
          failwith uu____2707
  
let (downgrade_ghost_effect_name :
  FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option) =
  fun l  ->
    let uu____2714 =
      FStar_Ident.lid_equals l FStar_Parser_Const.effect_Ghost_lid  in
    if uu____2714
    then FStar_Pervasives_Native.Some FStar_Parser_Const.effect_Pure_lid
    else
      (let uu____2718 =
         FStar_Ident.lid_equals l FStar_Parser_Const.effect_GTot_lid  in
       if uu____2718
       then FStar_Pervasives_Native.Some FStar_Parser_Const.effect_Tot_lid
       else
         (let uu____2722 =
            FStar_Ident.lid_equals l FStar_Parser_Const.effect_GHOST_lid  in
          if uu____2722
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
          let uu____2748 =
            FStar_List.fold_left
              (fun uu____2774  ->
                 fun u1  ->
                   match uu____2774 with
                   | (cur_kernel,cur_max,out) ->
                       let uu____2799 = FStar_Syntax_Util.univ_kernel u1  in
                       (match uu____2799 with
                        | (k_u,n1) ->
                            let uu____2814 =
                              FStar_Syntax_Util.eq_univs cur_kernel k_u  in
                            if uu____2814
                            then (cur_kernel, u1, out)
                            else (k_u, u1, (cur_max :: out))))
              (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero, [])
              us1
             in
          match uu____2748 with
          | (uu____2832,u1,out) -> FStar_List.rev (u1 :: out)  in
        let rec aux u1 =
          let u2 = FStar_Syntax_Subst.compress_univ u1  in
          match u2 with
          | FStar_Syntax_Syntax.U_bvar x ->
              (try
                 let uu____2857 =
                   let uu____2858 = FStar_List.nth env x  in
                   FStar_Pervasives_Native.snd uu____2858  in
                 match uu____2857 with
                 | Univ u3 -> aux u3
                 | Dummy  -> [u2]
                 | uu____2876 ->
                     failwith "Impossible: universe variable bound to a term"
               with
               | uu____2884 ->
                   if (cfg.steps).allow_unbound_universes
                   then [FStar_Syntax_Syntax.U_unknown]
                   else failwith "Universe variable not found")
          | FStar_Syntax_Syntax.U_unif uu____2890 when
              (cfg.steps).check_no_uvars -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_zero  -> [u2]
          | FStar_Syntax_Syntax.U_unif uu____2899 -> [u2]
          | FStar_Syntax_Syntax.U_name uu____2908 -> [u2]
          | FStar_Syntax_Syntax.U_unknown  -> [u2]
          | FStar_Syntax_Syntax.U_max [] -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_max us ->
              let us1 =
                let uu____2915 = FStar_List.collect aux us  in
                FStar_All.pipe_right uu____2915 norm_univs  in
              (match us1 with
               | u_k::hd1::rest ->
                   let rest1 = hd1 :: rest  in
                   let uu____2932 = FStar_Syntax_Util.univ_kernel u_k  in
                   (match uu____2932 with
                    | (FStar_Syntax_Syntax.U_zero ,n1) ->
                        let uu____2940 =
                          FStar_All.pipe_right rest1
                            (FStar_List.for_all
                               (fun u3  ->
                                  let uu____2948 =
                                    FStar_Syntax_Util.univ_kernel u3  in
                                  match uu____2948 with
                                  | (uu____2953,m) -> n1 <= m))
                           in
                        if uu____2940 then rest1 else us1
                    | uu____2958 -> us1)
               | uu____2963 -> us1)
          | FStar_Syntax_Syntax.U_succ u3 ->
              let uu____2967 = aux u3  in
              FStar_List.map (fun _0_40  -> FStar_Syntax_Syntax.U_succ _0_40)
                uu____2967
           in
        if (cfg.steps).erase_universes
        then FStar_Syntax_Syntax.U_unknown
        else
          (let uu____2971 = aux u  in
           match uu____2971 with
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
          (fun uu____3075  ->
             let uu____3076 = FStar_Syntax_Print.tag_of_term t  in
             let uu____3077 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.print2 ">>> %s Closure_as_term %s\n" uu____3076
               uu____3077);
        (match env with
         | [] when
             FStar_All.pipe_left Prims.op_Negation (cfg.steps).compress_uvars
             -> t
         | uu____3084 ->
             let t1 = FStar_Syntax_Subst.compress t  in
             (match t1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_delayed uu____3086 ->
                  failwith "Impossible"
              | FStar_Syntax_Syntax.Tm_unknown  -> t1
              | FStar_Syntax_Syntax.Tm_constant uu____3111 -> t1
              | FStar_Syntax_Syntax.Tm_name uu____3112 -> t1
              | FStar_Syntax_Syntax.Tm_lazy uu____3113 -> t1
              | FStar_Syntax_Syntax.Tm_fvar uu____3114 -> t1
              | FStar_Syntax_Syntax.Tm_uvar uu____3115 ->
                  if (cfg.steps).check_no_uvars
                  then
                    let uu____3132 =
                      let uu____3133 =
                        FStar_Range.string_of_range
                          t1.FStar_Syntax_Syntax.pos
                         in
                      let uu____3134 = FStar_Syntax_Print.term_to_string t1
                         in
                      FStar_Util.format2
                        "(%s): CheckNoUvars: Unexpected unification variable remains: %s"
                        uu____3133 uu____3134
                       in
                    failwith uu____3132
                  else t1
              | FStar_Syntax_Syntax.Tm_type u ->
                  let uu____3137 =
                    let uu____3138 = norm_universe cfg env u  in
                    FStar_Syntax_Syntax.Tm_type uu____3138  in
                  mk uu____3137 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
                  let uu____3145 = FStar_List.map (norm_universe cfg env) us
                     in
                  FStar_Syntax_Syntax.mk_Tm_uinst t' uu____3145
              | FStar_Syntax_Syntax.Tm_bvar x ->
                  let uu____3147 = lookup_bvar env x  in
                  (match uu____3147 with
                   | Univ uu____3150 ->
                       failwith
                         "Impossible: term variable is bound to a universe"
                   | Dummy  -> t1
                   | Clos (env1,t0,uu____3153,uu____3154) ->
                       closure_as_term cfg env1 t0)
              | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                  let head2 = closure_as_term_delayed cfg env head1  in
                  let args1 = closures_as_args_delayed cfg env args  in
                  mk (FStar_Syntax_Syntax.Tm_app (head2, args1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
                  let uu____3266 = closures_as_binders_delayed cfg env bs  in
                  (match uu____3266 with
                   | (bs1,env1) ->
                       let body1 = closure_as_term_delayed cfg env1 body  in
                       let uu____3294 =
                         let uu____3295 =
                           let uu____3312 = close_lcomp_opt cfg env1 lopt  in
                           (bs1, body1, uu____3312)  in
                         FStar_Syntax_Syntax.Tm_abs uu____3295  in
                       mk uu____3294 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                  let uu____3343 = closures_as_binders_delayed cfg env bs  in
                  (match uu____3343 with
                   | (bs1,env1) ->
                       let c1 = close_comp cfg env1 c  in
                       mk (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
                         t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
                  let uu____3385 =
                    let uu____3396 =
                      let uu____3403 = FStar_Syntax_Syntax.mk_binder x  in
                      [uu____3403]  in
                    closures_as_binders_delayed cfg env uu____3396  in
                  (match uu____3385 with
                   | (x1,env1) ->
                       let phi1 = closure_as_term_delayed cfg env1 phi  in
                       let uu____3421 =
                         let uu____3422 =
                           let uu____3429 =
                             let uu____3430 = FStar_List.hd x1  in
                             FStar_All.pipe_right uu____3430
                               FStar_Pervasives_Native.fst
                              in
                           (uu____3429, phi1)  in
                         FStar_Syntax_Syntax.Tm_refine uu____3422  in
                       mk uu____3421 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_ascribed (t11,(annot,tacopt),lopt) ->
                  let annot1 =
                    match annot with
                    | FStar_Util.Inl t2 ->
                        let uu____3521 = closure_as_term_delayed cfg env t2
                           in
                        FStar_Util.Inl uu____3521
                    | FStar_Util.Inr c ->
                        let uu____3535 = close_comp cfg env c  in
                        FStar_Util.Inr uu____3535
                     in
                  let tacopt1 =
                    FStar_Util.map_opt tacopt
                      (closure_as_term_delayed cfg env)
                     in
                  let uu____3551 =
                    let uu____3552 =
                      let uu____3579 = closure_as_term_delayed cfg env t11
                         in
                      (uu____3579, (annot1, tacopt1), lopt)  in
                    FStar_Syntax_Syntax.Tm_ascribed uu____3552  in
                  mk uu____3551 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_quoted (t',qi) ->
                  (match qi.FStar_Syntax_Syntax.qkind with
                   | FStar_Syntax_Syntax.Quote_dynamic  ->
                       let uu____3620 =
                         let uu____3621 =
                           let uu____3628 =
                             closure_as_term_delayed cfg env t'  in
                           (uu____3628, qi)  in
                         FStar_Syntax_Syntax.Tm_quoted uu____3621  in
                       mk uu____3620 t1.FStar_Syntax_Syntax.pos
                   | FStar_Syntax_Syntax.Quote_static  ->
                       let qi1 =
                         FStar_Syntax_Syntax.on_antiquoted
                           (closure_as_term_delayed cfg env) qi
                          in
                       mk (FStar_Syntax_Syntax.Tm_quoted (t', qi1))
                         t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_pattern args) ->
                  let uu____3652 =
                    let uu____3653 =
                      let uu____3660 = closure_as_term_delayed cfg env t'  in
                      let uu____3663 =
                        let uu____3664 =
                          FStar_All.pipe_right args
                            (FStar_List.map
                               (closures_as_args_delayed cfg env))
                           in
                        FStar_Syntax_Syntax.Meta_pattern uu____3664  in
                      (uu____3660, uu____3663)  in
                    FStar_Syntax_Syntax.Tm_meta uu____3653  in
                  mk uu____3652 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic (m,tbody)) ->
                  let uu____3724 =
                    let uu____3725 =
                      let uu____3732 = closure_as_term_delayed cfg env t'  in
                      let uu____3735 =
                        let uu____3736 =
                          let uu____3743 =
                            closure_as_term_delayed cfg env tbody  in
                          (m, uu____3743)  in
                        FStar_Syntax_Syntax.Meta_monadic uu____3736  in
                      (uu____3732, uu____3735)  in
                    FStar_Syntax_Syntax.Tm_meta uu____3725  in
                  mk uu____3724 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,tbody)) ->
                  let uu____3762 =
                    let uu____3763 =
                      let uu____3770 = closure_as_term_delayed cfg env t'  in
                      let uu____3773 =
                        let uu____3774 =
                          let uu____3783 =
                            closure_as_term_delayed cfg env tbody  in
                          (m1, m2, uu____3783)  in
                        FStar_Syntax_Syntax.Meta_monadic_lift uu____3774  in
                      (uu____3770, uu____3773)  in
                    FStar_Syntax_Syntax.Tm_meta uu____3763  in
                  mk uu____3762 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta (t',m) ->
                  let uu____3796 =
                    let uu____3797 =
                      let uu____3804 = closure_as_term_delayed cfg env t'  in
                      (uu____3804, m)  in
                    FStar_Syntax_Syntax.Tm_meta uu____3797  in
                  mk uu____3796 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                  let env0 = env  in
                  let env1 =
                    FStar_List.fold_left
                      (fun env1  -> fun uu____3844  -> dummy :: env1) env
                      lb.FStar_Syntax_Syntax.lbunivs
                     in
                  let typ =
                    closure_as_term_delayed cfg env1
                      lb.FStar_Syntax_Syntax.lbtyp
                     in
                  let def =
                    closure_as_term cfg env1 lb.FStar_Syntax_Syntax.lbdef  in
                  let uu____3863 =
                    let uu____3874 = FStar_Syntax_Syntax.is_top_level [lb]
                       in
                    if uu____3874
                    then ((lb.FStar_Syntax_Syntax.lbname), body)
                    else
                      (let x = FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                          in
                       let uu____3893 =
                         closure_as_term cfg (dummy :: env0) body  in
                       ((FStar_Util.Inl
                           (let uu___124_3905 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___124_3905.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___124_3905.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = typ
                            })), uu____3893))
                     in
                  (match uu____3863 with
                   | (nm,body1) ->
                       let lb1 =
                         let uu___125_3921 = lb  in
                         {
                           FStar_Syntax_Syntax.lbname = nm;
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___125_3921.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp = typ;
                           FStar_Syntax_Syntax.lbeff =
                             (uu___125_3921.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef = def;
                           FStar_Syntax_Syntax.lbattrs =
                             (uu___125_3921.FStar_Syntax_Syntax.lbattrs);
                           FStar_Syntax_Syntax.lbpos =
                             (uu___125_3921.FStar_Syntax_Syntax.lbpos)
                         }  in
                       mk
                         (FStar_Syntax_Syntax.Tm_let ((false, [lb1]), body1))
                         t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_let ((uu____3932,lbs),body) ->
                  let norm_one_lb env1 lb =
                    let env_univs =
                      FStar_List.fold_right
                        (fun uu____3991  -> fun env2  -> dummy :: env2)
                        lb.FStar_Syntax_Syntax.lbunivs env1
                       in
                    let env2 =
                      let uu____4016 = FStar_Syntax_Syntax.is_top_level lbs
                         in
                      if uu____4016
                      then env_univs
                      else
                        FStar_List.fold_right
                          (fun uu____4036  -> fun env2  -> dummy :: env2) lbs
                          env_univs
                       in
                    let ty =
                      closure_as_term cfg env_univs
                        lb.FStar_Syntax_Syntax.lbtyp
                       in
                    let nm =
                      let uu____4058 = FStar_Syntax_Syntax.is_top_level lbs
                         in
                      if uu____4058
                      then lb.FStar_Syntax_Syntax.lbname
                      else
                        (let x =
                           FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                         FStar_All.pipe_right
                           (let uu___126_4070 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___126_4070.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___126_4070.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = ty
                            }) (fun _0_41  -> FStar_Util.Inl _0_41))
                       in
                    let uu___127_4071 = lb  in
                    let uu____4072 =
                      closure_as_term cfg env2 lb.FStar_Syntax_Syntax.lbdef
                       in
                    {
                      FStar_Syntax_Syntax.lbname = nm;
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___127_4071.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = ty;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___127_4071.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = uu____4072;
                      FStar_Syntax_Syntax.lbattrs =
                        (uu___127_4071.FStar_Syntax_Syntax.lbattrs);
                      FStar_Syntax_Syntax.lbpos =
                        (uu___127_4071.FStar_Syntax_Syntax.lbpos)
                    }  in
                  let lbs1 =
                    FStar_All.pipe_right lbs
                      (FStar_List.map (norm_one_lb env))
                     in
                  let body1 =
                    let body_env =
                      FStar_List.fold_right
                        (fun uu____4102  -> fun env1  -> dummy :: env1) lbs1
                        env
                       in
                    closure_as_term cfg body_env body  in
                  mk (FStar_Syntax_Syntax.Tm_let ((true, lbs1), body1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
                  let head2 = closure_as_term cfg env head1  in
                  let norm_one_branch env1 uu____4191 =
                    match uu____4191 with
                    | (pat,w_opt,tm) ->
                        let rec norm_pat env2 p =
                          match p.FStar_Syntax_Syntax.v with
                          | FStar_Syntax_Syntax.Pat_constant uu____4246 ->
                              (p, env2)
                          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                              let uu____4267 =
                                FStar_All.pipe_right pats
                                  (FStar_List.fold_left
                                     (fun uu____4327  ->
                                        fun uu____4328  ->
                                          match (uu____4327, uu____4328) with
                                          | ((pats1,env3),(p1,b)) ->
                                              let uu____4419 =
                                                norm_pat env3 p1  in
                                              (match uu____4419 with
                                               | (p2,env4) ->
                                                   (((p2, b) :: pats1), env4)))
                                     ([], env2))
                                 in
                              (match uu____4267 with
                               | (pats1,env3) ->
                                   ((let uu___128_4501 = p  in
                                     {
                                       FStar_Syntax_Syntax.v =
                                         (FStar_Syntax_Syntax.Pat_cons
                                            (fv, (FStar_List.rev pats1)));
                                       FStar_Syntax_Syntax.p =
                                         (uu___128_4501.FStar_Syntax_Syntax.p)
                                     }), env3))
                          | FStar_Syntax_Syntax.Pat_var x ->
                              let x1 =
                                let uu___129_4520 = x  in
                                let uu____4521 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort
                                   in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___129_4520.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___129_4520.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____4521
                                }  in
                              ((let uu___130_4535 = p  in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_var x1);
                                  FStar_Syntax_Syntax.p =
                                    (uu___130_4535.FStar_Syntax_Syntax.p)
                                }), (dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_wild x ->
                              let x1 =
                                let uu___131_4546 = x  in
                                let uu____4547 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort
                                   in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___131_4546.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___131_4546.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____4547
                                }  in
                              ((let uu___132_4561 = p  in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_wild x1);
                                  FStar_Syntax_Syntax.p =
                                    (uu___132_4561.FStar_Syntax_Syntax.p)
                                }), (dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                              let x1 =
                                let uu___133_4577 = x  in
                                let uu____4578 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort
                                   in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___133_4577.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___133_4577.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____4578
                                }  in
                              let t3 = closure_as_term cfg env2 t2  in
                              ((let uu___134_4585 = p  in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_dot_term
                                       (x1, t3));
                                  FStar_Syntax_Syntax.p =
                                    (uu___134_4585.FStar_Syntax_Syntax.p)
                                }), env2)
                           in
                        let uu____4588 = norm_pat env1 pat  in
                        (match uu____4588 with
                         | (pat1,env2) ->
                             let w_opt1 =
                               match w_opt with
                               | FStar_Pervasives_Native.None  ->
                                   FStar_Pervasives_Native.None
                               | FStar_Pervasives_Native.Some w ->
                                   let uu____4617 =
                                     closure_as_term cfg env2 w  in
                                   FStar_Pervasives_Native.Some uu____4617
                                in
                             let tm1 = closure_as_term cfg env2 tm  in
                             (pat1, w_opt1, tm1))
                     in
                  let uu____4623 =
                    let uu____4624 =
                      let uu____4647 =
                        FStar_All.pipe_right branches
                          (FStar_List.map (norm_one_branch env))
                         in
                      (head2, uu____4647)  in
                    FStar_Syntax_Syntax.Tm_match uu____4624  in
                  mk uu____4623 t1.FStar_Syntax_Syntax.pos))

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
        | uu____4733 -> closure_as_term cfg env t

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
        | uu____4759 ->
            FStar_List.map
              (fun uu____4776  ->
                 match uu____4776 with
                 | (x,imp) ->
                     let uu____4795 = closure_as_term_delayed cfg env x  in
                     (uu____4795, imp)) args

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
        let uu____4809 =
          FStar_All.pipe_right bs
            (FStar_List.fold_left
               (fun uu____4858  ->
                  fun uu____4859  ->
                    match (uu____4858, uu____4859) with
                    | ((env1,out),(b,imp)) ->
                        let b1 =
                          let uu___135_4929 = b  in
                          let uu____4930 =
                            closure_as_term_delayed cfg env1
                              b.FStar_Syntax_Syntax.sort
                             in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___135_4929.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___135_4929.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = uu____4930
                          }  in
                        let env2 = dummy :: env1  in
                        (env2, ((b1, imp) :: out))) (env, []))
           in
        match uu____4809 with | (env1,bs1) -> ((FStar_List.rev bs1), env1)

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
        | uu____5023 ->
            (match c.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Total (t,uopt) ->
                 let uu____5036 = closure_as_term_delayed cfg env t  in
                 let uu____5037 =
                   FStar_Option.map (norm_universe cfg env) uopt  in
                 FStar_Syntax_Syntax.mk_Total' uu____5036 uu____5037
             | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                 let uu____5050 = closure_as_term_delayed cfg env t  in
                 let uu____5051 =
                   FStar_Option.map (norm_universe cfg env) uopt  in
                 FStar_Syntax_Syntax.mk_GTotal' uu____5050 uu____5051
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
                        (fun uu___82_5077  ->
                           match uu___82_5077 with
                           | FStar_Syntax_Syntax.DECREASES t ->
                               let uu____5081 =
                                 closure_as_term_delayed cfg env t  in
                               FStar_Syntax_Syntax.DECREASES uu____5081
                           | f -> f))
                    in
                 let uu____5085 =
                   let uu___136_5086 = c1  in
                   let uu____5087 =
                     FStar_List.map (norm_universe cfg env)
                       c1.FStar_Syntax_Syntax.comp_univs
                      in
                   {
                     FStar_Syntax_Syntax.comp_univs = uu____5087;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___136_5086.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ = rt;
                     FStar_Syntax_Syntax.effect_args = args;
                     FStar_Syntax_Syntax.flags = flags1
                   }  in
                 FStar_Syntax_Syntax.mk_Comp uu____5085)

and (filter_out_lcomp_cflags :
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun flags1  ->
    FStar_All.pipe_right flags1
      (FStar_List.filter
         (fun uu___83_5097  ->
            match uu___83_5097 with
            | FStar_Syntax_Syntax.DECREASES uu____5098 -> false
            | uu____5101 -> true))

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
                   (fun uu___84_5119  ->
                      match uu___84_5119 with
                      | FStar_Syntax_Syntax.DECREASES uu____5120 -> false
                      | uu____5123 -> true))
               in
            let rc1 =
              let uu___137_5125 = rc  in
              let uu____5126 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (closure_as_term cfg env)
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___137_5125.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____5126;
                FStar_Syntax_Syntax.residual_flags = flags1
              }  in
            FStar_Pervasives_Native.Some rc1
        | uu____5133 -> lopt

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
    let uu____5218 = FStar_Syntax_Embeddings.unembed_list_safe u  in
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a) uu____5218  in
  let arg_as_bounded_int uu____5246 =
    match uu____5246 with
    | (a,uu____5258) ->
        let uu____5265 =
          let uu____5266 = FStar_Syntax_Subst.compress a  in
          uu____5266.FStar_Syntax_Syntax.n  in
        (match uu____5265 with
         | FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv1;
                FStar_Syntax_Syntax.pos = uu____5276;
                FStar_Syntax_Syntax.vars = uu____5277;_},({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_constant
                                                              (FStar_Const.Const_int
                                                              (i,FStar_Pervasives_Native.None
                                                               ));
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____5279;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____5280;_},uu____5281)::[])
             when
             let uu____5320 =
               FStar_Ident.text_of_lid
                 (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                in
             FStar_Util.ends_with uu____5320 "int_to_t" ->
             let uu____5321 =
               let uu____5326 = FStar_BigInt.big_int_of_string i  in
               (fv1, uu____5326)  in
             FStar_Pervasives_Native.Some uu____5321
         | uu____5331 -> FStar_Pervasives_Native.None)
     in
  let lift_unary a b f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a)::[] ->
        let uu____5371 = f a  in FStar_Pervasives_Native.Some uu____5371
    | uu____5372 -> FStar_Pervasives_Native.None  in
  let lift_binary a b f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a0)::(FStar_Pervasives_Native.Some
        a1)::[] ->
        let uu____5420 = f a0 a1  in FStar_Pervasives_Native.Some uu____5420
    | uu____5421 -> FStar_Pervasives_Native.None  in
  let unary_op a415 a416 a417 a418 a419 =
    (Obj.magic
       (fun a  ->
          fun as_a  ->
            fun f  ->
              fun res  ->
                fun args  ->
                  let uu____5463 = FStar_List.map as_a args  in
                  lift_unary () ()
                    (fun a414  -> (Obj.magic (f res.psc_range)) a414)
                    uu____5463)) a415 a416 a417 a418 a419
     in
  let binary_op a422 a423 a424 a425 a426 =
    (Obj.magic
       (fun a  ->
          fun as_a  ->
            fun f  ->
              fun res  ->
                fun args  ->
                  let uu____5512 = FStar_List.map as_a args  in
                  lift_binary () ()
                    (fun a420  ->
                       fun a421  -> (Obj.magic (f res.psc_range)) a420 a421)
                    uu____5512)) a422 a423 a424 a425 a426
     in
  let as_primitive_step is_strong uu____5539 =
    match uu____5539 with
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
    unary_op () (fun a427  -> (Obj.magic arg_as_int) a427)
      (fun a428  ->
         fun a429  ->
           (Obj.magic
              (fun r  ->
                 fun x  ->
                   let uu____5587 = f x  in
                   FStar_Syntax_Embeddings.embed_int r uu____5587)) a428 a429)
     in
  let binary_int_op f =
    binary_op () (fun a430  -> (Obj.magic arg_as_int) a430)
      (fun a431  ->
         fun a432  ->
           fun a433  ->
             (Obj.magic
                (fun r  ->
                   fun x  ->
                     fun y  ->
                       let uu____5615 = f x y  in
                       FStar_Syntax_Embeddings.embed_int r uu____5615)) a431
               a432 a433)
     in
  let unary_bool_op f =
    unary_op () (fun a434  -> (Obj.magic arg_as_bool) a434)
      (fun a435  ->
         fun a436  ->
           (Obj.magic
              (fun r  ->
                 fun x  ->
                   let uu____5636 = f x  in
                   FStar_Syntax_Embeddings.embed_bool r uu____5636)) a435
             a436)
     in
  let binary_bool_op f =
    binary_op () (fun a437  -> (Obj.magic arg_as_bool) a437)
      (fun a438  ->
         fun a439  ->
           fun a440  ->
             (Obj.magic
                (fun r  ->
                   fun x  ->
                     fun y  ->
                       let uu____5664 = f x y  in
                       FStar_Syntax_Embeddings.embed_bool r uu____5664)) a438
               a439 a440)
     in
  let binary_string_op f =
    binary_op () (fun a441  -> (Obj.magic arg_as_string) a441)
      (fun a442  ->
         fun a443  ->
           fun a444  ->
             (Obj.magic
                (fun r  ->
                   fun x  ->
                     fun y  ->
                       let uu____5692 = f x y  in
                       FStar_Syntax_Embeddings.embed_string r uu____5692))
               a442 a443 a444)
     in
  let mixed_binary_op a b c as_a as_b embed_c f res args =
    match args with
    | a::b::[] ->
        let uu____5800 =
          let uu____5809 = as_a a  in
          let uu____5812 = as_b b  in (uu____5809, uu____5812)  in
        (match uu____5800 with
         | (FStar_Pervasives_Native.Some a1,FStar_Pervasives_Native.Some b1)
             ->
             let uu____5827 =
               let uu____5828 = f res.psc_range a1 b1  in
               embed_c res.psc_range uu____5828  in
             FStar_Pervasives_Native.Some uu____5827
         | uu____5829 -> FStar_Pervasives_Native.None)
    | uu____5838 -> FStar_Pervasives_Native.None  in
  let list_of_string' rng s =
    let name l =
      let uu____5852 =
        let uu____5853 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant
            FStar_Pervasives_Native.None
           in
        FStar_Syntax_Syntax.Tm_fvar uu____5853  in
      mk uu____5852 rng  in
    let char_t = name FStar_Parser_Const.char_lid  in
    let charterm c =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c)) rng  in
    let uu____5863 =
      let uu____5866 = FStar_String.list_of_string s  in
      FStar_List.map charterm uu____5866  in
    FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu____5863  in
  let string_of_list' rng l =
    let s = FStar_String.string_of_list l  in FStar_Syntax_Util.exp_string s
     in
  let string_compare' rng s1 s2 =
    let r = FStar_String.compare s1 s2  in
    let uu____5898 =
      let uu____5899 = FStar_Util.string_of_int r  in
      FStar_BigInt.big_int_of_string uu____5899  in
    FStar_Syntax_Embeddings.embed_int rng uu____5898  in
  let string_concat' psc args =
    match args with
    | a1::a2::[] ->
        let uu____5917 = arg_as_string a1  in
        (match uu____5917 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____5923 =
               Obj.magic
                 (arg_as_list ()
                    (Obj.magic FStar_Syntax_Embeddings.unembed_string_safe)
                    a2)
                in
             (match uu____5923 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2  in
                  let uu____5936 =
                    FStar_Syntax_Embeddings.embed_string psc.psc_range r  in
                  FStar_Pervasives_Native.Some uu____5936
              | uu____5937 -> FStar_Pervasives_Native.None)
         | uu____5942 -> FStar_Pervasives_Native.None)
    | uu____5945 -> FStar_Pervasives_Native.None  in
  let string_of_int1 rng i =
    let uu____5955 = FStar_BigInt.string_of_big_int i  in
    FStar_Syntax_Embeddings.embed_string rng uu____5955  in
  let string_of_bool1 rng b =
    FStar_Syntax_Embeddings.embed_string rng (if b then "true" else "false")
     in
  let mk_range1 psc args =
    match args with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____5984 =
          let uu____6005 = arg_as_string fn  in
          let uu____6008 = arg_as_int from_line  in
          let uu____6011 = arg_as_int from_col  in
          let uu____6014 = arg_as_int to_line  in
          let uu____6017 = arg_as_int to_col  in
          (uu____6005, uu____6008, uu____6011, uu____6014, uu____6017)  in
        (match uu____5984 with
         | (FStar_Pervasives_Native.Some fn1,FStar_Pervasives_Native.Some
            from_l,FStar_Pervasives_Native.Some
            from_c,FStar_Pervasives_Native.Some
            to_l,FStar_Pervasives_Native.Some to_c) ->
             let r =
               let uu____6048 =
                 let uu____6049 = FStar_BigInt.to_int_fs from_l  in
                 let uu____6050 = FStar_BigInt.to_int_fs from_c  in
                 FStar_Range.mk_pos uu____6049 uu____6050  in
               let uu____6051 =
                 let uu____6052 = FStar_BigInt.to_int_fs to_l  in
                 let uu____6053 = FStar_BigInt.to_int_fs to_c  in
                 FStar_Range.mk_pos uu____6052 uu____6053  in
               FStar_Range.mk_range fn1 uu____6048 uu____6051  in
             let uu____6054 =
               FStar_Syntax_Embeddings.embed_range psc.psc_range r  in
             FStar_Pervasives_Native.Some uu____6054
         | uu____6055 -> FStar_Pervasives_Native.None)
    | uu____6076 -> FStar_Pervasives_Native.None  in
  let decidable_eq neg psc args =
    let r = psc.psc_range  in
    let tru =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool true)) r
       in
    let fal =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool false)) r
       in
    match args with
    | (_typ,uu____6103)::(a1,uu____6105)::(a2,uu____6107)::[] ->
        let uu____6144 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____6144 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some (if neg then fal else tru)
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some (if neg then tru else fal)
         | uu____6157 -> FStar_Pervasives_Native.None)
    | uu____6158 -> failwith "Unexpected number of arguments"  in
  let prims_to_fstar_range_step psc args =
    match args with
    | (a1,uu____6185)::[] ->
        let uu____6194 = FStar_Syntax_Embeddings.unembed_range_safe a1  in
        (match uu____6194 with
         | FStar_Pervasives_Native.Some r ->
             let uu____6200 =
               FStar_Syntax_Embeddings.embed_range psc.psc_range r  in
             FStar_Pervasives_Native.Some uu____6200
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
    | uu____6201 -> failwith "Unexpected number of arguments"  in
  let basic_ops =
    let uu____6225 =
      let uu____6240 =
        let uu____6255 =
          let uu____6270 =
            let uu____6285 =
              let uu____6300 =
                let uu____6315 =
                  let uu____6330 =
                    let uu____6345 =
                      let uu____6360 =
                        let uu____6375 =
                          let uu____6390 =
                            let uu____6405 =
                              let uu____6420 =
                                let uu____6435 =
                                  let uu____6450 =
                                    let uu____6465 =
                                      let uu____6480 =
                                        let uu____6495 =
                                          let uu____6510 =
                                            let uu____6525 =
                                              let uu____6540 =
                                                let uu____6553 =
                                                  FStar_Parser_Const.p2l
                                                    ["FStar";
                                                    "String";
                                                    "list_of_string"]
                                                   in
                                                (uu____6553,
                                                  (Prims.parse_int "1"),
                                                  (unary_op ()
                                                     (fun a445  ->
                                                        (Obj.magic
                                                           arg_as_string)
                                                          a445)
                                                     (fun a446  ->
                                                        fun a447  ->
                                                          (Obj.magic
                                                             list_of_string')
                                                            a446 a447)))
                                                 in
                                              let uu____6560 =
                                                let uu____6575 =
                                                  let uu____6588 =
                                                    FStar_Parser_Const.p2l
                                                      ["FStar";
                                                      "String";
                                                      "string_of_list"]
                                                     in
                                                  (uu____6588,
                                                    (Prims.parse_int "1"),
                                                    (unary_op ()
                                                       (fun a448  ->
                                                          (Obj.magic
                                                             (arg_as_list ()
                                                                (Obj.magic
                                                                   FStar_Syntax_Embeddings.unembed_char_safe)))
                                                            a448)
                                                       (fun a449  ->
                                                          fun a450  ->
                                                            (Obj.magic
                                                               string_of_list')
                                                              a449 a450)))
                                                   in
                                                let uu____6595 =
                                                  let uu____6610 =
                                                    let uu____6625 =
                                                      FStar_Parser_Const.p2l
                                                        ["FStar";
                                                        "String";
                                                        "concat"]
                                                       in
                                                    (uu____6625,
                                                      (Prims.parse_int "2"),
                                                      string_concat')
                                                     in
                                                  let uu____6634 =
                                                    let uu____6651 =
                                                      let uu____6666 =
                                                        FStar_Parser_Const.p2l
                                                          ["Prims";
                                                          "mk_range"]
                                                         in
                                                      (uu____6666,
                                                        (Prims.parse_int "5"),
                                                        mk_range1)
                                                       in
                                                    [uu____6651]  in
                                                  uu____6610 :: uu____6634
                                                   in
                                                uu____6575 :: uu____6595  in
                                              uu____6540 :: uu____6560  in
                                            (FStar_Parser_Const.op_notEq,
                                              (Prims.parse_int "3"),
                                              (decidable_eq true)) ::
                                              uu____6525
                                             in
                                          (FStar_Parser_Const.op_Eq,
                                            (Prims.parse_int "3"),
                                            (decidable_eq false)) ::
                                            uu____6510
                                           in
                                        (FStar_Parser_Const.string_compare,
                                          (Prims.parse_int "2"),
                                          (binary_op ()
                                             (fun a451  ->
                                                (Obj.magic arg_as_string)
                                                  a451)
                                             (fun a452  ->
                                                fun a453  ->
                                                  fun a454  ->
                                                    (Obj.magic
                                                       string_compare') a452
                                                      a453 a454)))
                                          :: uu____6495
                                         in
                                      (FStar_Parser_Const.string_of_bool_lid,
                                        (Prims.parse_int "1"),
                                        (unary_op ()
                                           (fun a455  ->
                                              (Obj.magic arg_as_bool) a455)
                                           (fun a456  ->
                                              fun a457  ->
                                                (Obj.magic string_of_bool1)
                                                  a456 a457)))
                                        :: uu____6480
                                       in
                                    (FStar_Parser_Const.string_of_int_lid,
                                      (Prims.parse_int "1"),
                                      (unary_op ()
                                         (fun a458  ->
                                            (Obj.magic arg_as_int) a458)
                                         (fun a459  ->
                                            fun a460  ->
                                              (Obj.magic string_of_int1) a459
                                                a460)))
                                      :: uu____6465
                                     in
                                  (FStar_Parser_Const.str_make_lid,
                                    (Prims.parse_int "2"),
                                    (mixed_binary_op () () ()
                                       (fun a461  ->
                                          (Obj.magic arg_as_int) a461)
                                       (fun a462  ->
                                          (Obj.magic arg_as_char) a462)
                                       (fun a463  ->
                                          fun a464  ->
                                            (Obj.magic
                                               FStar_Syntax_Embeddings.embed_string)
                                              a463 a464)
                                       (fun a465  ->
                                          fun a466  ->
                                            fun a467  ->
                                              (Obj.magic
                                                 (fun r  ->
                                                    fun x  ->
                                                      fun y  ->
                                                        let uu____6857 =
                                                          FStar_BigInt.to_int_fs
                                                            x
                                                           in
                                                        FStar_String.make
                                                          uu____6857 y)) a465
                                                a466 a467)))
                                    :: uu____6450
                                   in
                                (FStar_Parser_Const.strcat_lid',
                                  (Prims.parse_int "2"),
                                  (binary_string_op
                                     (fun x  -> fun y  -> Prims.strcat x y)))
                                  :: uu____6435
                                 in
                              (FStar_Parser_Const.strcat_lid,
                                (Prims.parse_int "2"),
                                (binary_string_op
                                   (fun x  -> fun y  -> Prims.strcat x y)))
                                :: uu____6420
                               in
                            (FStar_Parser_Const.op_Or, (Prims.parse_int "2"),
                              (binary_bool_op (fun x  -> fun y  -> x || y)))
                              :: uu____6405
                             in
                          (FStar_Parser_Const.op_And, (Prims.parse_int "2"),
                            (binary_bool_op (fun x  -> fun y  -> x && y))) ::
                            uu____6390
                           in
                        (FStar_Parser_Const.op_Negation,
                          (Prims.parse_int "1"),
                          (unary_bool_op (fun x  -> Prims.op_Negation x))) ::
                          uu____6375
                         in
                      (FStar_Parser_Const.op_Modulus, (Prims.parse_int "2"),
                        (binary_int_op
                           (fun x  -> fun y  -> FStar_BigInt.mod_big_int x y)))
                        :: uu____6360
                       in
                    (FStar_Parser_Const.op_GTE, (Prims.parse_int "2"),
                      (binary_op ()
                         (fun a468  -> (Obj.magic arg_as_int) a468)
                         (fun a469  ->
                            fun a470  ->
                              fun a471  ->
                                (Obj.magic
                                   (fun r  ->
                                      fun x  ->
                                        fun y  ->
                                          let uu____7024 =
                                            FStar_BigInt.ge_big_int x y  in
                                          FStar_Syntax_Embeddings.embed_bool
                                            r uu____7024)) a469 a470 a471)))
                      :: uu____6345
                     in
                  (FStar_Parser_Const.op_GT, (Prims.parse_int "2"),
                    (binary_op () (fun a472  -> (Obj.magic arg_as_int) a472)
                       (fun a473  ->
                          fun a474  ->
                            fun a475  ->
                              (Obj.magic
                                 (fun r  ->
                                    fun x  ->
                                      fun y  ->
                                        let uu____7050 =
                                          FStar_BigInt.gt_big_int x y  in
                                        FStar_Syntax_Embeddings.embed_bool r
                                          uu____7050)) a473 a474 a475)))
                    :: uu____6330
                   in
                (FStar_Parser_Const.op_LTE, (Prims.parse_int "2"),
                  (binary_op () (fun a476  -> (Obj.magic arg_as_int) a476)
                     (fun a477  ->
                        fun a478  ->
                          fun a479  ->
                            (Obj.magic
                               (fun r  ->
                                  fun x  ->
                                    fun y  ->
                                      let uu____7076 =
                                        FStar_BigInt.le_big_int x y  in
                                      FStar_Syntax_Embeddings.embed_bool r
                                        uu____7076)) a477 a478 a479)))
                  :: uu____6315
                 in
              (FStar_Parser_Const.op_LT, (Prims.parse_int "2"),
                (binary_op () (fun a480  -> (Obj.magic arg_as_int) a480)
                   (fun a481  ->
                      fun a482  ->
                        fun a483  ->
                          (Obj.magic
                             (fun r  ->
                                fun x  ->
                                  fun y  ->
                                    let uu____7102 =
                                      FStar_BigInt.lt_big_int x y  in
                                    FStar_Syntax_Embeddings.embed_bool r
                                      uu____7102)) a481 a482 a483)))
                :: uu____6300
               in
            (FStar_Parser_Const.op_Division, (Prims.parse_int "2"),
              (binary_int_op
                 (fun x  -> fun y  -> FStar_BigInt.div_big_int x y)))
              :: uu____6285
             in
          (FStar_Parser_Const.op_Multiply, (Prims.parse_int "2"),
            (binary_int_op
               (fun x  -> fun y  -> FStar_BigInt.mult_big_int x y)))
            :: uu____6270
           in
        (FStar_Parser_Const.op_Subtraction, (Prims.parse_int "2"),
          (binary_int_op (fun x  -> fun y  -> FStar_BigInt.sub_big_int x y)))
          :: uu____6255
         in
      (FStar_Parser_Const.op_Addition, (Prims.parse_int "2"),
        (binary_int_op (fun x  -> fun y  -> FStar_BigInt.add_big_int x y)))
        :: uu____6240
       in
    (FStar_Parser_Const.op_Minus, (Prims.parse_int "1"),
      (unary_int_op (fun x  -> FStar_BigInt.minus_big_int x))) :: uu____6225
     in
  let weak_ops =
    let uu____7241 =
      let uu____7260 =
        FStar_Parser_Const.p2l ["FStar"; "Range"; "prims_to_fstar_range"]  in
      (uu____7260, (Prims.parse_int "1"), prims_to_fstar_range_step)  in
    [uu____7241]  in
  let bounded_arith_ops =
    let bounded_signed_int_types = ["Int8"; "Int16"; "Int32"; "Int64"]  in
    let bounded_unsigned_int_types =
      ["UInt8"; "UInt16"; "UInt32"; "UInt64"; "UInt128"]  in
    let int_as_bounded r int_to_t1 n1 =
      let c = FStar_Syntax_Embeddings.embed_int r n1  in
      let int_to_t2 = FStar_Syntax_Syntax.fv_to_tm int_to_t1  in
      let uu____7344 =
        let uu____7345 =
          let uu____7346 = FStar_Syntax_Syntax.as_arg c  in [uu____7346]  in
        FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____7345  in
      uu____7344 FStar_Pervasives_Native.None r  in
    let add_sub_mul_v =
      FStar_All.pipe_right
        (FStar_List.append bounded_signed_int_types
           bounded_unsigned_int_types)
        (FStar_List.collect
           (fun m  ->
              let uu____7396 =
                let uu____7409 = FStar_Parser_Const.p2l ["FStar"; m; "add"]
                   in
                (uu____7409, (Prims.parse_int "2"),
                  (binary_op ()
                     (fun a484  -> (Obj.magic arg_as_bounded_int) a484)
                     (fun a485  ->
                        fun a486  ->
                          fun a487  ->
                            (Obj.magic
                               (fun r  ->
                                  fun uu____7425  ->
                                    fun uu____7426  ->
                                      match (uu____7425, uu____7426) with
                                      | ((int_to_t1,x),(uu____7445,y)) ->
                                          let uu____7455 =
                                            FStar_BigInt.add_big_int x y  in
                                          int_as_bounded r int_to_t1
                                            uu____7455)) a485 a486 a487)))
                 in
              let uu____7456 =
                let uu____7471 =
                  let uu____7484 = FStar_Parser_Const.p2l ["FStar"; m; "sub"]
                     in
                  (uu____7484, (Prims.parse_int "2"),
                    (binary_op ()
                       (fun a488  -> (Obj.magic arg_as_bounded_int) a488)
                       (fun a489  ->
                          fun a490  ->
                            fun a491  ->
                              (Obj.magic
                                 (fun r  ->
                                    fun uu____7500  ->
                                      fun uu____7501  ->
                                        match (uu____7500, uu____7501) with
                                        | ((int_to_t1,x),(uu____7520,y)) ->
                                            let uu____7530 =
                                              FStar_BigInt.sub_big_int x y
                                               in
                                            int_as_bounded r int_to_t1
                                              uu____7530)) a489 a490 a491)))
                   in
                let uu____7531 =
                  let uu____7546 =
                    let uu____7559 =
                      FStar_Parser_Const.p2l ["FStar"; m; "mul"]  in
                    (uu____7559, (Prims.parse_int "2"),
                      (binary_op ()
                         (fun a492  -> (Obj.magic arg_as_bounded_int) a492)
                         (fun a493  ->
                            fun a494  ->
                              fun a495  ->
                                (Obj.magic
                                   (fun r  ->
                                      fun uu____7575  ->
                                        fun uu____7576  ->
                                          match (uu____7575, uu____7576) with
                                          | ((int_to_t1,x),(uu____7595,y)) ->
                                              let uu____7605 =
                                                FStar_BigInt.mult_big_int x y
                                                 in
                                              int_as_bounded r int_to_t1
                                                uu____7605)) a493 a494 a495)))
                     in
                  let uu____7606 =
                    let uu____7621 =
                      let uu____7634 =
                        FStar_Parser_Const.p2l ["FStar"; m; "v"]  in
                      (uu____7634, (Prims.parse_int "1"),
                        (unary_op ()
                           (fun a496  -> (Obj.magic arg_as_bounded_int) a496)
                           (fun a497  ->
                              fun a498  ->
                                (Obj.magic
                                   (fun r  ->
                                      fun uu____7646  ->
                                        match uu____7646 with
                                        | (int_to_t1,x) ->
                                            FStar_Syntax_Embeddings.embed_int
                                              r x)) a497 a498)))
                       in
                    [uu____7621]  in
                  uu____7546 :: uu____7606  in
                uu____7471 :: uu____7531  in
              uu____7396 :: uu____7456))
       in
    let div_mod_unsigned =
      FStar_All.pipe_right bounded_unsigned_int_types
        (FStar_List.collect
           (fun m  ->
              let uu____7760 =
                let uu____7773 = FStar_Parser_Const.p2l ["FStar"; m; "div"]
                   in
                (uu____7773, (Prims.parse_int "2"),
                  (binary_op ()
                     (fun a499  -> (Obj.magic arg_as_bounded_int) a499)
                     (fun a500  ->
                        fun a501  ->
                          fun a502  ->
                            (Obj.magic
                               (fun r  ->
                                  fun uu____7789  ->
                                    fun uu____7790  ->
                                      match (uu____7789, uu____7790) with
                                      | ((int_to_t1,x),(uu____7809,y)) ->
                                          let uu____7819 =
                                            FStar_BigInt.div_big_int x y  in
                                          int_as_bounded r int_to_t1
                                            uu____7819)) a500 a501 a502)))
                 in
              let uu____7820 =
                let uu____7835 =
                  let uu____7848 = FStar_Parser_Const.p2l ["FStar"; m; "rem"]
                     in
                  (uu____7848, (Prims.parse_int "2"),
                    (binary_op ()
                       (fun a503  -> (Obj.magic arg_as_bounded_int) a503)
                       (fun a504  ->
                          fun a505  ->
                            fun a506  ->
                              (Obj.magic
                                 (fun r  ->
                                    fun uu____7864  ->
                                      fun uu____7865  ->
                                        match (uu____7864, uu____7865) with
                                        | ((int_to_t1,x),(uu____7884,y)) ->
                                            let uu____7894 =
                                              FStar_BigInt.mod_big_int x y
                                               in
                                            int_as_bounded r int_to_t1
                                              uu____7894)) a504 a505 a506)))
                   in
                [uu____7835]  in
              uu____7760 :: uu____7820))
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
    | (_typ,uu____8006)::(a1,uu____8008)::(a2,uu____8010)::[] ->
        let uu____8047 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____8047 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___138_8053 = FStar_Syntax_Util.t_true  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___138_8053.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___138_8053.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___139_8057 = FStar_Syntax_Util.t_false  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___139_8057.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___139_8057.FStar_Syntax_Syntax.vars)
                })
         | uu____8058 -> FStar_Pervasives_Native.None)
    | (_typ,uu____8060)::uu____8061::(a1,uu____8063)::(a2,uu____8065)::[] ->
        let uu____8114 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____8114 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___138_8120 = FStar_Syntax_Util.t_true  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___138_8120.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___138_8120.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___139_8124 = FStar_Syntax_Util.t_false  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___139_8124.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___139_8124.FStar_Syntax_Syntax.vars)
                })
         | uu____8125 -> FStar_Pervasives_Native.None)
    | uu____8126 -> failwith "Unexpected number of arguments"  in
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
    let uu____8178 = FStar_ST.op_Bang unembed_binder_knot  in
    match uu____8178 with
    | FStar_Pervasives_Native.Some f -> f t
    | FStar_Pervasives_Native.None  ->
        (FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos
           (FStar_Errors.Warning_UnembedBinderKnot,
             "unembed_binder_knot is unset!");
         FStar_Pervasives_Native.None)
  
let mk_psc_subst :
  'Auu____8225 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____8225) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_Syntax_Syntax.subst_elt Prims.list
  =
  fun cfg  ->
    fun env  ->
      FStar_List.fold_right
        (fun uu____8285  ->
           fun subst1  ->
             match uu____8285 with
             | (binder_opt,closure) ->
                 (match (binder_opt, closure) with
                  | (FStar_Pervasives_Native.Some b,Clos
                     (env1,term,uu____8326,uu____8327)) ->
                      let uu____8386 = b  in
                      (match uu____8386 with
                       | (bv,uu____8394) ->
                           let uu____8395 =
                             let uu____8396 =
                               FStar_Syntax_Util.is_constructed_typ
                                 bv.FStar_Syntax_Syntax.sort
                                 FStar_Parser_Const.binder_lid
                                in
                             Prims.op_Negation uu____8396  in
                           if uu____8395
                           then subst1
                           else
                             (let term1 = closure_as_term cfg env1 term  in
                              let uu____8401 = unembed_binder term1  in
                              match uu____8401 with
                              | FStar_Pervasives_Native.None  -> subst1
                              | FStar_Pervasives_Native.Some x ->
                                  let b1 =
                                    let uu____8408 =
                                      let uu___140_8409 = bv  in
                                      let uu____8410 =
                                        FStar_Syntax_Subst.subst subst1
                                          (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort
                                         in
                                      {
                                        FStar_Syntax_Syntax.ppname =
                                          (uu___140_8409.FStar_Syntax_Syntax.ppname);
                                        FStar_Syntax_Syntax.index =
                                          (uu___140_8409.FStar_Syntax_Syntax.index);
                                        FStar_Syntax_Syntax.sort = uu____8410
                                      }  in
                                    FStar_Syntax_Syntax.freshen_bv uu____8408
                                     in
                                  let b_for_x =
                                    let uu____8414 =
                                      let uu____8421 =
                                        FStar_Syntax_Syntax.bv_to_name b1  in
                                      ((FStar_Pervasives_Native.fst x),
                                        uu____8421)
                                       in
                                    FStar_Syntax_Syntax.NT uu____8414  in
                                  let subst2 =
                                    FStar_List.filter
                                      (fun uu___85_8431  ->
                                         match uu___85_8431 with
                                         | FStar_Syntax_Syntax.NT
                                             (uu____8432,{
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_name
                                                             b';
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____8434;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____8435;_})
                                             ->
                                             let uu____8440 =
                                               FStar_Ident.ident_equals
                                                 b1.FStar_Syntax_Syntax.ppname
                                                 b'.FStar_Syntax_Syntax.ppname
                                                in
                                             Prims.op_Negation uu____8440
                                         | uu____8441 -> true) subst1
                                     in
                                  b_for_x :: subst2))
                  | uu____8442 -> subst1)) env []
  
let reduce_primops :
  'Auu____8459 'Auu____8460 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____8459) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____8460 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          if Prims.op_Negation (cfg.steps).primops
          then tm
          else
            (let uu____8502 = FStar_Syntax_Util.head_and_args tm  in
             match uu____8502 with
             | (head1,args) ->
                 let uu____8539 =
                   let uu____8540 = FStar_Syntax_Util.un_uinst head1  in
                   uu____8540.FStar_Syntax_Syntax.n  in
                 (match uu____8539 with
                  | FStar_Syntax_Syntax.Tm_fvar fv ->
                      let uu____8544 = find_prim_step cfg fv  in
                      (match uu____8544 with
                       | FStar_Pervasives_Native.Some prim_step when
                           prim_step.strong_reduction_ok ||
                             (Prims.op_Negation cfg.strong)
                           ->
                           if (FStar_List.length args) < prim_step.arity
                           then
                             (log_primops cfg
                                (fun uu____8559  ->
                                   let uu____8560 =
                                     FStar_Syntax_Print.lid_to_string
                                       prim_step.name
                                      in
                                   let uu____8561 =
                                     FStar_Util.string_of_int
                                       (FStar_List.length args)
                                      in
                                   let uu____8568 =
                                     FStar_Util.string_of_int prim_step.arity
                                      in
                                   FStar_Util.print3
                                     "primop: found partially applied %s (%s/%s args)\n"
                                     uu____8560 uu____8561 uu____8568);
                              tm)
                           else
                             (log_primops cfg
                                (fun uu____8573  ->
                                   let uu____8574 =
                                     FStar_Syntax_Print.term_to_string tm  in
                                   FStar_Util.print1
                                     "primop: trying to reduce <%s>\n"
                                     uu____8574);
                              (let psc =
                                 {
                                   psc_range =
                                     (head1.FStar_Syntax_Syntax.pos);
                                   psc_subst =
                                     (fun uu____8577  ->
                                        if
                                          prim_step.requires_binder_substitution
                                        then mk_psc_subst cfg env
                                        else [])
                                 }  in
                               let uu____8579 =
                                 prim_step.interpretation psc args  in
                               match uu____8579 with
                               | FStar_Pervasives_Native.None  ->
                                   (log_primops cfg
                                      (fun uu____8585  ->
                                         let uu____8586 =
                                           FStar_Syntax_Print.term_to_string
                                             tm
                                            in
                                         FStar_Util.print1
                                           "primop: <%s> did not reduce\n"
                                           uu____8586);
                                    tm)
                               | FStar_Pervasives_Native.Some reduced ->
                                   (log_primops cfg
                                      (fun uu____8592  ->
                                         let uu____8593 =
                                           FStar_Syntax_Print.term_to_string
                                             tm
                                            in
                                         let uu____8594 =
                                           FStar_Syntax_Print.term_to_string
                                             reduced
                                            in
                                         FStar_Util.print2
                                           "primop: <%s> reduced to <%s>\n"
                                           uu____8593 uu____8594);
                                    reduced)))
                       | FStar_Pervasives_Native.Some uu____8595 ->
                           (log_primops cfg
                              (fun uu____8599  ->
                                 let uu____8600 =
                                   FStar_Syntax_Print.term_to_string tm  in
                                 FStar_Util.print1
                                   "primop: not reducing <%s> since we're doing strong reduction\n"
                                   uu____8600);
                            tm)
                       | FStar_Pervasives_Native.None  -> tm)
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_range_of ) when
                      Prims.op_Negation cfg.strong ->
                      (log_primops cfg
                         (fun uu____8604  ->
                            let uu____8605 =
                              FStar_Syntax_Print.term_to_string tm  in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____8605);
                       (match args with
                        | (a1,uu____8607)::[] ->
                            FStar_Syntax_Embeddings.embed_range
                              tm.FStar_Syntax_Syntax.pos
                              a1.FStar_Syntax_Syntax.pos
                        | uu____8624 -> tm))
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_set_range_of ) when
                      Prims.op_Negation cfg.strong ->
                      (log_primops cfg
                         (fun uu____8636  ->
                            let uu____8637 =
                              FStar_Syntax_Print.term_to_string tm  in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____8637);
                       (match args with
                        | (t,uu____8639)::(r,uu____8641)::[] ->
                            let uu____8668 =
                              FStar_Syntax_Embeddings.unembed_range r  in
                            (match uu____8668 with
                             | FStar_Pervasives_Native.Some rng ->
                                 let uu___141_8672 = t  in
                                 {
                                   FStar_Syntax_Syntax.n =
                                     (uu___141_8672.FStar_Syntax_Syntax.n);
                                   FStar_Syntax_Syntax.pos = rng;
                                   FStar_Syntax_Syntax.vars =
                                     (uu___141_8672.FStar_Syntax_Syntax.vars)
                                 }
                             | FStar_Pervasives_Native.None  -> tm)
                        | uu____8675 -> tm))
                  | uu____8684 -> tm))
  
let reduce_equality :
  'Auu____8689 'Auu____8690 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____8689) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____8690 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun tm  ->
      reduce_primops
        (let uu___142_8728 = cfg  in
         {
           steps =
             (let uu___143_8731 = default_steps  in
              {
                beta = (uu___143_8731.beta);
                iota = (uu___143_8731.iota);
                zeta = (uu___143_8731.zeta);
                weak = (uu___143_8731.weak);
                hnf = (uu___143_8731.hnf);
                primops = true;
                no_delta_steps = (uu___143_8731.no_delta_steps);
                unfold_until = (uu___143_8731.unfold_until);
                unfold_only = (uu___143_8731.unfold_only);
                unfold_attr = (uu___143_8731.unfold_attr);
                unfold_tac = (uu___143_8731.unfold_tac);
                pure_subterms_within_computations =
                  (uu___143_8731.pure_subterms_within_computations);
                simplify = (uu___143_8731.simplify);
                erase_universes = (uu___143_8731.erase_universes);
                allow_unbound_universes =
                  (uu___143_8731.allow_unbound_universes);
                reify_ = (uu___143_8731.reify_);
                compress_uvars = (uu___143_8731.compress_uvars);
                no_full_norm = (uu___143_8731.no_full_norm);
                check_no_uvars = (uu___143_8731.check_no_uvars);
                unmeta = (uu___143_8731.unmeta);
                unascribe = (uu___143_8731.unascribe)
              });
           tcenv = (uu___142_8728.tcenv);
           debug = (uu___142_8728.debug);
           delta_level = (uu___142_8728.delta_level);
           primitive_steps = equality_ops;
           strong = (uu___142_8728.strong);
           memoize_lazy = (uu___142_8728.memoize_lazy);
           normalize_pure_lets = (uu___142_8728.normalize_pure_lets)
         }) tm
  
let is_norm_request :
  'Auu____8735 .
    FStar_Syntax_Syntax.term -> 'Auu____8735 Prims.list -> Prims.bool
  =
  fun hd1  ->
    fun args  ->
      let uu____8748 =
        let uu____8755 =
          let uu____8756 = FStar_Syntax_Util.un_uinst hd1  in
          uu____8756.FStar_Syntax_Syntax.n  in
        (uu____8755, args)  in
      match uu____8748 with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____8762::uu____8763::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____8767::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize
      | (FStar_Syntax_Syntax.Tm_fvar fv,steps::uu____8772::uu____8773::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm
      | uu____8776 -> false
  
let (tr_norm_step : FStar_Syntax_Embeddings.norm_step -> step Prims.list) =
  fun uu___86_8787  ->
    match uu___86_8787 with
    | FStar_Syntax_Embeddings.Zeta  -> [Zeta]
    | FStar_Syntax_Embeddings.Iota  -> [Iota]
    | FStar_Syntax_Embeddings.Delta  ->
        [UnfoldUntil FStar_Syntax_Syntax.Delta_constant]
    | FStar_Syntax_Embeddings.Simpl  -> [Simplify]
    | FStar_Syntax_Embeddings.Weak  -> [Weak]
    | FStar_Syntax_Embeddings.HNF  -> [HNF]
    | FStar_Syntax_Embeddings.Primops  -> [Primops]
    | FStar_Syntax_Embeddings.UnfoldOnly names1 ->
        let uu____8793 =
          let uu____8796 =
            let uu____8797 = FStar_List.map FStar_Ident.lid_of_str names1  in
            UnfoldOnly uu____8797  in
          [uu____8796]  in
        (UnfoldUntil FStar_Syntax_Syntax.Delta_constant) :: uu____8793
    | FStar_Syntax_Embeddings.UnfoldAttr t ->
        [UnfoldUntil FStar_Syntax_Syntax.Delta_constant; UnfoldAttr t]
  
let (tr_norm_steps :
  FStar_Syntax_Embeddings.norm_step Prims.list -> step Prims.list) =
  fun s  -> FStar_List.concatMap tr_norm_step s 
let get_norm_request :
  'Auu____8813 .
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
      (FStar_Syntax_Syntax.term,'Auu____8813) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (step Prims.list,FStar_Syntax_Syntax.term)
          FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun full_norm  ->
    fun args  ->
      let parse_steps s =
        try
          let uu____8866 =
            let uu____8869 =
              let uu____8872 =
                let uu____8877 =
                  FStar_Syntax_Embeddings.unembed_list_safe
                    FStar_Syntax_Embeddings.unembed_norm_step
                   in
                uu____8877 s  in
              FStar_All.pipe_right uu____8872 FStar_Util.must  in
            FStar_All.pipe_right uu____8869 tr_norm_steps  in
          FStar_Pervasives_Native.Some uu____8866
        with | uu____8905 -> FStar_Pervasives_Native.None  in
      match args with
      | uu____8916::(tm,uu____8918)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify]  in
          FStar_Pervasives_Native.Some (s, tm)
      | (tm,uu____8947)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify]  in
          FStar_Pervasives_Native.Some (s, tm)
      | (steps,uu____8968)::uu____8969::(tm,uu____8971)::[] ->
          let add_exclude s z =
            if FStar_List.contains z s then s else (Exclude z) :: s  in
          let uu____9008 =
            let uu____9013 = full_norm steps  in parse_steps uu____9013  in
          (match uu____9008 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some s ->
               let s1 = Beta :: s  in
               let s2 = add_exclude s1 Zeta  in
               let s3 = add_exclude s2 Iota  in
               FStar_Pervasives_Native.Some (s3, tm))
      | uu____9052 -> FStar_Pervasives_Native.None
  
let (is_reify_head : stack_elt Prims.list -> Prims.bool) =
  fun uu___87_9069  ->
    match uu___87_9069 with
    | (App
        (uu____9072,{
                      FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                        (FStar_Const.Const_reify );
                      FStar_Syntax_Syntax.pos = uu____9073;
                      FStar_Syntax_Syntax.vars = uu____9074;_},uu____9075,uu____9076))::uu____9077
        -> true
    | uu____9084 -> false
  
let firstn :
  'Auu____9090 .
    Prims.int ->
      'Auu____9090 Prims.list ->
        ('Auu____9090 Prims.list,'Auu____9090 Prims.list)
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
          (uu____9126,{
                        FStar_Syntax_Syntax.n =
                          FStar_Syntax_Syntax.Tm_constant
                          (FStar_Const.Const_reify );
                        FStar_Syntax_Syntax.pos = uu____9127;
                        FStar_Syntax_Syntax.vars = uu____9128;_},uu____9129,uu____9130))::uu____9131
          -> (cfg.steps).reify_
      | uu____9138 -> false
  
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
               | FStar_Syntax_Syntax.Tm_delayed uu____9322 ->
                   let uu____9347 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print1 "NORM delayed: %s\n" uu____9347
               | uu____9348 -> ())
            else ();
            FStar_Syntax_Subst.compress t  in
          log cfg
            (fun uu____9356  ->
               let uu____9357 = FStar_Syntax_Print.tag_of_term t1  in
               let uu____9358 = FStar_Syntax_Print.term_to_string t1  in
               let uu____9359 =
                 FStar_Util.string_of_int (FStar_List.length env)  in
               let uu____9366 =
                 let uu____9367 =
                   let uu____9370 = firstn (Prims.parse_int "4") stack  in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst uu____9370
                    in
                 stack_to_string uu____9367  in
               FStar_Util.print4
                 ">>> %s\nNorm %s with with %s env elements top of the stack %s \n"
                 uu____9357 uu____9358 uu____9359 uu____9366);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_constant uu____9393 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_name uu____9394 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_lazy uu____9395 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____9396;
                 FStar_Syntax_Syntax.fv_delta =
                   FStar_Syntax_Syntax.Delta_constant ;
                 FStar_Syntax_Syntax.fv_qual = uu____9397;_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____9400;
                 FStar_Syntax_Syntax.fv_delta = uu____9401;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Data_ctor );_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____9402;
                 FStar_Syntax_Syntax.fv_delta = uu____9403;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor uu____9404);_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_quoted uu____9411 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               ((Prims.op_Negation (cfg.steps).no_full_norm) &&
                  (is_norm_request hd1 args))
                 &&
                 (let uu____9447 =
                    FStar_Ident.lid_equals
                      (cfg.tcenv).FStar_TypeChecker_Env.curmodule
                      FStar_Parser_Const.prims_lid
                     in
                  Prims.op_Negation uu____9447)
               ->
               let cfg' =
                 let uu___146_9449 = cfg  in
                 {
                   steps =
                     (let uu___147_9452 = cfg.steps  in
                      {
                        beta = (uu___147_9452.beta);
                        iota = (uu___147_9452.iota);
                        zeta = (uu___147_9452.zeta);
                        weak = (uu___147_9452.weak);
                        hnf = (uu___147_9452.hnf);
                        primops = (uu___147_9452.primops);
                        no_delta_steps = false;
                        unfold_until = (uu___147_9452.unfold_until);
                        unfold_only = FStar_Pervasives_Native.None;
                        unfold_attr = (uu___147_9452.unfold_attr);
                        unfold_tac = (uu___147_9452.unfold_tac);
                        pure_subterms_within_computations =
                          (uu___147_9452.pure_subterms_within_computations);
                        simplify = (uu___147_9452.simplify);
                        erase_universes = (uu___147_9452.erase_universes);
                        allow_unbound_universes =
                          (uu___147_9452.allow_unbound_universes);
                        reify_ = (uu___147_9452.reify_);
                        compress_uvars = (uu___147_9452.compress_uvars);
                        no_full_norm = (uu___147_9452.no_full_norm);
                        check_no_uvars = (uu___147_9452.check_no_uvars);
                        unmeta = (uu___147_9452.unmeta);
                        unascribe = (uu___147_9452.unascribe)
                      });
                   tcenv = (uu___146_9449.tcenv);
                   debug = (uu___146_9449.debug);
                   delta_level =
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.Delta_constant];
                   primitive_steps = (uu___146_9449.primitive_steps);
                   strong = (uu___146_9449.strong);
                   memoize_lazy = (uu___146_9449.memoize_lazy);
                   normalize_pure_lets = true
                 }  in
               let uu____9455 = get_norm_request (norm cfg' env []) args  in
               (match uu____9455 with
                | FStar_Pervasives_Native.None  ->
                    let stack1 =
                      FStar_All.pipe_right stack
                        (FStar_List.fold_right
                           (fun uu____9486  ->
                              fun stack1  ->
                                match uu____9486 with
                                | (a,aq) ->
                                    let uu____9498 =
                                      let uu____9499 =
                                        let uu____9506 =
                                          let uu____9507 =
                                            let uu____9538 =
                                              FStar_Util.mk_ref
                                                FStar_Pervasives_Native.None
                                               in
                                            (env, a, uu____9538, false)  in
                                          Clos uu____9507  in
                                        (uu____9506, aq,
                                          (t1.FStar_Syntax_Syntax.pos))
                                         in
                                      Arg uu____9499  in
                                    uu____9498 :: stack1) args)
                       in
                    (log cfg
                       (fun uu____9622  ->
                          let uu____9623 =
                            FStar_All.pipe_left FStar_Util.string_of_int
                              (FStar_List.length args)
                             in
                          FStar_Util.print1 "\tPushed %s arguments\n"
                            uu____9623);
                     norm cfg env stack1 hd1)
                | FStar_Pervasives_Native.Some (s,tm) ->
                    let delta_level =
                      let uu____9645 =
                        FStar_All.pipe_right s
                          (FStar_Util.for_some
                             (fun uu___88_9650  ->
                                match uu___88_9650 with
                                | UnfoldUntil uu____9651 -> true
                                | UnfoldOnly uu____9652 -> true
                                | uu____9655 -> false))
                         in
                      if uu____9645
                      then
                        [FStar_TypeChecker_Env.Unfold
                           FStar_Syntax_Syntax.Delta_constant]
                      else [FStar_TypeChecker_Env.NoDelta]  in
                    let cfg'1 =
                      let uu___148_9660 = cfg  in
                      let uu____9661 = to_fsteps s  in
                      {
                        steps = uu____9661;
                        tcenv = (uu___148_9660.tcenv);
                        debug = (uu___148_9660.debug);
                        delta_level;
                        primitive_steps = (uu___148_9660.primitive_steps);
                        strong = (uu___148_9660.strong);
                        memoize_lazy = (uu___148_9660.memoize_lazy);
                        normalize_pure_lets = true
                      }  in
                    let stack' =
                      let tail1 = (Cfg cfg) :: stack  in
                      if (cfg.debug).print_normalized
                      then
                        let uu____9670 =
                          let uu____9671 =
                            let uu____9676 = FStar_Util.now ()  in
                            (t1, uu____9676)  in
                          Debug uu____9671  in
                        uu____9670 :: tail1
                      else tail1  in
                    norm cfg'1 env stack' tm)
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u  in
               let uu____9680 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack uu____9680
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               if (cfg.steps).erase_universes
               then norm cfg env stack t'
               else
                 (let us1 =
                    let uu____9689 =
                      let uu____9696 =
                        FStar_List.map (norm_universe cfg env) us  in
                      (uu____9696, (t1.FStar_Syntax_Syntax.pos))  in
                    UnivArgs uu____9689  in
                  let stack1 = us1 :: stack  in norm cfg env stack1 t')
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let qninfo =
                 let uu____9706 = FStar_Syntax_Syntax.lid_of_fv fv  in
                 FStar_TypeChecker_Env.lookup_qname cfg.tcenv uu____9706  in
               let uu____9707 = FStar_TypeChecker_Env.qninfo_is_action qninfo
                  in
               if uu____9707
               then
                 let b = should_reify cfg stack  in
                 (log cfg
                    (fun uu____9713  ->
                       let uu____9714 = FStar_Syntax_Print.term_to_string t1
                          in
                       let uu____9715 = FStar_Util.string_of_bool b  in
                       FStar_Util.print2
                         ">>> For DM4F action %s, should_reify = %s\n"
                         uu____9714 uu____9715);
                  if b
                  then
                    (let uu____9716 = FStar_List.tl stack  in
                     do_unfold_fv cfg env uu____9716 t1 qninfo fv)
                  else rebuild cfg env stack t1)
               else
                 (let should_delta =
                    (let uu____9724 = find_prim_step cfg fv  in
                     FStar_Option.isNone uu____9724) &&
                      (FStar_All.pipe_right cfg.delta_level
                         (FStar_Util.for_some
                            (fun uu___89_9730  ->
                               match uu___89_9730 with
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
                          (let uu____9740 =
                             cases
                               (FStar_Util.for_some
                                  (FStar_Syntax_Util.attr_eq
                                     FStar_Syntax_Util.tac_opaque_attr))
                               false attrs
                              in
                           Prims.op_Negation uu____9740))
                         &&
                         ((match (cfg.steps).unfold_only with
                           | FStar_Pervasives_Native.None  -> true
                           | FStar_Pervasives_Native.Some lids ->
                               FStar_Util.for_some
                                 (FStar_Syntax_Syntax.fv_eq_lid fv) lids)
                            ||
                            (match (attrs, ((cfg.steps).unfold_attr)) with
                             | (FStar_Pervasives_Native.None
                                ,FStar_Pervasives_Native.Some uu____9759) ->
                                 false
                             | (FStar_Pervasives_Native.Some
                                ats,FStar_Pervasives_Native.Some ats') ->
                                 FStar_Util.for_some
                                   (fun at  ->
                                      FStar_Util.for_some
                                        (FStar_Syntax_Util.attr_eq at) ats')
                                   ats
                             | (uu____9794,uu____9795) -> false)))
                     in
                  log cfg
                    (fun uu____9817  ->
                       let uu____9818 = FStar_Syntax_Print.term_to_string t1
                          in
                       let uu____9819 =
                         FStar_Range.string_of_range
                           t1.FStar_Syntax_Syntax.pos
                          in
                       let uu____9820 =
                         FStar_Util.string_of_bool should_delta1  in
                       FStar_Util.print3
                         ">>> For %s (%s), should_delta = %s\n" uu____9818
                         uu____9819 uu____9820);
                  if should_delta1
                  then do_unfold_fv cfg env stack t1 qninfo fv
                  else rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____9823 = lookup_bvar env x  in
               (match uu____9823 with
                | Univ uu____9826 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if (Prims.op_Negation fix) || (cfg.steps).zeta
                    then
                      let uu____9875 = FStar_ST.op_Bang r  in
                      (match uu____9875 with
                       | FStar_Pervasives_Native.Some (env2,t') ->
                           (log cfg
                              (fun uu____9993  ->
                                 let uu____9994 =
                                   FStar_Syntax_Print.term_to_string t1  in
                                 let uu____9995 =
                                   FStar_Syntax_Print.term_to_string t'  in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____9994
                                   uu____9995);
                            (let uu____9996 =
                               let uu____9997 =
                                 FStar_Syntax_Subst.compress t'  in
                               uu____9997.FStar_Syntax_Syntax.n  in
                             match uu____9996 with
                             | FStar_Syntax_Syntax.Tm_abs uu____10000 ->
                                 norm cfg env2 stack t'
                             | uu____10017 -> rebuild cfg env2 stack t'))
                       | FStar_Pervasives_Native.None  ->
                           norm cfg env1 ((MemoLazy r) :: stack) t0)
                    else norm cfg env1 stack t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack with
                | (UnivArgs uu____10087)::uu____10088 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Match uu____10097)::uu____10098 ->
                    failwith
                      "Ill-typed term: cannot pattern match an abstraction"
                | (Arg (c,uu____10108,uu____10109))::stack_rest ->
                    (match c with
                     | Univ uu____10113 ->
                         norm cfg ((FStar_Pervasives_Native.None, c) :: env)
                           stack_rest t1
                     | uu____10122 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | b::[] ->
                              (log cfg
                                 (fun uu____10143  ->
                                    let uu____10144 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____10144);
                               norm cfg
                                 (((FStar_Pervasives_Native.Some b), c) ::
                                 env) stack_rest body)
                          | b::tl1 ->
                              (log cfg
                                 (fun uu____10184  ->
                                    let uu____10185 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____10185);
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
                       (fun uu____10263  ->
                          let uu____10264 =
                            FStar_Syntax_Print.term_to_string t1  in
                          FStar_Util.print1 "\tSet memo %s\n" uu____10264);
                     norm cfg env stack1 t1)
                | (Debug uu____10265)::uu____10266 ->
                    if (cfg.steps).weak
                    then
                      let uu____10273 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____10273
                    else
                      (let uu____10275 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____10275 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____10317  -> dummy :: env1) env)
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
                                          let uu____10354 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____10354)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___149_10359 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___149_10359.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___149_10359.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____10360 -> lopt  in
                           (log cfg
                              (fun uu____10366  ->
                                 let uu____10367 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____10367);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___150_10376 = cfg  in
                               {
                                 steps = (uu___150_10376.steps);
                                 tcenv = (uu___150_10376.tcenv);
                                 debug = (uu___150_10376.debug);
                                 delta_level = (uu___150_10376.delta_level);
                                 primitive_steps =
                                   (uu___150_10376.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___150_10376.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___150_10376.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Meta uu____10387)::uu____10388 ->
                    if (cfg.steps).weak
                    then
                      let uu____10395 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____10395
                    else
                      (let uu____10397 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____10397 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____10439  -> dummy :: env1) env)
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
                                          let uu____10476 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____10476)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___149_10481 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___149_10481.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___149_10481.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____10482 -> lopt  in
                           (log cfg
                              (fun uu____10488  ->
                                 let uu____10489 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____10489);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___150_10498 = cfg  in
                               {
                                 steps = (uu___150_10498.steps);
                                 tcenv = (uu___150_10498.tcenv);
                                 debug = (uu___150_10498.debug);
                                 delta_level = (uu___150_10498.delta_level);
                                 primitive_steps =
                                   (uu___150_10498.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___150_10498.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___150_10498.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Let uu____10509)::uu____10510 ->
                    if (cfg.steps).weak
                    then
                      let uu____10521 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____10521
                    else
                      (let uu____10523 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____10523 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____10565  -> dummy :: env1) env)
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
                                          let uu____10602 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____10602)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___149_10607 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___149_10607.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___149_10607.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____10608 -> lopt  in
                           (log cfg
                              (fun uu____10614  ->
                                 let uu____10615 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____10615);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___150_10624 = cfg  in
                               {
                                 steps = (uu___150_10624.steps);
                                 tcenv = (uu___150_10624.tcenv);
                                 debug = (uu___150_10624.debug);
                                 delta_level = (uu___150_10624.delta_level);
                                 primitive_steps =
                                   (uu___150_10624.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___150_10624.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___150_10624.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (App uu____10635)::uu____10636 ->
                    if (cfg.steps).weak
                    then
                      let uu____10647 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____10647
                    else
                      (let uu____10649 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____10649 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____10691  -> dummy :: env1) env)
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
                                          let uu____10728 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____10728)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___149_10733 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___149_10733.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___149_10733.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____10734 -> lopt  in
                           (log cfg
                              (fun uu____10740  ->
                                 let uu____10741 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____10741);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___150_10750 = cfg  in
                               {
                                 steps = (uu___150_10750.steps);
                                 tcenv = (uu___150_10750.tcenv);
                                 debug = (uu___150_10750.debug);
                                 delta_level = (uu___150_10750.delta_level);
                                 primitive_steps =
                                   (uu___150_10750.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___150_10750.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___150_10750.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Abs uu____10761)::uu____10762 ->
                    if (cfg.steps).weak
                    then
                      let uu____10777 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____10777
                    else
                      (let uu____10779 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____10779 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____10821  -> dummy :: env1) env)
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
                                          let uu____10858 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____10858)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___149_10863 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___149_10863.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___149_10863.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____10864 -> lopt  in
                           (log cfg
                              (fun uu____10870  ->
                                 let uu____10871 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____10871);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___150_10880 = cfg  in
                               {
                                 steps = (uu___150_10880.steps);
                                 tcenv = (uu___150_10880.tcenv);
                                 debug = (uu___150_10880.debug);
                                 delta_level = (uu___150_10880.delta_level);
                                 primitive_steps =
                                   (uu___150_10880.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___150_10880.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___150_10880.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | [] ->
                    if (cfg.steps).weak
                    then
                      let uu____10891 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____10891
                    else
                      (let uu____10893 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____10893 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____10935  -> dummy :: env1) env)
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
                                          let uu____10972 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____10972)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___149_10977 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___149_10977.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___149_10977.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____10978 -> lopt  in
                           (log cfg
                              (fun uu____10984  ->
                                 let uu____10985 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____10985);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___150_10994 = cfg  in
                               {
                                 steps = (uu___150_10994.steps);
                                 tcenv = (uu___150_10994.tcenv);
                                 debug = (uu___150_10994.debug);
                                 delta_level = (uu___150_10994.delta_level);
                                 primitive_steps =
                                   (uu___150_10994.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___150_10994.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___150_10994.normalize_pure_lets)
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
                      (fun uu____11043  ->
                         fun stack1  ->
                           match uu____11043 with
                           | (a,aq) ->
                               let uu____11055 =
                                 let uu____11056 =
                                   let uu____11063 =
                                     let uu____11064 =
                                       let uu____11095 =
                                         FStar_Util.mk_ref
                                           FStar_Pervasives_Native.None
                                          in
                                       (env, a, uu____11095, false)  in
                                     Clos uu____11064  in
                                   (uu____11063, aq,
                                     (t1.FStar_Syntax_Syntax.pos))
                                    in
                                 Arg uu____11056  in
                               uu____11055 :: stack1) args)
                  in
               (log cfg
                  (fun uu____11179  ->
                     let uu____11180 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args)
                        in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____11180);
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
                             ((let uu___151_11216 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___151_11216.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___151_11216.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos
                         in
                      rebuild cfg env stack t2
                  | uu____11217 ->
                      let uu____11222 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____11222)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort  in
                  let uu____11225 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] f
                     in
                  match uu____11225 with
                  | (closing,f1) ->
                      let f2 = norm cfg (dummy :: env) [] f1  in
                      let t2 =
                        let uu____11256 =
                          let uu____11257 =
                            let uu____11264 =
                              FStar_Syntax_Subst.close closing f2  in
                            ((let uu___152_11266 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___152_11266.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___152_11266.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____11264)
                             in
                          FStar_Syntax_Syntax.Tm_refine uu____11257  in
                        mk uu____11256 t1.FStar_Syntax_Syntax.pos  in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if (cfg.steps).weak
               then
                 let uu____11285 = closure_as_term cfg env t1  in
                 rebuild cfg env stack uu____11285
               else
                 (let uu____11287 = FStar_Syntax_Subst.open_comp bs c  in
                  match uu____11287 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____11295 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun uu____11319  -> dummy :: env1) env)
                           in
                        norm_comp cfg uu____11295 c1  in
                      let t2 =
                        let uu____11341 = norm_binders cfg env bs1  in
                        FStar_Syntax_Util.arrow uu____11341 c2  in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) when
               (cfg.steps).unascribe -> norm cfg env stack t11
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack with
                | (Match uu____11452)::uu____11453 ->
                    (log cfg
                       (fun uu____11464  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (Arg uu____11465)::uu____11466 ->
                    (log cfg
                       (fun uu____11477  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (App
                    (uu____11478,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_constant
                                     (FStar_Const.Const_reify );
                                   FStar_Syntax_Syntax.pos = uu____11479;
                                   FStar_Syntax_Syntax.vars = uu____11480;_},uu____11481,uu____11482))::uu____11483
                    ->
                    (log cfg
                       (fun uu____11492  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (MemoLazy uu____11493)::uu____11494 ->
                    (log cfg
                       (fun uu____11505  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | uu____11506 ->
                    (log cfg
                       (fun uu____11509  ->
                          FStar_Util.print_string "+++ Keeping ascription \n");
                     (let t12 = norm cfg env [] t11  in
                      log cfg
                        (fun uu____11513  ->
                           FStar_Util.print_string
                             "+++ Normalizing ascription \n");
                      (let tc1 =
                         match tc with
                         | FStar_Util.Inl t2 ->
                             let uu____11530 = norm cfg env [] t2  in
                             FStar_Util.Inl uu____11530
                         | FStar_Util.Inr c ->
                             let uu____11538 = norm_comp cfg env c  in
                             FStar_Util.Inr uu____11538
                          in
                       let tacopt1 =
                         FStar_Util.map_opt tacopt (norm cfg env [])  in
                       match stack with
                       | (Cfg cfg1)::stack1 ->
                           let t2 =
                             let uu____11551 =
                               let uu____11552 =
                                 let uu____11579 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____11579, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____11552
                                in
                             mk uu____11551 t1.FStar_Syntax_Syntax.pos  in
                           norm cfg1 env stack1 t2
                       | uu____11598 ->
                           let uu____11599 =
                             let uu____11600 =
                               let uu____11601 =
                                 let uu____11628 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____11628, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____11601
                                in
                             mk uu____11600 t1.FStar_Syntax_Syntax.pos  in
                           rebuild cfg env stack uu____11599))))
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
                         let uu____11738 =
                           FStar_Syntax_Subst.univ_var_opening
                             lb.FStar_Syntax_Syntax.lbunivs
                            in
                         match uu____11738 with
                         | (openings,lbunivs) ->
                             let cfg1 =
                               let uu___153_11758 = cfg  in
                               let uu____11759 =
                                 FStar_TypeChecker_Env.push_univ_vars
                                   cfg.tcenv lbunivs
                                  in
                               {
                                 steps = (uu___153_11758.steps);
                                 tcenv = uu____11759;
                                 debug = (uu___153_11758.debug);
                                 delta_level = (uu___153_11758.delta_level);
                                 primitive_steps =
                                   (uu___153_11758.primitive_steps);
                                 strong = (uu___153_11758.strong);
                                 memoize_lazy = (uu___153_11758.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___153_11758.normalize_pure_lets)
                               }  in
                             let norm1 t2 =
                               let uu____11764 =
                                 let uu____11765 =
                                   FStar_Syntax_Subst.subst openings t2  in
                                 norm cfg1 env [] uu____11765  in
                               FStar_Syntax_Subst.close_univ_vars lbunivs
                                 uu____11764
                                in
                             let lbtyp = norm1 lb.FStar_Syntax_Syntax.lbtyp
                                in
                             let lbdef = norm1 lb.FStar_Syntax_Syntax.lbdef
                                in
                             let uu___154_11768 = lb  in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___154_11768.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs = lbunivs;
                               FStar_Syntax_Syntax.lbtyp = lbtyp;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___154_11768.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = lbdef;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___154_11768.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___154_11768.FStar_Syntax_Syntax.lbpos)
                             }))
                  in
               let uu____11769 =
                 mk (FStar_Syntax_Syntax.Tm_let ((b, lbs1), lbody))
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack uu____11769
           | FStar_Syntax_Syntax.Tm_let
               ((uu____11780,{
                               FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                 uu____11781;
                               FStar_Syntax_Syntax.lbunivs = uu____11782;
                               FStar_Syntax_Syntax.lbtyp = uu____11783;
                               FStar_Syntax_Syntax.lbeff = uu____11784;
                               FStar_Syntax_Syntax.lbdef = uu____11785;
                               FStar_Syntax_Syntax.lbattrs = uu____11786;
                               FStar_Syntax_Syntax.lbpos = uu____11787;_}::uu____11788),uu____11789)
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff
                  in
               let uu____11829 =
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
               if uu____11829
               then
                 let binder =
                   let uu____11831 =
                     FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                   FStar_Syntax_Syntax.mk_binder uu____11831  in
                 let env1 =
                   let uu____11841 =
                     let uu____11848 =
                       let uu____11849 =
                         let uu____11880 =
                           FStar_Util.mk_ref FStar_Pervasives_Native.None  in
                         (env, (lb.FStar_Syntax_Syntax.lbdef), uu____11880,
                           false)
                          in
                       Clos uu____11849  in
                     ((FStar_Pervasives_Native.Some binder), uu____11848)  in
                   uu____11841 :: env  in
                 (log cfg
                    (fun uu____11973  ->
                       FStar_Util.print_string "+++ Reducing Tm_let\n");
                  norm cfg env1 stack body)
               else
                 if (cfg.steps).weak
                 then
                   (log cfg
                      (fun uu____11977  ->
                         FStar_Util.print_string "+++ Not touching Tm_let\n");
                    (let uu____11978 = closure_as_term cfg env t1  in
                     rebuild cfg env stack uu____11978))
                 else
                   (let uu____11980 =
                      let uu____11985 =
                        let uu____11986 =
                          let uu____11987 =
                            FStar_All.pipe_right
                              lb.FStar_Syntax_Syntax.lbname FStar_Util.left
                             in
                          FStar_All.pipe_right uu____11987
                            FStar_Syntax_Syntax.mk_binder
                           in
                        [uu____11986]  in
                      FStar_Syntax_Subst.open_term uu____11985 body  in
                    match uu____11980 with
                    | (bs,body1) ->
                        (log cfg
                           (fun uu____11996  ->
                              FStar_Util.print_string
                                "+++ Normalizing Tm_let -- type");
                         (let ty =
                            norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                          let lbname =
                            let x =
                              let uu____12004 = FStar_List.hd bs  in
                              FStar_Pervasives_Native.fst uu____12004  in
                            FStar_Util.Inl
                              (let uu___155_12014 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___155_12014.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___155_12014.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               })
                             in
                          log cfg
                            (fun uu____12017  ->
                               FStar_Util.print_string
                                 "+++ Normalizing Tm_let -- definiens\n");
                          (let lb1 =
                             let uu___156_12019 = lb  in
                             let uu____12020 =
                               norm cfg env [] lb.FStar_Syntax_Syntax.lbdef
                                in
                             {
                               FStar_Syntax_Syntax.lbname = lbname;
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___156_12019.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp = ty;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___156_12019.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = uu____12020;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___156_12019.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___156_12019.FStar_Syntax_Syntax.lbpos)
                             }  in
                           let env' =
                             FStar_All.pipe_right bs
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12055  -> dummy :: env1) env)
                              in
                           let stack1 = (Cfg cfg) :: stack  in
                           let cfg1 =
                             let uu___157_12078 = cfg  in
                             {
                               steps = (uu___157_12078.steps);
                               tcenv = (uu___157_12078.tcenv);
                               debug = (uu___157_12078.debug);
                               delta_level = (uu___157_12078.delta_level);
                               primitive_steps =
                                 (uu___157_12078.primitive_steps);
                               strong = true;
                               memoize_lazy = (uu___157_12078.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___157_12078.normalize_pure_lets)
                             }  in
                           log cfg1
                             (fun uu____12081  ->
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
               let uu____12098 = FStar_Syntax_Subst.open_let_rec lbs body  in
               (match uu____12098 with
                | (lbs1,body1) ->
                    let lbs2 =
                      FStar_List.map
                        (fun lb  ->
                           let ty =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                           let lbname =
                             let uu____12134 =
                               let uu___158_12135 =
                                 FStar_Util.left
                                   lb.FStar_Syntax_Syntax.lbname
                                  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___158_12135.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___158_12135.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               }  in
                             FStar_Util.Inl uu____12134  in
                           let uu____12136 =
                             FStar_Syntax_Util.abs_formals
                               lb.FStar_Syntax_Syntax.lbdef
                              in
                           match uu____12136 with
                           | (xs,def_body,lopt) ->
                               let xs1 = norm_binders cfg env xs  in
                               let env1 =
                                 let uu____12162 =
                                   FStar_List.map (fun uu____12178  -> dummy)
                                     lbs1
                                    in
                                 let uu____12179 =
                                   let uu____12188 =
                                     FStar_List.map
                                       (fun uu____12208  -> dummy) xs1
                                      in
                                   FStar_List.append uu____12188 env  in
                                 FStar_List.append uu____12162 uu____12179
                                  in
                               let def_body1 = norm cfg env1 [] def_body  in
                               let lopt1 =
                                 match lopt with
                                 | FStar_Pervasives_Native.Some rc ->
                                     let uu____12232 =
                                       let uu___159_12233 = rc  in
                                       let uu____12234 =
                                         FStar_Util.map_opt
                                           rc.FStar_Syntax_Syntax.residual_typ
                                           (norm cfg env1 [])
                                          in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___159_12233.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           uu____12234;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___159_12233.FStar_Syntax_Syntax.residual_flags)
                                       }  in
                                     FStar_Pervasives_Native.Some uu____12232
                                 | uu____12241 -> lopt  in
                               let def =
                                 FStar_Syntax_Util.abs xs1 def_body1 lopt1
                                  in
                               let uu___160_12245 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname = lbname;
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___160_12245.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp = ty;
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___160_12245.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___160_12245.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___160_12245.FStar_Syntax_Syntax.lbpos)
                               }) lbs1
                       in
                    let env' =
                      let uu____12255 =
                        FStar_List.map (fun uu____12271  -> dummy) lbs2  in
                      FStar_List.append uu____12255 env  in
                    let body2 = norm cfg env' [] body1  in
                    let uu____12279 =
                      FStar_Syntax_Subst.close_let_rec lbs2 body2  in
                    (match uu____12279 with
                     | (lbs3,body3) ->
                         let t2 =
                           let uu___161_12295 = t1  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_let
                                  ((true, lbs3), body3));
                             FStar_Syntax_Syntax.pos =
                               (uu___161_12295.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___161_12295.FStar_Syntax_Syntax.vars)
                           }  in
                         rebuild cfg env stack t2))
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               Prims.op_Negation (cfg.steps).zeta ->
               let uu____12322 = closure_as_term cfg env t1  in
               rebuild cfg env stack uu____12322
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____12341 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____12417  ->
                        match uu____12417 with
                        | (rec_env,memos,i) ->
                            let bv =
                              let uu___162_12538 =
                                FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                                 in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___162_12538.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index = i;
                                FStar_Syntax_Syntax.sort =
                                  (uu___162_12538.FStar_Syntax_Syntax.sort)
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
               (match uu____12341 with
                | (rec_env,memos,uu____12751) ->
                    let uu____12804 =
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
                             let uu____13115 =
                               let uu____13122 =
                                 let uu____13123 =
                                   let uu____13154 =
                                     FStar_Util.mk_ref
                                       FStar_Pervasives_Native.None
                                      in
                                   (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                     uu____13154, false)
                                    in
                                 Clos uu____13123  in
                               (FStar_Pervasives_Native.None, uu____13122)
                                in
                             uu____13115 :: env1)
                        (FStar_Pervasives_Native.snd lbs) env
                       in
                    norm cfg body_env stack body)
           | FStar_Syntax_Syntax.Tm_meta (head1,m) ->
               (log cfg
                  (fun uu____13264  ->
                     let uu____13265 =
                       FStar_Syntax_Print.metadata_to_string m  in
                     FStar_Util.print1 ">> metadata = %s\n" uu____13265);
                (match m with
                 | FStar_Syntax_Syntax.Meta_monadic (m1,t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inl m1) t2
                 | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inr (m1, m')) t2
                 | uu____13287 ->
                     if (cfg.steps).unmeta
                     then norm cfg env stack head1
                     else
                       (match stack with
                        | uu____13289::uu____13290 ->
                            (match m with
                             | FStar_Syntax_Syntax.Meta_labeled
                                 (l,r,uu____13295) ->
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
                             | uu____13318 -> norm cfg env stack head1)
                        | [] ->
                            let head2 = norm cfg env [] head1  in
                            let m1 =
                              match m with
                              | FStar_Syntax_Syntax.Meta_pattern args ->
                                  let uu____13332 =
                                    norm_pattern_args cfg env args  in
                                  FStar_Syntax_Syntax.Meta_pattern
                                    uu____13332
                              | uu____13343 -> m  in
                            let t2 =
                              mk (FStar_Syntax_Syntax.Tm_meta (head2, m1))
                                t1.FStar_Syntax_Syntax.pos
                               in
                            rebuild cfg env stack t2)))
           | FStar_Syntax_Syntax.Tm_delayed uu____13347 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               norm cfg env stack t2
           | FStar_Syntax_Syntax.Tm_uvar uu____13373 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               (match t2.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_uvar uu____13391 ->
                    if (cfg.steps).check_no_uvars
                    then
                      let uu____13408 =
                        let uu____13409 =
                          FStar_Range.string_of_range
                            t2.FStar_Syntax_Syntax.pos
                           in
                        let uu____13410 =
                          FStar_Syntax_Print.term_to_string t2  in
                        FStar_Util.format2
                          "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                          uu____13409 uu____13410
                         in
                      failwith uu____13408
                    else rebuild cfg env stack t2
                | uu____13412 -> norm cfg env stack t2))

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
                let uu____13422 = FStar_Syntax_Syntax.range_of_fv f  in
                FStar_TypeChecker_Env.set_range cfg.tcenv uu____13422  in
              let uu____13423 =
                FStar_TypeChecker_Env.lookup_definition_qninfo
                  cfg.delta_level
                  (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                  qninfo
                 in
              match uu____13423 with
              | FStar_Pervasives_Native.None  ->
                  (log cfg
                     (fun uu____13436  ->
                        FStar_Util.print "Tm_fvar case 2\n" []);
                   rebuild cfg env stack t0)
              | FStar_Pervasives_Native.Some (us,t) ->
                  (log cfg
                     (fun uu____13447  ->
                        let uu____13448 =
                          FStar_Syntax_Print.term_to_string t0  in
                        let uu____13449 = FStar_Syntax_Print.term_to_string t
                           in
                        FStar_Util.print2 ">>> Unfolded %s to %s\n"
                          uu____13448 uu____13449);
                   (let t1 =
                      if
                        ((cfg.steps).unfold_until =
                           (FStar_Pervasives_Native.Some
                              FStar_Syntax_Syntax.Delta_constant))
                          && (Prims.op_Negation (cfg.steps).unfold_tac)
                      then t
                      else
                        (let uu____13454 =
                           FStar_Ident.range_of_lid
                             (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                            in
                         FStar_Syntax_Subst.set_use_range uu____13454 t)
                       in
                    let n1 = FStar_List.length us  in
                    if n1 > (Prims.parse_int "0")
                    then
                      match stack with
                      | (UnivArgs (us',uu____13463))::stack1 ->
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
                      | uu____13518 when
                          (cfg.steps).erase_universes ||
                            (cfg.steps).allow_unbound_universes
                          -> norm cfg env stack t1
                      | uu____13521 ->
                          let uu____13524 =
                            let uu____13525 =
                              FStar_Syntax_Print.lid_to_string
                                (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                               in
                            FStar_Util.format1
                              "Impossible: missing universe instantiation on %s"
                              uu____13525
                             in
                          failwith uu____13524
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
                  let uu___163_13549 = cfg  in
                  let uu____13550 =
                    FStar_List.fold_right fstep_add_one new_steps cfg.steps
                     in
                  {
                    steps = uu____13550;
                    tcenv = (uu___163_13549.tcenv);
                    debug = (uu___163_13549.debug);
                    delta_level =
                      [FStar_TypeChecker_Env.Inlining;
                      FStar_TypeChecker_Env.Eager_unfolding_only];
                    primitive_steps = (uu___163_13549.primitive_steps);
                    strong = (uu___163_13549.strong);
                    memoize_lazy = (uu___163_13549.memoize_lazy);
                    normalize_pure_lets =
                      (uu___163_13549.normalize_pure_lets)
                  }
                else
                  (let uu___164_13552 = cfg  in
                   {
                     steps =
                       (let uu___165_13555 = cfg.steps  in
                        {
                          beta = (uu___165_13555.beta);
                          iota = (uu___165_13555.iota);
                          zeta = false;
                          weak = (uu___165_13555.weak);
                          hnf = (uu___165_13555.hnf);
                          primops = (uu___165_13555.primops);
                          no_delta_steps = (uu___165_13555.no_delta_steps);
                          unfold_until = (uu___165_13555.unfold_until);
                          unfold_only = (uu___165_13555.unfold_only);
                          unfold_attr = (uu___165_13555.unfold_attr);
                          unfold_tac = (uu___165_13555.unfold_tac);
                          pure_subterms_within_computations =
                            (uu___165_13555.pure_subterms_within_computations);
                          simplify = (uu___165_13555.simplify);
                          erase_universes = (uu___165_13555.erase_universes);
                          allow_unbound_universes =
                            (uu___165_13555.allow_unbound_universes);
                          reify_ = (uu___165_13555.reify_);
                          compress_uvars = (uu___165_13555.compress_uvars);
                          no_full_norm = (uu___165_13555.no_full_norm);
                          check_no_uvars = (uu___165_13555.check_no_uvars);
                          unmeta = (uu___165_13555.unmeta);
                          unascribe = (uu___165_13555.unascribe)
                        });
                     tcenv = (uu___164_13552.tcenv);
                     debug = (uu___164_13552.debug);
                     delta_level = (uu___164_13552.delta_level);
                     primitive_steps = (uu___164_13552.primitive_steps);
                     strong = (uu___164_13552.strong);
                     memoize_lazy = (uu___164_13552.memoize_lazy);
                     normalize_pure_lets =
                       (uu___164_13552.normalize_pure_lets)
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
                  (fun uu____13585  ->
                     let uu____13586 = FStar_Syntax_Print.tag_of_term head2
                        in
                     let uu____13587 =
                       FStar_Syntax_Print.term_to_string head2  in
                     FStar_Util.print2 "Reifying: (%s) %s\n" uu____13586
                       uu____13587);
                (let head3 = FStar_Syntax_Util.unmeta_safe head2  in
                 let uu____13589 =
                   let uu____13590 = FStar_Syntax_Subst.compress head3  in
                   uu____13590.FStar_Syntax_Syntax.n  in
                 match uu____13589 with
                 | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                     let ed =
                       let uu____13608 =
                         FStar_TypeChecker_Env.norm_eff_name cfg.tcenv m  in
                       FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                         uu____13608
                        in
                     let uu____13609 = ed.FStar_Syntax_Syntax.bind_repr  in
                     (match uu____13609 with
                      | (uu____13610,bind_repr) ->
                          (match lb.FStar_Syntax_Syntax.lbname with
                           | FStar_Util.Inr uu____13616 ->
                               failwith
                                 "Cannot reify a top-level let binding"
                           | FStar_Util.Inl x ->
                               let is_return e =
                                 let uu____13624 =
                                   let uu____13625 =
                                     FStar_Syntax_Subst.compress e  in
                                   uu____13625.FStar_Syntax_Syntax.n  in
                                 match uu____13624 with
                                 | FStar_Syntax_Syntax.Tm_meta
                                     (e1,FStar_Syntax_Syntax.Meta_monadic
                                      (uu____13631,uu____13632))
                                     ->
                                     let uu____13641 =
                                       let uu____13642 =
                                         FStar_Syntax_Subst.compress e1  in
                                       uu____13642.FStar_Syntax_Syntax.n  in
                                     (match uu____13641 with
                                      | FStar_Syntax_Syntax.Tm_meta
                                          (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                           (uu____13648,msrc,uu____13650))
                                          when
                                          FStar_Syntax_Util.is_pure_effect
                                            msrc
                                          ->
                                          let uu____13659 =
                                            FStar_Syntax_Subst.compress e2
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____13659
                                      | uu____13660 ->
                                          FStar_Pervasives_Native.None)
                                 | uu____13661 ->
                                     FStar_Pervasives_Native.None
                                  in
                               let uu____13662 =
                                 is_return lb.FStar_Syntax_Syntax.lbdef  in
                               (match uu____13662 with
                                | FStar_Pervasives_Native.Some e ->
                                    let lb1 =
                                      let uu___166_13667 = lb  in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          (uu___166_13667.FStar_Syntax_Syntax.lbname);
                                        FStar_Syntax_Syntax.lbunivs =
                                          (uu___166_13667.FStar_Syntax_Syntax.lbunivs);
                                        FStar_Syntax_Syntax.lbtyp =
                                          (uu___166_13667.FStar_Syntax_Syntax.lbtyp);
                                        FStar_Syntax_Syntax.lbeff =
                                          FStar_Parser_Const.effect_PURE_lid;
                                        FStar_Syntax_Syntax.lbdef = e;
                                        FStar_Syntax_Syntax.lbattrs =
                                          (uu___166_13667.FStar_Syntax_Syntax.lbattrs);
                                        FStar_Syntax_Syntax.lbpos =
                                          (uu___166_13667.FStar_Syntax_Syntax.lbpos)
                                      }  in
                                    let uu____13668 = FStar_List.tl stack  in
                                    let uu____13669 =
                                      let uu____13670 =
                                        let uu____13673 =
                                          let uu____13674 =
                                            let uu____13687 =
                                              FStar_Syntax_Util.mk_reify body
                                               in
                                            ((false, [lb1]), uu____13687)  in
                                          FStar_Syntax_Syntax.Tm_let
                                            uu____13674
                                           in
                                        FStar_Syntax_Syntax.mk uu____13673
                                         in
                                      uu____13670
                                        FStar_Pervasives_Native.None
                                        head3.FStar_Syntax_Syntax.pos
                                       in
                                    norm cfg env uu____13668 uu____13669
                                | FStar_Pervasives_Native.None  ->
                                    let uu____13703 =
                                      let uu____13704 = is_return body  in
                                      match uu____13704 with
                                      | FStar_Pervasives_Native.Some
                                          {
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_bvar y;
                                            FStar_Syntax_Syntax.pos =
                                              uu____13708;
                                            FStar_Syntax_Syntax.vars =
                                              uu____13709;_}
                                          -> FStar_Syntax_Syntax.bv_eq x y
                                      | uu____13714 -> false  in
                                    if uu____13703
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
                                         let uu____13737 =
                                           let uu____13740 =
                                             let uu____13741 =
                                               let uu____13758 =
                                                 let uu____13761 =
                                                   FStar_Syntax_Syntax.mk_binder
                                                     x
                                                    in
                                                 [uu____13761]  in
                                               (uu____13758, body1,
                                                 (FStar_Pervasives_Native.Some
                                                    body_rc))
                                                in
                                             FStar_Syntax_Syntax.Tm_abs
                                               uu____13741
                                              in
                                           FStar_Syntax_Syntax.mk uu____13740
                                            in
                                         uu____13737
                                           FStar_Pervasives_Native.None
                                           body1.FStar_Syntax_Syntax.pos
                                          in
                                       let close1 = closure_as_term cfg env
                                          in
                                       let bind_inst =
                                         let uu____13777 =
                                           let uu____13778 =
                                             FStar_Syntax_Subst.compress
                                               bind_repr
                                              in
                                           uu____13778.FStar_Syntax_Syntax.n
                                            in
                                         match uu____13777 with
                                         | FStar_Syntax_Syntax.Tm_uinst
                                             (bind1,uu____13784::uu____13785::[])
                                             ->
                                             let uu____13792 =
                                               let uu____13795 =
                                                 let uu____13796 =
                                                   let uu____13803 =
                                                     let uu____13806 =
                                                       let uu____13807 =
                                                         close1
                                                           lb.FStar_Syntax_Syntax.lbtyp
                                                          in
                                                       (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                         cfg.tcenv
                                                         uu____13807
                                                        in
                                                     let uu____13808 =
                                                       let uu____13811 =
                                                         let uu____13812 =
                                                           close1 t  in
                                                         (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                           cfg.tcenv
                                                           uu____13812
                                                          in
                                                       [uu____13811]  in
                                                     uu____13806 ::
                                                       uu____13808
                                                      in
                                                   (bind1, uu____13803)  in
                                                 FStar_Syntax_Syntax.Tm_uinst
                                                   uu____13796
                                                  in
                                               FStar_Syntax_Syntax.mk
                                                 uu____13795
                                                in
                                             uu____13792
                                               FStar_Pervasives_Native.None
                                               rng
                                         | uu____13820 ->
                                             failwith
                                               "NIY : Reification of indexed effects"
                                          in
                                       let maybe_range_arg =
                                         let uu____13826 =
                                           FStar_Util.for_some
                                             (FStar_Syntax_Util.attr_eq
                                                FStar_Syntax_Util.dm4f_bind_range_attr)
                                             ed.FStar_Syntax_Syntax.eff_attrs
                                            in
                                         if uu____13826
                                         then
                                           let uu____13829 =
                                             let uu____13830 =
                                               FStar_Syntax_Embeddings.embed_range
                                                 lb.FStar_Syntax_Syntax.lbpos
                                                 lb.FStar_Syntax_Syntax.lbpos
                                                in
                                             FStar_Syntax_Syntax.as_arg
                                               uu____13830
                                              in
                                           let uu____13831 =
                                             let uu____13834 =
                                               let uu____13835 =
                                                 FStar_Syntax_Embeddings.embed_range
                                                   body2.FStar_Syntax_Syntax.pos
                                                   body2.FStar_Syntax_Syntax.pos
                                                  in
                                               FStar_Syntax_Syntax.as_arg
                                                 uu____13835
                                                in
                                             [uu____13834]  in
                                           uu____13829 :: uu____13831
                                         else []  in
                                       let reified =
                                         let uu____13840 =
                                           let uu____13843 =
                                             let uu____13844 =
                                               let uu____13859 =
                                                 let uu____13862 =
                                                   let uu____13865 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       lb.FStar_Syntax_Syntax.lbtyp
                                                      in
                                                   let uu____13866 =
                                                     let uu____13869 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         t
                                                        in
                                                     [uu____13869]  in
                                                   uu____13865 :: uu____13866
                                                    in
                                                 let uu____13870 =
                                                   let uu____13873 =
                                                     let uu____13876 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         FStar_Syntax_Syntax.tun
                                                        in
                                                     let uu____13877 =
                                                       let uu____13880 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           head4
                                                          in
                                                       let uu____13881 =
                                                         let uu____13884 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             FStar_Syntax_Syntax.tun
                                                            in
                                                         let uu____13885 =
                                                           let uu____13888 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               body2
                                                              in
                                                           [uu____13888]  in
                                                         uu____13884 ::
                                                           uu____13885
                                                          in
                                                       uu____13880 ::
                                                         uu____13881
                                                        in
                                                     uu____13876 ::
                                                       uu____13877
                                                      in
                                                   FStar_List.append
                                                     maybe_range_arg
                                                     uu____13873
                                                    in
                                                 FStar_List.append
                                                   uu____13862 uu____13870
                                                  in
                                               (bind_inst, uu____13859)  in
                                             FStar_Syntax_Syntax.Tm_app
                                               uu____13844
                                              in
                                           FStar_Syntax_Syntax.mk uu____13843
                                            in
                                         uu____13840
                                           FStar_Pervasives_Native.None rng
                                          in
                                       log cfg
                                         (fun uu____13900  ->
                                            let uu____13901 =
                                              FStar_Syntax_Print.term_to_string
                                                head0
                                               in
                                            let uu____13902 =
                                              FStar_Syntax_Print.term_to_string
                                                reified
                                               in
                                            FStar_Util.print2
                                              "Reified (1) <%s> to %s\n"
                                              uu____13901 uu____13902);
                                       (let uu____13903 = FStar_List.tl stack
                                           in
                                        norm cfg env uu____13903 reified)))))
                 | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                     let ed =
                       let uu____13927 =
                         FStar_TypeChecker_Env.norm_eff_name cfg.tcenv m  in
                       FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                         uu____13927
                        in
                     let uu____13928 = ed.FStar_Syntax_Syntax.bind_repr  in
                     (match uu____13928 with
                      | (uu____13929,bind_repr) ->
                          let maybe_unfold_action head4 =
                            let maybe_extract_fv t1 =
                              let t2 =
                                let uu____13964 =
                                  let uu____13965 =
                                    FStar_Syntax_Subst.compress t1  in
                                  uu____13965.FStar_Syntax_Syntax.n  in
                                match uu____13964 with
                                | FStar_Syntax_Syntax.Tm_uinst
                                    (t2,uu____13971) -> t2
                                | uu____13976 -> head4  in
                              let uu____13977 =
                                let uu____13978 =
                                  FStar_Syntax_Subst.compress t2  in
                                uu____13978.FStar_Syntax_Syntax.n  in
                              match uu____13977 with
                              | FStar_Syntax_Syntax.Tm_fvar x ->
                                  FStar_Pervasives_Native.Some x
                              | uu____13984 -> FStar_Pervasives_Native.None
                               in
                            let uu____13985 = maybe_extract_fv head4  in
                            match uu____13985 with
                            | FStar_Pervasives_Native.Some x when
                                let uu____13995 =
                                  FStar_Syntax_Syntax.lid_of_fv x  in
                                FStar_TypeChecker_Env.is_action cfg.tcenv
                                  uu____13995
                                ->
                                let head5 = norm cfg env [] head4  in
                                let action_unfolded =
                                  let uu____14000 = maybe_extract_fv head5
                                     in
                                  match uu____14000 with
                                  | FStar_Pervasives_Native.Some uu____14005
                                      -> FStar_Pervasives_Native.Some true
                                  | uu____14006 ->
                                      FStar_Pervasives_Native.Some false
                                   in
                                (head5, action_unfolded)
                            | uu____14011 ->
                                (head4, FStar_Pervasives_Native.None)
                             in
                          ((let is_arg_impure uu____14026 =
                              match uu____14026 with
                              | (e,q) ->
                                  let uu____14033 =
                                    let uu____14034 =
                                      FStar_Syntax_Subst.compress e  in
                                    uu____14034.FStar_Syntax_Syntax.n  in
                                  (match uu____14033 with
                                   | FStar_Syntax_Syntax.Tm_meta
                                       (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                        (m1,m2,t'))
                                       ->
                                       let uu____14049 =
                                         FStar_Syntax_Util.is_pure_effect m1
                                          in
                                       Prims.op_Negation uu____14049
                                   | uu____14050 -> false)
                               in
                            let uu____14051 =
                              let uu____14052 =
                                let uu____14059 =
                                  FStar_Syntax_Syntax.as_arg head_app  in
                                uu____14059 :: args  in
                              FStar_Util.for_some is_arg_impure uu____14052
                               in
                            if uu____14051
                            then
                              let uu____14064 =
                                let uu____14065 =
                                  FStar_Syntax_Print.term_to_string head3  in
                                FStar_Util.format1
                                  "Incompability between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                  uu____14065
                                 in
                              failwith uu____14064
                            else ());
                           (let uu____14067 = maybe_unfold_action head_app
                               in
                            match uu____14067 with
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
                                   (fun uu____14108  ->
                                      let uu____14109 =
                                        FStar_Syntax_Print.term_to_string
                                          head0
                                         in
                                      let uu____14110 =
                                        FStar_Syntax_Print.term_to_string
                                          body1
                                         in
                                      FStar_Util.print2
                                        "Reified (2) <%s> to %s\n"
                                        uu____14109 uu____14110);
                                 (let uu____14111 = FStar_List.tl stack  in
                                  norm cfg env uu____14111 body1)))))
                 | FStar_Syntax_Syntax.Tm_meta
                     (e,FStar_Syntax_Syntax.Meta_monadic uu____14113) ->
                     do_reify_monadic fallback cfg env stack e m t
                 | FStar_Syntax_Syntax.Tm_meta
                     (e,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,t'))
                     ->
                     let lifted =
                       let uu____14137 = closure_as_term cfg env t'  in
                       reify_lift cfg e msrc mtgt uu____14137  in
                     (log cfg
                        (fun uu____14141  ->
                           let uu____14142 =
                             FStar_Syntax_Print.term_to_string lifted  in
                           FStar_Util.print1 "Reified lift to (2): %s\n"
                             uu____14142);
                      (let uu____14143 = FStar_List.tl stack  in
                       norm cfg env uu____14143 lifted))
                 | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                     let branches1 =
                       FStar_All.pipe_right branches
                         (FStar_List.map
                            (fun uu____14264  ->
                               match uu____14264 with
                               | (pat,wopt,tm) ->
                                   let uu____14312 =
                                     FStar_Syntax_Util.mk_reify tm  in
                                   (pat, wopt, uu____14312)))
                        in
                     let tm =
                       mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                         head3.FStar_Syntax_Syntax.pos
                        in
                     let uu____14344 = FStar_List.tl stack  in
                     norm cfg env uu____14344 tm
                 | uu____14345 -> fallback ())

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
              (fun uu____14359  ->
                 let uu____14360 = FStar_Ident.string_of_lid msrc  in
                 let uu____14361 = FStar_Ident.string_of_lid mtgt  in
                 let uu____14362 = FStar_Syntax_Print.term_to_string e  in
                 FStar_Util.print3 "Reifying lift %s -> %s: %s\n" uu____14360
                   uu____14361 uu____14362);
            (let uu____14363 =
               (FStar_Syntax_Util.is_pure_effect msrc) ||
                 (FStar_Syntax_Util.is_div_effect msrc)
                in
             if uu____14363
             then
               let ed =
                 let uu____14365 =
                   FStar_TypeChecker_Env.norm_eff_name cfg.tcenv mtgt  in
                 FStar_TypeChecker_Env.get_effect_decl env uu____14365  in
               let uu____14366 = ed.FStar_Syntax_Syntax.return_repr  in
               match uu____14366 with
               | (uu____14367,return_repr) ->
                   let return_inst =
                     let uu____14376 =
                       let uu____14377 =
                         FStar_Syntax_Subst.compress return_repr  in
                       uu____14377.FStar_Syntax_Syntax.n  in
                     match uu____14376 with
                     | FStar_Syntax_Syntax.Tm_uinst
                         (return_tm,uu____14383::[]) ->
                         let uu____14390 =
                           let uu____14393 =
                             let uu____14394 =
                               let uu____14401 =
                                 let uu____14404 =
                                   env.FStar_TypeChecker_Env.universe_of env
                                     t
                                    in
                                 [uu____14404]  in
                               (return_tm, uu____14401)  in
                             FStar_Syntax_Syntax.Tm_uinst uu____14394  in
                           FStar_Syntax_Syntax.mk uu____14393  in
                         uu____14390 FStar_Pervasives_Native.None
                           e.FStar_Syntax_Syntax.pos
                     | uu____14412 ->
                         failwith "NIY : Reification of indexed effects"
                      in
                   let uu____14415 =
                     let uu____14418 =
                       let uu____14419 =
                         let uu____14434 =
                           let uu____14437 = FStar_Syntax_Syntax.as_arg t  in
                           let uu____14438 =
                             let uu____14441 = FStar_Syntax_Syntax.as_arg e
                                in
                             [uu____14441]  in
                           uu____14437 :: uu____14438  in
                         (return_inst, uu____14434)  in
                       FStar_Syntax_Syntax.Tm_app uu____14419  in
                     FStar_Syntax_Syntax.mk uu____14418  in
                   uu____14415 FStar_Pervasives_Native.None
                     e.FStar_Syntax_Syntax.pos
             else
               (let uu____14450 =
                  FStar_TypeChecker_Env.monad_leq env msrc mtgt  in
                match uu____14450 with
                | FStar_Pervasives_Native.None  ->
                    let uu____14453 =
                      let uu____14454 = FStar_Ident.text_of_lid msrc  in
                      let uu____14455 = FStar_Ident.text_of_lid mtgt  in
                      FStar_Util.format2
                        "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                        uu____14454 uu____14455
                       in
                    failwith uu____14453
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____14456;
                      FStar_TypeChecker_Env.mtarget = uu____14457;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____14458;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.None ;_};_}
                    ->
                    let uu____14473 =
                      let uu____14474 = FStar_Ident.text_of_lid msrc  in
                      let uu____14475 = FStar_Ident.text_of_lid mtgt  in
                      FStar_Util.format2
                        "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
                        uu____14474 uu____14475
                       in
                    failwith uu____14473
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____14476;
                      FStar_TypeChecker_Env.mtarget = uu____14477;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____14478;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.Some lift;_};_}
                    ->
                    let uu____14502 =
                      env.FStar_TypeChecker_Env.universe_of env t  in
                    let uu____14503 = FStar_Syntax_Util.mk_reify e  in
                    lift uu____14502 t FStar_Syntax_Syntax.tun uu____14503))

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
                (fun uu____14559  ->
                   match uu____14559 with
                   | (a,imp) ->
                       let uu____14570 = norm cfg env [] a  in
                       (uu____14570, imp))))

and (norm_comp :
  cfg -> env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp) =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        match comp.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total (t,uopt) ->
            let uu___167_14584 = comp  in
            let uu____14585 =
              let uu____14586 =
                let uu____14595 = norm cfg env [] t  in
                let uu____14596 =
                  FStar_Option.map (norm_universe cfg env) uopt  in
                (uu____14595, uu____14596)  in
              FStar_Syntax_Syntax.Total uu____14586  in
            {
              FStar_Syntax_Syntax.n = uu____14585;
              FStar_Syntax_Syntax.pos =
                (uu___167_14584.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___167_14584.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
            let uu___168_14611 = comp  in
            let uu____14612 =
              let uu____14613 =
                let uu____14622 = norm cfg env [] t  in
                let uu____14623 =
                  FStar_Option.map (norm_universe cfg env) uopt  in
                (uu____14622, uu____14623)  in
              FStar_Syntax_Syntax.GTotal uu____14613  in
            {
              FStar_Syntax_Syntax.n = uu____14612;
              FStar_Syntax_Syntax.pos =
                (uu___168_14611.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___168_14611.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let norm_args args =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____14675  ->
                      match uu____14675 with
                      | (a,i) ->
                          let uu____14686 = norm cfg env [] a  in
                          (uu____14686, i)))
               in
            let flags1 =
              FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                (FStar_List.map
                   (fun uu___90_14697  ->
                      match uu___90_14697 with
                      | FStar_Syntax_Syntax.DECREASES t ->
                          let uu____14701 = norm cfg env [] t  in
                          FStar_Syntax_Syntax.DECREASES uu____14701
                      | f -> f))
               in
            let uu___169_14705 = comp  in
            let uu____14706 =
              let uu____14707 =
                let uu___170_14708 = ct  in
                let uu____14709 =
                  FStar_List.map (norm_universe cfg env)
                    ct.FStar_Syntax_Syntax.comp_univs
                   in
                let uu____14710 =
                  norm cfg env [] ct.FStar_Syntax_Syntax.result_typ  in
                let uu____14713 =
                  norm_args ct.FStar_Syntax_Syntax.effect_args  in
                {
                  FStar_Syntax_Syntax.comp_univs = uu____14709;
                  FStar_Syntax_Syntax.effect_name =
                    (uu___170_14708.FStar_Syntax_Syntax.effect_name);
                  FStar_Syntax_Syntax.result_typ = uu____14710;
                  FStar_Syntax_Syntax.effect_args = uu____14713;
                  FStar_Syntax_Syntax.flags = flags1
                }  in
              FStar_Syntax_Syntax.Comp uu____14707  in
            {
              FStar_Syntax_Syntax.n = uu____14706;
              FStar_Syntax_Syntax.pos =
                (uu___169_14705.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___169_14705.FStar_Syntax_Syntax.vars)
            }

and (norm_binder :
  cfg -> env -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder) =
  fun cfg  ->
    fun env  ->
      fun uu____14724  ->
        match uu____14724 with
        | (x,imp) ->
            let uu____14727 =
              let uu___171_14728 = x  in
              let uu____14729 = norm cfg env [] x.FStar_Syntax_Syntax.sort
                 in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___171_14728.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___171_14728.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____14729
              }  in
            (uu____14727, imp)

and (norm_binders :
  cfg -> env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders) =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____14735 =
          FStar_List.fold_left
            (fun uu____14753  ->
               fun b  ->
                 match uu____14753 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b  in
                     ((b1 :: nbs'), (dummy :: env1))) ([], env) bs
           in
        match uu____14735 with | (nbs,uu____14793) -> FStar_List.rev nbs

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
            let uu____14809 =
              let uu___172_14810 = rc  in
              let uu____14811 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (norm cfg env [])
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___172_14810.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____14811;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___172_14810.FStar_Syntax_Syntax.residual_flags)
              }  in
            FStar_Pervasives_Native.Some uu____14809
        | uu____14818 -> lopt

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
            (let uu____14839 = FStar_Syntax_Print.term_to_string tm  in
             let uu____14840 = FStar_Syntax_Print.term_to_string tm'  in
             FStar_Util.print3 "%sSimplified\n\t%s to\n\t%s\n"
               (if (cfg.steps).simplify then "" else "NOT ") uu____14839
               uu____14840)
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
          let uu____14860 =
            FStar_All.pipe_left Prims.op_Negation (cfg.steps).simplify  in
          if uu____14860
          then tm1
          else
            (let w t =
               let uu___173_14872 = t  in
               {
                 FStar_Syntax_Syntax.n =
                   (uu___173_14872.FStar_Syntax_Syntax.n);
                 FStar_Syntax_Syntax.pos = (tm1.FStar_Syntax_Syntax.pos);
                 FStar_Syntax_Syntax.vars =
                   (uu___173_14872.FStar_Syntax_Syntax.vars)
               }  in
             let simp_t t =
               let uu____14881 =
                 let uu____14882 = FStar_Syntax_Util.unmeta t  in
                 uu____14882.FStar_Syntax_Syntax.n  in
               match uu____14881 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_Pervasives_Native.Some true
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.false_lid
                   -> FStar_Pervasives_Native.Some false
               | uu____14889 -> FStar_Pervasives_Native.None  in
             let rec args_are_binders args bs =
               match (args, bs) with
               | ((t,uu____14934)::args1,(bv,uu____14937)::bs1) ->
                   let uu____14971 =
                     let uu____14972 = FStar_Syntax_Subst.compress t  in
                     uu____14972.FStar_Syntax_Syntax.n  in
                   (match uu____14971 with
                    | FStar_Syntax_Syntax.Tm_name bv' ->
                        (FStar_Syntax_Syntax.bv_eq bv bv') &&
                          (args_are_binders args1 bs1)
                    | uu____14976 -> false)
               | ([],[]) -> true
               | (uu____14997,uu____14998) -> false  in
             let is_applied bs t =
               let uu____15034 = FStar_Syntax_Util.head_and_args' t  in
               match uu____15034 with
               | (hd1,args) ->
                   let uu____15067 =
                     let uu____15068 = FStar_Syntax_Subst.compress hd1  in
                     uu____15068.FStar_Syntax_Syntax.n  in
                   (match uu____15067 with
                    | FStar_Syntax_Syntax.Tm_name bv when
                        args_are_binders args bs ->
                        FStar_Pervasives_Native.Some bv
                    | uu____15074 -> FStar_Pervasives_Native.None)
                in
             let is_applied_maybe_squashed bs t =
               let uu____15086 = FStar_Syntax_Util.is_squash t  in
               match uu____15086 with
               | FStar_Pervasives_Native.Some (uu____15097,t') ->
                   is_applied bs t'
               | uu____15109 ->
                   let uu____15118 = FStar_Syntax_Util.is_auto_squash t  in
                   (match uu____15118 with
                    | FStar_Pervasives_Native.Some (uu____15129,t') ->
                        is_applied bs t'
                    | uu____15141 -> is_applied bs t)
                in
             let is_quantified_const phi =
               let uu____15158 =
                 FStar_Syntax_Util.destruct_typ_as_formula phi  in
               match uu____15158 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
                   (lid,(p,uu____15165)::(q,uu____15167)::[])) when
                   FStar_Ident.lid_equals lid FStar_Parser_Const.imp_lid ->
                   let uu____15202 =
                     FStar_Syntax_Util.destruct_typ_as_formula p  in
                   (match uu____15202 with
                    | FStar_Pervasives_Native.None  ->
                        let uu____15207 =
                          let uu____15208 = FStar_Syntax_Subst.compress p  in
                          uu____15208.FStar_Syntax_Syntax.n  in
                        (match uu____15207 with
                         | FStar_Syntax_Syntax.Tm_bvar bv ->
                             let uu____15214 =
                               FStar_Syntax_Subst.subst
                                 [FStar_Syntax_Syntax.NT
                                    (bv, FStar_Syntax_Util.t_true)] q
                                in
                             FStar_Pervasives_Native.Some uu____15214
                         | uu____15215 -> FStar_Pervasives_Native.None)
                    | FStar_Pervasives_Native.Some
                        (FStar_Syntax_Util.BaseConn
                        (lid1,(p1,uu____15218)::[])) when
                        FStar_Ident.lid_equals lid1
                          FStar_Parser_Const.not_lid
                        ->
                        let uu____15243 =
                          let uu____15244 = FStar_Syntax_Subst.compress p1
                             in
                          uu____15244.FStar_Syntax_Syntax.n  in
                        (match uu____15243 with
                         | FStar_Syntax_Syntax.Tm_bvar bv ->
                             let uu____15250 =
                               FStar_Syntax_Subst.subst
                                 [FStar_Syntax_Syntax.NT
                                    (bv, FStar_Syntax_Util.t_false)] q
                                in
                             FStar_Pervasives_Native.Some uu____15250
                         | uu____15251 -> FStar_Pervasives_Native.None)
                    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
                        (bs,pats,phi1)) ->
                        let uu____15255 =
                          FStar_Syntax_Util.destruct_typ_as_formula phi1  in
                        (match uu____15255 with
                         | FStar_Pervasives_Native.None  ->
                             let uu____15260 =
                               is_applied_maybe_squashed bs phi1  in
                             (match uu____15260 with
                              | FStar_Pervasives_Native.Some bv ->
                                  let ftrue =
                                    FStar_Syntax_Util.abs bs
                                      FStar_Syntax_Util.t_true
                                      (FStar_Pervasives_Native.Some
                                         (FStar_Syntax_Util.residual_tot
                                            FStar_Syntax_Util.ktype0))
                                     in
                                  let uu____15267 =
                                    FStar_Syntax_Subst.subst
                                      [FStar_Syntax_Syntax.NT (bv, ftrue)] q
                                     in
                                  FStar_Pervasives_Native.Some uu____15267
                              | FStar_Pervasives_Native.None  ->
                                  FStar_Pervasives_Native.None)
                         | FStar_Pervasives_Native.Some
                             (FStar_Syntax_Util.BaseConn
                             (lid1,(p1,uu____15270)::[])) when
                             FStar_Ident.lid_equals lid1
                               FStar_Parser_Const.not_lid
                             ->
                             let uu____15295 =
                               is_applied_maybe_squashed bs p1  in
                             (match uu____15295 with
                              | FStar_Pervasives_Native.Some bv ->
                                  let ffalse =
                                    FStar_Syntax_Util.abs bs
                                      FStar_Syntax_Util.t_false
                                      (FStar_Pervasives_Native.Some
                                         (FStar_Syntax_Util.residual_tot
                                            FStar_Syntax_Util.ktype0))
                                     in
                                  let uu____15302 =
                                    FStar_Syntax_Subst.subst
                                      [FStar_Syntax_Syntax.NT (bv, ffalse)] q
                                     in
                                  FStar_Pervasives_Native.Some uu____15302
                              | uu____15303 -> FStar_Pervasives_Native.None)
                         | uu____15306 -> FStar_Pervasives_Native.None)
                    | uu____15309 -> FStar_Pervasives_Native.None)
               | uu____15312 -> FStar_Pervasives_Native.None  in
             let is_const_match phi =
               let uu____15323 =
                 let uu____15324 = FStar_Syntax_Subst.compress phi  in
                 uu____15324.FStar_Syntax_Syntax.n  in
               match uu____15323 with
               | FStar_Syntax_Syntax.Tm_match (uu____15329,br::brs) ->
                   let uu____15396 = br  in
                   (match uu____15396 with
                    | (uu____15413,uu____15414,e) ->
                        let r =
                          let uu____15435 = simp_t e  in
                          match uu____15435 with
                          | FStar_Pervasives_Native.None  ->
                              FStar_Pervasives_Native.None
                          | FStar_Pervasives_Native.Some b ->
                              let uu____15441 =
                                FStar_List.for_all
                                  (fun uu____15459  ->
                                     match uu____15459 with
                                     | (uu____15472,uu____15473,e') ->
                                         let uu____15487 = simp_t e'  in
                                         uu____15487 =
                                           (FStar_Pervasives_Native.Some b))
                                  brs
                                 in
                              if uu____15441
                              then FStar_Pervasives_Native.Some b
                              else FStar_Pervasives_Native.None
                           in
                        r)
               | uu____15495 -> FStar_Pervasives_Native.None  in
             let maybe_auto_squash t =
               let uu____15500 = FStar_Syntax_Util.is_sub_singleton t  in
               if uu____15500
               then t
               else
                 FStar_Syntax_Util.mk_auto_squash FStar_Syntax_Syntax.U_zero
                   t
                in
             let squashed_head_un_auto_squash_args t =
               let maybe_un_auto_squash_arg uu____15521 =
                 match uu____15521 with
                 | (t1,q) ->
                     let uu____15534 = FStar_Syntax_Util.is_auto_squash t1
                        in
                     (match uu____15534 with
                      | FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.U_zero ,t2) -> (t2, q)
                      | uu____15562 -> (t1, q))
                  in
               let uu____15571 = FStar_Syntax_Util.head_and_args t  in
               match uu____15571 with
               | (head1,args) ->
                   let args1 = FStar_List.map maybe_un_auto_squash_arg args
                      in
                   FStar_Syntax_Syntax.mk_Tm_app head1 args1
                     FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
                in
             let rec clearly_inhabited ty =
               let uu____15633 =
                 let uu____15634 = FStar_Syntax_Util.unmeta ty  in
                 uu____15634.FStar_Syntax_Syntax.n  in
               match uu____15633 with
               | FStar_Syntax_Syntax.Tm_uinst (t,uu____15638) ->
                   clearly_inhabited t
               | FStar_Syntax_Syntax.Tm_arrow (uu____15643,c) ->
                   clearly_inhabited (FStar_Syntax_Util.comp_result c)
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   let l = FStar_Syntax_Syntax.lid_of_fv fv  in
                   (((FStar_Ident.lid_equals l FStar_Parser_Const.int_lid) ||
                       (FStar_Ident.lid_equals l FStar_Parser_Const.bool_lid))
                      ||
                      (FStar_Ident.lid_equals l FStar_Parser_Const.string_lid))
                     || (FStar_Ident.lid_equals l FStar_Parser_Const.exn_lid)
               | uu____15663 -> false  in
             let simplify1 arg =
               let uu____15686 = simp_t (FStar_Pervasives_Native.fst arg)  in
               (uu____15686, arg)  in
             let uu____15695 = is_quantified_const tm1  in
             match uu____15695 with
             | FStar_Pervasives_Native.Some tm2 ->
                 let uu____15699 = norm cfg env [] tm2  in
                 maybe_simplify_aux cfg env stack uu____15699
             | FStar_Pervasives_Native.None  ->
                 let uu____15700 =
                   let uu____15701 = FStar_Syntax_Subst.compress tm1  in
                   uu____15701.FStar_Syntax_Syntax.n  in
                 (match uu____15700 with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                           ({
                              FStar_Syntax_Syntax.n =
                                FStar_Syntax_Syntax.Tm_fvar fv;
                              FStar_Syntax_Syntax.pos = uu____15705;
                              FStar_Syntax_Syntax.vars = uu____15706;_},uu____15707);
                         FStar_Syntax_Syntax.pos = uu____15708;
                         FStar_Syntax_Syntax.vars = uu____15709;_},args)
                      ->
                      let uu____15735 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid
                         in
                      if uu____15735
                      then
                        let uu____15736 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        (match uu____15736 with
                         | (FStar_Pervasives_Native.Some (true ),uu____15783)::
                             (uu____15784,(arg,uu____15786))::[] ->
                             maybe_auto_squash arg
                         | (uu____15835,(arg,uu____15837))::(FStar_Pervasives_Native.Some
                                                             (true
                                                             ),uu____15838)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____15887)::uu____15888::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____15939::(FStar_Pervasives_Native.Some (false
                                         ),uu____15940)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____15991 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____16005 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid
                            in
                         if uu____16005
                         then
                           let uu____16006 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify1)
                              in
                           match uu____16006 with
                           | (FStar_Pervasives_Native.Some (true
                              ),uu____16053)::uu____16054::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____16105::(FStar_Pervasives_Native.Some (true
                                           ),uu____16106)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false
                              ),uu____16157)::(uu____16158,(arg,uu____16160))::[]
                               -> maybe_auto_squash arg
                           | (uu____16209,(arg,uu____16211))::(FStar_Pervasives_Native.Some
                                                               (false
                                                               ),uu____16212)::[]
                               -> maybe_auto_squash arg
                           | uu____16261 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____16275 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid
                               in
                            if uu____16275
                            then
                              let uu____16276 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify1)
                                 in
                              match uu____16276 with
                              | uu____16323::(FStar_Pervasives_Native.Some
                                              (true ),uu____16324)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false
                                 ),uu____16375)::uu____16376::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true
                                 ),uu____16427)::(uu____16428,(arg,uu____16430))::[]
                                  -> maybe_auto_squash arg
                              | (uu____16479,(p,uu____16481))::(uu____16482,
                                                                (q,uu____16484))::[]
                                  ->
                                  let uu____16531 =
                                    FStar_Syntax_Util.term_eq p q  in
                                  (if uu____16531
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____16533 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____16547 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid
                                  in
                               if uu____16547
                               then
                                 let uu____16548 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify1)
                                    in
                                 match uu____16548 with
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____16595)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____16596)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____16647)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____16648)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____16699)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____16700)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____16751)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____16752)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____16803,(arg,uu____16805))::(FStar_Pervasives_Native.Some
                                                                    (true
                                                                    ),uu____16806)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____16855)::(uu____16856,(arg,uu____16858))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____16907,(arg,uu____16909))::(FStar_Pervasives_Native.Some
                                                                    (false
                                                                    ),uu____16910)::[]
                                     ->
                                     let uu____16959 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____16959
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____16960)::(uu____16961,(arg,uu____16963))::[]
                                     ->
                                     let uu____17012 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____17012
                                 | (uu____17013,(p,uu____17015))::(uu____17016,
                                                                   (q,uu____17018))::[]
                                     ->
                                     let uu____17065 =
                                       FStar_Syntax_Util.term_eq p q  in
                                     (if uu____17065
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____17067 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____17081 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid
                                     in
                                  if uu____17081
                                  then
                                    let uu____17082 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify1)
                                       in
                                    match uu____17082 with
                                    | (FStar_Pervasives_Native.Some (true
                                       ),uu____17129)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false
                                       ),uu____17160)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____17191 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____17205 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid
                                        in
                                     if uu____17205
                                     then
                                       match args with
                                       | (t,uu____17207)::[] ->
                                           let uu____17224 =
                                             let uu____17225 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____17225.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____17224 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____17228::[],body,uu____17230)
                                                ->
                                                let uu____17257 = simp_t body
                                                   in
                                                (match uu____17257 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____17260 -> tm1)
                                            | uu____17263 -> tm1)
                                       | (ty,FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____17265))::(t,uu____17267)::[]
                                           ->
                                           let uu____17306 =
                                             let uu____17307 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____17307.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____17306 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____17310::[],body,uu____17312)
                                                ->
                                                let uu____17339 = simp_t body
                                                   in
                                                (match uu____17339 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false ) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____17342 -> tm1)
                                            | uu____17345 -> tm1)
                                       | uu____17346 -> tm1
                                     else
                                       (let uu____17356 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid
                                           in
                                        if uu____17356
                                        then
                                          match args with
                                          | (t,uu____17358)::[] ->
                                              let uu____17375 =
                                                let uu____17376 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____17376.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____17375 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____17379::[],body,uu____17381)
                                                   ->
                                                   let uu____17408 =
                                                     simp_t body  in
                                                   (match uu____17408 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____17411 -> tm1)
                                               | uu____17414 -> tm1)
                                          | (ty,FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____17416))::(t,uu____17418)::[]
                                              ->
                                              let uu____17457 =
                                                let uu____17458 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____17458.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____17457 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____17461::[],body,uu____17463)
                                                   ->
                                                   let uu____17490 =
                                                     simp_t body  in
                                                   (match uu____17490 with
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
                                                    | uu____17493 -> tm1)
                                               | uu____17496 -> tm1)
                                          | uu____17497 -> tm1
                                        else
                                          (let uu____17507 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid
                                              in
                                           if uu____17507
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____17508;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____17509;_},uu____17510)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____17527;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____17528;_},uu____17529)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____17546 -> tm1
                                           else
                                             (let uu____17556 =
                                                FStar_Syntax_Util.is_auto_squash
                                                  tm1
                                                 in
                                              match uu____17556 with
                                              | FStar_Pervasives_Native.Some
                                                  (FStar_Syntax_Syntax.U_zero
                                                   ,t)
                                                  when
                                                  FStar_Syntax_Util.is_sub_singleton
                                                    t
                                                  -> t
                                              | uu____17576 ->
                                                  reduce_equality cfg env
                                                    stack tm1))))))))
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____17586;
                         FStar_Syntax_Syntax.vars = uu____17587;_},args)
                      ->
                      let uu____17609 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid
                         in
                      if uu____17609
                      then
                        let uu____17610 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        (match uu____17610 with
                         | (FStar_Pervasives_Native.Some (true ),uu____17657)::
                             (uu____17658,(arg,uu____17660))::[] ->
                             maybe_auto_squash arg
                         | (uu____17709,(arg,uu____17711))::(FStar_Pervasives_Native.Some
                                                             (true
                                                             ),uu____17712)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____17761)::uu____17762::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____17813::(FStar_Pervasives_Native.Some (false
                                         ),uu____17814)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____17865 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____17879 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid
                            in
                         if uu____17879
                         then
                           let uu____17880 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify1)
                              in
                           match uu____17880 with
                           | (FStar_Pervasives_Native.Some (true
                              ),uu____17927)::uu____17928::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____17979::(FStar_Pervasives_Native.Some (true
                                           ),uu____17980)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false
                              ),uu____18031)::(uu____18032,(arg,uu____18034))::[]
                               -> maybe_auto_squash arg
                           | (uu____18083,(arg,uu____18085))::(FStar_Pervasives_Native.Some
                                                               (false
                                                               ),uu____18086)::[]
                               -> maybe_auto_squash arg
                           | uu____18135 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____18149 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid
                               in
                            if uu____18149
                            then
                              let uu____18150 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify1)
                                 in
                              match uu____18150 with
                              | uu____18197::(FStar_Pervasives_Native.Some
                                              (true ),uu____18198)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false
                                 ),uu____18249)::uu____18250::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true
                                 ),uu____18301)::(uu____18302,(arg,uu____18304))::[]
                                  -> maybe_auto_squash arg
                              | (uu____18353,(p,uu____18355))::(uu____18356,
                                                                (q,uu____18358))::[]
                                  ->
                                  let uu____18405 =
                                    FStar_Syntax_Util.term_eq p q  in
                                  (if uu____18405
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____18407 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____18421 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid
                                  in
                               if uu____18421
                               then
                                 let uu____18422 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify1)
                                    in
                                 match uu____18422 with
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____18469)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____18470)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____18521)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____18522)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____18573)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____18574)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____18625)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____18626)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____18677,(arg,uu____18679))::(FStar_Pervasives_Native.Some
                                                                    (true
                                                                    ),uu____18680)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____18729)::(uu____18730,(arg,uu____18732))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____18781,(arg,uu____18783))::(FStar_Pervasives_Native.Some
                                                                    (false
                                                                    ),uu____18784)::[]
                                     ->
                                     let uu____18833 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____18833
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____18834)::(uu____18835,(arg,uu____18837))::[]
                                     ->
                                     let uu____18886 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____18886
                                 | (uu____18887,(p,uu____18889))::(uu____18890,
                                                                   (q,uu____18892))::[]
                                     ->
                                     let uu____18939 =
                                       FStar_Syntax_Util.term_eq p q  in
                                     (if uu____18939
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____18941 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____18955 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid
                                     in
                                  if uu____18955
                                  then
                                    let uu____18956 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify1)
                                       in
                                    match uu____18956 with
                                    | (FStar_Pervasives_Native.Some (true
                                       ),uu____19003)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false
                                       ),uu____19034)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____19065 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____19079 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid
                                        in
                                     if uu____19079
                                     then
                                       match args with
                                       | (t,uu____19081)::[] ->
                                           let uu____19098 =
                                             let uu____19099 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____19099.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____19098 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____19102::[],body,uu____19104)
                                                ->
                                                let uu____19131 = simp_t body
                                                   in
                                                (match uu____19131 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____19134 -> tm1)
                                            | uu____19137 -> tm1)
                                       | (ty,FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____19139))::(t,uu____19141)::[]
                                           ->
                                           let uu____19180 =
                                             let uu____19181 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____19181.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____19180 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____19184::[],body,uu____19186)
                                                ->
                                                let uu____19213 = simp_t body
                                                   in
                                                (match uu____19213 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false ) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____19216 -> tm1)
                                            | uu____19219 -> tm1)
                                       | uu____19220 -> tm1
                                     else
                                       (let uu____19230 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid
                                           in
                                        if uu____19230
                                        then
                                          match args with
                                          | (t,uu____19232)::[] ->
                                              let uu____19249 =
                                                let uu____19250 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____19250.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____19249 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____19253::[],body,uu____19255)
                                                   ->
                                                   let uu____19282 =
                                                     simp_t body  in
                                                   (match uu____19282 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____19285 -> tm1)
                                               | uu____19288 -> tm1)
                                          | (ty,FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____19290))::(t,uu____19292)::[]
                                              ->
                                              let uu____19331 =
                                                let uu____19332 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____19332.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____19331 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____19335::[],body,uu____19337)
                                                   ->
                                                   let uu____19364 =
                                                     simp_t body  in
                                                   (match uu____19364 with
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
                                                    | uu____19367 -> tm1)
                                               | uu____19370 -> tm1)
                                          | uu____19371 -> tm1
                                        else
                                          (let uu____19381 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid
                                              in
                                           if uu____19381
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____19382;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____19383;_},uu____19384)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____19401;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____19402;_},uu____19403)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____19420 -> tm1
                                           else
                                             (let uu____19430 =
                                                FStar_Syntax_Util.is_auto_squash
                                                  tm1
                                                 in
                                              match uu____19430 with
                                              | FStar_Pervasives_Native.Some
                                                  (FStar_Syntax_Syntax.U_zero
                                                   ,t)
                                                  when
                                                  FStar_Syntax_Util.is_sub_singleton
                                                    t
                                                  -> t
                                              | uu____19450 ->
                                                  reduce_equality cfg env
                                                    stack tm1))))))))
                  | FStar_Syntax_Syntax.Tm_refine (bv,t) ->
                      let uu____19465 = simp_t t  in
                      (match uu____19465 with
                       | FStar_Pervasives_Native.Some (true ) ->
                           bv.FStar_Syntax_Syntax.sort
                       | FStar_Pervasives_Native.Some (false ) -> tm1
                       | FStar_Pervasives_Native.None  -> tm1)
                  | FStar_Syntax_Syntax.Tm_match uu____19468 ->
                      let uu____19491 = is_const_match tm1  in
                      (match uu____19491 with
                       | FStar_Pervasives_Native.Some (true ) ->
                           w FStar_Syntax_Util.t_true
                       | FStar_Pervasives_Native.Some (false ) ->
                           w FStar_Syntax_Util.t_false
                       | FStar_Pervasives_Native.None  -> tm1)
                  | uu____19494 -> tm1))

and (rebuild :
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          log cfg
            (fun uu____19505  ->
               let uu____19506 = FStar_Syntax_Print.tag_of_term t  in
               let uu____19507 = FStar_Syntax_Print.term_to_string t  in
               let uu____19508 =
                 FStar_Util.string_of_int (FStar_List.length env)  in
               let uu____19515 =
                 let uu____19516 =
                   let uu____19519 = firstn (Prims.parse_int "4") stack  in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____19519
                    in
                 stack_to_string uu____19516  in
               FStar_Util.print4
                 ">>> %s\nRebuild %s with %s env elements and top of the stack %s \n"
                 uu____19506 uu____19507 uu____19508 uu____19515);
          (let t1 = maybe_simplify cfg env stack t  in
           match stack with
           | [] -> t1
           | (Debug (tm,time_then))::stack1 ->
               (if (cfg.debug).print_normalized
                then
                  (let time_now = FStar_Util.now ()  in
                   let uu____19550 =
                     let uu____19551 =
                       let uu____19552 =
                         FStar_Util.time_diff time_then time_now  in
                       FStar_Pervasives_Native.snd uu____19552  in
                     FStar_Util.string_of_int uu____19551  in
                   let uu____19557 = FStar_Syntax_Print.term_to_string tm  in
                   let uu____19558 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.print3 "Normalized (%s ms) %s\n\tto %s\n"
                     uu____19550 uu____19557 uu____19558)
                else ();
                rebuild cfg env stack1 t1)
           | (Cfg cfg1)::stack1 -> rebuild cfg1 env stack1 t1
           | (Meta (m,r))::stack1 ->
               let t2 = mk (FStar_Syntax_Syntax.Tm_meta (t1, m)) r  in
               rebuild cfg env stack1 t2
           | (MemoLazy r)::stack1 ->
               (set_memo cfg r (env, t1);
                log cfg
                  (fun uu____19612  ->
                     let uu____19613 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 "\tSet memo %s\n" uu____19613);
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
               let uu____19649 =
                 let uu___174_19650 = FStar_Syntax_Util.abs bs1 t1 lopt1  in
                 {
                   FStar_Syntax_Syntax.n =
                     (uu___174_19650.FStar_Syntax_Syntax.n);
                   FStar_Syntax_Syntax.pos = r;
                   FStar_Syntax_Syntax.vars =
                     (uu___174_19650.FStar_Syntax_Syntax.vars)
                 }  in
               rebuild cfg env stack1 uu____19649
           | (Arg (Univ uu____19651,uu____19652,uu____19653))::uu____19654 ->
               failwith "Impossible"
           | (Arg (Dummy ,uu____19657,uu____19658))::uu____19659 ->
               failwith "Impossible"
           | (UnivArgs (us,r))::stack1 ->
               let t2 = FStar_Syntax_Syntax.mk_Tm_uinst t1 us  in
               rebuild cfg env stack1 t2
           | (Arg (Clos (env_arg,tm,uu____19674,uu____19675),aq,r))::stack1
               when
               let uu____19725 = head_of t1  in
               FStar_Syntax_Util.is_fstar_tactics_by_tactic uu____19725 ->
               let t2 =
                 let uu____19729 =
                   let uu____19730 =
                     let uu____19731 = closure_as_term cfg env_arg tm  in
                     (uu____19731, aq)  in
                   FStar_Syntax_Syntax.extend_app t1 uu____19730  in
                 uu____19729 FStar_Pervasives_Native.None r  in
               rebuild cfg env stack1 t2
           | (Arg (Clos (env_arg,tm,m,uu____19737),aq,r))::stack1 ->
               (log cfg
                  (fun uu____19790  ->
                     let uu____19791 = FStar_Syntax_Print.term_to_string tm
                        in
                     FStar_Util.print1 "Rebuilding with arg %s\n" uu____19791);
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
                  (let uu____19801 = FStar_ST.op_Bang m  in
                   match uu____19801 with
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
                   | FStar_Pervasives_Native.Some (uu____19938,a) ->
                       let t2 =
                         FStar_Syntax_Syntax.extend_app t1 (a, aq)
                           FStar_Pervasives_Native.None r
                          in
                       rebuild cfg env_arg stack1 t2))
           | (App (env1,head1,aq,r))::stack' when should_reify cfg stack ->
               let t0 = t1  in
               let fallback msg uu____19985 =
                 log cfg
                   (fun uu____19989  ->
                      let uu____19990 = FStar_Syntax_Print.term_to_string t1
                         in
                      FStar_Util.print2 "Not reifying%s: %s\n" msg
                        uu____19990);
                 (let t2 =
                    FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                      FStar_Pervasives_Native.None r
                     in
                  rebuild cfg env1 stack' t2)
                  in
               let uu____19994 =
                 let uu____19995 = FStar_Syntax_Subst.compress t1  in
                 uu____19995.FStar_Syntax_Syntax.n  in
               (match uu____19994 with
                | FStar_Syntax_Syntax.Tm_meta
                    (t2,FStar_Syntax_Syntax.Meta_monadic (m,ty)) ->
                    do_reify_monadic (fallback " (1)") cfg env1 stack t2 m ty
                | FStar_Syntax_Syntax.Tm_meta
                    (t2,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,ty))
                    ->
                    let lifted =
                      let uu____20022 = closure_as_term cfg env1 ty  in
                      reify_lift cfg t2 msrc mtgt uu____20022  in
                    (log cfg
                       (fun uu____20026  ->
                          let uu____20027 =
                            FStar_Syntax_Print.term_to_string lifted  in
                          FStar_Util.print1 "Reified lift to (1): %s\n"
                            uu____20027);
                     (let uu____20028 = FStar_List.tl stack  in
                      norm cfg env1 uu____20028 lifted))
                | FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reflect uu____20029);
                       FStar_Syntax_Syntax.pos = uu____20030;
                       FStar_Syntax_Syntax.vars = uu____20031;_},(e,uu____20033)::[])
                    -> norm cfg env1 stack' e
                | FStar_Syntax_Syntax.Tm_app uu____20062 when
                    (cfg.steps).primops ->
                    let uu____20077 = FStar_Syntax_Util.head_and_args t1  in
                    (match uu____20077 with
                     | (hd1,args) ->
                         let uu____20114 =
                           let uu____20115 = FStar_Syntax_Util.un_uinst hd1
                              in
                           uu____20115.FStar_Syntax_Syntax.n  in
                         (match uu____20114 with
                          | FStar_Syntax_Syntax.Tm_fvar fv ->
                              let uu____20119 = find_prim_step cfg fv  in
                              (match uu____20119 with
                               | FStar_Pervasives_Native.Some
                                   { name = uu____20122; arity = uu____20123;
                                     auto_reflect =
                                       FStar_Pervasives_Native.Some n1;
                                     strong_reduction_ok = uu____20125;
                                     requires_binder_substitution =
                                       uu____20126;
                                     interpretation = uu____20127;_}
                                   when (FStar_List.length args) = n1 ->
                                   norm cfg env1 stack' t1
                               | uu____20140 -> fallback " (3)" ())
                          | uu____20143 -> fallback " (4)" ()))
                | uu____20144 -> fallback " (2)" ())
           | (App (env1,head1,aq,r))::stack1 ->
               let t2 =
                 FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                   FStar_Pervasives_Native.None r
                  in
               rebuild cfg env1 stack1 t2
           | (Match (env1,branches,r))::stack1 ->
               (log cfg
                  (fun uu____20164  ->
                     let uu____20165 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1
                       "Rebuilding with match, scrutinee is %s ...\n"
                       uu____20165);
                (let scrutinee = t1  in
                 let norm_and_rebuild_match uu____20170 =
                   log cfg
                     (fun uu____20175  ->
                        let uu____20176 =
                          FStar_Syntax_Print.term_to_string scrutinee  in
                        let uu____20177 =
                          let uu____20178 =
                            FStar_All.pipe_right branches
                              (FStar_List.map
                                 (fun uu____20195  ->
                                    match uu____20195 with
                                    | (p,uu____20205,uu____20206) ->
                                        FStar_Syntax_Print.pat_to_string p))
                             in
                          FStar_All.pipe_right uu____20178
                            (FStar_String.concat "\n\t")
                           in
                        FStar_Util.print2
                          "match is irreducible: scrutinee=%s\nbranches=%s\n"
                          uu____20176 uu____20177);
                   (let whnf = (cfg.steps).weak || (cfg.steps).hnf  in
                    let cfg_exclude_iota_zeta =
                      let new_delta =
                        FStar_All.pipe_right cfg.delta_level
                          (FStar_List.filter
                             (fun uu___91_20223  ->
                                match uu___91_20223 with
                                | FStar_TypeChecker_Env.Inlining  -> true
                                | FStar_TypeChecker_Env.Eager_unfolding_only 
                                    -> true
                                | uu____20224 -> false))
                         in
                      let uu___175_20225 = cfg  in
                      {
                        steps =
                          (let uu___176_20228 = cfg.steps  in
                           {
                             beta = (uu___176_20228.beta);
                             iota = (uu___176_20228.iota);
                             zeta = false;
                             weak = (uu___176_20228.weak);
                             hnf = (uu___176_20228.hnf);
                             primops = (uu___176_20228.primops);
                             no_delta_steps = (uu___176_20228.no_delta_steps);
                             unfold_until = (uu___176_20228.unfold_until);
                             unfold_only = (uu___176_20228.unfold_only);
                             unfold_attr = (uu___176_20228.unfold_attr);
                             unfold_tac = (uu___176_20228.unfold_tac);
                             pure_subterms_within_computations =
                               (uu___176_20228.pure_subterms_within_computations);
                             simplify = (uu___176_20228.simplify);
                             erase_universes =
                               (uu___176_20228.erase_universes);
                             allow_unbound_universes =
                               (uu___176_20228.allow_unbound_universes);
                             reify_ = (uu___176_20228.reify_);
                             compress_uvars = (uu___176_20228.compress_uvars);
                             no_full_norm = (uu___176_20228.no_full_norm);
                             check_no_uvars = (uu___176_20228.check_no_uvars);
                             unmeta = (uu___176_20228.unmeta);
                             unascribe = (uu___176_20228.unascribe)
                           });
                        tcenv = (uu___175_20225.tcenv);
                        debug = (uu___175_20225.debug);
                        delta_level = new_delta;
                        primitive_steps = (uu___175_20225.primitive_steps);
                        strong = true;
                        memoize_lazy = (uu___175_20225.memoize_lazy);
                        normalize_pure_lets =
                          (uu___175_20225.normalize_pure_lets)
                      }  in
                    let norm_or_whnf env2 t2 =
                      if whnf
                      then closure_as_term cfg_exclude_iota_zeta env2 t2
                      else norm cfg_exclude_iota_zeta env2 [] t2  in
                    let rec norm_pat env2 p =
                      match p.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_constant uu____20260 ->
                          (p, env2)
                      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                          let uu____20281 =
                            FStar_All.pipe_right pats
                              (FStar_List.fold_left
                                 (fun uu____20341  ->
                                    fun uu____20342  ->
                                      match (uu____20341, uu____20342) with
                                      | ((pats1,env3),(p1,b)) ->
                                          let uu____20433 = norm_pat env3 p1
                                             in
                                          (match uu____20433 with
                                           | (p2,env4) ->
                                               (((p2, b) :: pats1), env4)))
                                 ([], env2))
                             in
                          (match uu____20281 with
                           | (pats1,env3) ->
                               ((let uu___177_20515 = p  in
                                 {
                                   FStar_Syntax_Syntax.v =
                                     (FStar_Syntax_Syntax.Pat_cons
                                        (fv, (FStar_List.rev pats1)));
                                   FStar_Syntax_Syntax.p =
                                     (uu___177_20515.FStar_Syntax_Syntax.p)
                                 }), env3))
                      | FStar_Syntax_Syntax.Pat_var x ->
                          let x1 =
                            let uu___178_20534 = x  in
                            let uu____20535 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___178_20534.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___178_20534.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____20535
                            }  in
                          ((let uu___179_20549 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_var x1);
                              FStar_Syntax_Syntax.p =
                                (uu___179_20549.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_wild x ->
                          let x1 =
                            let uu___180_20560 = x  in
                            let uu____20561 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___180_20560.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___180_20560.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____20561
                            }  in
                          ((let uu___181_20575 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_wild x1);
                              FStar_Syntax_Syntax.p =
                                (uu___181_20575.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                          let x1 =
                            let uu___182_20591 = x  in
                            let uu____20592 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___182_20591.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___182_20591.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____20592
                            }  in
                          let t3 = norm_or_whnf env2 t2  in
                          ((let uu___183_20599 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_dot_term (x1, t3));
                              FStar_Syntax_Syntax.p =
                                (uu___183_20599.FStar_Syntax_Syntax.p)
                            }), env2)
                       in
                    let branches1 =
                      match env1 with
                      | [] when whnf -> branches
                      | uu____20609 ->
                          FStar_All.pipe_right branches
                            (FStar_List.map
                               (fun branch1  ->
                                  let uu____20623 =
                                    FStar_Syntax_Subst.open_branch branch1
                                     in
                                  match uu____20623 with
                                  | (p,wopt,e) ->
                                      let uu____20643 = norm_pat env1 p  in
                                      (match uu____20643 with
                                       | (p1,env2) ->
                                           let wopt1 =
                                             match wopt with
                                             | FStar_Pervasives_Native.None 
                                                 ->
                                                 FStar_Pervasives_Native.None
                                             | FStar_Pervasives_Native.Some w
                                                 ->
                                                 let uu____20668 =
                                                   norm_or_whnf env2 w  in
                                                 FStar_Pervasives_Native.Some
                                                   uu____20668
                                              in
                                           let e1 = norm_or_whnf env2 e  in
                                           FStar_Syntax_Util.branch
                                             (p1, wopt1, e1))))
                       in
                    let uu____20674 =
                      mk
                        (FStar_Syntax_Syntax.Tm_match (scrutinee, branches1))
                        r
                       in
                    rebuild cfg env1 stack1 uu____20674)
                    in
                 let rec is_cons head1 =
                   let uu____20679 =
                     let uu____20680 = FStar_Syntax_Subst.compress head1  in
                     uu____20680.FStar_Syntax_Syntax.n  in
                   match uu____20679 with
                   | FStar_Syntax_Syntax.Tm_uinst (h,uu____20684) ->
                       is_cons h
                   | FStar_Syntax_Syntax.Tm_constant uu____20689 -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____20690;
                         FStar_Syntax_Syntax.fv_delta = uu____20691;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Data_ctor );_}
                       -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____20692;
                         FStar_Syntax_Syntax.fv_delta = uu____20693;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Record_ctor uu____20694);_}
                       -> true
                   | uu____20701 -> false  in
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
                   let uu____20846 =
                     FStar_Syntax_Util.head_and_args scrutinee1  in
                   match uu____20846 with
                   | (head1,args) ->
                       (match p.FStar_Syntax_Syntax.v with
                        | FStar_Syntax_Syntax.Pat_var bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_wild bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_dot_term uu____20933 ->
                            FStar_Util.Inl []
                        | FStar_Syntax_Syntax.Pat_constant s ->
                            (match scrutinee1.FStar_Syntax_Syntax.n with
                             | FStar_Syntax_Syntax.Tm_constant s' when
                                 FStar_Const.eq_const s s' ->
                                 FStar_Util.Inl []
                             | uu____20972 ->
                                 let uu____20973 =
                                   let uu____20974 = is_cons head1  in
                                   Prims.op_Negation uu____20974  in
                                 FStar_Util.Inr uu____20973)
                        | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                            let uu____20999 =
                              let uu____21000 =
                                FStar_Syntax_Util.un_uinst head1  in
                              uu____21000.FStar_Syntax_Syntax.n  in
                            (match uu____20999 with
                             | FStar_Syntax_Syntax.Tm_fvar fv' when
                                 FStar_Syntax_Syntax.fv_eq fv fv' ->
                                 matches_args [] args arg_pats
                             | uu____21018 ->
                                 let uu____21019 =
                                   let uu____21020 = is_cons head1  in
                                   Prims.op_Negation uu____21020  in
                                 FStar_Util.Inr uu____21019))
                 
                 and matches_args out a p =
                   match (a, p) with
                   | ([],[]) -> FStar_Util.Inl out
                   | ((t2,uu____21089)::rest_a,(p1,uu____21092)::rest_p) ->
                       let uu____21136 = matches_pat t2 p1  in
                       (match uu____21136 with
                        | FStar_Util.Inl s ->
                            matches_args (FStar_List.append out s) rest_a
                              rest_p
                        | m -> m)
                   | uu____21185 -> FStar_Util.Inr false
                  in
                 let rec matches scrutinee1 p =
                   match p with
                   | [] -> norm_and_rebuild_match ()
                   | (p1,wopt,b)::rest ->
                       let uu____21291 = matches_pat scrutinee1 p1  in
                       (match uu____21291 with
                        | FStar_Util.Inr (false ) -> matches scrutinee1 rest
                        | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                        | FStar_Util.Inl s ->
                            (log cfg
                               (fun uu____21331  ->
                                  let uu____21332 =
                                    FStar_Syntax_Print.pat_to_string p1  in
                                  let uu____21333 =
                                    let uu____21334 =
                                      FStar_List.map
                                        (fun uu____21344  ->
                                           match uu____21344 with
                                           | (uu____21349,t2) ->
                                               FStar_Syntax_Print.term_to_string
                                                 t2) s
                                       in
                                    FStar_All.pipe_right uu____21334
                                      (FStar_String.concat "; ")
                                     in
                                  FStar_Util.print2
                                    "Matches pattern %s with subst = %s\n"
                                    uu____21332 uu____21333);
                             (let env2 =
                                FStar_List.fold_left
                                  (fun env2  ->
                                     fun uu____21380  ->
                                       match uu____21380 with
                                       | (bv,t2) ->
                                           let uu____21403 =
                                             let uu____21410 =
                                               let uu____21413 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   bv
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 uu____21413
                                                in
                                             let uu____21414 =
                                               let uu____21415 =
                                                 let uu____21446 =
                                                   FStar_Util.mk_ref
                                                     (FStar_Pervasives_Native.Some
                                                        ([], t2))
                                                    in
                                                 ([], t2, uu____21446, false)
                                                  in
                                               Clos uu____21415  in
                                             (uu____21410, uu____21414)  in
                                           uu____21403 :: env2) env1 s
                                 in
                              let uu____21563 = guard_when_clause wopt b rest
                                 in
                              norm cfg env2 stack1 uu____21563)))
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
    let uu____21586 =
      let uu____21589 = FStar_ST.op_Bang plugins  in p :: uu____21589  in
    FStar_ST.op_Colon_Equals plugins uu____21586  in
  let retrieve uu____21687 = FStar_ST.op_Bang plugins  in
  (register, retrieve) 
let (register_plugin : primitive_step -> Prims.unit) =
  fun p  -> FStar_Pervasives_Native.fst plugins p 
let (retrieve_plugins : Prims.unit -> primitive_step Prims.list) =
  fun uu____21752  -> FStar_Pervasives_Native.snd plugins () 
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
               (fun uu___92_21785  ->
                  match uu___92_21785 with
                  | UnfoldUntil k -> [FStar_TypeChecker_Env.Unfold k]
                  | Eager_unfolding  ->
                      [FStar_TypeChecker_Env.Eager_unfolding_only]
                  | Inlining  -> [FStar_TypeChecker_Env.Inlining]
                  | UnfoldTac  -> [FStar_TypeChecker_Env.UnfoldTac]
                  | uu____21789 -> []))
           in
        let d1 =
          match d with
          | [] -> [FStar_TypeChecker_Env.NoDelta]
          | uu____21795 -> d  in
        let uu____21798 = to_fsteps s  in
        let uu____21799 =
          let uu____21800 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Norm")  in
          let uu____21801 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Primops")  in
          let uu____21802 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "380")  in
          let uu____21803 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "NormDelayed")
             in
          let uu____21804 =
            FStar_TypeChecker_Env.debug e
              (FStar_Options.Other "print_normalized_terms")
             in
          {
            gen = uu____21800;
            primop = uu____21801;
            b380 = uu____21802;
            norm_delayed = uu____21803;
            print_normalized = uu____21804
          }  in
        let uu____21805 =
          let uu____21808 =
            let uu____21811 = retrieve_plugins ()  in
            FStar_List.append uu____21811 psteps  in
          add_steps built_in_primitive_steps uu____21808  in
        let uu____21814 =
          (FStar_Options.normalize_pure_terms_for_extraction ()) ||
            (let uu____21816 =
               FStar_All.pipe_right s
                 (FStar_List.contains PureSubtermsWithinComputations)
                in
             Prims.op_Negation uu____21816)
           in
        {
          steps = uu____21798;
          tcenv = e;
          debug = uu____21799;
          delta_level = d1;
          primitive_steps = uu____21805;
          strong = false;
          memoize_lazy = true;
          normalize_pure_lets = uu____21814
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
      fun t  -> let uu____21874 = config s e  in norm_comp uu____21874 [] t
  
let (normalize_universe :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun u  ->
      let uu____21887 = config [] env  in norm_universe uu____21887 [] u
  
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
        let uu____21905 = norm cfg [] [] t  in
        FStar_Syntax_Util.non_informative uu____21905  in
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____21912 -> c
      | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
          let uu___184_21931 = c  in
          {
            FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
            FStar_Syntax_Syntax.pos =
              (uu___184_21931.FStar_Syntax_Syntax.pos);
            FStar_Syntax_Syntax.vars =
              (uu___184_21931.FStar_Syntax_Syntax.vars)
          }
      | FStar_Syntax_Syntax.Comp ct ->
          let l =
            FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
              ct.FStar_Syntax_Syntax.effect_name
             in
          let uu____21938 =
            (FStar_Syntax_Util.is_ghost_effect l) &&
              (non_info ct.FStar_Syntax_Syntax.result_typ)
             in
          if uu____21938
          then
            let ct1 =
              let uu____21940 =
                downgrade_ghost_effect_name
                  ct.FStar_Syntax_Syntax.effect_name
                 in
              match uu____21940 with
              | FStar_Pervasives_Native.Some pure_eff ->
                  let flags1 =
                    let uu____21947 =
                      FStar_Ident.lid_equals pure_eff
                        FStar_Parser_Const.effect_Tot_lid
                       in
                    if uu____21947
                    then FStar_Syntax_Syntax.TOTAL ::
                      (ct.FStar_Syntax_Syntax.flags)
                    else ct.FStar_Syntax_Syntax.flags  in
                  let uu___185_21951 = ct  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___185_21951.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name = pure_eff;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___185_21951.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___185_21951.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags = flags1
                  }
              | FStar_Pervasives_Native.None  ->
                  let ct1 =
                    FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c
                     in
                  let uu___186_21953 = ct1  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___186_21953.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name =
                      FStar_Parser_Const.effect_PURE_lid;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___186_21953.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___186_21953.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags =
                      (uu___186_21953.FStar_Syntax_Syntax.flags)
                  }
               in
            let uu___187_21954 = c  in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
              FStar_Syntax_Syntax.pos =
                (uu___187_21954.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___187_21954.FStar_Syntax_Syntax.vars)
            }
          else c
      | uu____21956 -> c
  
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
        let uu____21968 = norm cfg [] [] t  in
        FStar_Syntax_Util.non_informative uu____21968  in
      let uu____21975 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ)
         in
      if uu____21975
      then
        let uu____21976 =
          downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name  in
        match uu____21976 with
        | FStar_Pervasives_Native.Some pure_eff ->
            FStar_Syntax_Syntax.mk_lcomp pure_eff
              lc.FStar_Syntax_Syntax.res_typ lc.FStar_Syntax_Syntax.cflags
              (fun uu____21982  ->
                 let uu____21983 = FStar_Syntax_Syntax.lcomp_comp lc  in
                 ghost_to_pure env uu____21983)
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
            ((let uu____22000 =
                let uu____22005 =
                  let uu____22006 = FStar_Util.message_of_exn e  in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____22006
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____22005)  in
              FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____22000);
             t)
         in
      FStar_Syntax_Print.term_to_string' env.FStar_TypeChecker_Env.dsenv t1
  
let (comp_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string) =
  fun env  ->
    fun c  ->
      let c1 =
        try
          let uu____22017 = config [AllowUnboundUniverses] env  in
          norm_comp uu____22017 [] c
        with
        | e ->
            ((let uu____22030 =
                let uu____22035 =
                  let uu____22036 = FStar_Util.message_of_exn e  in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____22036
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____22035)  in
              FStar_Errors.log_issue c.FStar_Syntax_Syntax.pos uu____22030);
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
                   let uu____22073 =
                     let uu____22074 =
                       let uu____22081 = FStar_Syntax_Util.mk_conj phi1 phi
                          in
                       (y, uu____22081)  in
                     FStar_Syntax_Syntax.Tm_refine uu____22074  in
                   mk uu____22073 t01.FStar_Syntax_Syntax.pos
               | uu____22086 -> t2)
          | uu____22087 -> t2  in
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
        let uu____22127 = FStar_Syntax_Util.arrow_formals_comp t_e  in
        match uu____22127 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____22156 ->
                 let uu____22163 = FStar_Syntax_Util.abs_formals e  in
                 (match uu____22163 with
                  | (actuals,uu____22173,uu____22174) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____22188 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders
                            in
                         match uu____22188 with
                         | (binders,args) ->
                             let uu____22205 =
                               FStar_Syntax_Syntax.mk_Tm_app e args
                                 FStar_Pervasives_Native.None
                                 e.FStar_Syntax_Syntax.pos
                                in
                             FStar_Syntax_Util.abs binders uu____22205
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
      | uu____22213 ->
          let uu____22214 = FStar_Syntax_Util.head_and_args t  in
          (match uu____22214 with
           | (head1,args) ->
               let uu____22251 =
                 let uu____22252 = FStar_Syntax_Subst.compress head1  in
                 uu____22252.FStar_Syntax_Syntax.n  in
               (match uu____22251 with
                | FStar_Syntax_Syntax.Tm_uvar (uu____22255,thead) ->
                    let uu____22281 = FStar_Syntax_Util.arrow_formals thead
                       in
                    (match uu____22281 with
                     | (formals,tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____22323 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___192_22331 = env  in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___192_22331.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___192_22331.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___192_22331.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___192_22331.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___192_22331.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___192_22331.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___192_22331.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___192_22331.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___192_22331.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___192_22331.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___192_22331.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___192_22331.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___192_22331.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___192_22331.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___192_22331.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___192_22331.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___192_22331.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___192_22331.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___192_22331.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___192_22331.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___192_22331.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___192_22331.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___192_22331.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___192_22331.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                     =
                                     (uu___192_22331.FStar_TypeChecker_Env.qtbl_name_and_index);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___192_22331.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth_hook =
                                     (uu___192_22331.FStar_TypeChecker_Env.synth_hook);
                                   FStar_TypeChecker_Env.splice =
                                     (uu___192_22331.FStar_TypeChecker_Env.splice);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___192_22331.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___192_22331.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___192_22331.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___192_22331.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.dep_graph =
                                     (uu___192_22331.FStar_TypeChecker_Env.dep_graph)
                                 }) t
                               in
                            match uu____22323 with
                            | (uu____22332,ty,uu____22334) ->
                                eta_expand_with_type env t ty))
                | uu____22335 ->
                    let uu____22336 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___193_22344 = env  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___193_22344.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___193_22344.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___193_22344.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___193_22344.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___193_22344.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___193_22344.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___193_22344.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___193_22344.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___193_22344.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___193_22344.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___193_22344.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___193_22344.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___193_22344.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___193_22344.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___193_22344.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___193_22344.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___193_22344.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___193_22344.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.failhard =
                             (uu___193_22344.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___193_22344.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___193_22344.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___193_22344.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___193_22344.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___193_22344.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qtbl_name_and_index =
                             (uu___193_22344.FStar_TypeChecker_Env.qtbl_name_and_index);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___193_22344.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth_hook =
                             (uu___193_22344.FStar_TypeChecker_Env.synth_hook);
                           FStar_TypeChecker_Env.splice =
                             (uu___193_22344.FStar_TypeChecker_Env.splice);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___193_22344.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___193_22344.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___193_22344.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___193_22344.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.dep_graph =
                             (uu___193_22344.FStar_TypeChecker_Env.dep_graph)
                         }) t
                       in
                    (match uu____22336 with
                     | (uu____22345,ty,uu____22347) ->
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
      let uu___194_22404 = x  in
      let uu____22405 = elim_delayed_subst_term x.FStar_Syntax_Syntax.sort
         in
      {
        FStar_Syntax_Syntax.ppname =
          (uu___194_22404.FStar_Syntax_Syntax.ppname);
        FStar_Syntax_Syntax.index =
          (uu___194_22404.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = uu____22405
      }  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____22408 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_bvar uu____22433 -> t1
    | FStar_Syntax_Syntax.Tm_name uu____22434 -> t1
    | FStar_Syntax_Syntax.Tm_fvar uu____22435 -> t1
    | FStar_Syntax_Syntax.Tm_uinst uu____22436 -> t1
    | FStar_Syntax_Syntax.Tm_constant uu____22443 -> t1
    | FStar_Syntax_Syntax.Tm_type uu____22444 -> t1
    | FStar_Syntax_Syntax.Tm_lazy uu____22445 -> t1
    | FStar_Syntax_Syntax.Tm_unknown  -> t1
    | FStar_Syntax_Syntax.Tm_abs (bs,t2,rc_opt) ->
        let elim_rc rc =
          let uu___195_22473 = rc  in
          let uu____22474 =
            FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
              elim_delayed_subst_term
             in
          let uu____22481 =
            elim_delayed_subst_cflags rc.FStar_Syntax_Syntax.residual_flags
             in
          {
            FStar_Syntax_Syntax.residual_effect =
              (uu___195_22473.FStar_Syntax_Syntax.residual_effect);
            FStar_Syntax_Syntax.residual_typ = uu____22474;
            FStar_Syntax_Syntax.residual_flags = uu____22481
          }  in
        let uu____22484 =
          let uu____22485 =
            let uu____22502 = elim_delayed_subst_binders bs  in
            let uu____22509 = elim_delayed_subst_term t2  in
            let uu____22510 = FStar_Util.map_opt rc_opt elim_rc  in
            (uu____22502, uu____22509, uu____22510)  in
          FStar_Syntax_Syntax.Tm_abs uu____22485  in
        mk1 uu____22484
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____22539 =
          let uu____22540 =
            let uu____22553 = elim_delayed_subst_binders bs  in
            let uu____22560 = elim_delayed_subst_comp c  in
            (uu____22553, uu____22560)  in
          FStar_Syntax_Syntax.Tm_arrow uu____22540  in
        mk1 uu____22539
    | FStar_Syntax_Syntax.Tm_refine (bv,phi) ->
        let uu____22573 =
          let uu____22574 =
            let uu____22581 = elim_bv bv  in
            let uu____22582 = elim_delayed_subst_term phi  in
            (uu____22581, uu____22582)  in
          FStar_Syntax_Syntax.Tm_refine uu____22574  in
        mk1 uu____22573
    | FStar_Syntax_Syntax.Tm_app (t2,args) ->
        let uu____22605 =
          let uu____22606 =
            let uu____22621 = elim_delayed_subst_term t2  in
            let uu____22622 = elim_delayed_subst_args args  in
            (uu____22621, uu____22622)  in
          FStar_Syntax_Syntax.Tm_app uu____22606  in
        mk1 uu____22605
    | FStar_Syntax_Syntax.Tm_match (t2,branches) ->
        let rec elim_pat p =
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_var x ->
              let uu___196_22686 = p  in
              let uu____22687 =
                let uu____22688 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_var uu____22688  in
              {
                FStar_Syntax_Syntax.v = uu____22687;
                FStar_Syntax_Syntax.p =
                  (uu___196_22686.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_wild x ->
              let uu___197_22690 = p  in
              let uu____22691 =
                let uu____22692 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_wild uu____22692  in
              {
                FStar_Syntax_Syntax.v = uu____22691;
                FStar_Syntax_Syntax.p =
                  (uu___197_22690.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
              let uu___198_22699 = p  in
              let uu____22700 =
                let uu____22701 =
                  let uu____22708 = elim_bv x  in
                  let uu____22709 = elim_delayed_subst_term t0  in
                  (uu____22708, uu____22709)  in
                FStar_Syntax_Syntax.Pat_dot_term uu____22701  in
              {
                FStar_Syntax_Syntax.v = uu____22700;
                FStar_Syntax_Syntax.p =
                  (uu___198_22699.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
              let uu___199_22728 = p  in
              let uu____22729 =
                let uu____22730 =
                  let uu____22743 =
                    FStar_List.map
                      (fun uu____22766  ->
                         match uu____22766 with
                         | (x,b) ->
                             let uu____22779 = elim_pat x  in
                             (uu____22779, b)) pats
                     in
                  (fv, uu____22743)  in
                FStar_Syntax_Syntax.Pat_cons uu____22730  in
              {
                FStar_Syntax_Syntax.v = uu____22729;
                FStar_Syntax_Syntax.p =
                  (uu___199_22728.FStar_Syntax_Syntax.p)
              }
          | uu____22792 -> p  in
        let elim_branch uu____22814 =
          match uu____22814 with
          | (pat,wopt,t3) ->
              let uu____22840 = elim_pat pat  in
              let uu____22843 =
                FStar_Util.map_opt wopt elim_delayed_subst_term  in
              let uu____22846 = elim_delayed_subst_term t3  in
              (uu____22840, uu____22843, uu____22846)
           in
        let uu____22851 =
          let uu____22852 =
            let uu____22875 = elim_delayed_subst_term t2  in
            let uu____22876 = FStar_List.map elim_branch branches  in
            (uu____22875, uu____22876)  in
          FStar_Syntax_Syntax.Tm_match uu____22852  in
        mk1 uu____22851
    | FStar_Syntax_Syntax.Tm_ascribed (t2,a,lopt) ->
        let elim_ascription uu____22985 =
          match uu____22985 with
          | (tc,topt) ->
              let uu____23020 =
                match tc with
                | FStar_Util.Inl t3 ->
                    let uu____23030 = elim_delayed_subst_term t3  in
                    FStar_Util.Inl uu____23030
                | FStar_Util.Inr c ->
                    let uu____23032 = elim_delayed_subst_comp c  in
                    FStar_Util.Inr uu____23032
                 in
              let uu____23033 =
                FStar_Util.map_opt topt elim_delayed_subst_term  in
              (uu____23020, uu____23033)
           in
        let uu____23042 =
          let uu____23043 =
            let uu____23070 = elim_delayed_subst_term t2  in
            let uu____23071 = elim_ascription a  in
            (uu____23070, uu____23071, lopt)  in
          FStar_Syntax_Syntax.Tm_ascribed uu____23043  in
        mk1 uu____23042
    | FStar_Syntax_Syntax.Tm_let (lbs,t2) ->
        let elim_lb lb =
          let uu___200_23116 = lb  in
          let uu____23117 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbtyp  in
          let uu____23120 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbdef  in
          {
            FStar_Syntax_Syntax.lbname =
              (uu___200_23116.FStar_Syntax_Syntax.lbname);
            FStar_Syntax_Syntax.lbunivs =
              (uu___200_23116.FStar_Syntax_Syntax.lbunivs);
            FStar_Syntax_Syntax.lbtyp = uu____23117;
            FStar_Syntax_Syntax.lbeff =
              (uu___200_23116.FStar_Syntax_Syntax.lbeff);
            FStar_Syntax_Syntax.lbdef = uu____23120;
            FStar_Syntax_Syntax.lbattrs =
              (uu___200_23116.FStar_Syntax_Syntax.lbattrs);
            FStar_Syntax_Syntax.lbpos =
              (uu___200_23116.FStar_Syntax_Syntax.lbpos)
          }  in
        let uu____23123 =
          let uu____23124 =
            let uu____23137 =
              let uu____23144 =
                FStar_List.map elim_lb (FStar_Pervasives_Native.snd lbs)  in
              ((FStar_Pervasives_Native.fst lbs), uu____23144)  in
            let uu____23153 = elim_delayed_subst_term t2  in
            (uu____23137, uu____23153)  in
          FStar_Syntax_Syntax.Tm_let uu____23124  in
        mk1 uu____23123
    | FStar_Syntax_Syntax.Tm_uvar (uv,t2) ->
        let uu____23186 =
          let uu____23187 =
            let uu____23204 = elim_delayed_subst_term t2  in
            (uv, uu____23204)  in
          FStar_Syntax_Syntax.Tm_uvar uu____23187  in
        mk1 uu____23186
    | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
        let qi1 =
          FStar_Syntax_Syntax.on_antiquoted elim_delayed_subst_term qi  in
        let uu____23222 =
          let uu____23223 =
            let uu____23230 = elim_delayed_subst_term tm  in
            (uu____23230, qi1)  in
          FStar_Syntax_Syntax.Tm_quoted uu____23223  in
        mk1 uu____23222
    | FStar_Syntax_Syntax.Tm_meta (t2,md) ->
        let uu____23237 =
          let uu____23238 =
            let uu____23245 = elim_delayed_subst_term t2  in
            let uu____23246 = elim_delayed_subst_meta md  in
            (uu____23245, uu____23246)  in
          FStar_Syntax_Syntax.Tm_meta uu____23238  in
        mk1 uu____23237

and (elim_delayed_subst_cflags :
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun flags1  ->
    FStar_List.map
      (fun uu___93_23253  ->
         match uu___93_23253 with
         | FStar_Syntax_Syntax.DECREASES t ->
             let uu____23257 = elim_delayed_subst_term t  in
             FStar_Syntax_Syntax.DECREASES uu____23257
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
        let uu____23278 =
          let uu____23279 =
            let uu____23288 = elim_delayed_subst_term t  in
            (uu____23288, uopt)  in
          FStar_Syntax_Syntax.Total uu____23279  in
        mk1 uu____23278
    | FStar_Syntax_Syntax.GTotal (t,uopt) ->
        let uu____23301 =
          let uu____23302 =
            let uu____23311 = elim_delayed_subst_term t  in
            (uu____23311, uopt)  in
          FStar_Syntax_Syntax.GTotal uu____23302  in
        mk1 uu____23301
    | FStar_Syntax_Syntax.Comp ct ->
        let ct1 =
          let uu___201_23316 = ct  in
          let uu____23317 =
            elim_delayed_subst_term ct.FStar_Syntax_Syntax.result_typ  in
          let uu____23320 =
            elim_delayed_subst_args ct.FStar_Syntax_Syntax.effect_args  in
          let uu____23329 =
            elim_delayed_subst_cflags ct.FStar_Syntax_Syntax.flags  in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___201_23316.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___201_23316.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ = uu____23317;
            FStar_Syntax_Syntax.effect_args = uu____23320;
            FStar_Syntax_Syntax.flags = uu____23329
          }  in
        mk1 (FStar_Syntax_Syntax.Comp ct1)

and (elim_delayed_subst_meta :
  FStar_Syntax_Syntax.metadata -> FStar_Syntax_Syntax.metadata) =
  fun uu___94_23332  ->
    match uu___94_23332 with
    | FStar_Syntax_Syntax.Meta_pattern args ->
        let uu____23344 = FStar_List.map elim_delayed_subst_args args  in
        FStar_Syntax_Syntax.Meta_pattern uu____23344
    | FStar_Syntax_Syntax.Meta_monadic (m,t) ->
        let uu____23377 =
          let uu____23384 = elim_delayed_subst_term t  in (m, uu____23384)
           in
        FStar_Syntax_Syntax.Meta_monadic uu____23377
    | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,t) ->
        let uu____23392 =
          let uu____23401 = elim_delayed_subst_term t  in
          (m1, m2, uu____23401)  in
        FStar_Syntax_Syntax.Meta_monadic_lift uu____23392
    | m -> m

and (elim_delayed_subst_args :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun args  ->
    FStar_List.map
      (fun uu____23424  ->
         match uu____23424 with
         | (t,q) ->
             let uu____23435 = elim_delayed_subst_term t  in (uu____23435, q))
      args

and (elim_delayed_subst_binders :
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun bs  ->
    FStar_List.map
      (fun uu____23455  ->
         match uu____23455 with
         | (x,q) ->
             let uu____23466 =
               let uu___202_23467 = x  in
               let uu____23468 =
                 elim_delayed_subst_term x.FStar_Syntax_Syntax.sort  in
               {
                 FStar_Syntax_Syntax.ppname =
                   (uu___202_23467.FStar_Syntax_Syntax.ppname);
                 FStar_Syntax_Syntax.index =
                   (uu___202_23467.FStar_Syntax_Syntax.index);
                 FStar_Syntax_Syntax.sort = uu____23468
               }  in
             (uu____23466, q)) bs

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
            | (uu____23544,FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c))
                  FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
            | (uu____23550,FStar_Util.Inl t) ->
                let uu____23556 =
                  let uu____23559 =
                    let uu____23560 =
                      let uu____23573 = FStar_Syntax_Syntax.mk_Total t  in
                      (binders, uu____23573)  in
                    FStar_Syntax_Syntax.Tm_arrow uu____23560  in
                  FStar_Syntax_Syntax.mk uu____23559  in
                uu____23556 FStar_Pervasives_Native.None
                  t.FStar_Syntax_Syntax.pos
             in
          let uu____23577 = FStar_Syntax_Subst.open_univ_vars univ_names t
             in
          match uu____23577 with
          | (univ_names1,t1) ->
              let t2 = remove_uvar_solutions env t1  in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2  in
              let t4 = elim_delayed_subst_term t3  in
              let uu____23605 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t4))
                | uu____23660 ->
                    let uu____23661 =
                      let uu____23670 =
                        let uu____23671 = FStar_Syntax_Subst.compress t4  in
                        uu____23671.FStar_Syntax_Syntax.n  in
                      (uu____23670, tc)  in
                    (match uu____23661 with
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inr uu____23696) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inl uu____23733) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____23772,FStar_Util.Inl uu____23773) ->
                         ([], (FStar_Util.Inl t4))
                     | uu____23796 -> failwith "Impossible")
                 in
              (match uu____23605 with
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
          let uu____23901 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl t)  in
          match uu____23901 with
          | (univ_names1,binders1,tc) ->
              let uu____23959 = FStar_Util.left tc  in
              (univ_names1, binders1, uu____23959)
  
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
          let uu____23994 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr c)  in
          match uu____23994 with
          | (univ_names1,binders1,tc) ->
              let uu____24054 = FStar_Util.right tc  in
              (univ_names1, binders1, uu____24054)
  
let rec (elim_uvars :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt)
  =
  fun env  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univ_names,binders,typ,lids,lids') ->
          let uu____24087 = elim_uvars_aux_t env univ_names binders typ  in
          (match uu____24087 with
           | (univ_names1,binders1,typ1) ->
               let uu___203_24115 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___203_24115.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___203_24115.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___203_24115.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___203_24115.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
          let uu___204_24136 = s  in
          let uu____24137 =
            let uu____24138 =
              let uu____24147 = FStar_List.map (elim_uvars env) sigs  in
              (uu____24147, lids)  in
            FStar_Syntax_Syntax.Sig_bundle uu____24138  in
          {
            FStar_Syntax_Syntax.sigel = uu____24137;
            FStar_Syntax_Syntax.sigrng =
              (uu___204_24136.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___204_24136.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___204_24136.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___204_24136.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_datacon (lid,univ_names,typ,lident,i,lids) ->
          let uu____24164 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____24164 with
           | (univ_names1,uu____24182,typ1) ->
               let uu___205_24196 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___205_24196.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___205_24196.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___205_24196.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___205_24196.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univ_names,typ) ->
          let uu____24202 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____24202 with
           | (univ_names1,uu____24220,typ1) ->
               let uu___206_24234 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___206_24234.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___206_24234.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___206_24234.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___206_24234.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____24268 =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs
                       in
                    match uu____24268 with
                    | (opening,lbunivs) ->
                        let elim t =
                          let uu____24291 =
                            let uu____24292 =
                              let uu____24293 =
                                FStar_Syntax_Subst.subst opening t  in
                              remove_uvar_solutions env uu____24293  in
                            FStar_Syntax_Subst.close_univ_vars lbunivs
                              uu____24292
                             in
                          elim_delayed_subst_term uu____24291  in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp  in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef  in
                        let uu___207_24296 = lb  in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___207_24296.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___207_24296.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___207_24296.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___207_24296.FStar_Syntax_Syntax.lbpos)
                        }))
             in
          let uu___208_24297 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids));
            FStar_Syntax_Syntax.sigrng =
              (uu___208_24297.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___208_24297.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___208_24297.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___208_24297.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_main t ->
          let uu___209_24309 = s  in
          let uu____24310 =
            let uu____24311 = remove_uvar_solutions env t  in
            FStar_Syntax_Syntax.Sig_main uu____24311  in
          {
            FStar_Syntax_Syntax.sigel = uu____24310;
            FStar_Syntax_Syntax.sigrng =
              (uu___209_24309.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___209_24309.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___209_24309.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___209_24309.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_assume (l,us,t) ->
          let uu____24315 = elim_uvars_aux_t env us [] t  in
          (match uu____24315 with
           | (us1,uu____24333,t1) ->
               let uu___210_24347 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___210_24347.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___210_24347.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___210_24347.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___210_24347.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____24348 ->
          failwith "Impossible: should have been desugared already"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____24350 =
            elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature
             in
          (match uu____24350 with
           | (univs1,binders,signature) ->
               let uu____24378 =
                 let uu____24387 = FStar_Syntax_Subst.univ_var_opening univs1
                    in
                 match uu____24387 with
                 | (univs_opening,univs2) ->
                     let uu____24414 =
                       FStar_Syntax_Subst.univ_var_closing univs2  in
                     (univs_opening, uu____24414)
                  in
               (match uu____24378 with
                | (univs_opening,univs_closing) ->
                    let uu____24431 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders
                         in
                      let uu____24437 =
                        FStar_Syntax_Subst.opening_of_binders binders1  in
                      let uu____24438 =
                        FStar_Syntax_Subst.closing_of_binders binders1  in
                      (uu____24437, uu____24438)  in
                    (match uu____24431 with
                     | (b_opening,b_closing) ->
                         let n1 = FStar_List.length univs1  in
                         let n_binders = FStar_List.length binders  in
                         let elim_tscheme uu____24460 =
                           match uu____24460 with
                           | (us,t) ->
                               let n_us = FStar_List.length us  in
                               let uu____24478 =
                                 FStar_Syntax_Subst.open_univ_vars us t  in
                               (match uu____24478 with
                                | (us1,t1) ->
                                    let uu____24489 =
                                      let uu____24494 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      let uu____24501 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      (uu____24494, uu____24501)  in
                                    (match uu____24489 with
                                     | (b_opening1,b_closing1) ->
                                         let uu____24514 =
                                           let uu____24519 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us)
                                              in
                                           let uu____24528 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us)
                                              in
                                           (uu____24519, uu____24528)  in
                                         (match uu____24514 with
                                          | (univs_opening1,univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____24544 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1
                                                   in
                                                FStar_Syntax_Subst.subst
                                                  univs_opening1 uu____24544
                                                 in
                                              let uu____24545 =
                                                elim_uvars_aux_t env [] [] t2
                                                 in
                                              (match uu____24545 with
                                               | (uu____24566,uu____24567,t3)
                                                   ->
                                                   let t4 =
                                                     let uu____24582 =
                                                       let uu____24583 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3
                                                          in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
                                                         uu____24583
                                                        in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____24582
                                                      in
                                                   (us1, t4)))))
                            in
                         let elim_term t =
                           let uu____24588 =
                             elim_uvars_aux_t env univs1 binders t  in
                           match uu____24588 with
                           | (uu____24601,uu____24602,t1) -> t1  in
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
                             | uu____24662 ->
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_abs
                                      ((a.FStar_Syntax_Syntax.action_params),
                                        body, FStar_Pervasives_Native.None))
                                   FStar_Pervasives_Native.None
                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                              in
                           let destruct_action_body body =
                             let uu____24679 =
                               let uu____24680 =
                                 FStar_Syntax_Subst.compress body  in
                               uu____24680.FStar_Syntax_Syntax.n  in
                             match uu____24679 with
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,(FStar_Util.Inl
                                        typ,FStar_Pervasives_Native.None ),FStar_Pervasives_Native.None
                                  )
                                 -> (defn, typ)
                             | uu____24739 -> failwith "Impossible"  in
                           let destruct_action_typ_templ t =
                             let uu____24768 =
                               let uu____24769 =
                                 FStar_Syntax_Subst.compress t  in
                               uu____24769.FStar_Syntax_Syntax.n  in
                             match uu____24768 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (pars,body,uu____24790) ->
                                 let uu____24811 = destruct_action_body body
                                    in
                                 (match uu____24811 with
                                  | (defn,typ) -> (pars, defn, typ))
                             | uu____24856 ->
                                 let uu____24857 = destruct_action_body t  in
                                 (match uu____24857 with
                                  | (defn,typ) -> ([], defn, typ))
                              in
                           let uu____24906 =
                             elim_tscheme
                               ((a.FStar_Syntax_Syntax.action_univs),
                                 action_typ_templ)
                              in
                           match uu____24906 with
                           | (action_univs,t) ->
                               let uu____24915 = destruct_action_typ_templ t
                                  in
                               (match uu____24915 with
                                | (action_params,action_defn,action_typ) ->
                                    let a' =
                                      let uu___211_24956 = a  in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___211_24956.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___211_24956.FStar_Syntax_Syntax.action_unqualified_name);
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
                           let uu___212_24958 = ed  in
                           let uu____24959 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ret_wp  in
                           let uu____24960 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_wp  in
                           let uu____24961 =
                             elim_tscheme ed.FStar_Syntax_Syntax.if_then_else
                              in
                           let uu____24962 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ite_wp  in
                           let uu____24963 =
                             elim_tscheme ed.FStar_Syntax_Syntax.stronger  in
                           let uu____24964 =
                             elim_tscheme ed.FStar_Syntax_Syntax.close_wp  in
                           let uu____24965 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assert_p  in
                           let uu____24966 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assume_p  in
                           let uu____24967 =
                             elim_tscheme ed.FStar_Syntax_Syntax.null_wp  in
                           let uu____24968 =
                             elim_tscheme ed.FStar_Syntax_Syntax.trivial  in
                           let uu____24969 =
                             elim_term ed.FStar_Syntax_Syntax.repr  in
                           let uu____24970 =
                             elim_tscheme ed.FStar_Syntax_Syntax.return_repr
                              in
                           let uu____24971 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_repr
                              in
                           let uu____24972 =
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions
                              in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___212_24958.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___212_24958.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs = univs1;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp = uu____24959;
                             FStar_Syntax_Syntax.bind_wp = uu____24960;
                             FStar_Syntax_Syntax.if_then_else = uu____24961;
                             FStar_Syntax_Syntax.ite_wp = uu____24962;
                             FStar_Syntax_Syntax.stronger = uu____24963;
                             FStar_Syntax_Syntax.close_wp = uu____24964;
                             FStar_Syntax_Syntax.assert_p = uu____24965;
                             FStar_Syntax_Syntax.assume_p = uu____24966;
                             FStar_Syntax_Syntax.null_wp = uu____24967;
                             FStar_Syntax_Syntax.trivial = uu____24968;
                             FStar_Syntax_Syntax.repr = uu____24969;
                             FStar_Syntax_Syntax.return_repr = uu____24970;
                             FStar_Syntax_Syntax.bind_repr = uu____24971;
                             FStar_Syntax_Syntax.actions = uu____24972;
                             FStar_Syntax_Syntax.eff_attrs =
                               (uu___212_24958.FStar_Syntax_Syntax.eff_attrs)
                           }  in
                         let uu___213_24975 = s  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___213_24975.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___213_24975.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___213_24975.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___213_24975.FStar_Syntax_Syntax.sigattrs)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___95_24992 =
            match uu___95_24992 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (us,t) ->
                let uu____25019 = elim_uvars_aux_t env us [] t  in
                (match uu____25019 with
                 | (us1,uu____25043,t1) ->
                     FStar_Pervasives_Native.Some (us1, t1))
             in
          let sub_eff1 =
            let uu___214_25062 = sub_eff  in
            let uu____25063 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp  in
            let uu____25066 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift  in
            {
              FStar_Syntax_Syntax.source =
                (uu___214_25062.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___214_25062.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____25063;
              FStar_Syntax_Syntax.lift = uu____25066
            }  in
          let uu___215_25069 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___215_25069.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___215_25069.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___215_25069.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___215_25069.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,univ_names,binders,comp,flags1) ->
          let uu____25079 = elim_uvars_aux_c env univ_names binders comp  in
          (match uu____25079 with
           | (univ_names1,binders1,comp1) ->
               let uu___216_25113 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___216_25113.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___216_25113.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___216_25113.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___216_25113.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____25124 -> s
      | FStar_Syntax_Syntax.Sig_splice uu____25125 -> s
  
let (erase_universes :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  -> normalize [EraseUniverses; AllowUnboundUniverses] env t
  