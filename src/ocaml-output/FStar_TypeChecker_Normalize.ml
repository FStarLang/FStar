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
  | Match of (env,branches,cfg,FStar_Range.range)
  FStar_Pervasives_Native.tuple4 
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
    match projectee with | Arg _0 -> true | uu____1971 -> false
  
let (__proj__Arg__item___0 :
  stack_elt ->
    (closure,FStar_Syntax_Syntax.aqual,FStar_Range.range)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | Arg _0 -> _0 
let (uu___is_UnivArgs : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnivArgs _0 -> true | uu____2007 -> false
  
let (__proj__UnivArgs__item___0 :
  stack_elt ->
    (FStar_Syntax_Syntax.universe Prims.list,FStar_Range.range)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | UnivArgs _0 -> _0 
let (uu___is_MemoLazy : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | MemoLazy _0 -> true | uu____2043 -> false
  
let (__proj__MemoLazy__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.term) FStar_Pervasives_Native.tuple2
      FStar_Syntax_Syntax.memo)
  = fun projectee  -> match projectee with | MemoLazy _0 -> _0 
let (uu___is_Match : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____2114 -> false
  
let (__proj__Match__item___0 :
  stack_elt ->
    (env,branches,cfg,FStar_Range.range) FStar_Pervasives_Native.tuple4)
  = fun projectee  -> match projectee with | Match _0 -> _0 
let (uu___is_Abs : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Abs _0 -> true | uu____2162 -> false
  
let (__proj__Abs__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.binders,env,FStar_Syntax_Syntax.residual_comp
                                           FStar_Pervasives_Native.option,
      FStar_Range.range) FStar_Pervasives_Native.tuple5)
  = fun projectee  -> match projectee with | Abs _0 -> _0 
let (uu___is_App : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____2218 -> false
  
let (__proj__App__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual,FStar_Range.range)
      FStar_Pervasives_Native.tuple4)
  = fun projectee  -> match projectee with | App _0 -> _0 
let (uu___is_Meta : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Meta _0 -> true | uu____2258 -> false
  
let (__proj__Meta__item___0 :
  stack_elt ->
    (FStar_Syntax_Syntax.metadata,FStar_Range.range)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Meta _0 -> _0 
let (uu___is_Let : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Let _0 -> true | uu____2290 -> false
  
let (__proj__Let__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.letbinding,FStar_Range.range)
      FStar_Pervasives_Native.tuple4)
  = fun projectee  -> match projectee with | Let _0 -> _0 
let (uu___is_Cfg : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Cfg _0 -> true | uu____2326 -> false
  
let (__proj__Cfg__item___0 : stack_elt -> cfg) =
  fun projectee  -> match projectee with | Cfg _0 -> _0 
let (uu___is_Debug : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Debug _0 -> true | uu____2342 -> false
  
let (__proj__Debug__item___0 :
  stack_elt ->
    (FStar_Syntax_Syntax.term,FStar_Util.time) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Debug _0 -> _0 
type stack = stack_elt Prims.list[@@deriving show]
let (head_of : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____2367 = FStar_Syntax_Util.head_and_args' t  in
    match uu____2367 with | (hd1,uu____2381) -> hd1
  
let mk :
  'Auu____2401 .
    'Auu____2401 ->
      FStar_Range.range -> 'Auu____2401 FStar_Syntax_Syntax.syntax
  =
  fun t  -> fun r  -> FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None r 
let set_memo : 'a . cfg -> 'a FStar_Syntax_Syntax.memo -> 'a -> Prims.unit =
  fun cfg  ->
    fun r  ->
      fun t  ->
        if cfg.memoize_lazy
        then
          let uu____2455 = FStar_ST.op_Bang r  in
          match uu____2455 with
          | FStar_Pervasives_Native.Some uu____2503 ->
              failwith "Unexpected set_memo: thunk already evaluated"
          | FStar_Pervasives_Native.None  ->
              FStar_ST.op_Colon_Equals r (FStar_Pervasives_Native.Some t)
        else ()
  
let (env_to_string : closure Prims.list -> Prims.string) =
  fun env  ->
    let uu____2557 = FStar_List.map closure_to_string env  in
    FStar_All.pipe_right uu____2557 (FStar_String.concat "; ")
  
let (stack_elt_to_string : stack_elt -> Prims.string) =
  fun uu___80_2564  ->
    match uu___80_2564 with
    | Arg (c,uu____2566,uu____2567) ->
        let uu____2568 = closure_to_string c  in
        FStar_Util.format1 "Closure %s" uu____2568
    | MemoLazy uu____2569 -> "MemoLazy"
    | Abs (uu____2576,bs,uu____2578,uu____2579,uu____2580) ->
        let uu____2585 =
          FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs)
           in
        FStar_Util.format1 "Abs %s" uu____2585
    | UnivArgs uu____2590 -> "UnivArgs"
    | Match uu____2597 -> "Match"
    | App (uu____2606,t,uu____2608,uu____2609) ->
        let uu____2610 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "App %s" uu____2610
    | Meta (m,uu____2612) -> "Meta"
    | Let uu____2613 -> "Let"
    | Cfg uu____2622 -> "Cfg"
    | Debug (t,uu____2624) ->
        let uu____2625 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "Debug %s" uu____2625
  
let (stack_to_string : stack_elt Prims.list -> Prims.string) =
  fun s  ->
    let uu____2633 = FStar_List.map stack_elt_to_string s  in
    FStar_All.pipe_right uu____2633 (FStar_String.concat "; ")
  
let (log : cfg -> (Prims.unit -> Prims.unit) -> Prims.unit) =
  fun cfg  -> fun f  -> if (cfg.debug).gen then f () else () 
let (log_primops : cfg -> (Prims.unit -> Prims.unit) -> Prims.unit) =
  fun cfg  -> fun f  -> if (cfg.debug).primop then f () else () 
let is_empty : 'Auu____2664 . 'Auu____2664 Prims.list -> Prims.bool =
  fun uu___81_2670  ->
    match uu___81_2670 with | [] -> true | uu____2673 -> false
  
let lookup_bvar :
  'Auu____2680 'Auu____2681 .
    ('Auu____2680,'Auu____2681) FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Syntax_Syntax.bv -> 'Auu____2681
  =
  fun env  ->
    fun x  ->
      try
        let uu____2705 = FStar_List.nth env x.FStar_Syntax_Syntax.index  in
        FStar_Pervasives_Native.snd uu____2705
      with
      | uu____2718 ->
          let uu____2719 =
            let uu____2720 = FStar_Syntax_Print.db_to_string x  in
            FStar_Util.format1 "Failed to find %s\n" uu____2720  in
          failwith uu____2719
  
let (downgrade_ghost_effect_name :
  FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option) =
  fun l  ->
    let uu____2726 =
      FStar_Ident.lid_equals l FStar_Parser_Const.effect_Ghost_lid  in
    if uu____2726
    then FStar_Pervasives_Native.Some FStar_Parser_Const.effect_Pure_lid
    else
      (let uu____2730 =
         FStar_Ident.lid_equals l FStar_Parser_Const.effect_GTot_lid  in
       if uu____2730
       then FStar_Pervasives_Native.Some FStar_Parser_Const.effect_Tot_lid
       else
         (let uu____2734 =
            FStar_Ident.lid_equals l FStar_Parser_Const.effect_GHOST_lid  in
          if uu____2734
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
          let uu____2760 =
            FStar_List.fold_left
              (fun uu____2786  ->
                 fun u1  ->
                   match uu____2786 with
                   | (cur_kernel,cur_max,out) ->
                       let uu____2811 = FStar_Syntax_Util.univ_kernel u1  in
                       (match uu____2811 with
                        | (k_u,n1) ->
                            let uu____2826 =
                              FStar_Syntax_Util.eq_univs cur_kernel k_u  in
                            if uu____2826
                            then (cur_kernel, u1, out)
                            else (k_u, u1, (cur_max :: out))))
              (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero, [])
              us1
             in
          match uu____2760 with
          | (uu____2844,u1,out) -> FStar_List.rev (u1 :: out)  in
        let rec aux u1 =
          let u2 = FStar_Syntax_Subst.compress_univ u1  in
          match u2 with
          | FStar_Syntax_Syntax.U_bvar x ->
              (try
                 let uu____2869 =
                   let uu____2870 = FStar_List.nth env x  in
                   FStar_Pervasives_Native.snd uu____2870  in
                 match uu____2869 with
                 | Univ u3 -> aux u3
                 | Dummy  -> [u2]
                 | uu____2888 ->
                     failwith "Impossible: universe variable bound to a term"
               with
               | uu____2896 ->
                   if (cfg.steps).allow_unbound_universes
                   then [FStar_Syntax_Syntax.U_unknown]
                   else failwith "Universe variable not found")
          | FStar_Syntax_Syntax.U_unif uu____2902 when
              (cfg.steps).check_no_uvars -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_zero  -> [u2]
          | FStar_Syntax_Syntax.U_unif uu____2911 -> [u2]
          | FStar_Syntax_Syntax.U_name uu____2920 -> [u2]
          | FStar_Syntax_Syntax.U_unknown  -> [u2]
          | FStar_Syntax_Syntax.U_max [] -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_max us ->
              let us1 =
                let uu____2927 = FStar_List.collect aux us  in
                FStar_All.pipe_right uu____2927 norm_univs  in
              (match us1 with
               | u_k::hd1::rest ->
                   let rest1 = hd1 :: rest  in
                   let uu____2944 = FStar_Syntax_Util.univ_kernel u_k  in
                   (match uu____2944 with
                    | (FStar_Syntax_Syntax.U_zero ,n1) ->
                        let uu____2952 =
                          FStar_All.pipe_right rest1
                            (FStar_List.for_all
                               (fun u3  ->
                                  let uu____2960 =
                                    FStar_Syntax_Util.univ_kernel u3  in
                                  match uu____2960 with
                                  | (uu____2965,m) -> n1 <= m))
                           in
                        if uu____2952 then rest1 else us1
                    | uu____2970 -> us1)
               | uu____2975 -> us1)
          | FStar_Syntax_Syntax.U_succ u3 ->
              let uu____2979 = aux u3  in
              FStar_List.map (fun _0_40  -> FStar_Syntax_Syntax.U_succ _0_40)
                uu____2979
           in
        if (cfg.steps).erase_universes
        then FStar_Syntax_Syntax.U_unknown
        else
          (let uu____2983 = aux u  in
           match uu____2983 with
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
            (fun uu____3086  ->
               let uu____3087 = FStar_Syntax_Print.tag_of_term t  in
               let uu____3088 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print2 ">>> %s Closure_as_term %s\n" uu____3087
                 uu____3088);
          (match env with
           | [] when
               FStar_All.pipe_left Prims.op_Negation
                 (cfg.steps).compress_uvars
               -> rebuild_closure cfg env stack t
           | uu____3097 ->
               let t1 = FStar_Syntax_Subst.compress t  in
               (match t1.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_delayed uu____3101 ->
                    failwith "Impossible"
                | FStar_Syntax_Syntax.Tm_unknown  ->
                    rebuild_closure cfg env stack t1
                | FStar_Syntax_Syntax.Tm_constant uu____3128 ->
                    rebuild_closure cfg env stack t1
                | FStar_Syntax_Syntax.Tm_name uu____3129 ->
                    rebuild_closure cfg env stack t1
                | FStar_Syntax_Syntax.Tm_lazy uu____3130 ->
                    rebuild_closure cfg env stack t1
                | FStar_Syntax_Syntax.Tm_fvar uu____3131 ->
                    rebuild_closure cfg env stack t1
                | FStar_Syntax_Syntax.Tm_uvar uu____3132 ->
                    if (cfg.steps).check_no_uvars
                    then
                      let uu____3151 =
                        let uu____3152 =
                          FStar_Range.string_of_range
                            t1.FStar_Syntax_Syntax.pos
                           in
                        let uu____3153 = FStar_Syntax_Print.term_to_string t1
                           in
                        FStar_Util.format2
                          "(%s): CheckNoUvars: Unexpected unification variable remains: %s"
                          uu____3152 uu____3153
                         in
                      failwith uu____3151
                    else rebuild_closure cfg env stack t1
                | FStar_Syntax_Syntax.Tm_type u ->
                    let t2 =
                      let uu____3161 =
                        let uu____3162 = norm_universe cfg env u  in
                        FStar_Syntax_Syntax.Tm_type uu____3162  in
                      mk uu____3161 t1.FStar_Syntax_Syntax.pos  in
                    rebuild_closure cfg env stack t2
                | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
                    let t2 =
                      let uu____3170 =
                        FStar_List.map (norm_universe cfg env) us  in
                      FStar_Syntax_Syntax.mk_Tm_uinst t' uu____3170  in
                    rebuild_closure cfg env stack t2
                | FStar_Syntax_Syntax.Tm_bvar x ->
                    let uu____3172 = lookup_bvar env x  in
                    (match uu____3172 with
                     | Univ uu____3177 ->
                         failwith
                           "Impossible: term variable is bound to a universe"
                     | Dummy  ->
                         let x1 =
                           let uu___124_3181 = x  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___124_3181.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___124_3181.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort =
                               FStar_Syntax_Syntax.tun
                           }  in
                         let t2 =
                           mk (FStar_Syntax_Syntax.Tm_bvar x1)
                             t1.FStar_Syntax_Syntax.pos
                            in
                         rebuild_closure cfg env stack t2
                     | Clos (env1,t0,uu____3187,uu____3188) ->
                         inline_closure_env cfg env1 stack t0)
                | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                    let stack1 =
                      FStar_All.pipe_right stack
                        (FStar_List.fold_right
                           (fun uu____3273  ->
                              fun stack1  ->
                                match uu____3273 with
                                | (a,aq) ->
                                    let uu____3285 =
                                      let uu____3286 =
                                        let uu____3293 =
                                          let uu____3294 =
                                            let uu____3325 =
                                              FStar_Util.mk_ref
                                                FStar_Pervasives_Native.None
                                               in
                                            (env, a, uu____3325, false)  in
                                          Clos uu____3294  in
                                        (uu____3293, aq,
                                          (t1.FStar_Syntax_Syntax.pos))
                                         in
                                      Arg uu____3286  in
                                    uu____3285 :: stack1) args)
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
                      (Abs
                         (env, bs, env', lopt, (t1.FStar_Syntax_Syntax.pos)))
                      :: stack  in
                    inline_closure_env cfg env' stack1 body
                | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                    let uu____3519 = close_binders cfg env bs  in
                    (match uu____3519 with
                     | (bs1,env') ->
                         let c1 = close_comp cfg env' c  in
                         let t2 =
                           mk (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
                             t1.FStar_Syntax_Syntax.pos
                            in
                         rebuild_closure cfg env stack t2)
                | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
                    let uu____3566 =
                      let uu____3577 =
                        let uu____3584 = FStar_Syntax_Syntax.mk_binder x  in
                        [uu____3584]  in
                      close_binders cfg env uu____3577  in
                    (match uu____3566 with
                     | (x1,env1) ->
                         let phi1 = non_tail_inline_closure_env cfg env1 phi
                            in
                         let t2 =
                           let uu____3607 =
                             let uu____3608 =
                               let uu____3615 =
                                 let uu____3616 = FStar_List.hd x1  in
                                 FStar_All.pipe_right uu____3616
                                   FStar_Pervasives_Native.fst
                                  in
                               (uu____3615, phi1)  in
                             FStar_Syntax_Syntax.Tm_refine uu____3608  in
                           mk uu____3607 t1.FStar_Syntax_Syntax.pos  in
                         rebuild_closure cfg env1 stack t2)
                | FStar_Syntax_Syntax.Tm_ascribed (t11,(annot,tacopt),lopt)
                    ->
                    let annot1 =
                      match annot with
                      | FStar_Util.Inl t2 ->
                          let uu____3707 =
                            non_tail_inline_closure_env cfg env t2  in
                          FStar_Util.Inl uu____3707
                      | FStar_Util.Inr c ->
                          let uu____3721 = close_comp cfg env c  in
                          FStar_Util.Inr uu____3721
                       in
                    let tacopt1 =
                      FStar_Util.map_opt tacopt
                        (non_tail_inline_closure_env cfg env)
                       in
                    let t2 =
                      let uu____3740 =
                        let uu____3741 =
                          let uu____3768 =
                            non_tail_inline_closure_env cfg env t11  in
                          (uu____3768, (annot1, tacopt1), lopt)  in
                        FStar_Syntax_Syntax.Tm_ascribed uu____3741  in
                      mk uu____3740 t1.FStar_Syntax_Syntax.pos  in
                    rebuild_closure cfg env stack t2
                | FStar_Syntax_Syntax.Tm_quoted (t',qi) ->
                    let t2 =
                      match qi.FStar_Syntax_Syntax.qkind with
                      | FStar_Syntax_Syntax.Quote_dynamic  ->
                          let uu____3814 =
                            let uu____3815 =
                              let uu____3822 =
                                non_tail_inline_closure_env cfg env t'  in
                              (uu____3822, qi)  in
                            FStar_Syntax_Syntax.Tm_quoted uu____3815  in
                          mk uu____3814 t1.FStar_Syntax_Syntax.pos
                      | FStar_Syntax_Syntax.Quote_static  ->
                          let qi1 =
                            FStar_Syntax_Syntax.on_antiquoted
                              (non_tail_inline_closure_env cfg env) qi
                             in
                          mk (FStar_Syntax_Syntax.Tm_quoted (t', qi1))
                            t1.FStar_Syntax_Syntax.pos
                       in
                    rebuild_closure cfg env stack t2
                | FStar_Syntax_Syntax.Tm_meta (t',m) ->
                    let stack1 = (Meta (m, (t1.FStar_Syntax_Syntax.pos))) ::
                      stack  in
                    inline_closure_env cfg env stack1 t'
                | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                    let env0 = env  in
                    let env1 =
                      FStar_List.fold_left
                        (fun env1  -> fun uu____3874  -> dummy :: env1) env
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
                    let uu____3895 =
                      let uu____3906 = FStar_Syntax_Syntax.is_top_level [lb]
                         in
                      if uu____3906
                      then ((lb.FStar_Syntax_Syntax.lbname), body)
                      else
                        (let x =
                           FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                         let uu____3925 =
                           non_tail_inline_closure_env cfg (dummy :: env0)
                             body
                            in
                         ((FStar_Util.Inl
                             (let uu___125_3941 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___125_3941.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___125_3941.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = typ
                              })), uu____3925))
                       in
                    (match uu____3895 with
                     | (nm,body1) ->
                         let lb1 =
                           let uu___126_3959 = lb  in
                           {
                             FStar_Syntax_Syntax.lbname = nm;
                             FStar_Syntax_Syntax.lbunivs =
                               (uu___126_3959.FStar_Syntax_Syntax.lbunivs);
                             FStar_Syntax_Syntax.lbtyp = typ;
                             FStar_Syntax_Syntax.lbeff =
                               (uu___126_3959.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = def;
                             FStar_Syntax_Syntax.lbattrs =
                               (uu___126_3959.FStar_Syntax_Syntax.lbattrs);
                             FStar_Syntax_Syntax.lbpos =
                               (uu___126_3959.FStar_Syntax_Syntax.lbpos)
                           }  in
                         let t2 =
                           mk
                             (FStar_Syntax_Syntax.Tm_let
                                ((false, [lb1]), body1))
                             t1.FStar_Syntax_Syntax.pos
                            in
                         rebuild_closure cfg env1 stack t2)
                | FStar_Syntax_Syntax.Tm_let ((uu____3973,lbs),body) ->
                    let norm_one_lb env1 lb =
                      let env_univs =
                        FStar_List.fold_right
                          (fun uu____4032  -> fun env2  -> dummy :: env2)
                          lb.FStar_Syntax_Syntax.lbunivs env1
                         in
                      let env2 =
                        let uu____4057 = FStar_Syntax_Syntax.is_top_level lbs
                           in
                        if uu____4057
                        then env_univs
                        else
                          FStar_List.fold_right
                            (fun uu____4077  -> fun env2  -> dummy :: env2)
                            lbs env_univs
                         in
                      let ty =
                        non_tail_inline_closure_env cfg env_univs
                          lb.FStar_Syntax_Syntax.lbtyp
                         in
                      let nm =
                        let uu____4101 = FStar_Syntax_Syntax.is_top_level lbs
                           in
                        if uu____4101
                        then lb.FStar_Syntax_Syntax.lbname
                        else
                          (let x =
                             FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                              in
                           FStar_Util.Inl
                             (let uu___127_4109 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___127_4109.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___127_4109.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = ty
                              }))
                         in
                      let uu___128_4110 = lb  in
                      let uu____4111 =
                        non_tail_inline_closure_env cfg env2
                          lb.FStar_Syntax_Syntax.lbdef
                         in
                      {
                        FStar_Syntax_Syntax.lbname = nm;
                        FStar_Syntax_Syntax.lbunivs =
                          (uu___128_4110.FStar_Syntax_Syntax.lbunivs);
                        FStar_Syntax_Syntax.lbtyp = ty;
                        FStar_Syntax_Syntax.lbeff =
                          (uu___128_4110.FStar_Syntax_Syntax.lbeff);
                        FStar_Syntax_Syntax.lbdef = uu____4111;
                        FStar_Syntax_Syntax.lbattrs =
                          (uu___128_4110.FStar_Syntax_Syntax.lbattrs);
                        FStar_Syntax_Syntax.lbpos =
                          (uu___128_4110.FStar_Syntax_Syntax.lbpos)
                      }  in
                    let lbs1 =
                      FStar_All.pipe_right lbs
                        (FStar_List.map (norm_one_lb env))
                       in
                    let body1 =
                      let body_env =
                        FStar_List.fold_right
                          (fun uu____4143  -> fun env1  -> dummy :: env1)
                          lbs1 env
                         in
                      non_tail_inline_closure_env cfg body_env body  in
                    let t2 =
                      mk (FStar_Syntax_Syntax.Tm_let ((true, lbs1), body1))
                        t1.FStar_Syntax_Syntax.pos
                       in
                    rebuild_closure cfg env stack t2
                | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
                    let stack1 =
                      (Match
                         (env, branches, cfg, (t1.FStar_Syntax_Syntax.pos)))
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
          match stack with
          | [] -> t
          | (Arg (Clos (env_arg,tm,uu____4244,uu____4245),aq,r))::stack1 ->
              let stack2 = (App (env, t, aq, r)) :: stack1  in
              inline_closure_env cfg env_arg stack2 tm
          | (App (env1,head1,aq,r))::stack1 ->
              let t1 =
                FStar_Syntax_Syntax.extend_app head1 (t, aq)
                  FStar_Pervasives_Native.None r
                 in
              rebuild_closure cfg env1 stack1 t1
          | (Abs (env',bs,env'',lopt,r))::stack1 ->
              let uu____4320 = close_binders cfg env' bs  in
              (match uu____4320 with
               | (bs1,uu____4334) ->
                   let lopt1 = close_lcomp_opt cfg env'' lopt  in
                   let uu____4350 =
                     let uu___129_4351 = FStar_Syntax_Util.abs bs1 t lopt1
                        in
                     {
                       FStar_Syntax_Syntax.n =
                         (uu___129_4351.FStar_Syntax_Syntax.n);
                       FStar_Syntax_Syntax.pos = r;
                       FStar_Syntax_Syntax.vars =
                         (uu___129_4351.FStar_Syntax_Syntax.vars)
                     }  in
                   rebuild_closure cfg env stack1 uu____4350)
          | (Match (env1,branches,cfg1,r))::stack1 ->
              let close_one_branch env2 uu____4393 =
                match uu____4393 with
                | (pat,w_opt,tm) ->
                    let rec norm_pat env3 p =
                      match p.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_constant uu____4464 ->
                          (p, env3)
                      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                          let uu____4485 =
                            FStar_All.pipe_right pats
                              (FStar_List.fold_left
                                 (fun uu____4545  ->
                                    fun uu____4546  ->
                                      match (uu____4545, uu____4546) with
                                      | ((pats1,env4),(p1,b)) ->
                                          let uu____4637 = norm_pat env4 p1
                                             in
                                          (match uu____4637 with
                                           | (p2,env5) ->
                                               (((p2, b) :: pats1), env5)))
                                 ([], env3))
                             in
                          (match uu____4485 with
                           | (pats1,env4) ->
                               ((let uu___130_4719 = p  in
                                 {
                                   FStar_Syntax_Syntax.v =
                                     (FStar_Syntax_Syntax.Pat_cons
                                        (fv, (FStar_List.rev pats1)));
                                   FStar_Syntax_Syntax.p =
                                     (uu___130_4719.FStar_Syntax_Syntax.p)
                                 }), env4))
                      | FStar_Syntax_Syntax.Pat_var x ->
                          let x1 =
                            let uu___131_4738 = x  in
                            let uu____4739 =
                              non_tail_inline_closure_env cfg1 env3
                                x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___131_4738.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___131_4738.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____4739
                            }  in
                          ((let uu___132_4753 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_var x1);
                              FStar_Syntax_Syntax.p =
                                (uu___132_4753.FStar_Syntax_Syntax.p)
                            }), (dummy :: env3))
                      | FStar_Syntax_Syntax.Pat_wild x ->
                          let x1 =
                            let uu___133_4764 = x  in
                            let uu____4765 =
                              non_tail_inline_closure_env cfg1 env3
                                x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___133_4764.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___133_4764.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____4765
                            }  in
                          ((let uu___134_4779 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_wild x1);
                              FStar_Syntax_Syntax.p =
                                (uu___134_4779.FStar_Syntax_Syntax.p)
                            }), (dummy :: env3))
                      | FStar_Syntax_Syntax.Pat_dot_term (x,t1) ->
                          let x1 =
                            let uu___135_4795 = x  in
                            let uu____4796 =
                              non_tail_inline_closure_env cfg1 env3
                                x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___135_4795.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___135_4795.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____4796
                            }  in
                          let t2 = non_tail_inline_closure_env cfg1 env3 t1
                             in
                          ((let uu___136_4805 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_dot_term (x1, t2));
                              FStar_Syntax_Syntax.p =
                                (uu___136_4805.FStar_Syntax_Syntax.p)
                            }), env3)
                       in
                    let uu____4810 = norm_pat env2 pat  in
                    (match uu____4810 with
                     | (pat1,env3) ->
                         let w_opt1 =
                           match w_opt with
                           | FStar_Pervasives_Native.None  ->
                               FStar_Pervasives_Native.None
                           | FStar_Pervasives_Native.Some w ->
                               let uu____4855 =
                                 non_tail_inline_closure_env cfg1 env3 w  in
                               FStar_Pervasives_Native.Some uu____4855
                            in
                         let tm1 = non_tail_inline_closure_env cfg1 env3 tm
                            in
                         (pat1, w_opt1, tm1))
                 in
              let t1 =
                let uu____4874 =
                  let uu____4875 =
                    let uu____4898 =
                      FStar_All.pipe_right branches
                        (FStar_List.map (close_one_branch env1))
                       in
                    (t, uu____4898)  in
                  FStar_Syntax_Syntax.Tm_match uu____4875  in
                mk uu____4874 t.FStar_Syntax_Syntax.pos  in
              rebuild_closure cfg1 env1 stack1 t1
          | (Meta (m,r))::stack1 ->
              let m1 =
                match m with
                | FStar_Syntax_Syntax.Meta_pattern args ->
                    let uu____4992 =
                      FStar_All.pipe_right args
                        (FStar_List.map
                           (fun args1  ->
                              FStar_All.pipe_right args1
                                (FStar_List.map
                                   (fun uu____5081  ->
                                      match uu____5081 with
                                      | (a,q) ->
                                          let uu____5100 =
                                            non_tail_inline_closure_env cfg
                                              env a
                                             in
                                          (uu____5100, q)))))
                       in
                    FStar_Syntax_Syntax.Meta_pattern uu____4992
                | FStar_Syntax_Syntax.Meta_monadic (m1,tbody) ->
                    let uu____5111 =
                      let uu____5118 =
                        non_tail_inline_closure_env cfg env tbody  in
                      (m1, uu____5118)  in
                    FStar_Syntax_Syntax.Meta_monadic uu____5111
                | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,tbody) ->
                    let uu____5130 =
                      let uu____5139 =
                        non_tail_inline_closure_env cfg env tbody  in
                      (m1, m2, uu____5139)  in
                    FStar_Syntax_Syntax.Meta_monadic_lift uu____5130
                | uu____5144 -> m  in
              let t1 = mk (FStar_Syntax_Syntax.Tm_meta (t, m1)) r  in
              rebuild_closure cfg env stack1 t1
          | uu____5148 -> failwith "Impossible: unexpected stack element"

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
        let uu____5162 =
          FStar_All.pipe_right bs
            (FStar_List.fold_left
               (fun uu____5211  ->
                  fun uu____5212  ->
                    match (uu____5211, uu____5212) with
                    | ((env1,out),(b,imp)) ->
                        let b1 =
                          let uu___137_5282 = b  in
                          let uu____5283 =
                            inline_closure_env cfg env1 []
                              b.FStar_Syntax_Syntax.sort
                             in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___137_5282.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___137_5282.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = uu____5283
                          }  in
                        let env2 = dummy :: env1  in
                        (env2, ((b1, imp) :: out))) (env, []))
           in
        match uu____5162 with | (env1,bs1) -> ((FStar_List.rev bs1), env1)

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
        | uu____5376 ->
            (match c.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Total (t,uopt) ->
                 let uu____5389 = inline_closure_env cfg env [] t  in
                 let uu____5390 =
                   FStar_Option.map (norm_universe cfg env) uopt  in
                 FStar_Syntax_Syntax.mk_Total' uu____5389 uu____5390
             | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                 let uu____5403 = inline_closure_env cfg env [] t  in
                 let uu____5404 =
                   FStar_Option.map (norm_universe cfg env) uopt  in
                 FStar_Syntax_Syntax.mk_GTotal' uu____5403 uu____5404
             | FStar_Syntax_Syntax.Comp c1 ->
                 let rt =
                   inline_closure_env cfg env []
                     c1.FStar_Syntax_Syntax.result_typ
                    in
                 let args =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args
                     (FStar_List.map
                        (fun uu____5450  ->
                           match uu____5450 with
                           | (a,q) ->
                               let uu____5463 =
                                 inline_closure_env cfg env [] a  in
                               (uu____5463, q)))
                    in
                 let flags1 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_List.map
                        (fun uu___82_5478  ->
                           match uu___82_5478 with
                           | FStar_Syntax_Syntax.DECREASES t ->
                               let uu____5482 =
                                 inline_closure_env cfg env [] t  in
                               FStar_Syntax_Syntax.DECREASES uu____5482
                           | f -> f))
                    in
                 let uu____5486 =
                   let uu___138_5487 = c1  in
                   let uu____5488 =
                     FStar_List.map (norm_universe cfg env)
                       c1.FStar_Syntax_Syntax.comp_univs
                      in
                   {
                     FStar_Syntax_Syntax.comp_univs = uu____5488;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___138_5487.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ = rt;
                     FStar_Syntax_Syntax.effect_args = args;
                     FStar_Syntax_Syntax.flags = flags1
                   }  in
                 FStar_Syntax_Syntax.mk_Comp uu____5486)

and (filter_out_lcomp_cflags :
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun flags1  ->
    FStar_All.pipe_right flags1
      (FStar_List.filter
         (fun uu___83_5498  ->
            match uu___83_5498 with
            | FStar_Syntax_Syntax.DECREASES uu____5499 -> false
            | uu____5502 -> true))

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
                   (fun uu___84_5520  ->
                      match uu___84_5520 with
                      | FStar_Syntax_Syntax.DECREASES uu____5521 -> false
                      | uu____5524 -> true))
               in
            let rc1 =
              let uu___139_5526 = rc  in
              let uu____5527 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (inline_closure_env cfg env [])
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___139_5526.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____5527;
                FStar_Syntax_Syntax.residual_flags = flags1
              }  in
            FStar_Pervasives_Native.Some rc1
        | uu____5536 -> lopt

let (closure_as_term :
  cfg -> env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun cfg  -> fun env  -> fun t  -> non_tail_inline_closure_env cfg env t 
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
    let uu____5630 = FStar_Syntax_Embeddings.unembed_list_safe u  in
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a) uu____5630  in
  let arg_as_bounded_int uu____5658 =
    match uu____5658 with
    | (a,uu____5670) ->
        let uu____5677 =
          let uu____5678 = FStar_Syntax_Subst.compress a  in
          uu____5678.FStar_Syntax_Syntax.n  in
        (match uu____5677 with
         | FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv1;
                FStar_Syntax_Syntax.pos = uu____5688;
                FStar_Syntax_Syntax.vars = uu____5689;_},({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_constant
                                                              (FStar_Const.Const_int
                                                              (i,FStar_Pervasives_Native.None
                                                               ));
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____5691;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____5692;_},uu____5693)::[])
             when
             let uu____5732 =
               FStar_Ident.text_of_lid
                 (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                in
             FStar_Util.ends_with uu____5732 "int_to_t" ->
             let uu____5733 =
               let uu____5738 = FStar_BigInt.big_int_of_string i  in
               (fv1, uu____5738)  in
             FStar_Pervasives_Native.Some uu____5733
         | uu____5743 -> FStar_Pervasives_Native.None)
     in
  let lift_unary a b f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a)::[] ->
        let uu____5783 = f a  in FStar_Pervasives_Native.Some uu____5783
    | uu____5784 -> FStar_Pervasives_Native.None  in
  let lift_binary a b f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a0)::(FStar_Pervasives_Native.Some
        a1)::[] ->
        let uu____5832 = f a0 a1  in FStar_Pervasives_Native.Some uu____5832
    | uu____5833 -> FStar_Pervasives_Native.None  in
  let unary_op a422 a423 a424 a425 a426 =
    (Obj.magic
       (fun a  ->
          fun as_a  ->
            fun f  ->
              fun res  ->
                fun args  ->
                  let uu____5875 = FStar_List.map as_a args  in
                  lift_unary () ()
                    (fun a421  -> (Obj.magic (f res.psc_range)) a421)
                    uu____5875)) a422 a423 a424 a425 a426
     in
  let binary_op a429 a430 a431 a432 a433 =
    (Obj.magic
       (fun a  ->
          fun as_a  ->
            fun f  ->
              fun res  ->
                fun args  ->
                  let uu____5924 = FStar_List.map as_a args  in
                  lift_binary () ()
                    (fun a427  ->
                       fun a428  -> (Obj.magic (f res.psc_range)) a427 a428)
                    uu____5924)) a429 a430 a431 a432 a433
     in
  let as_primitive_step is_strong uu____5951 =
    match uu____5951 with
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
    unary_op () (fun a434  -> (Obj.magic arg_as_int) a434)
      (fun a435  ->
         fun a436  ->
           (Obj.magic
              (fun r  ->
                 fun x  ->
                   let uu____5999 = f x  in
                   FStar_Syntax_Embeddings.embed_int r uu____5999)) a435 a436)
     in
  let binary_int_op f =
    binary_op () (fun a437  -> (Obj.magic arg_as_int) a437)
      (fun a438  ->
         fun a439  ->
           fun a440  ->
             (Obj.magic
                (fun r  ->
                   fun x  ->
                     fun y  ->
                       let uu____6027 = f x y  in
                       FStar_Syntax_Embeddings.embed_int r uu____6027)) a438
               a439 a440)
     in
  let unary_bool_op f =
    unary_op () (fun a441  -> (Obj.magic arg_as_bool) a441)
      (fun a442  ->
         fun a443  ->
           (Obj.magic
              (fun r  ->
                 fun x  ->
                   let uu____6048 = f x  in
                   FStar_Syntax_Embeddings.embed_bool r uu____6048)) a442
             a443)
     in
  let binary_bool_op f =
    binary_op () (fun a444  -> (Obj.magic arg_as_bool) a444)
      (fun a445  ->
         fun a446  ->
           fun a447  ->
             (Obj.magic
                (fun r  ->
                   fun x  ->
                     fun y  ->
                       let uu____6076 = f x y  in
                       FStar_Syntax_Embeddings.embed_bool r uu____6076)) a445
               a446 a447)
     in
  let binary_string_op f =
    binary_op () (fun a448  -> (Obj.magic arg_as_string) a448)
      (fun a449  ->
         fun a450  ->
           fun a451  ->
             (Obj.magic
                (fun r  ->
                   fun x  ->
                     fun y  ->
                       let uu____6104 = f x y  in
                       FStar_Syntax_Embeddings.embed_string r uu____6104))
               a449 a450 a451)
     in
  let mixed_binary_op a b c as_a as_b embed_c f res args =
    match args with
    | a::b::[] ->
        let uu____6212 =
          let uu____6221 = as_a a  in
          let uu____6224 = as_b b  in (uu____6221, uu____6224)  in
        (match uu____6212 with
         | (FStar_Pervasives_Native.Some a1,FStar_Pervasives_Native.Some b1)
             ->
             let uu____6239 =
               let uu____6240 = f res.psc_range a1 b1  in
               embed_c res.psc_range uu____6240  in
             FStar_Pervasives_Native.Some uu____6239
         | uu____6241 -> FStar_Pervasives_Native.None)
    | uu____6250 -> FStar_Pervasives_Native.None  in
  let list_of_string' rng s =
    let name l =
      let uu____6264 =
        let uu____6265 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant
            FStar_Pervasives_Native.None
           in
        FStar_Syntax_Syntax.Tm_fvar uu____6265  in
      mk uu____6264 rng  in
    let char_t = name FStar_Parser_Const.char_lid  in
    let charterm c =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c)) rng  in
    let uu____6275 =
      let uu____6278 = FStar_String.list_of_string s  in
      FStar_List.map charterm uu____6278  in
    FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu____6275  in
  let string_of_list' rng l =
    let s = FStar_String.string_of_list l  in FStar_Syntax_Util.exp_string s
     in
  let string_compare' rng s1 s2 =
    let r = FStar_String.compare s1 s2  in
    let uu____6310 =
      let uu____6311 = FStar_Util.string_of_int r  in
      FStar_BigInt.big_int_of_string uu____6311  in
    FStar_Syntax_Embeddings.embed_int rng uu____6310  in
  let string_concat' psc args =
    match args with
    | a1::a2::[] ->
        let uu____6329 = arg_as_string a1  in
        (match uu____6329 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____6335 =
               Obj.magic
                 (arg_as_list ()
                    (Obj.magic FStar_Syntax_Embeddings.unembed_string_safe)
                    a2)
                in
             (match uu____6335 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2  in
                  let uu____6348 =
                    FStar_Syntax_Embeddings.embed_string psc.psc_range r  in
                  FStar_Pervasives_Native.Some uu____6348
              | uu____6349 -> FStar_Pervasives_Native.None)
         | uu____6354 -> FStar_Pervasives_Native.None)
    | uu____6357 -> FStar_Pervasives_Native.None  in
  let string_of_int1 rng i =
    let uu____6367 = FStar_BigInt.string_of_big_int i  in
    FStar_Syntax_Embeddings.embed_string rng uu____6367  in
  let string_of_bool1 rng b =
    FStar_Syntax_Embeddings.embed_string rng (if b then "true" else "false")
     in
  let mk_range1 psc args =
    match args with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____6396 =
          let uu____6417 = arg_as_string fn  in
          let uu____6420 = arg_as_int from_line  in
          let uu____6423 = arg_as_int from_col  in
          let uu____6426 = arg_as_int to_line  in
          let uu____6429 = arg_as_int to_col  in
          (uu____6417, uu____6420, uu____6423, uu____6426, uu____6429)  in
        (match uu____6396 with
         | (FStar_Pervasives_Native.Some fn1,FStar_Pervasives_Native.Some
            from_l,FStar_Pervasives_Native.Some
            from_c,FStar_Pervasives_Native.Some
            to_l,FStar_Pervasives_Native.Some to_c) ->
             let r =
               let uu____6460 =
                 let uu____6461 = FStar_BigInt.to_int_fs from_l  in
                 let uu____6462 = FStar_BigInt.to_int_fs from_c  in
                 FStar_Range.mk_pos uu____6461 uu____6462  in
               let uu____6463 =
                 let uu____6464 = FStar_BigInt.to_int_fs to_l  in
                 let uu____6465 = FStar_BigInt.to_int_fs to_c  in
                 FStar_Range.mk_pos uu____6464 uu____6465  in
               FStar_Range.mk_range fn1 uu____6460 uu____6463  in
             let uu____6466 =
               FStar_Syntax_Embeddings.embed_range psc.psc_range r  in
             FStar_Pervasives_Native.Some uu____6466
         | uu____6467 -> FStar_Pervasives_Native.None)
    | uu____6488 -> FStar_Pervasives_Native.None  in
  let decidable_eq neg psc args =
    let r = psc.psc_range  in
    let tru =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool true)) r
       in
    let fal =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool false)) r
       in
    match args with
    | (_typ,uu____6515)::(a1,uu____6517)::(a2,uu____6519)::[] ->
        let uu____6556 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____6556 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some (if neg then fal else tru)
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some (if neg then tru else fal)
         | uu____6569 -> FStar_Pervasives_Native.None)
    | uu____6570 -> failwith "Unexpected number of arguments"  in
  let prims_to_fstar_range_step psc args =
    match args with
    | (a1,uu____6597)::[] ->
        let uu____6606 = FStar_Syntax_Embeddings.unembed_range_safe a1  in
        (match uu____6606 with
         | FStar_Pervasives_Native.Some r ->
             let uu____6612 =
               FStar_Syntax_Embeddings.embed_range psc.psc_range r  in
             FStar_Pervasives_Native.Some uu____6612
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
    | uu____6613 -> failwith "Unexpected number of arguments"  in
  let basic_ops =
    let uu____6637 =
      let uu____6652 =
        let uu____6667 =
          let uu____6682 =
            let uu____6697 =
              let uu____6712 =
                let uu____6727 =
                  let uu____6742 =
                    let uu____6757 =
                      let uu____6772 =
                        let uu____6787 =
                          let uu____6802 =
                            let uu____6817 =
                              let uu____6832 =
                                let uu____6847 =
                                  let uu____6862 =
                                    let uu____6877 =
                                      let uu____6892 =
                                        let uu____6907 =
                                          let uu____6922 =
                                            let uu____6937 =
                                              let uu____6952 =
                                                let uu____6965 =
                                                  FStar_Parser_Const.p2l
                                                    ["FStar";
                                                    "String";
                                                    "list_of_string"]
                                                   in
                                                (uu____6965,
                                                  (Prims.parse_int "1"),
                                                  (unary_op ()
                                                     (fun a452  ->
                                                        (Obj.magic
                                                           arg_as_string)
                                                          a452)
                                                     (fun a453  ->
                                                        fun a454  ->
                                                          (Obj.magic
                                                             list_of_string')
                                                            a453 a454)))
                                                 in
                                              let uu____6972 =
                                                let uu____6987 =
                                                  let uu____7000 =
                                                    FStar_Parser_Const.p2l
                                                      ["FStar";
                                                      "String";
                                                      "string_of_list"]
                                                     in
                                                  (uu____7000,
                                                    (Prims.parse_int "1"),
                                                    (unary_op ()
                                                       (fun a455  ->
                                                          (Obj.magic
                                                             (arg_as_list ()
                                                                (Obj.magic
                                                                   FStar_Syntax_Embeddings.unembed_char_safe)))
                                                            a455)
                                                       (fun a456  ->
                                                          fun a457  ->
                                                            (Obj.magic
                                                               string_of_list')
                                                              a456 a457)))
                                                   in
                                                let uu____7007 =
                                                  let uu____7022 =
                                                    let uu____7037 =
                                                      FStar_Parser_Const.p2l
                                                        ["FStar";
                                                        "String";
                                                        "concat"]
                                                       in
                                                    (uu____7037,
                                                      (Prims.parse_int "2"),
                                                      string_concat')
                                                     in
                                                  let uu____7046 =
                                                    let uu____7063 =
                                                      let uu____7078 =
                                                        FStar_Parser_Const.p2l
                                                          ["Prims";
                                                          "mk_range"]
                                                         in
                                                      (uu____7078,
                                                        (Prims.parse_int "5"),
                                                        mk_range1)
                                                       in
                                                    [uu____7063]  in
                                                  uu____7022 :: uu____7046
                                                   in
                                                uu____6987 :: uu____7007  in
                                              uu____6952 :: uu____6972  in
                                            (FStar_Parser_Const.op_notEq,
                                              (Prims.parse_int "3"),
                                              (decidable_eq true)) ::
                                              uu____6937
                                             in
                                          (FStar_Parser_Const.op_Eq,
                                            (Prims.parse_int "3"),
                                            (decidable_eq false)) ::
                                            uu____6922
                                           in
                                        (FStar_Parser_Const.string_compare,
                                          (Prims.parse_int "2"),
                                          (binary_op ()
                                             (fun a458  ->
                                                (Obj.magic arg_as_string)
                                                  a458)
                                             (fun a459  ->
                                                fun a460  ->
                                                  fun a461  ->
                                                    (Obj.magic
                                                       string_compare') a459
                                                      a460 a461)))
                                          :: uu____6907
                                         in
                                      (FStar_Parser_Const.string_of_bool_lid,
                                        (Prims.parse_int "1"),
                                        (unary_op ()
                                           (fun a462  ->
                                              (Obj.magic arg_as_bool) a462)
                                           (fun a463  ->
                                              fun a464  ->
                                                (Obj.magic string_of_bool1)
                                                  a463 a464)))
                                        :: uu____6892
                                       in
                                    (FStar_Parser_Const.string_of_int_lid,
                                      (Prims.parse_int "1"),
                                      (unary_op ()
                                         (fun a465  ->
                                            (Obj.magic arg_as_int) a465)
                                         (fun a466  ->
                                            fun a467  ->
                                              (Obj.magic string_of_int1) a466
                                                a467)))
                                      :: uu____6877
                                     in
                                  (FStar_Parser_Const.str_make_lid,
                                    (Prims.parse_int "2"),
                                    (mixed_binary_op () () ()
                                       (fun a468  ->
                                          (Obj.magic arg_as_int) a468)
                                       (fun a469  ->
                                          (Obj.magic arg_as_char) a469)
                                       (fun a470  ->
                                          fun a471  ->
                                            (Obj.magic
                                               FStar_Syntax_Embeddings.embed_string)
                                              a470 a471)
                                       (fun a472  ->
                                          fun a473  ->
                                            fun a474  ->
                                              (Obj.magic
                                                 (fun r  ->
                                                    fun x  ->
                                                      fun y  ->
                                                        let uu____7269 =
                                                          FStar_BigInt.to_int_fs
                                                            x
                                                           in
                                                        FStar_String.make
                                                          uu____7269 y)) a472
                                                a473 a474)))
                                    :: uu____6862
                                   in
                                (FStar_Parser_Const.strcat_lid',
                                  (Prims.parse_int "2"),
                                  (binary_string_op
                                     (fun x  -> fun y  -> Prims.strcat x y)))
                                  :: uu____6847
                                 in
                              (FStar_Parser_Const.strcat_lid,
                                (Prims.parse_int "2"),
                                (binary_string_op
                                   (fun x  -> fun y  -> Prims.strcat x y)))
                                :: uu____6832
                               in
                            (FStar_Parser_Const.op_Or, (Prims.parse_int "2"),
                              (binary_bool_op (fun x  -> fun y  -> x || y)))
                              :: uu____6817
                             in
                          (FStar_Parser_Const.op_And, (Prims.parse_int "2"),
                            (binary_bool_op (fun x  -> fun y  -> x && y))) ::
                            uu____6802
                           in
                        (FStar_Parser_Const.op_Negation,
                          (Prims.parse_int "1"),
                          (unary_bool_op (fun x  -> Prims.op_Negation x))) ::
                          uu____6787
                         in
                      (FStar_Parser_Const.op_Modulus, (Prims.parse_int "2"),
                        (binary_int_op
                           (fun x  -> fun y  -> FStar_BigInt.mod_big_int x y)))
                        :: uu____6772
                       in
                    (FStar_Parser_Const.op_GTE, (Prims.parse_int "2"),
                      (binary_op ()
                         (fun a475  -> (Obj.magic arg_as_int) a475)
                         (fun a476  ->
                            fun a477  ->
                              fun a478  ->
                                (Obj.magic
                                   (fun r  ->
                                      fun x  ->
                                        fun y  ->
                                          let uu____7436 =
                                            FStar_BigInt.ge_big_int x y  in
                                          FStar_Syntax_Embeddings.embed_bool
                                            r uu____7436)) a476 a477 a478)))
                      :: uu____6757
                     in
                  (FStar_Parser_Const.op_GT, (Prims.parse_int "2"),
                    (binary_op () (fun a479  -> (Obj.magic arg_as_int) a479)
                       (fun a480  ->
                          fun a481  ->
                            fun a482  ->
                              (Obj.magic
                                 (fun r  ->
                                    fun x  ->
                                      fun y  ->
                                        let uu____7462 =
                                          FStar_BigInt.gt_big_int x y  in
                                        FStar_Syntax_Embeddings.embed_bool r
                                          uu____7462)) a480 a481 a482)))
                    :: uu____6742
                   in
                (FStar_Parser_Const.op_LTE, (Prims.parse_int "2"),
                  (binary_op () (fun a483  -> (Obj.magic arg_as_int) a483)
                     (fun a484  ->
                        fun a485  ->
                          fun a486  ->
                            (Obj.magic
                               (fun r  ->
                                  fun x  ->
                                    fun y  ->
                                      let uu____7488 =
                                        FStar_BigInt.le_big_int x y  in
                                      FStar_Syntax_Embeddings.embed_bool r
                                        uu____7488)) a484 a485 a486)))
                  :: uu____6727
                 in
              (FStar_Parser_Const.op_LT, (Prims.parse_int "2"),
                (binary_op () (fun a487  -> (Obj.magic arg_as_int) a487)
                   (fun a488  ->
                      fun a489  ->
                        fun a490  ->
                          (Obj.magic
                             (fun r  ->
                                fun x  ->
                                  fun y  ->
                                    let uu____7514 =
                                      FStar_BigInt.lt_big_int x y  in
                                    FStar_Syntax_Embeddings.embed_bool r
                                      uu____7514)) a488 a489 a490)))
                :: uu____6712
               in
            (FStar_Parser_Const.op_Division, (Prims.parse_int "2"),
              (binary_int_op
                 (fun x  -> fun y  -> FStar_BigInt.div_big_int x y)))
              :: uu____6697
             in
          (FStar_Parser_Const.op_Multiply, (Prims.parse_int "2"),
            (binary_int_op
               (fun x  -> fun y  -> FStar_BigInt.mult_big_int x y)))
            :: uu____6682
           in
        (FStar_Parser_Const.op_Subtraction, (Prims.parse_int "2"),
          (binary_int_op (fun x  -> fun y  -> FStar_BigInt.sub_big_int x y)))
          :: uu____6667
         in
      (FStar_Parser_Const.op_Addition, (Prims.parse_int "2"),
        (binary_int_op (fun x  -> fun y  -> FStar_BigInt.add_big_int x y)))
        :: uu____6652
       in
    (FStar_Parser_Const.op_Minus, (Prims.parse_int "1"),
      (unary_int_op (fun x  -> FStar_BigInt.minus_big_int x))) :: uu____6637
     in
  let weak_ops =
    let uu____7653 =
      let uu____7672 =
        FStar_Parser_Const.p2l ["FStar"; "Range"; "prims_to_fstar_range"]  in
      (uu____7672, (Prims.parse_int "1"), prims_to_fstar_range_step)  in
    [uu____7653]  in
  let bounded_arith_ops =
    let bounded_signed_int_types = ["Int8"; "Int16"; "Int32"; "Int64"]  in
    let bounded_unsigned_int_types =
      ["UInt8"; "UInt16"; "UInt32"; "UInt64"; "UInt128"]  in
    let int_as_bounded r int_to_t1 n1 =
      let c = FStar_Syntax_Embeddings.embed_int r n1  in
      let int_to_t2 = FStar_Syntax_Syntax.fv_to_tm int_to_t1  in
      let uu____7756 =
        let uu____7757 =
          let uu____7758 = FStar_Syntax_Syntax.as_arg c  in [uu____7758]  in
        FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____7757  in
      uu____7756 FStar_Pervasives_Native.None r  in
    let add_sub_mul_v =
      FStar_All.pipe_right
        (FStar_List.append bounded_signed_int_types
           bounded_unsigned_int_types)
        (FStar_List.collect
           (fun m  ->
              let uu____7808 =
                let uu____7821 = FStar_Parser_Const.p2l ["FStar"; m; "add"]
                   in
                (uu____7821, (Prims.parse_int "2"),
                  (binary_op ()
                     (fun a491  -> (Obj.magic arg_as_bounded_int) a491)
                     (fun a492  ->
                        fun a493  ->
                          fun a494  ->
                            (Obj.magic
                               (fun r  ->
                                  fun uu____7837  ->
                                    fun uu____7838  ->
                                      match (uu____7837, uu____7838) with
                                      | ((int_to_t1,x),(uu____7857,y)) ->
                                          let uu____7867 =
                                            FStar_BigInt.add_big_int x y  in
                                          int_as_bounded r int_to_t1
                                            uu____7867)) a492 a493 a494)))
                 in
              let uu____7868 =
                let uu____7883 =
                  let uu____7896 = FStar_Parser_Const.p2l ["FStar"; m; "sub"]
                     in
                  (uu____7896, (Prims.parse_int "2"),
                    (binary_op ()
                       (fun a495  -> (Obj.magic arg_as_bounded_int) a495)
                       (fun a496  ->
                          fun a497  ->
                            fun a498  ->
                              (Obj.magic
                                 (fun r  ->
                                    fun uu____7912  ->
                                      fun uu____7913  ->
                                        match (uu____7912, uu____7913) with
                                        | ((int_to_t1,x),(uu____7932,y)) ->
                                            let uu____7942 =
                                              FStar_BigInt.sub_big_int x y
                                               in
                                            int_as_bounded r int_to_t1
                                              uu____7942)) a496 a497 a498)))
                   in
                let uu____7943 =
                  let uu____7958 =
                    let uu____7971 =
                      FStar_Parser_Const.p2l ["FStar"; m; "mul"]  in
                    (uu____7971, (Prims.parse_int "2"),
                      (binary_op ()
                         (fun a499  -> (Obj.magic arg_as_bounded_int) a499)
                         (fun a500  ->
                            fun a501  ->
                              fun a502  ->
                                (Obj.magic
                                   (fun r  ->
                                      fun uu____7987  ->
                                        fun uu____7988  ->
                                          match (uu____7987, uu____7988) with
                                          | ((int_to_t1,x),(uu____8007,y)) ->
                                              let uu____8017 =
                                                FStar_BigInt.mult_big_int x y
                                                 in
                                              int_as_bounded r int_to_t1
                                                uu____8017)) a500 a501 a502)))
                     in
                  let uu____8018 =
                    let uu____8033 =
                      let uu____8046 =
                        FStar_Parser_Const.p2l ["FStar"; m; "v"]  in
                      (uu____8046, (Prims.parse_int "1"),
                        (unary_op ()
                           (fun a503  -> (Obj.magic arg_as_bounded_int) a503)
                           (fun a504  ->
                              fun a505  ->
                                (Obj.magic
                                   (fun r  ->
                                      fun uu____8058  ->
                                        match uu____8058 with
                                        | (int_to_t1,x) ->
                                            FStar_Syntax_Embeddings.embed_int
                                              r x)) a504 a505)))
                       in
                    [uu____8033]  in
                  uu____7958 :: uu____8018  in
                uu____7883 :: uu____7943  in
              uu____7808 :: uu____7868))
       in
    let div_mod_unsigned =
      FStar_All.pipe_right bounded_unsigned_int_types
        (FStar_List.collect
           (fun m  ->
              let uu____8172 =
                let uu____8185 = FStar_Parser_Const.p2l ["FStar"; m; "div"]
                   in
                (uu____8185, (Prims.parse_int "2"),
                  (binary_op ()
                     (fun a506  -> (Obj.magic arg_as_bounded_int) a506)
                     (fun a507  ->
                        fun a508  ->
                          fun a509  ->
                            (Obj.magic
                               (fun r  ->
                                  fun uu____8201  ->
                                    fun uu____8202  ->
                                      match (uu____8201, uu____8202) with
                                      | ((int_to_t1,x),(uu____8221,y)) ->
                                          let uu____8231 =
                                            FStar_BigInt.div_big_int x y  in
                                          int_as_bounded r int_to_t1
                                            uu____8231)) a507 a508 a509)))
                 in
              let uu____8232 =
                let uu____8247 =
                  let uu____8260 = FStar_Parser_Const.p2l ["FStar"; m; "rem"]
                     in
                  (uu____8260, (Prims.parse_int "2"),
                    (binary_op ()
                       (fun a510  -> (Obj.magic arg_as_bounded_int) a510)
                       (fun a511  ->
                          fun a512  ->
                            fun a513  ->
                              (Obj.magic
                                 (fun r  ->
                                    fun uu____8276  ->
                                      fun uu____8277  ->
                                        match (uu____8276, uu____8277) with
                                        | ((int_to_t1,x),(uu____8296,y)) ->
                                            let uu____8306 =
                                              FStar_BigInt.mod_big_int x y
                                               in
                                            int_as_bounded r int_to_t1
                                              uu____8306)) a511 a512 a513)))
                   in
                [uu____8247]  in
              uu____8172 :: uu____8232))
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
    | (_typ,uu____8418)::(a1,uu____8420)::(a2,uu____8422)::[] ->
        let uu____8459 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____8459 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___140_8465 = FStar_Syntax_Util.t_true  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___140_8465.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___140_8465.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___141_8469 = FStar_Syntax_Util.t_false  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___141_8469.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___141_8469.FStar_Syntax_Syntax.vars)
                })
         | uu____8470 -> FStar_Pervasives_Native.None)
    | (_typ,uu____8472)::uu____8473::(a1,uu____8475)::(a2,uu____8477)::[] ->
        let uu____8526 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____8526 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___140_8532 = FStar_Syntax_Util.t_true  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___140_8532.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___140_8532.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___141_8536 = FStar_Syntax_Util.t_false  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___141_8536.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___141_8536.FStar_Syntax_Syntax.vars)
                })
         | uu____8537 -> FStar_Pervasives_Native.None)
    | uu____8538 -> failwith "Unexpected number of arguments"  in
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
    let uu____8590 = FStar_ST.op_Bang unembed_binder_knot  in
    match uu____8590 with
    | FStar_Pervasives_Native.Some f -> f t
    | FStar_Pervasives_Native.None  ->
        (FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos
           (FStar_Errors.Warning_UnembedBinderKnot,
             "unembed_binder_knot is unset!");
         FStar_Pervasives_Native.None)
  
let mk_psc_subst :
  'Auu____8637 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____8637) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_Syntax_Syntax.subst_elt Prims.list
  =
  fun cfg  ->
    fun env  ->
      FStar_List.fold_right
        (fun uu____8697  ->
           fun subst1  ->
             match uu____8697 with
             | (binder_opt,closure) ->
                 (match (binder_opt, closure) with
                  | (FStar_Pervasives_Native.Some b,Clos
                     (env1,term,uu____8738,uu____8739)) ->
                      let uu____8798 = b  in
                      (match uu____8798 with
                       | (bv,uu____8806) ->
                           let uu____8807 =
                             let uu____8808 =
                               FStar_Syntax_Util.is_constructed_typ
                                 bv.FStar_Syntax_Syntax.sort
                                 FStar_Parser_Const.binder_lid
                                in
                             Prims.op_Negation uu____8808  in
                           if uu____8807
                           then subst1
                           else
                             (let term1 = closure_as_term cfg env1 term  in
                              let uu____8813 = unembed_binder term1  in
                              match uu____8813 with
                              | FStar_Pervasives_Native.None  -> subst1
                              | FStar_Pervasives_Native.Some x ->
                                  let b1 =
                                    let uu____8820 =
                                      let uu___142_8821 = bv  in
                                      let uu____8822 =
                                        FStar_Syntax_Subst.subst subst1
                                          (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort
                                         in
                                      {
                                        FStar_Syntax_Syntax.ppname =
                                          (uu___142_8821.FStar_Syntax_Syntax.ppname);
                                        FStar_Syntax_Syntax.index =
                                          (uu___142_8821.FStar_Syntax_Syntax.index);
                                        FStar_Syntax_Syntax.sort = uu____8822
                                      }  in
                                    FStar_Syntax_Syntax.freshen_bv uu____8820
                                     in
                                  let b_for_x =
                                    let uu____8826 =
                                      let uu____8833 =
                                        FStar_Syntax_Syntax.bv_to_name b1  in
                                      ((FStar_Pervasives_Native.fst x),
                                        uu____8833)
                                       in
                                    FStar_Syntax_Syntax.NT uu____8826  in
                                  let subst2 =
                                    FStar_List.filter
                                      (fun uu___85_8843  ->
                                         match uu___85_8843 with
                                         | FStar_Syntax_Syntax.NT
                                             (uu____8844,{
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_name
                                                             b';
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____8846;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____8847;_})
                                             ->
                                             let uu____8852 =
                                               FStar_Ident.ident_equals
                                                 b1.FStar_Syntax_Syntax.ppname
                                                 b'.FStar_Syntax_Syntax.ppname
                                                in
                                             Prims.op_Negation uu____8852
                                         | uu____8853 -> true) subst1
                                     in
                                  b_for_x :: subst2))
                  | uu____8854 -> subst1)) env []
  
let reduce_primops :
  'Auu____8871 'Auu____8872 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____8871) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____8872 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          if Prims.op_Negation (cfg.steps).primops
          then tm
          else
            (let uu____8914 = FStar_Syntax_Util.head_and_args tm  in
             match uu____8914 with
             | (head1,args) ->
                 let uu____8951 =
                   let uu____8952 = FStar_Syntax_Util.un_uinst head1  in
                   uu____8952.FStar_Syntax_Syntax.n  in
                 (match uu____8951 with
                  | FStar_Syntax_Syntax.Tm_fvar fv ->
                      let uu____8956 = find_prim_step cfg fv  in
                      (match uu____8956 with
                       | FStar_Pervasives_Native.Some prim_step when
                           prim_step.strong_reduction_ok ||
                             (Prims.op_Negation cfg.strong)
                           ->
                           let l = FStar_List.length args  in
                           if l < prim_step.arity
                           then
                             (log_primops cfg
                                (fun uu____8978  ->
                                   let uu____8979 =
                                     FStar_Syntax_Print.lid_to_string
                                       prim_step.name
                                      in
                                   let uu____8980 =
                                     FStar_Util.string_of_int l  in
                                   let uu____8987 =
                                     FStar_Util.string_of_int prim_step.arity
                                      in
                                   FStar_Util.print3
                                     "primop: found partially applied %s (%s/%s args)\n"
                                     uu____8979 uu____8980 uu____8987);
                              tm)
                           else
                             (let uu____8989 =
                                if l = prim_step.arity
                                then (args, [])
                                else FStar_List.splitAt prim_step.arity args
                                 in
                              match uu____8989 with
                              | (args_1,args_2) ->
                                  (log_primops cfg
                                     (fun uu____9100  ->
                                        let uu____9101 =
                                          FStar_Syntax_Print.term_to_string
                                            tm
                                           in
                                        FStar_Util.print1
                                          "primop: trying to reduce <%s>\n"
                                          uu____9101);
                                   (let psc =
                                      {
                                        psc_range =
                                          (head1.FStar_Syntax_Syntax.pos);
                                        psc_subst =
                                          (fun uu____9104  ->
                                             if
                                               prim_step.requires_binder_substitution
                                             then mk_psc_subst cfg env
                                             else [])
                                      }  in
                                    let uu____9106 =
                                      prim_step.interpretation psc args_1  in
                                    match uu____9106 with
                                    | FStar_Pervasives_Native.None  ->
                                        (log_primops cfg
                                           (fun uu____9112  ->
                                              let uu____9113 =
                                                FStar_Syntax_Print.term_to_string
                                                  tm
                                                 in
                                              FStar_Util.print1
                                                "primop: <%s> did not reduce\n"
                                                uu____9113);
                                         tm)
                                    | FStar_Pervasives_Native.Some reduced ->
                                        (log_primops cfg
                                           (fun uu____9119  ->
                                              let uu____9120 =
                                                FStar_Syntax_Print.term_to_string
                                                  tm
                                                 in
                                              let uu____9121 =
                                                FStar_Syntax_Print.term_to_string
                                                  reduced
                                                 in
                                              FStar_Util.print2
                                                "primop: <%s> reduced to <%s>\n"
                                                uu____9120 uu____9121);
                                         FStar_Syntax_Util.mk_app reduced
                                           args_2))))
                       | FStar_Pervasives_Native.Some uu____9122 ->
                           (log_primops cfg
                              (fun uu____9126  ->
                                 let uu____9127 =
                                   FStar_Syntax_Print.term_to_string tm  in
                                 FStar_Util.print1
                                   "primop: not reducing <%s> since we're doing strong reduction\n"
                                   uu____9127);
                            tm)
                       | FStar_Pervasives_Native.None  -> tm)
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_range_of ) when
                      Prims.op_Negation cfg.strong ->
                      (log_primops cfg
                         (fun uu____9131  ->
                            let uu____9132 =
                              FStar_Syntax_Print.term_to_string tm  in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____9132);
                       (match args with
                        | (a1,uu____9134)::[] ->
                            FStar_Syntax_Embeddings.embed_range
                              tm.FStar_Syntax_Syntax.pos
                              a1.FStar_Syntax_Syntax.pos
                        | uu____9151 -> tm))
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_set_range_of ) when
                      Prims.op_Negation cfg.strong ->
                      (log_primops cfg
                         (fun uu____9163  ->
                            let uu____9164 =
                              FStar_Syntax_Print.term_to_string tm  in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____9164);
                       (match args with
                        | (t,uu____9166)::(r,uu____9168)::[] ->
                            let uu____9195 =
                              FStar_Syntax_Embeddings.unembed_range r  in
                            (match uu____9195 with
                             | FStar_Pervasives_Native.Some rng ->
                                 let uu___143_9199 = t  in
                                 {
                                   FStar_Syntax_Syntax.n =
                                     (uu___143_9199.FStar_Syntax_Syntax.n);
                                   FStar_Syntax_Syntax.pos = rng;
                                   FStar_Syntax_Syntax.vars =
                                     (uu___143_9199.FStar_Syntax_Syntax.vars)
                                 }
                             | FStar_Pervasives_Native.None  -> tm)
                        | uu____9202 -> tm))
                  | uu____9211 -> tm))
  
let reduce_equality :
  'Auu____9216 'Auu____9217 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____9216) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____9217 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun tm  ->
      reduce_primops
        (let uu___144_9255 = cfg  in
         {
           steps =
             (let uu___145_9258 = default_steps  in
              {
                beta = (uu___145_9258.beta);
                iota = (uu___145_9258.iota);
                zeta = (uu___145_9258.zeta);
                weak = (uu___145_9258.weak);
                hnf = (uu___145_9258.hnf);
                primops = true;
                no_delta_steps = (uu___145_9258.no_delta_steps);
                unfold_until = (uu___145_9258.unfold_until);
                unfold_only = (uu___145_9258.unfold_only);
                unfold_attr = (uu___145_9258.unfold_attr);
                unfold_tac = (uu___145_9258.unfold_tac);
                pure_subterms_within_computations =
                  (uu___145_9258.pure_subterms_within_computations);
                simplify = (uu___145_9258.simplify);
                erase_universes = (uu___145_9258.erase_universes);
                allow_unbound_universes =
                  (uu___145_9258.allow_unbound_universes);
                reify_ = (uu___145_9258.reify_);
                compress_uvars = (uu___145_9258.compress_uvars);
                no_full_norm = (uu___145_9258.no_full_norm);
                check_no_uvars = (uu___145_9258.check_no_uvars);
                unmeta = (uu___145_9258.unmeta);
                unascribe = (uu___145_9258.unascribe)
              });
           tcenv = (uu___144_9255.tcenv);
           debug = (uu___144_9255.debug);
           delta_level = (uu___144_9255.delta_level);
           primitive_steps = equality_ops;
           strong = (uu___144_9255.strong);
           memoize_lazy = (uu___144_9255.memoize_lazy);
           normalize_pure_lets = (uu___144_9255.normalize_pure_lets)
         }) tm
  
let is_norm_request :
  'Auu____9262 .
    FStar_Syntax_Syntax.term -> 'Auu____9262 Prims.list -> Prims.bool
  =
  fun hd1  ->
    fun args  ->
      let uu____9275 =
        let uu____9282 =
          let uu____9283 = FStar_Syntax_Util.un_uinst hd1  in
          uu____9283.FStar_Syntax_Syntax.n  in
        (uu____9282, args)  in
      match uu____9275 with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____9289::uu____9290::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____9294::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize
      | (FStar_Syntax_Syntax.Tm_fvar fv,steps::uu____9299::uu____9300::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm
      | uu____9303 -> false
  
let (tr_norm_step : FStar_Syntax_Embeddings.norm_step -> step Prims.list) =
  fun uu___86_9314  ->
    match uu___86_9314 with
    | FStar_Syntax_Embeddings.Zeta  -> [Zeta]
    | FStar_Syntax_Embeddings.Iota  -> [Iota]
    | FStar_Syntax_Embeddings.Delta  ->
        [UnfoldUntil FStar_Syntax_Syntax.Delta_constant]
    | FStar_Syntax_Embeddings.Simpl  -> [Simplify]
    | FStar_Syntax_Embeddings.Weak  -> [Weak]
    | FStar_Syntax_Embeddings.HNF  -> [HNF]
    | FStar_Syntax_Embeddings.Primops  -> [Primops]
    | FStar_Syntax_Embeddings.UnfoldOnly names1 ->
        let uu____9320 =
          let uu____9323 =
            let uu____9324 = FStar_List.map FStar_Ident.lid_of_str names1  in
            UnfoldOnly uu____9324  in
          [uu____9323]  in
        (UnfoldUntil FStar_Syntax_Syntax.Delta_constant) :: uu____9320
    | FStar_Syntax_Embeddings.UnfoldAttr t ->
        [UnfoldUntil FStar_Syntax_Syntax.Delta_constant; UnfoldAttr t]
  
let (tr_norm_steps :
  FStar_Syntax_Embeddings.norm_step Prims.list -> step Prims.list) =
  fun s  -> FStar_List.concatMap tr_norm_step s 
let get_norm_request :
  'Auu____9340 .
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
      (FStar_Syntax_Syntax.term,'Auu____9340) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (step Prims.list,FStar_Syntax_Syntax.term)
          FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun full_norm  ->
    fun args  ->
      let parse_steps s =
        try
          let uu____9393 =
            let uu____9396 =
              let uu____9399 =
                let uu____9404 =
                  FStar_Syntax_Embeddings.unembed_list_safe
                    FStar_Syntax_Embeddings.unembed_norm_step
                   in
                uu____9404 s  in
              FStar_All.pipe_right uu____9399 FStar_Util.must  in
            FStar_All.pipe_right uu____9396 tr_norm_steps  in
          FStar_Pervasives_Native.Some uu____9393
        with | uu____9432 -> FStar_Pervasives_Native.None  in
      match args with
      | uu____9443::(tm,uu____9445)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify]  in
          FStar_Pervasives_Native.Some (s, tm)
      | (tm,uu____9474)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify]  in
          FStar_Pervasives_Native.Some (s, tm)
      | (steps,uu____9495)::uu____9496::(tm,uu____9498)::[] ->
          let add_exclude s z =
            if FStar_List.contains z s then s else (Exclude z) :: s  in
          let uu____9535 =
            let uu____9540 = full_norm steps  in parse_steps uu____9540  in
          (match uu____9535 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some s ->
               let s1 = Beta :: s  in
               let s2 = add_exclude s1 Zeta  in
               let s3 = add_exclude s2 Iota  in
               FStar_Pervasives_Native.Some (s3, tm))
      | uu____9579 -> FStar_Pervasives_Native.None
  
let (is_reify_head : stack_elt Prims.list -> Prims.bool) =
  fun uu___87_9596  ->
    match uu___87_9596 with
    | (App
        (uu____9599,{
                      FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                        (FStar_Const.Const_reify );
                      FStar_Syntax_Syntax.pos = uu____9600;
                      FStar_Syntax_Syntax.vars = uu____9601;_},uu____9602,uu____9603))::uu____9604
        -> true
    | uu____9611 -> false
  
let firstn :
  'Auu____9617 .
    Prims.int ->
      'Auu____9617 Prims.list ->
        ('Auu____9617 Prims.list,'Auu____9617 Prims.list)
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
          (uu____9653,{
                        FStar_Syntax_Syntax.n =
                          FStar_Syntax_Syntax.Tm_constant
                          (FStar_Const.Const_reify );
                        FStar_Syntax_Syntax.pos = uu____9654;
                        FStar_Syntax_Syntax.vars = uu____9655;_},uu____9656,uu____9657))::uu____9658
          -> (cfg.steps).reify_
      | uu____9665 -> false
  
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
               | FStar_Syntax_Syntax.Tm_delayed uu____9849 ->
                   let uu____9874 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print1 "NORM delayed: %s\n" uu____9874
               | uu____9875 -> ())
            else ();
            FStar_Syntax_Subst.compress t  in
          log cfg
            (fun uu____9883  ->
               let uu____9884 = FStar_Syntax_Print.tag_of_term t1  in
               let uu____9885 = FStar_Syntax_Print.term_to_string t1  in
               let uu____9886 =
                 FStar_Util.string_of_int (FStar_List.length env)  in
               let uu____9893 =
                 let uu____9894 =
                   let uu____9897 = firstn (Prims.parse_int "4") stack  in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst uu____9897
                    in
                 stack_to_string uu____9894  in
               FStar_Util.print4
                 ">>> %s\nNorm %s with with %s env elements top of the stack %s \n"
                 uu____9884 uu____9885 uu____9886 uu____9893);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_constant uu____9920 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_name uu____9921 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_lazy uu____9922 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____9923;
                 FStar_Syntax_Syntax.fv_delta =
                   FStar_Syntax_Syntax.Delta_constant ;
                 FStar_Syntax_Syntax.fv_qual = uu____9924;_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____9927;
                 FStar_Syntax_Syntax.fv_delta = uu____9928;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Data_ctor );_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____9929;
                 FStar_Syntax_Syntax.fv_delta = uu____9930;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor uu____9931);_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_quoted uu____9938 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               ((Prims.op_Negation (cfg.steps).no_full_norm) &&
                  (is_norm_request hd1 args))
                 &&
                 (let uu____9974 =
                    FStar_Ident.lid_equals
                      (cfg.tcenv).FStar_TypeChecker_Env.curmodule
                      FStar_Parser_Const.prims_lid
                     in
                  Prims.op_Negation uu____9974)
               ->
               let cfg' =
                 let uu___148_9976 = cfg  in
                 {
                   steps =
                     (let uu___149_9979 = cfg.steps  in
                      {
                        beta = (uu___149_9979.beta);
                        iota = (uu___149_9979.iota);
                        zeta = (uu___149_9979.zeta);
                        weak = (uu___149_9979.weak);
                        hnf = (uu___149_9979.hnf);
                        primops = (uu___149_9979.primops);
                        no_delta_steps = false;
                        unfold_until = (uu___149_9979.unfold_until);
                        unfold_only = FStar_Pervasives_Native.None;
                        unfold_attr = (uu___149_9979.unfold_attr);
                        unfold_tac = (uu___149_9979.unfold_tac);
                        pure_subterms_within_computations =
                          (uu___149_9979.pure_subterms_within_computations);
                        simplify = (uu___149_9979.simplify);
                        erase_universes = (uu___149_9979.erase_universes);
                        allow_unbound_universes =
                          (uu___149_9979.allow_unbound_universes);
                        reify_ = (uu___149_9979.reify_);
                        compress_uvars = (uu___149_9979.compress_uvars);
                        no_full_norm = (uu___149_9979.no_full_norm);
                        check_no_uvars = (uu___149_9979.check_no_uvars);
                        unmeta = (uu___149_9979.unmeta);
                        unascribe = (uu___149_9979.unascribe)
                      });
                   tcenv = (uu___148_9976.tcenv);
                   debug = (uu___148_9976.debug);
                   delta_level =
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.Delta_constant];
                   primitive_steps = (uu___148_9976.primitive_steps);
                   strong = (uu___148_9976.strong);
                   memoize_lazy = (uu___148_9976.memoize_lazy);
                   normalize_pure_lets = true
                 }  in
               let uu____9982 = get_norm_request (norm cfg' env []) args  in
               (match uu____9982 with
                | FStar_Pervasives_Native.None  ->
                    let stack1 =
                      FStar_All.pipe_right stack
                        (FStar_List.fold_right
                           (fun uu____10013  ->
                              fun stack1  ->
                                match uu____10013 with
                                | (a,aq) ->
                                    let uu____10025 =
                                      let uu____10026 =
                                        let uu____10033 =
                                          let uu____10034 =
                                            let uu____10065 =
                                              FStar_Util.mk_ref
                                                FStar_Pervasives_Native.None
                                               in
                                            (env, a, uu____10065, false)  in
                                          Clos uu____10034  in
                                        (uu____10033, aq,
                                          (t1.FStar_Syntax_Syntax.pos))
                                         in
                                      Arg uu____10026  in
                                    uu____10025 :: stack1) args)
                       in
                    (log cfg
                       (fun uu____10149  ->
                          let uu____10150 =
                            FStar_All.pipe_left FStar_Util.string_of_int
                              (FStar_List.length args)
                             in
                          FStar_Util.print1 "\tPushed %s arguments\n"
                            uu____10150);
                     norm cfg env stack1 hd1)
                | FStar_Pervasives_Native.Some (s,tm) ->
                    let delta_level =
                      let uu____10172 =
                        FStar_All.pipe_right s
                          (FStar_Util.for_some
                             (fun uu___88_10177  ->
                                match uu___88_10177 with
                                | UnfoldUntil uu____10178 -> true
                                | UnfoldOnly uu____10179 -> true
                                | uu____10182 -> false))
                         in
                      if uu____10172
                      then
                        [FStar_TypeChecker_Env.Unfold
                           FStar_Syntax_Syntax.Delta_constant]
                      else [FStar_TypeChecker_Env.NoDelta]  in
                    let cfg'1 =
                      let uu___150_10187 = cfg  in
                      let uu____10188 = to_fsteps s  in
                      {
                        steps = uu____10188;
                        tcenv = (uu___150_10187.tcenv);
                        debug = (uu___150_10187.debug);
                        delta_level;
                        primitive_steps = (uu___150_10187.primitive_steps);
                        strong = (uu___150_10187.strong);
                        memoize_lazy = (uu___150_10187.memoize_lazy);
                        normalize_pure_lets = true
                      }  in
                    let stack' =
                      let tail1 = (Cfg cfg) :: stack  in
                      if (cfg.debug).print_normalized
                      then
                        let uu____10197 =
                          let uu____10198 =
                            let uu____10203 = FStar_Util.now ()  in
                            (t1, uu____10203)  in
                          Debug uu____10198  in
                        uu____10197 :: tail1
                      else tail1  in
                    norm cfg'1 env stack' tm)
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u  in
               let uu____10207 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack uu____10207
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               if (cfg.steps).erase_universes
               then norm cfg env stack t'
               else
                 (let us1 =
                    let uu____10216 =
                      let uu____10223 =
                        FStar_List.map (norm_universe cfg env) us  in
                      (uu____10223, (t1.FStar_Syntax_Syntax.pos))  in
                    UnivArgs uu____10216  in
                  let stack1 = us1 :: stack  in norm cfg env stack1 t')
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let qninfo =
                 let uu____10233 = FStar_Syntax_Syntax.lid_of_fv fv  in
                 FStar_TypeChecker_Env.lookup_qname cfg.tcenv uu____10233  in
               let uu____10234 =
                 FStar_TypeChecker_Env.qninfo_is_action qninfo  in
               if uu____10234
               then
                 let b = should_reify cfg stack  in
                 (log cfg
                    (fun uu____10240  ->
                       let uu____10241 = FStar_Syntax_Print.term_to_string t1
                          in
                       let uu____10242 = FStar_Util.string_of_bool b  in
                       FStar_Util.print2
                         ">>> For DM4F action %s, should_reify = %s\n"
                         uu____10241 uu____10242);
                  if b
                  then
                    (let uu____10243 = FStar_List.tl stack  in
                     do_unfold_fv cfg env uu____10243 t1 qninfo fv)
                  else rebuild cfg env stack t1)
               else
                 (let should_delta =
                    (let uu____10251 = find_prim_step cfg fv  in
                     FStar_Option.isNone uu____10251) &&
                      (FStar_All.pipe_right cfg.delta_level
                         (FStar_Util.for_some
                            (fun uu___89_10257  ->
                               match uu___89_10257 with
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
                          (let uu____10267 =
                             cases
                               (FStar_Util.for_some
                                  (FStar_Syntax_Util.attr_eq
                                     FStar_Syntax_Util.tac_opaque_attr))
                               false attrs
                              in
                           Prims.op_Negation uu____10267))
                         &&
                         ((match (cfg.steps).unfold_only with
                           | FStar_Pervasives_Native.None  -> true
                           | FStar_Pervasives_Native.Some lids ->
                               FStar_Util.for_some
                                 (FStar_Syntax_Syntax.fv_eq_lid fv) lids)
                            ||
                            (match (attrs, ((cfg.steps).unfold_attr)) with
                             | (FStar_Pervasives_Native.None
                                ,FStar_Pervasives_Native.Some uu____10286) ->
                                 false
                             | (FStar_Pervasives_Native.Some
                                ats,FStar_Pervasives_Native.Some ats') ->
                                 FStar_Util.for_some
                                   (fun at  ->
                                      FStar_Util.for_some
                                        (FStar_Syntax_Util.attr_eq at) ats')
                                   ats
                             | (uu____10321,uu____10322) -> false)))
                     in
                  log cfg
                    (fun uu____10344  ->
                       let uu____10345 = FStar_Syntax_Print.term_to_string t1
                          in
                       let uu____10346 =
                         FStar_Range.string_of_range
                           t1.FStar_Syntax_Syntax.pos
                          in
                       let uu____10347 =
                         FStar_Util.string_of_bool should_delta1  in
                       FStar_Util.print3
                         ">>> For %s (%s), should_delta = %s\n" uu____10345
                         uu____10346 uu____10347);
                  if should_delta1
                  then do_unfold_fv cfg env stack t1 qninfo fv
                  else rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____10350 = lookup_bvar env x  in
               (match uu____10350 with
                | Univ uu____10353 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if (Prims.op_Negation fix) || (cfg.steps).zeta
                    then
                      let uu____10402 = FStar_ST.op_Bang r  in
                      (match uu____10402 with
                       | FStar_Pervasives_Native.Some (env2,t') ->
                           (log cfg
                              (fun uu____10520  ->
                                 let uu____10521 =
                                   FStar_Syntax_Print.term_to_string t1  in
                                 let uu____10522 =
                                   FStar_Syntax_Print.term_to_string t'  in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____10521
                                   uu____10522);
                            (let uu____10523 =
                               let uu____10524 =
                                 FStar_Syntax_Subst.compress t'  in
                               uu____10524.FStar_Syntax_Syntax.n  in
                             match uu____10523 with
                             | FStar_Syntax_Syntax.Tm_abs uu____10527 ->
                                 norm cfg env2 stack t'
                             | uu____10544 -> rebuild cfg env2 stack t'))
                       | FStar_Pervasives_Native.None  ->
                           norm cfg env1 ((MemoLazy r) :: stack) t0)
                    else norm cfg env1 stack t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack with
                | (UnivArgs uu____10614)::uu____10615 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Match uu____10624)::uu____10625 ->
                    failwith
                      "Ill-typed term: cannot pattern match an abstraction"
                | (Arg (c,uu____10637,uu____10638))::stack_rest ->
                    (match c with
                     | Univ uu____10642 ->
                         norm cfg ((FStar_Pervasives_Native.None, c) :: env)
                           stack_rest t1
                     | uu____10651 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | b::[] ->
                              (log cfg
                                 (fun uu____10672  ->
                                    let uu____10673 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____10673);
                               norm cfg
                                 (((FStar_Pervasives_Native.Some b), c) ::
                                 env) stack_rest body)
                          | b::tl1 ->
                              (log cfg
                                 (fun uu____10713  ->
                                    let uu____10714 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____10714);
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
                       (fun uu____10792  ->
                          let uu____10793 =
                            FStar_Syntax_Print.term_to_string t1  in
                          FStar_Util.print1 "\tSet memo %s\n" uu____10793);
                     norm cfg env stack1 t1)
                | (Debug uu____10794)::uu____10795 ->
                    if (cfg.steps).weak
                    then
                      let uu____10802 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____10802
                    else
                      (let uu____10804 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____10804 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____10846  -> dummy :: env1) env)
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
                                          let uu____10883 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____10883)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___151_10888 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___151_10888.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___151_10888.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____10889 -> lopt  in
                           (log cfg
                              (fun uu____10895  ->
                                 let uu____10896 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____10896);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___152_10905 = cfg  in
                               {
                                 steps = (uu___152_10905.steps);
                                 tcenv = (uu___152_10905.tcenv);
                                 debug = (uu___152_10905.debug);
                                 delta_level = (uu___152_10905.delta_level);
                                 primitive_steps =
                                   (uu___152_10905.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___152_10905.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___152_10905.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Meta uu____10916)::uu____10917 ->
                    if (cfg.steps).weak
                    then
                      let uu____10924 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____10924
                    else
                      (let uu____10926 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____10926 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____10968  -> dummy :: env1) env)
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
                                          let uu____11005 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____11005)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___151_11010 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___151_11010.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___151_11010.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11011 -> lopt  in
                           (log cfg
                              (fun uu____11017  ->
                                 let uu____11018 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11018);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___152_11027 = cfg  in
                               {
                                 steps = (uu___152_11027.steps);
                                 tcenv = (uu___152_11027.tcenv);
                                 debug = (uu___152_11027.debug);
                                 delta_level = (uu___152_11027.delta_level);
                                 primitive_steps =
                                   (uu___152_11027.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___152_11027.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___152_11027.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Let uu____11038)::uu____11039 ->
                    if (cfg.steps).weak
                    then
                      let uu____11050 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____11050
                    else
                      (let uu____11052 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____11052 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11094  -> dummy :: env1) env)
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
                                          let uu____11131 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____11131)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___151_11136 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___151_11136.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___151_11136.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11137 -> lopt  in
                           (log cfg
                              (fun uu____11143  ->
                                 let uu____11144 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11144);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___152_11153 = cfg  in
                               {
                                 steps = (uu___152_11153.steps);
                                 tcenv = (uu___152_11153.tcenv);
                                 debug = (uu___152_11153.debug);
                                 delta_level = (uu___152_11153.delta_level);
                                 primitive_steps =
                                   (uu___152_11153.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___152_11153.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___152_11153.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (App uu____11164)::uu____11165 ->
                    if (cfg.steps).weak
                    then
                      let uu____11176 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____11176
                    else
                      (let uu____11178 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____11178 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11220  -> dummy :: env1) env)
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
                                          let uu____11257 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____11257)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___151_11262 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___151_11262.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___151_11262.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11263 -> lopt  in
                           (log cfg
                              (fun uu____11269  ->
                                 let uu____11270 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11270);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___152_11279 = cfg  in
                               {
                                 steps = (uu___152_11279.steps);
                                 tcenv = (uu___152_11279.tcenv);
                                 debug = (uu___152_11279.debug);
                                 delta_level = (uu___152_11279.delta_level);
                                 primitive_steps =
                                   (uu___152_11279.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___152_11279.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___152_11279.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Abs uu____11290)::uu____11291 ->
                    if (cfg.steps).weak
                    then
                      let uu____11306 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____11306
                    else
                      (let uu____11308 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____11308 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11350  -> dummy :: env1) env)
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
                                          let uu____11387 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____11387)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___151_11392 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___151_11392.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___151_11392.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11393 -> lopt  in
                           (log cfg
                              (fun uu____11399  ->
                                 let uu____11400 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11400);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___152_11409 = cfg  in
                               {
                                 steps = (uu___152_11409.steps);
                                 tcenv = (uu___152_11409.tcenv);
                                 debug = (uu___152_11409.debug);
                                 delta_level = (uu___152_11409.delta_level);
                                 primitive_steps =
                                   (uu___152_11409.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___152_11409.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___152_11409.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | [] ->
                    if (cfg.steps).weak
                    then
                      let uu____11420 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____11420
                    else
                      (let uu____11422 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____11422 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11464  -> dummy :: env1) env)
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
                                          let uu____11501 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____11501)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___151_11506 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___151_11506.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___151_11506.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11507 -> lopt  in
                           (log cfg
                              (fun uu____11513  ->
                                 let uu____11514 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11514);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___152_11523 = cfg  in
                               {
                                 steps = (uu___152_11523.steps);
                                 tcenv = (uu___152_11523.tcenv);
                                 debug = (uu___152_11523.debug);
                                 delta_level = (uu___152_11523.delta_level);
                                 primitive_steps =
                                   (uu___152_11523.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___152_11523.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___152_11523.normalize_pure_lets)
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
                      (fun uu____11572  ->
                         fun stack1  ->
                           match uu____11572 with
                           | (a,aq) ->
                               let uu____11584 =
                                 let uu____11585 =
                                   let uu____11592 =
                                     let uu____11593 =
                                       let uu____11624 =
                                         FStar_Util.mk_ref
                                           FStar_Pervasives_Native.None
                                          in
                                       (env, a, uu____11624, false)  in
                                     Clos uu____11593  in
                                   (uu____11592, aq,
                                     (t1.FStar_Syntax_Syntax.pos))
                                    in
                                 Arg uu____11585  in
                               uu____11584 :: stack1) args)
                  in
               (log cfg
                  (fun uu____11708  ->
                     let uu____11709 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args)
                        in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____11709);
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
                             ((let uu___153_11745 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___153_11745.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___153_11745.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos
                         in
                      rebuild cfg env stack t2
                  | uu____11746 ->
                      let uu____11751 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____11751)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort  in
                  let uu____11754 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] f
                     in
                  match uu____11754 with
                  | (closing,f1) ->
                      let f2 = norm cfg (dummy :: env) [] f1  in
                      let t2 =
                        let uu____11785 =
                          let uu____11786 =
                            let uu____11793 =
                              FStar_Syntax_Subst.close closing f2  in
                            ((let uu___154_11795 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___154_11795.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___154_11795.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____11793)
                             in
                          FStar_Syntax_Syntax.Tm_refine uu____11786  in
                        mk uu____11785 t1.FStar_Syntax_Syntax.pos  in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if (cfg.steps).weak
               then
                 let uu____11814 = closure_as_term cfg env t1  in
                 rebuild cfg env stack uu____11814
               else
                 (let uu____11816 = FStar_Syntax_Subst.open_comp bs c  in
                  match uu____11816 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____11824 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun uu____11848  -> dummy :: env1) env)
                           in
                        norm_comp cfg uu____11824 c1  in
                      let t2 =
                        let uu____11870 = norm_binders cfg env bs1  in
                        FStar_Syntax_Util.arrow uu____11870 c2  in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) when
               (cfg.steps).unascribe -> norm cfg env stack t11
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack with
                | (Match uu____11981)::uu____11982 ->
                    (log cfg
                       (fun uu____11995  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (Arg uu____11996)::uu____11997 ->
                    (log cfg
                       (fun uu____12008  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (App
                    (uu____12009,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_constant
                                     (FStar_Const.Const_reify );
                                   FStar_Syntax_Syntax.pos = uu____12010;
                                   FStar_Syntax_Syntax.vars = uu____12011;_},uu____12012,uu____12013))::uu____12014
                    ->
                    (log cfg
                       (fun uu____12023  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (MemoLazy uu____12024)::uu____12025 ->
                    (log cfg
                       (fun uu____12036  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | uu____12037 ->
                    (log cfg
                       (fun uu____12040  ->
                          FStar_Util.print_string "+++ Keeping ascription \n");
                     (let t12 = norm cfg env [] t11  in
                      log cfg
                        (fun uu____12044  ->
                           FStar_Util.print_string
                             "+++ Normalizing ascription \n");
                      (let tc1 =
                         match tc with
                         | FStar_Util.Inl t2 ->
                             let uu____12061 = norm cfg env [] t2  in
                             FStar_Util.Inl uu____12061
                         | FStar_Util.Inr c ->
                             let uu____12069 = norm_comp cfg env c  in
                             FStar_Util.Inr uu____12069
                          in
                       let tacopt1 =
                         FStar_Util.map_opt tacopt (norm cfg env [])  in
                       match stack with
                       | (Cfg cfg1)::stack1 ->
                           let t2 =
                             let uu____12082 =
                               let uu____12083 =
                                 let uu____12110 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____12110, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____12083
                                in
                             mk uu____12082 t1.FStar_Syntax_Syntax.pos  in
                           norm cfg1 env stack1 t2
                       | uu____12129 ->
                           let uu____12130 =
                             let uu____12131 =
                               let uu____12132 =
                                 let uu____12159 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____12159, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____12132
                                in
                             mk uu____12131 t1.FStar_Syntax_Syntax.pos  in
                           rebuild cfg env stack uu____12130))))
           | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
               let stack1 =
                 (Match (env, branches, cfg, (t1.FStar_Syntax_Syntax.pos)))
                 :: stack  in
               let cfg1 =
                 let uu___155_12236 = cfg  in
                 {
                   steps =
                     (let uu___156_12239 = cfg.steps  in
                      {
                        beta = (uu___156_12239.beta);
                        iota = (uu___156_12239.iota);
                        zeta = (uu___156_12239.zeta);
                        weak = true;
                        hnf = true;
                        primops = (uu___156_12239.primops);
                        no_delta_steps = (uu___156_12239.no_delta_steps);
                        unfold_until = (uu___156_12239.unfold_until);
                        unfold_only = (uu___156_12239.unfold_only);
                        unfold_attr = (uu___156_12239.unfold_attr);
                        unfold_tac = (uu___156_12239.unfold_tac);
                        pure_subterms_within_computations =
                          (uu___156_12239.pure_subterms_within_computations);
                        simplify = (uu___156_12239.simplify);
                        erase_universes = (uu___156_12239.erase_universes);
                        allow_unbound_universes =
                          (uu___156_12239.allow_unbound_universes);
                        reify_ = (uu___156_12239.reify_);
                        compress_uvars = (uu___156_12239.compress_uvars);
                        no_full_norm = (uu___156_12239.no_full_norm);
                        check_no_uvars = (uu___156_12239.check_no_uvars);
                        unmeta = (uu___156_12239.unmeta);
                        unascribe = (uu___156_12239.unascribe)
                      });
                   tcenv = (uu___155_12236.tcenv);
                   debug = (uu___155_12236.debug);
                   delta_level = (uu___155_12236.delta_level);
                   primitive_steps = (uu___155_12236.primitive_steps);
                   strong = (uu___155_12236.strong);
                   memoize_lazy = (uu___155_12236.memoize_lazy);
                   normalize_pure_lets = (uu___155_12236.normalize_pure_lets)
                 }  in
               norm cfg1 env stack1 head1
           | FStar_Syntax_Syntax.Tm_let ((b,lbs),lbody) when
               (FStar_Syntax_Syntax.is_top_level lbs) &&
                 (cfg.steps).compress_uvars
               ->
               let lbs1 =
                 FStar_All.pipe_right lbs
                   (FStar_List.map
                      (fun lb  ->
                         let uu____12274 =
                           FStar_Syntax_Subst.univ_var_opening
                             lb.FStar_Syntax_Syntax.lbunivs
                            in
                         match uu____12274 with
                         | (openings,lbunivs) ->
                             let cfg1 =
                               let uu___157_12294 = cfg  in
                               let uu____12295 =
                                 FStar_TypeChecker_Env.push_univ_vars
                                   cfg.tcenv lbunivs
                                  in
                               {
                                 steps = (uu___157_12294.steps);
                                 tcenv = uu____12295;
                                 debug = (uu___157_12294.debug);
                                 delta_level = (uu___157_12294.delta_level);
                                 primitive_steps =
                                   (uu___157_12294.primitive_steps);
                                 strong = (uu___157_12294.strong);
                                 memoize_lazy = (uu___157_12294.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___157_12294.normalize_pure_lets)
                               }  in
                             let norm1 t2 =
                               let uu____12300 =
                                 let uu____12301 =
                                   FStar_Syntax_Subst.subst openings t2  in
                                 norm cfg1 env [] uu____12301  in
                               FStar_Syntax_Subst.close_univ_vars lbunivs
                                 uu____12300
                                in
                             let lbtyp = norm1 lb.FStar_Syntax_Syntax.lbtyp
                                in
                             let lbdef = norm1 lb.FStar_Syntax_Syntax.lbdef
                                in
                             let uu___158_12304 = lb  in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___158_12304.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs = lbunivs;
                               FStar_Syntax_Syntax.lbtyp = lbtyp;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___158_12304.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = lbdef;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___158_12304.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___158_12304.FStar_Syntax_Syntax.lbpos)
                             }))
                  in
               let uu____12305 =
                 mk (FStar_Syntax_Syntax.Tm_let ((b, lbs1), lbody))
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack uu____12305
           | FStar_Syntax_Syntax.Tm_let
               ((uu____12316,{
                               FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                 uu____12317;
                               FStar_Syntax_Syntax.lbunivs = uu____12318;
                               FStar_Syntax_Syntax.lbtyp = uu____12319;
                               FStar_Syntax_Syntax.lbeff = uu____12320;
                               FStar_Syntax_Syntax.lbdef = uu____12321;
                               FStar_Syntax_Syntax.lbattrs = uu____12322;
                               FStar_Syntax_Syntax.lbpos = uu____12323;_}::uu____12324),uu____12325)
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff
                  in
               let uu____12365 =
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
               if uu____12365
               then
                 let binder =
                   let uu____12367 =
                     FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                   FStar_Syntax_Syntax.mk_binder uu____12367  in
                 let env1 =
                   let uu____12377 =
                     let uu____12384 =
                       let uu____12385 =
                         let uu____12416 =
                           FStar_Util.mk_ref FStar_Pervasives_Native.None  in
                         (env, (lb.FStar_Syntax_Syntax.lbdef), uu____12416,
                           false)
                          in
                       Clos uu____12385  in
                     ((FStar_Pervasives_Native.Some binder), uu____12384)  in
                   uu____12377 :: env  in
                 (log cfg
                    (fun uu____12509  ->
                       FStar_Util.print_string "+++ Reducing Tm_let\n");
                  norm cfg env1 stack body)
               else
                 if (cfg.steps).weak
                 then
                   (log cfg
                      (fun uu____12513  ->
                         FStar_Util.print_string "+++ Not touching Tm_let\n");
                    (let uu____12514 = closure_as_term cfg env t1  in
                     rebuild cfg env stack uu____12514))
                 else
                   (let uu____12516 =
                      let uu____12521 =
                        let uu____12522 =
                          let uu____12523 =
                            FStar_All.pipe_right
                              lb.FStar_Syntax_Syntax.lbname FStar_Util.left
                             in
                          FStar_All.pipe_right uu____12523
                            FStar_Syntax_Syntax.mk_binder
                           in
                        [uu____12522]  in
                      FStar_Syntax_Subst.open_term uu____12521 body  in
                    match uu____12516 with
                    | (bs,body1) ->
                        (log cfg
                           (fun uu____12532  ->
                              FStar_Util.print_string
                                "+++ Normalizing Tm_let -- type");
                         (let ty =
                            norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                          let lbname =
                            let x =
                              let uu____12540 = FStar_List.hd bs  in
                              FStar_Pervasives_Native.fst uu____12540  in
                            FStar_Util.Inl
                              (let uu___159_12550 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___159_12550.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___159_12550.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               })
                             in
                          log cfg
                            (fun uu____12553  ->
                               FStar_Util.print_string
                                 "+++ Normalizing Tm_let -- definiens\n");
                          (let lb1 =
                             let uu___160_12555 = lb  in
                             let uu____12556 =
                               norm cfg env [] lb.FStar_Syntax_Syntax.lbdef
                                in
                             {
                               FStar_Syntax_Syntax.lbname = lbname;
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___160_12555.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp = ty;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___160_12555.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = uu____12556;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___160_12555.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___160_12555.FStar_Syntax_Syntax.lbpos)
                             }  in
                           let env' =
                             FStar_All.pipe_right bs
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12591  -> dummy :: env1) env)
                              in
                           let stack1 = (Cfg cfg) :: stack  in
                           let cfg1 =
                             let uu___161_12614 = cfg  in
                             {
                               steps = (uu___161_12614.steps);
                               tcenv = (uu___161_12614.tcenv);
                               debug = (uu___161_12614.debug);
                               delta_level = (uu___161_12614.delta_level);
                               primitive_steps =
                                 (uu___161_12614.primitive_steps);
                               strong = true;
                               memoize_lazy = (uu___161_12614.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___161_12614.normalize_pure_lets)
                             }  in
                           log cfg1
                             (fun uu____12617  ->
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
               let uu____12634 = FStar_Syntax_Subst.open_let_rec lbs body  in
               (match uu____12634 with
                | (lbs1,body1) ->
                    let lbs2 =
                      FStar_List.map
                        (fun lb  ->
                           let ty =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                           let lbname =
                             let uu____12670 =
                               let uu___162_12671 =
                                 FStar_Util.left
                                   lb.FStar_Syntax_Syntax.lbname
                                  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___162_12671.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___162_12671.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               }  in
                             FStar_Util.Inl uu____12670  in
                           let uu____12672 =
                             FStar_Syntax_Util.abs_formals
                               lb.FStar_Syntax_Syntax.lbdef
                              in
                           match uu____12672 with
                           | (xs,def_body,lopt) ->
                               let xs1 = norm_binders cfg env xs  in
                               let env1 =
                                 let uu____12698 =
                                   FStar_List.map (fun uu____12714  -> dummy)
                                     lbs1
                                    in
                                 let uu____12715 =
                                   let uu____12724 =
                                     FStar_List.map
                                       (fun uu____12744  -> dummy) xs1
                                      in
                                   FStar_List.append uu____12724 env  in
                                 FStar_List.append uu____12698 uu____12715
                                  in
                               let def_body1 = norm cfg env1 [] def_body  in
                               let lopt1 =
                                 match lopt with
                                 | FStar_Pervasives_Native.Some rc ->
                                     let uu____12768 =
                                       let uu___163_12769 = rc  in
                                       let uu____12770 =
                                         FStar_Util.map_opt
                                           rc.FStar_Syntax_Syntax.residual_typ
                                           (norm cfg env1 [])
                                          in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___163_12769.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           uu____12770;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___163_12769.FStar_Syntax_Syntax.residual_flags)
                                       }  in
                                     FStar_Pervasives_Native.Some uu____12768
                                 | uu____12777 -> lopt  in
                               let def =
                                 FStar_Syntax_Util.abs xs1 def_body1 lopt1
                                  in
                               let uu___164_12781 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname = lbname;
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___164_12781.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp = ty;
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___164_12781.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___164_12781.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___164_12781.FStar_Syntax_Syntax.lbpos)
                               }) lbs1
                       in
                    let env' =
                      let uu____12791 =
                        FStar_List.map (fun uu____12807  -> dummy) lbs2  in
                      FStar_List.append uu____12791 env  in
                    let body2 = norm cfg env' [] body1  in
                    let uu____12815 =
                      FStar_Syntax_Subst.close_let_rec lbs2 body2  in
                    (match uu____12815 with
                     | (lbs3,body3) ->
                         let t2 =
                           let uu___165_12831 = t1  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_let
                                  ((true, lbs3), body3));
                             FStar_Syntax_Syntax.pos =
                               (uu___165_12831.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___165_12831.FStar_Syntax_Syntax.vars)
                           }  in
                         rebuild cfg env stack t2))
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               Prims.op_Negation (cfg.steps).zeta ->
               let uu____12858 = closure_as_term cfg env t1  in
               rebuild cfg env stack uu____12858
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____12877 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____12953  ->
                        match uu____12953 with
                        | (rec_env,memos,i) ->
                            let bv =
                              let uu___166_13074 =
                                FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                                 in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___166_13074.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index = i;
                                FStar_Syntax_Syntax.sort =
                                  (uu___166_13074.FStar_Syntax_Syntax.sort)
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
               (match uu____12877 with
                | (rec_env,memos,uu____13287) ->
                    let uu____13340 =
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
                             let uu____13651 =
                               let uu____13658 =
                                 let uu____13659 =
                                   let uu____13690 =
                                     FStar_Util.mk_ref
                                       FStar_Pervasives_Native.None
                                      in
                                   (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                     uu____13690, false)
                                    in
                                 Clos uu____13659  in
                               (FStar_Pervasives_Native.None, uu____13658)
                                in
                             uu____13651 :: env1)
                        (FStar_Pervasives_Native.snd lbs) env
                       in
                    norm cfg body_env stack body)
           | FStar_Syntax_Syntax.Tm_meta (head1,m) ->
               (log cfg
                  (fun uu____13800  ->
                     let uu____13801 =
                       FStar_Syntax_Print.metadata_to_string m  in
                     FStar_Util.print1 ">> metadata = %s\n" uu____13801);
                (match m with
                 | FStar_Syntax_Syntax.Meta_monadic (m1,t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inl m1) t2
                 | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inr (m1, m')) t2
                 | uu____13823 ->
                     if (cfg.steps).unmeta
                     then norm cfg env stack head1
                     else
                       (match stack with
                        | uu____13825::uu____13826 ->
                            (match m with
                             | FStar_Syntax_Syntax.Meta_labeled
                                 (l,r,uu____13831) ->
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
                             | uu____13854 -> norm cfg env stack head1)
                        | [] ->
                            let head2 = norm cfg env [] head1  in
                            let m1 =
                              match m with
                              | FStar_Syntax_Syntax.Meta_pattern args ->
                                  let uu____13868 =
                                    norm_pattern_args cfg env args  in
                                  FStar_Syntax_Syntax.Meta_pattern
                                    uu____13868
                              | uu____13879 -> m  in
                            let t2 =
                              mk (FStar_Syntax_Syntax.Tm_meta (head2, m1))
                                t1.FStar_Syntax_Syntax.pos
                               in
                            rebuild cfg env stack t2)))
           | FStar_Syntax_Syntax.Tm_delayed uu____13883 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               norm cfg env stack t2
           | FStar_Syntax_Syntax.Tm_uvar uu____13909 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               (match t2.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_uvar uu____13927 ->
                    if (cfg.steps).check_no_uvars
                    then
                      let uu____13944 =
                        let uu____13945 =
                          FStar_Range.string_of_range
                            t2.FStar_Syntax_Syntax.pos
                           in
                        let uu____13946 =
                          FStar_Syntax_Print.term_to_string t2  in
                        FStar_Util.format2
                          "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                          uu____13945 uu____13946
                         in
                      failwith uu____13944
                    else rebuild cfg env stack t2
                | uu____13948 -> norm cfg env stack t2))

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
                let uu____13958 = FStar_Syntax_Syntax.range_of_fv f  in
                FStar_TypeChecker_Env.set_range cfg.tcenv uu____13958  in
              let uu____13959 =
                FStar_TypeChecker_Env.lookup_definition_qninfo
                  cfg.delta_level
                  (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                  qninfo
                 in
              match uu____13959 with
              | FStar_Pervasives_Native.None  ->
                  (log cfg
                     (fun uu____13972  ->
                        FStar_Util.print "Tm_fvar case 2\n" []);
                   rebuild cfg env stack t0)
              | FStar_Pervasives_Native.Some (us,t) ->
                  (log cfg
                     (fun uu____13983  ->
                        let uu____13984 =
                          FStar_Syntax_Print.term_to_string t0  in
                        let uu____13985 = FStar_Syntax_Print.term_to_string t
                           in
                        FStar_Util.print2 ">>> Unfolded %s to %s\n"
                          uu____13984 uu____13985);
                   (let t1 =
                      if
                        ((cfg.steps).unfold_until =
                           (FStar_Pervasives_Native.Some
                              FStar_Syntax_Syntax.Delta_constant))
                          && (Prims.op_Negation (cfg.steps).unfold_tac)
                      then t
                      else
                        (let uu____13990 =
                           FStar_Ident.range_of_lid
                             (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                            in
                         FStar_Syntax_Subst.set_use_range uu____13990 t)
                       in
                    let n1 = FStar_List.length us  in
                    if n1 > (Prims.parse_int "0")
                    then
                      match stack with
                      | (UnivArgs (us',uu____13999))::stack1 ->
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
                      | uu____14054 when
                          (cfg.steps).erase_universes ||
                            (cfg.steps).allow_unbound_universes
                          -> norm cfg env stack t1
                      | uu____14057 ->
                          let uu____14060 =
                            let uu____14061 =
                              FStar_Syntax_Print.lid_to_string
                                (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                               in
                            FStar_Util.format1
                              "Impossible: missing universe instantiation on %s"
                              uu____14061
                             in
                          failwith uu____14060
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
                  let uu___167_14085 = cfg  in
                  let uu____14086 =
                    FStar_List.fold_right fstep_add_one new_steps cfg.steps
                     in
                  {
                    steps = uu____14086;
                    tcenv = (uu___167_14085.tcenv);
                    debug = (uu___167_14085.debug);
                    delta_level =
                      [FStar_TypeChecker_Env.Inlining;
                      FStar_TypeChecker_Env.Eager_unfolding_only];
                    primitive_steps = (uu___167_14085.primitive_steps);
                    strong = (uu___167_14085.strong);
                    memoize_lazy = (uu___167_14085.memoize_lazy);
                    normalize_pure_lets =
                      (uu___167_14085.normalize_pure_lets)
                  }
                else
                  (let uu___168_14088 = cfg  in
                   {
                     steps =
                       (let uu___169_14091 = cfg.steps  in
                        {
                          beta = (uu___169_14091.beta);
                          iota = (uu___169_14091.iota);
                          zeta = false;
                          weak = (uu___169_14091.weak);
                          hnf = (uu___169_14091.hnf);
                          primops = (uu___169_14091.primops);
                          no_delta_steps = (uu___169_14091.no_delta_steps);
                          unfold_until = (uu___169_14091.unfold_until);
                          unfold_only = (uu___169_14091.unfold_only);
                          unfold_attr = (uu___169_14091.unfold_attr);
                          unfold_tac = (uu___169_14091.unfold_tac);
                          pure_subterms_within_computations =
                            (uu___169_14091.pure_subterms_within_computations);
                          simplify = (uu___169_14091.simplify);
                          erase_universes = (uu___169_14091.erase_universes);
                          allow_unbound_universes =
                            (uu___169_14091.allow_unbound_universes);
                          reify_ = (uu___169_14091.reify_);
                          compress_uvars = (uu___169_14091.compress_uvars);
                          no_full_norm = (uu___169_14091.no_full_norm);
                          check_no_uvars = (uu___169_14091.check_no_uvars);
                          unmeta = (uu___169_14091.unmeta);
                          unascribe = (uu___169_14091.unascribe)
                        });
                     tcenv = (uu___168_14088.tcenv);
                     debug = (uu___168_14088.debug);
                     delta_level = (uu___168_14088.delta_level);
                     primitive_steps = (uu___168_14088.primitive_steps);
                     strong = (uu___168_14088.strong);
                     memoize_lazy = (uu___168_14088.memoize_lazy);
                     normalize_pure_lets =
                       (uu___168_14088.normalize_pure_lets)
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
                  (fun uu____14121  ->
                     let uu____14122 = FStar_Syntax_Print.tag_of_term head2
                        in
                     let uu____14123 =
                       FStar_Syntax_Print.term_to_string head2  in
                     FStar_Util.print2 "Reifying: (%s) %s\n" uu____14122
                       uu____14123);
                (let head3 = FStar_Syntax_Util.unmeta_safe head2  in
                 let uu____14125 =
                   let uu____14126 = FStar_Syntax_Subst.compress head3  in
                   uu____14126.FStar_Syntax_Syntax.n  in
                 match uu____14125 with
                 | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                     let ed =
                       let uu____14144 =
                         FStar_TypeChecker_Env.norm_eff_name cfg.tcenv m  in
                       FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                         uu____14144
                        in
                     let uu____14145 = ed.FStar_Syntax_Syntax.bind_repr  in
                     (match uu____14145 with
                      | (uu____14146,bind_repr) ->
                          (match lb.FStar_Syntax_Syntax.lbname with
                           | FStar_Util.Inr uu____14152 ->
                               failwith
                                 "Cannot reify a top-level let binding"
                           | FStar_Util.Inl x ->
                               let is_return e =
                                 let uu____14160 =
                                   let uu____14161 =
                                     FStar_Syntax_Subst.compress e  in
                                   uu____14161.FStar_Syntax_Syntax.n  in
                                 match uu____14160 with
                                 | FStar_Syntax_Syntax.Tm_meta
                                     (e1,FStar_Syntax_Syntax.Meta_monadic
                                      (uu____14167,uu____14168))
                                     ->
                                     let uu____14177 =
                                       let uu____14178 =
                                         FStar_Syntax_Subst.compress e1  in
                                       uu____14178.FStar_Syntax_Syntax.n  in
                                     (match uu____14177 with
                                      | FStar_Syntax_Syntax.Tm_meta
                                          (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                           (uu____14184,msrc,uu____14186))
                                          when
                                          FStar_Syntax_Util.is_pure_effect
                                            msrc
                                          ->
                                          let uu____14195 =
                                            FStar_Syntax_Subst.compress e2
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____14195
                                      | uu____14196 ->
                                          FStar_Pervasives_Native.None)
                                 | uu____14197 ->
                                     FStar_Pervasives_Native.None
                                  in
                               let uu____14198 =
                                 is_return lb.FStar_Syntax_Syntax.lbdef  in
                               (match uu____14198 with
                                | FStar_Pervasives_Native.Some e ->
                                    let lb1 =
                                      let uu___170_14203 = lb  in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          (uu___170_14203.FStar_Syntax_Syntax.lbname);
                                        FStar_Syntax_Syntax.lbunivs =
                                          (uu___170_14203.FStar_Syntax_Syntax.lbunivs);
                                        FStar_Syntax_Syntax.lbtyp =
                                          (uu___170_14203.FStar_Syntax_Syntax.lbtyp);
                                        FStar_Syntax_Syntax.lbeff =
                                          FStar_Parser_Const.effect_PURE_lid;
                                        FStar_Syntax_Syntax.lbdef = e;
                                        FStar_Syntax_Syntax.lbattrs =
                                          (uu___170_14203.FStar_Syntax_Syntax.lbattrs);
                                        FStar_Syntax_Syntax.lbpos =
                                          (uu___170_14203.FStar_Syntax_Syntax.lbpos)
                                      }  in
                                    let uu____14204 = FStar_List.tl stack  in
                                    let uu____14205 =
                                      let uu____14206 =
                                        let uu____14209 =
                                          let uu____14210 =
                                            let uu____14223 =
                                              FStar_Syntax_Util.mk_reify body
                                               in
                                            ((false, [lb1]), uu____14223)  in
                                          FStar_Syntax_Syntax.Tm_let
                                            uu____14210
                                           in
                                        FStar_Syntax_Syntax.mk uu____14209
                                         in
                                      uu____14206
                                        FStar_Pervasives_Native.None
                                        head3.FStar_Syntax_Syntax.pos
                                       in
                                    norm cfg env uu____14204 uu____14205
                                | FStar_Pervasives_Native.None  ->
                                    let uu____14239 =
                                      let uu____14240 = is_return body  in
                                      match uu____14240 with
                                      | FStar_Pervasives_Native.Some
                                          {
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_bvar y;
                                            FStar_Syntax_Syntax.pos =
                                              uu____14244;
                                            FStar_Syntax_Syntax.vars =
                                              uu____14245;_}
                                          -> FStar_Syntax_Syntax.bv_eq x y
                                      | uu____14250 -> false  in
                                    if uu____14239
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
                                         let uu____14273 =
                                           let uu____14276 =
                                             let uu____14277 =
                                               let uu____14294 =
                                                 let uu____14297 =
                                                   FStar_Syntax_Syntax.mk_binder
                                                     x
                                                    in
                                                 [uu____14297]  in
                                               (uu____14294, body1,
                                                 (FStar_Pervasives_Native.Some
                                                    body_rc))
                                                in
                                             FStar_Syntax_Syntax.Tm_abs
                                               uu____14277
                                              in
                                           FStar_Syntax_Syntax.mk uu____14276
                                            in
                                         uu____14273
                                           FStar_Pervasives_Native.None
                                           body1.FStar_Syntax_Syntax.pos
                                          in
                                       let close1 = closure_as_term cfg env
                                          in
                                       let bind_inst =
                                         let uu____14313 =
                                           let uu____14314 =
                                             FStar_Syntax_Subst.compress
                                               bind_repr
                                              in
                                           uu____14314.FStar_Syntax_Syntax.n
                                            in
                                         match uu____14313 with
                                         | FStar_Syntax_Syntax.Tm_uinst
                                             (bind1,uu____14320::uu____14321::[])
                                             ->
                                             let uu____14328 =
                                               let uu____14331 =
                                                 let uu____14332 =
                                                   let uu____14339 =
                                                     let uu____14342 =
                                                       let uu____14343 =
                                                         close1
                                                           lb.FStar_Syntax_Syntax.lbtyp
                                                          in
                                                       (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                         cfg.tcenv
                                                         uu____14343
                                                        in
                                                     let uu____14344 =
                                                       let uu____14347 =
                                                         let uu____14348 =
                                                           close1 t  in
                                                         (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                           cfg.tcenv
                                                           uu____14348
                                                          in
                                                       [uu____14347]  in
                                                     uu____14342 ::
                                                       uu____14344
                                                      in
                                                   (bind1, uu____14339)  in
                                                 FStar_Syntax_Syntax.Tm_uinst
                                                   uu____14332
                                                  in
                                               FStar_Syntax_Syntax.mk
                                                 uu____14331
                                                in
                                             uu____14328
                                               FStar_Pervasives_Native.None
                                               rng
                                         | uu____14356 ->
                                             failwith
                                               "NIY : Reification of indexed effects"
                                          in
                                       let maybe_range_arg =
                                         let uu____14362 =
                                           FStar_Util.for_some
                                             (FStar_Syntax_Util.attr_eq
                                                FStar_Syntax_Util.dm4f_bind_range_attr)
                                             ed.FStar_Syntax_Syntax.eff_attrs
                                            in
                                         if uu____14362
                                         then
                                           let uu____14365 =
                                             let uu____14366 =
                                               FStar_Syntax_Embeddings.embed_range
                                                 lb.FStar_Syntax_Syntax.lbpos
                                                 lb.FStar_Syntax_Syntax.lbpos
                                                in
                                             FStar_Syntax_Syntax.as_arg
                                               uu____14366
                                              in
                                           let uu____14367 =
                                             let uu____14370 =
                                               let uu____14371 =
                                                 FStar_Syntax_Embeddings.embed_range
                                                   body2.FStar_Syntax_Syntax.pos
                                                   body2.FStar_Syntax_Syntax.pos
                                                  in
                                               FStar_Syntax_Syntax.as_arg
                                                 uu____14371
                                                in
                                             [uu____14370]  in
                                           uu____14365 :: uu____14367
                                         else []  in
                                       let reified =
                                         let uu____14376 =
                                           let uu____14379 =
                                             let uu____14380 =
                                               let uu____14395 =
                                                 let uu____14398 =
                                                   let uu____14401 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       lb.FStar_Syntax_Syntax.lbtyp
                                                      in
                                                   let uu____14402 =
                                                     let uu____14405 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         t
                                                        in
                                                     [uu____14405]  in
                                                   uu____14401 :: uu____14402
                                                    in
                                                 let uu____14406 =
                                                   let uu____14409 =
                                                     let uu____14412 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         FStar_Syntax_Syntax.tun
                                                        in
                                                     let uu____14413 =
                                                       let uu____14416 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           head4
                                                          in
                                                       let uu____14417 =
                                                         let uu____14420 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             FStar_Syntax_Syntax.tun
                                                            in
                                                         let uu____14421 =
                                                           let uu____14424 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               body2
                                                              in
                                                           [uu____14424]  in
                                                         uu____14420 ::
                                                           uu____14421
                                                          in
                                                       uu____14416 ::
                                                         uu____14417
                                                        in
                                                     uu____14412 ::
                                                       uu____14413
                                                      in
                                                   FStar_List.append
                                                     maybe_range_arg
                                                     uu____14409
                                                    in
                                                 FStar_List.append
                                                   uu____14398 uu____14406
                                                  in
                                               (bind_inst, uu____14395)  in
                                             FStar_Syntax_Syntax.Tm_app
                                               uu____14380
                                              in
                                           FStar_Syntax_Syntax.mk uu____14379
                                            in
                                         uu____14376
                                           FStar_Pervasives_Native.None rng
                                          in
                                       log cfg
                                         (fun uu____14436  ->
                                            let uu____14437 =
                                              FStar_Syntax_Print.term_to_string
                                                head0
                                               in
                                            let uu____14438 =
                                              FStar_Syntax_Print.term_to_string
                                                reified
                                               in
                                            FStar_Util.print2
                                              "Reified (1) <%s> to %s\n"
                                              uu____14437 uu____14438);
                                       (let uu____14439 = FStar_List.tl stack
                                           in
                                        norm cfg env uu____14439 reified)))))
                 | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                     let ed =
                       let uu____14463 =
                         FStar_TypeChecker_Env.norm_eff_name cfg.tcenv m  in
                       FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                         uu____14463
                        in
                     let uu____14464 = ed.FStar_Syntax_Syntax.bind_repr  in
                     (match uu____14464 with
                      | (uu____14465,bind_repr) ->
                          let maybe_unfold_action head4 =
                            let maybe_extract_fv t1 =
                              let t2 =
                                let uu____14500 =
                                  let uu____14501 =
                                    FStar_Syntax_Subst.compress t1  in
                                  uu____14501.FStar_Syntax_Syntax.n  in
                                match uu____14500 with
                                | FStar_Syntax_Syntax.Tm_uinst
                                    (t2,uu____14507) -> t2
                                | uu____14512 -> head4  in
                              let uu____14513 =
                                let uu____14514 =
                                  FStar_Syntax_Subst.compress t2  in
                                uu____14514.FStar_Syntax_Syntax.n  in
                              match uu____14513 with
                              | FStar_Syntax_Syntax.Tm_fvar x ->
                                  FStar_Pervasives_Native.Some x
                              | uu____14520 -> FStar_Pervasives_Native.None
                               in
                            let uu____14521 = maybe_extract_fv head4  in
                            match uu____14521 with
                            | FStar_Pervasives_Native.Some x when
                                let uu____14531 =
                                  FStar_Syntax_Syntax.lid_of_fv x  in
                                FStar_TypeChecker_Env.is_action cfg.tcenv
                                  uu____14531
                                ->
                                let head5 = norm cfg env [] head4  in
                                let action_unfolded =
                                  let uu____14536 = maybe_extract_fv head5
                                     in
                                  match uu____14536 with
                                  | FStar_Pervasives_Native.Some uu____14541
                                      -> FStar_Pervasives_Native.Some true
                                  | uu____14542 ->
                                      FStar_Pervasives_Native.Some false
                                   in
                                (head5, action_unfolded)
                            | uu____14547 ->
                                (head4, FStar_Pervasives_Native.None)
                             in
                          ((let is_arg_impure uu____14562 =
                              match uu____14562 with
                              | (e,q) ->
                                  let uu____14569 =
                                    let uu____14570 =
                                      FStar_Syntax_Subst.compress e  in
                                    uu____14570.FStar_Syntax_Syntax.n  in
                                  (match uu____14569 with
                                   | FStar_Syntax_Syntax.Tm_meta
                                       (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                        (m1,m2,t'))
                                       ->
                                       let uu____14585 =
                                         FStar_Syntax_Util.is_pure_effect m1
                                          in
                                       Prims.op_Negation uu____14585
                                   | uu____14586 -> false)
                               in
                            let uu____14587 =
                              let uu____14588 =
                                let uu____14595 =
                                  FStar_Syntax_Syntax.as_arg head_app  in
                                uu____14595 :: args  in
                              FStar_Util.for_some is_arg_impure uu____14588
                               in
                            if uu____14587
                            then
                              let uu____14600 =
                                let uu____14601 =
                                  FStar_Syntax_Print.term_to_string head3  in
                                FStar_Util.format1
                                  "Incompability between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                  uu____14601
                                 in
                              failwith uu____14600
                            else ());
                           (let uu____14603 = maybe_unfold_action head_app
                               in
                            match uu____14603 with
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
                                   (fun uu____14644  ->
                                      let uu____14645 =
                                        FStar_Syntax_Print.term_to_string
                                          head0
                                         in
                                      let uu____14646 =
                                        FStar_Syntax_Print.term_to_string
                                          body1
                                         in
                                      FStar_Util.print2
                                        "Reified (2) <%s> to %s\n"
                                        uu____14645 uu____14646);
                                 (let uu____14647 = FStar_List.tl stack  in
                                  norm cfg env uu____14647 body1)))))
                 | FStar_Syntax_Syntax.Tm_meta
                     (e,FStar_Syntax_Syntax.Meta_monadic uu____14649) ->
                     do_reify_monadic fallback cfg env stack e m t
                 | FStar_Syntax_Syntax.Tm_meta
                     (e,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,t'))
                     ->
                     let lifted =
                       let uu____14673 = closure_as_term cfg env t'  in
                       reify_lift cfg e msrc mtgt uu____14673  in
                     (log cfg
                        (fun uu____14677  ->
                           let uu____14678 =
                             FStar_Syntax_Print.term_to_string lifted  in
                           FStar_Util.print1 "Reified lift to (2): %s\n"
                             uu____14678);
                      (let uu____14679 = FStar_List.tl stack  in
                       norm cfg env uu____14679 lifted))
                 | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                     let branches1 =
                       FStar_All.pipe_right branches
                         (FStar_List.map
                            (fun uu____14800  ->
                               match uu____14800 with
                               | (pat,wopt,tm) ->
                                   let uu____14848 =
                                     FStar_Syntax_Util.mk_reify tm  in
                                   (pat, wopt, uu____14848)))
                        in
                     let tm =
                       mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                         head3.FStar_Syntax_Syntax.pos
                        in
                     let uu____14880 = FStar_List.tl stack  in
                     norm cfg env uu____14880 tm
                 | uu____14881 -> fallback ())

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
              (fun uu____14895  ->
                 let uu____14896 = FStar_Ident.string_of_lid msrc  in
                 let uu____14897 = FStar_Ident.string_of_lid mtgt  in
                 let uu____14898 = FStar_Syntax_Print.term_to_string e  in
                 FStar_Util.print3 "Reifying lift %s -> %s: %s\n" uu____14896
                   uu____14897 uu____14898);
            (let uu____14899 =
               (FStar_Syntax_Util.is_pure_effect msrc) ||
                 (FStar_Syntax_Util.is_div_effect msrc)
                in
             if uu____14899
             then
               let ed =
                 let uu____14901 =
                   FStar_TypeChecker_Env.norm_eff_name cfg.tcenv mtgt  in
                 FStar_TypeChecker_Env.get_effect_decl env uu____14901  in
               let uu____14902 = ed.FStar_Syntax_Syntax.return_repr  in
               match uu____14902 with
               | (uu____14903,return_repr) ->
                   let return_inst =
                     let uu____14912 =
                       let uu____14913 =
                         FStar_Syntax_Subst.compress return_repr  in
                       uu____14913.FStar_Syntax_Syntax.n  in
                     match uu____14912 with
                     | FStar_Syntax_Syntax.Tm_uinst
                         (return_tm,uu____14919::[]) ->
                         let uu____14926 =
                           let uu____14929 =
                             let uu____14930 =
                               let uu____14937 =
                                 let uu____14940 =
                                   env.FStar_TypeChecker_Env.universe_of env
                                     t
                                    in
                                 [uu____14940]  in
                               (return_tm, uu____14937)  in
                             FStar_Syntax_Syntax.Tm_uinst uu____14930  in
                           FStar_Syntax_Syntax.mk uu____14929  in
                         uu____14926 FStar_Pervasives_Native.None
                           e.FStar_Syntax_Syntax.pos
                     | uu____14948 ->
                         failwith "NIY : Reification of indexed effects"
                      in
                   let uu____14951 =
                     let uu____14954 =
                       let uu____14955 =
                         let uu____14970 =
                           let uu____14973 = FStar_Syntax_Syntax.as_arg t  in
                           let uu____14974 =
                             let uu____14977 = FStar_Syntax_Syntax.as_arg e
                                in
                             [uu____14977]  in
                           uu____14973 :: uu____14974  in
                         (return_inst, uu____14970)  in
                       FStar_Syntax_Syntax.Tm_app uu____14955  in
                     FStar_Syntax_Syntax.mk uu____14954  in
                   uu____14951 FStar_Pervasives_Native.None
                     e.FStar_Syntax_Syntax.pos
             else
               (let uu____14986 =
                  FStar_TypeChecker_Env.monad_leq env msrc mtgt  in
                match uu____14986 with
                | FStar_Pervasives_Native.None  ->
                    let uu____14989 =
                      let uu____14990 = FStar_Ident.text_of_lid msrc  in
                      let uu____14991 = FStar_Ident.text_of_lid mtgt  in
                      FStar_Util.format2
                        "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                        uu____14990 uu____14991
                       in
                    failwith uu____14989
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____14992;
                      FStar_TypeChecker_Env.mtarget = uu____14993;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____14994;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.None ;_};_}
                    ->
                    let uu____15009 =
                      let uu____15010 = FStar_Ident.text_of_lid msrc  in
                      let uu____15011 = FStar_Ident.text_of_lid mtgt  in
                      FStar_Util.format2
                        "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
                        uu____15010 uu____15011
                       in
                    failwith uu____15009
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____15012;
                      FStar_TypeChecker_Env.mtarget = uu____15013;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____15014;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.Some lift;_};_}
                    ->
                    let uu____15038 =
                      env.FStar_TypeChecker_Env.universe_of env t  in
                    let uu____15039 = FStar_Syntax_Util.mk_reify e  in
                    lift uu____15038 t FStar_Syntax_Syntax.tun uu____15039))

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
                (fun uu____15095  ->
                   match uu____15095 with
                   | (a,imp) ->
                       let uu____15106 = norm cfg env [] a  in
                       (uu____15106, imp))))

and (norm_comp :
  cfg -> env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp) =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        match comp.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total (t,uopt) ->
            let uu___171_15120 = comp  in
            let uu____15121 =
              let uu____15122 =
                let uu____15131 = norm cfg env [] t  in
                let uu____15132 =
                  FStar_Option.map (norm_universe cfg env) uopt  in
                (uu____15131, uu____15132)  in
              FStar_Syntax_Syntax.Total uu____15122  in
            {
              FStar_Syntax_Syntax.n = uu____15121;
              FStar_Syntax_Syntax.pos =
                (uu___171_15120.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___171_15120.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
            let uu___172_15147 = comp  in
            let uu____15148 =
              let uu____15149 =
                let uu____15158 = norm cfg env [] t  in
                let uu____15159 =
                  FStar_Option.map (norm_universe cfg env) uopt  in
                (uu____15158, uu____15159)  in
              FStar_Syntax_Syntax.GTotal uu____15149  in
            {
              FStar_Syntax_Syntax.n = uu____15148;
              FStar_Syntax_Syntax.pos =
                (uu___172_15147.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___172_15147.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let norm_args args =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____15211  ->
                      match uu____15211 with
                      | (a,i) ->
                          let uu____15222 = norm cfg env [] a  in
                          (uu____15222, i)))
               in
            let flags1 =
              FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                (FStar_List.map
                   (fun uu___90_15233  ->
                      match uu___90_15233 with
                      | FStar_Syntax_Syntax.DECREASES t ->
                          let uu____15237 = norm cfg env [] t  in
                          FStar_Syntax_Syntax.DECREASES uu____15237
                      | f -> f))
               in
            let uu___173_15241 = comp  in
            let uu____15242 =
              let uu____15243 =
                let uu___174_15244 = ct  in
                let uu____15245 =
                  FStar_List.map (norm_universe cfg env)
                    ct.FStar_Syntax_Syntax.comp_univs
                   in
                let uu____15246 =
                  norm cfg env [] ct.FStar_Syntax_Syntax.result_typ  in
                let uu____15249 =
                  norm_args ct.FStar_Syntax_Syntax.effect_args  in
                {
                  FStar_Syntax_Syntax.comp_univs = uu____15245;
                  FStar_Syntax_Syntax.effect_name =
                    (uu___174_15244.FStar_Syntax_Syntax.effect_name);
                  FStar_Syntax_Syntax.result_typ = uu____15246;
                  FStar_Syntax_Syntax.effect_args = uu____15249;
                  FStar_Syntax_Syntax.flags = flags1
                }  in
              FStar_Syntax_Syntax.Comp uu____15243  in
            {
              FStar_Syntax_Syntax.n = uu____15242;
              FStar_Syntax_Syntax.pos =
                (uu___173_15241.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___173_15241.FStar_Syntax_Syntax.vars)
            }

and (norm_binder :
  cfg -> env -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder) =
  fun cfg  ->
    fun env  ->
      fun uu____15260  ->
        match uu____15260 with
        | (x,imp) ->
            let uu____15263 =
              let uu___175_15264 = x  in
              let uu____15265 = norm cfg env [] x.FStar_Syntax_Syntax.sort
                 in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___175_15264.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___175_15264.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____15265
              }  in
            (uu____15263, imp)

and (norm_binders :
  cfg -> env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders) =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____15271 =
          FStar_List.fold_left
            (fun uu____15289  ->
               fun b  ->
                 match uu____15289 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b  in
                     ((b1 :: nbs'), (dummy :: env1))) ([], env) bs
           in
        match uu____15271 with | (nbs,uu____15329) -> FStar_List.rev nbs

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
            let uu____15345 =
              let uu___176_15346 = rc  in
              let uu____15347 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (norm cfg env [])
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___176_15346.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____15347;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___176_15346.FStar_Syntax_Syntax.residual_flags)
              }  in
            FStar_Pervasives_Native.Some uu____15345
        | uu____15354 -> lopt

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
            (let uu____15375 = FStar_Syntax_Print.term_to_string tm  in
             let uu____15376 = FStar_Syntax_Print.term_to_string tm'  in
             FStar_Util.print3 "%sSimplified\n\t%s to\n\t%s\n"
               (if (cfg.steps).simplify then "" else "NOT ") uu____15375
               uu____15376)
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
          let uu____15396 =
            FStar_All.pipe_left Prims.op_Negation (cfg.steps).simplify  in
          if uu____15396
          then tm1
          else
            (let w t =
               let uu___177_15408 = t  in
               {
                 FStar_Syntax_Syntax.n =
                   (uu___177_15408.FStar_Syntax_Syntax.n);
                 FStar_Syntax_Syntax.pos = (tm1.FStar_Syntax_Syntax.pos);
                 FStar_Syntax_Syntax.vars =
                   (uu___177_15408.FStar_Syntax_Syntax.vars)
               }  in
             let simp_t t =
               let uu____15417 =
                 let uu____15418 = FStar_Syntax_Util.unmeta t  in
                 uu____15418.FStar_Syntax_Syntax.n  in
               match uu____15417 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_Pervasives_Native.Some true
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.false_lid
                   -> FStar_Pervasives_Native.Some false
               | uu____15425 -> FStar_Pervasives_Native.None  in
             let rec args_are_binders args bs =
               match (args, bs) with
               | ((t,uu____15470)::args1,(bv,uu____15473)::bs1) ->
                   let uu____15507 =
                     let uu____15508 = FStar_Syntax_Subst.compress t  in
                     uu____15508.FStar_Syntax_Syntax.n  in
                   (match uu____15507 with
                    | FStar_Syntax_Syntax.Tm_name bv' ->
                        (FStar_Syntax_Syntax.bv_eq bv bv') &&
                          (args_are_binders args1 bs1)
                    | uu____15512 -> false)
               | ([],[]) -> true
               | (uu____15533,uu____15534) -> false  in
             let is_applied bs t =
               let uu____15570 = FStar_Syntax_Util.head_and_args' t  in
               match uu____15570 with
               | (hd1,args) ->
                   let uu____15603 =
                     let uu____15604 = FStar_Syntax_Subst.compress hd1  in
                     uu____15604.FStar_Syntax_Syntax.n  in
                   (match uu____15603 with
                    | FStar_Syntax_Syntax.Tm_name bv when
                        args_are_binders args bs ->
                        FStar_Pervasives_Native.Some bv
                    | uu____15610 -> FStar_Pervasives_Native.None)
                in
             let is_applied_maybe_squashed bs t =
               let uu____15622 = FStar_Syntax_Util.is_squash t  in
               match uu____15622 with
               | FStar_Pervasives_Native.Some (uu____15633,t') ->
                   is_applied bs t'
               | uu____15645 ->
                   let uu____15654 = FStar_Syntax_Util.is_auto_squash t  in
                   (match uu____15654 with
                    | FStar_Pervasives_Native.Some (uu____15665,t') ->
                        is_applied bs t'
                    | uu____15677 -> is_applied bs t)
                in
             let is_quantified_const phi =
               let uu____15694 =
                 FStar_Syntax_Util.destruct_typ_as_formula phi  in
               match uu____15694 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
                   (lid,(p,uu____15701)::(q,uu____15703)::[])) when
                   FStar_Ident.lid_equals lid FStar_Parser_Const.imp_lid ->
                   let uu____15738 =
                     FStar_Syntax_Util.destruct_typ_as_formula p  in
                   (match uu____15738 with
                    | FStar_Pervasives_Native.None  ->
                        let uu____15743 =
                          let uu____15744 = FStar_Syntax_Subst.compress p  in
                          uu____15744.FStar_Syntax_Syntax.n  in
                        (match uu____15743 with
                         | FStar_Syntax_Syntax.Tm_bvar bv ->
                             let uu____15750 =
                               FStar_Syntax_Subst.subst
                                 [FStar_Syntax_Syntax.NT
                                    (bv, FStar_Syntax_Util.t_true)] q
                                in
                             FStar_Pervasives_Native.Some uu____15750
                         | uu____15751 -> FStar_Pervasives_Native.None)
                    | FStar_Pervasives_Native.Some
                        (FStar_Syntax_Util.BaseConn
                        (lid1,(p1,uu____15754)::[])) when
                        FStar_Ident.lid_equals lid1
                          FStar_Parser_Const.not_lid
                        ->
                        let uu____15779 =
                          let uu____15780 = FStar_Syntax_Subst.compress p1
                             in
                          uu____15780.FStar_Syntax_Syntax.n  in
                        (match uu____15779 with
                         | FStar_Syntax_Syntax.Tm_bvar bv ->
                             let uu____15786 =
                               FStar_Syntax_Subst.subst
                                 [FStar_Syntax_Syntax.NT
                                    (bv, FStar_Syntax_Util.t_false)] q
                                in
                             FStar_Pervasives_Native.Some uu____15786
                         | uu____15787 -> FStar_Pervasives_Native.None)
                    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
                        (bs,pats,phi1)) ->
                        let uu____15791 =
                          FStar_Syntax_Util.destruct_typ_as_formula phi1  in
                        (match uu____15791 with
                         | FStar_Pervasives_Native.None  ->
                             let uu____15796 =
                               is_applied_maybe_squashed bs phi1  in
                             (match uu____15796 with
                              | FStar_Pervasives_Native.Some bv ->
                                  let ftrue =
                                    FStar_Syntax_Util.abs bs
                                      FStar_Syntax_Util.t_true
                                      (FStar_Pervasives_Native.Some
                                         (FStar_Syntax_Util.residual_tot
                                            FStar_Syntax_Util.ktype0))
                                     in
                                  let uu____15803 =
                                    FStar_Syntax_Subst.subst
                                      [FStar_Syntax_Syntax.NT (bv, ftrue)] q
                                     in
                                  FStar_Pervasives_Native.Some uu____15803
                              | FStar_Pervasives_Native.None  ->
                                  FStar_Pervasives_Native.None)
                         | FStar_Pervasives_Native.Some
                             (FStar_Syntax_Util.BaseConn
                             (lid1,(p1,uu____15806)::[])) when
                             FStar_Ident.lid_equals lid1
                               FStar_Parser_Const.not_lid
                             ->
                             let uu____15831 =
                               is_applied_maybe_squashed bs p1  in
                             (match uu____15831 with
                              | FStar_Pervasives_Native.Some bv ->
                                  let ffalse =
                                    FStar_Syntax_Util.abs bs
                                      FStar_Syntax_Util.t_false
                                      (FStar_Pervasives_Native.Some
                                         (FStar_Syntax_Util.residual_tot
                                            FStar_Syntax_Util.ktype0))
                                     in
                                  let uu____15838 =
                                    FStar_Syntax_Subst.subst
                                      [FStar_Syntax_Syntax.NT (bv, ffalse)] q
                                     in
                                  FStar_Pervasives_Native.Some uu____15838
                              | uu____15839 -> FStar_Pervasives_Native.None)
                         | uu____15842 -> FStar_Pervasives_Native.None)
                    | uu____15845 -> FStar_Pervasives_Native.None)
               | uu____15848 -> FStar_Pervasives_Native.None  in
             let is_const_match phi =
               let uu____15859 =
                 let uu____15860 = FStar_Syntax_Subst.compress phi  in
                 uu____15860.FStar_Syntax_Syntax.n  in
               match uu____15859 with
               | FStar_Syntax_Syntax.Tm_match (uu____15865,br::brs) ->
                   let uu____15932 = br  in
                   (match uu____15932 with
                    | (uu____15949,uu____15950,e) ->
                        let r =
                          let uu____15971 = simp_t e  in
                          match uu____15971 with
                          | FStar_Pervasives_Native.None  ->
                              FStar_Pervasives_Native.None
                          | FStar_Pervasives_Native.Some b ->
                              let uu____15977 =
                                FStar_List.for_all
                                  (fun uu____15995  ->
                                     match uu____15995 with
                                     | (uu____16008,uu____16009,e') ->
                                         let uu____16023 = simp_t e'  in
                                         uu____16023 =
                                           (FStar_Pervasives_Native.Some b))
                                  brs
                                 in
                              if uu____15977
                              then FStar_Pervasives_Native.Some b
                              else FStar_Pervasives_Native.None
                           in
                        r)
               | uu____16031 -> FStar_Pervasives_Native.None  in
             let maybe_auto_squash t =
               let uu____16036 = FStar_Syntax_Util.is_sub_singleton t  in
               if uu____16036
               then t
               else
                 FStar_Syntax_Util.mk_auto_squash FStar_Syntax_Syntax.U_zero
                   t
                in
             let squashed_head_un_auto_squash_args t =
               let maybe_un_auto_squash_arg uu____16057 =
                 match uu____16057 with
                 | (t1,q) ->
                     let uu____16070 = FStar_Syntax_Util.is_auto_squash t1
                        in
                     (match uu____16070 with
                      | FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.U_zero ,t2) -> (t2, q)
                      | uu____16098 -> (t1, q))
                  in
               let uu____16107 = FStar_Syntax_Util.head_and_args t  in
               match uu____16107 with
               | (head1,args) ->
                   let args1 = FStar_List.map maybe_un_auto_squash_arg args
                      in
                   FStar_Syntax_Syntax.mk_Tm_app head1 args1
                     FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
                in
             let rec clearly_inhabited ty =
               let uu____16169 =
                 let uu____16170 = FStar_Syntax_Util.unmeta ty  in
                 uu____16170.FStar_Syntax_Syntax.n  in
               match uu____16169 with
               | FStar_Syntax_Syntax.Tm_uinst (t,uu____16174) ->
                   clearly_inhabited t
               | FStar_Syntax_Syntax.Tm_arrow (uu____16179,c) ->
                   clearly_inhabited (FStar_Syntax_Util.comp_result c)
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   let l = FStar_Syntax_Syntax.lid_of_fv fv  in
                   (((FStar_Ident.lid_equals l FStar_Parser_Const.int_lid) ||
                       (FStar_Ident.lid_equals l FStar_Parser_Const.bool_lid))
                      ||
                      (FStar_Ident.lid_equals l FStar_Parser_Const.string_lid))
                     || (FStar_Ident.lid_equals l FStar_Parser_Const.exn_lid)
               | uu____16199 -> false  in
             let simplify1 arg =
               let uu____16222 = simp_t (FStar_Pervasives_Native.fst arg)  in
               (uu____16222, arg)  in
             let uu____16231 = is_quantified_const tm1  in
             match uu____16231 with
             | FStar_Pervasives_Native.Some tm2 ->
                 let uu____16235 = norm cfg env [] tm2  in
                 maybe_simplify_aux cfg env stack uu____16235
             | FStar_Pervasives_Native.None  ->
                 let uu____16236 =
                   let uu____16237 = FStar_Syntax_Subst.compress tm1  in
                   uu____16237.FStar_Syntax_Syntax.n  in
                 (match uu____16236 with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                           ({
                              FStar_Syntax_Syntax.n =
                                FStar_Syntax_Syntax.Tm_fvar fv;
                              FStar_Syntax_Syntax.pos = uu____16241;
                              FStar_Syntax_Syntax.vars = uu____16242;_},uu____16243);
                         FStar_Syntax_Syntax.pos = uu____16244;
                         FStar_Syntax_Syntax.vars = uu____16245;_},args)
                      ->
                      let uu____16271 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid
                         in
                      if uu____16271
                      then
                        let uu____16272 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        (match uu____16272 with
                         | (FStar_Pervasives_Native.Some (true ),uu____16319)::
                             (uu____16320,(arg,uu____16322))::[] ->
                             maybe_auto_squash arg
                         | (uu____16371,(arg,uu____16373))::(FStar_Pervasives_Native.Some
                                                             (true
                                                             ),uu____16374)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____16423)::uu____16424::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____16475::(FStar_Pervasives_Native.Some (false
                                         ),uu____16476)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____16527 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____16541 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid
                            in
                         if uu____16541
                         then
                           let uu____16542 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify1)
                              in
                           match uu____16542 with
                           | (FStar_Pervasives_Native.Some (true
                              ),uu____16589)::uu____16590::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____16641::(FStar_Pervasives_Native.Some (true
                                           ),uu____16642)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false
                              ),uu____16693)::(uu____16694,(arg,uu____16696))::[]
                               -> maybe_auto_squash arg
                           | (uu____16745,(arg,uu____16747))::(FStar_Pervasives_Native.Some
                                                               (false
                                                               ),uu____16748)::[]
                               -> maybe_auto_squash arg
                           | uu____16797 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____16811 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid
                               in
                            if uu____16811
                            then
                              let uu____16812 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify1)
                                 in
                              match uu____16812 with
                              | uu____16859::(FStar_Pervasives_Native.Some
                                              (true ),uu____16860)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false
                                 ),uu____16911)::uu____16912::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true
                                 ),uu____16963)::(uu____16964,(arg,uu____16966))::[]
                                  -> maybe_auto_squash arg
                              | (uu____17015,(p,uu____17017))::(uu____17018,
                                                                (q,uu____17020))::[]
                                  ->
                                  let uu____17067 =
                                    FStar_Syntax_Util.term_eq p q  in
                                  (if uu____17067
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____17069 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____17083 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid
                                  in
                               if uu____17083
                               then
                                 let uu____17084 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify1)
                                    in
                                 match uu____17084 with
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____17131)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____17132)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____17183)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____17184)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____17235)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____17236)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____17287)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____17288)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____17339,(arg,uu____17341))::(FStar_Pervasives_Native.Some
                                                                    (true
                                                                    ),uu____17342)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____17391)::(uu____17392,(arg,uu____17394))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____17443,(arg,uu____17445))::(FStar_Pervasives_Native.Some
                                                                    (false
                                                                    ),uu____17446)::[]
                                     ->
                                     let uu____17495 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____17495
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____17496)::(uu____17497,(arg,uu____17499))::[]
                                     ->
                                     let uu____17548 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____17548
                                 | (uu____17549,(p,uu____17551))::(uu____17552,
                                                                   (q,uu____17554))::[]
                                     ->
                                     let uu____17601 =
                                       FStar_Syntax_Util.term_eq p q  in
                                     (if uu____17601
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____17603 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____17617 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid
                                     in
                                  if uu____17617
                                  then
                                    let uu____17618 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify1)
                                       in
                                    match uu____17618 with
                                    | (FStar_Pervasives_Native.Some (true
                                       ),uu____17665)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false
                                       ),uu____17696)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____17727 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____17741 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid
                                        in
                                     if uu____17741
                                     then
                                       match args with
                                       | (t,uu____17743)::[] ->
                                           let uu____17760 =
                                             let uu____17761 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____17761.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____17760 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____17764::[],body,uu____17766)
                                                ->
                                                let uu____17793 = simp_t body
                                                   in
                                                (match uu____17793 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____17796 -> tm1)
                                            | uu____17799 -> tm1)
                                       | (ty,FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____17801))::(t,uu____17803)::[]
                                           ->
                                           let uu____17842 =
                                             let uu____17843 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____17843.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____17842 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____17846::[],body,uu____17848)
                                                ->
                                                let uu____17875 = simp_t body
                                                   in
                                                (match uu____17875 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false ) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____17878 -> tm1)
                                            | uu____17881 -> tm1)
                                       | uu____17882 -> tm1
                                     else
                                       (let uu____17892 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid
                                           in
                                        if uu____17892
                                        then
                                          match args with
                                          | (t,uu____17894)::[] ->
                                              let uu____17911 =
                                                let uu____17912 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____17912.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____17911 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____17915::[],body,uu____17917)
                                                   ->
                                                   let uu____17944 =
                                                     simp_t body  in
                                                   (match uu____17944 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____17947 -> tm1)
                                               | uu____17950 -> tm1)
                                          | (ty,FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____17952))::(t,uu____17954)::[]
                                              ->
                                              let uu____17993 =
                                                let uu____17994 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____17994.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____17993 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____17997::[],body,uu____17999)
                                                   ->
                                                   let uu____18026 =
                                                     simp_t body  in
                                                   (match uu____18026 with
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
                                                    | uu____18029 -> tm1)
                                               | uu____18032 -> tm1)
                                          | uu____18033 -> tm1
                                        else
                                          (let uu____18043 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid
                                              in
                                           if uu____18043
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____18044;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____18045;_},uu____18046)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____18063;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____18064;_},uu____18065)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____18082 -> tm1
                                           else
                                             (let uu____18092 =
                                                FStar_Syntax_Util.is_auto_squash
                                                  tm1
                                                 in
                                              match uu____18092 with
                                              | FStar_Pervasives_Native.Some
                                                  (FStar_Syntax_Syntax.U_zero
                                                   ,t)
                                                  when
                                                  FStar_Syntax_Util.is_sub_singleton
                                                    t
                                                  -> t
                                              | uu____18112 ->
                                                  reduce_equality cfg env
                                                    stack tm1))))))))
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____18122;
                         FStar_Syntax_Syntax.vars = uu____18123;_},args)
                      ->
                      let uu____18145 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid
                         in
                      if uu____18145
                      then
                        let uu____18146 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        (match uu____18146 with
                         | (FStar_Pervasives_Native.Some (true ),uu____18193)::
                             (uu____18194,(arg,uu____18196))::[] ->
                             maybe_auto_squash arg
                         | (uu____18245,(arg,uu____18247))::(FStar_Pervasives_Native.Some
                                                             (true
                                                             ),uu____18248)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____18297)::uu____18298::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____18349::(FStar_Pervasives_Native.Some (false
                                         ),uu____18350)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____18401 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____18415 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid
                            in
                         if uu____18415
                         then
                           let uu____18416 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify1)
                              in
                           match uu____18416 with
                           | (FStar_Pervasives_Native.Some (true
                              ),uu____18463)::uu____18464::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____18515::(FStar_Pervasives_Native.Some (true
                                           ),uu____18516)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false
                              ),uu____18567)::(uu____18568,(arg,uu____18570))::[]
                               -> maybe_auto_squash arg
                           | (uu____18619,(arg,uu____18621))::(FStar_Pervasives_Native.Some
                                                               (false
                                                               ),uu____18622)::[]
                               -> maybe_auto_squash arg
                           | uu____18671 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____18685 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid
                               in
                            if uu____18685
                            then
                              let uu____18686 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify1)
                                 in
                              match uu____18686 with
                              | uu____18733::(FStar_Pervasives_Native.Some
                                              (true ),uu____18734)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false
                                 ),uu____18785)::uu____18786::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true
                                 ),uu____18837)::(uu____18838,(arg,uu____18840))::[]
                                  -> maybe_auto_squash arg
                              | (uu____18889,(p,uu____18891))::(uu____18892,
                                                                (q,uu____18894))::[]
                                  ->
                                  let uu____18941 =
                                    FStar_Syntax_Util.term_eq p q  in
                                  (if uu____18941
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____18943 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____18957 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid
                                  in
                               if uu____18957
                               then
                                 let uu____18958 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify1)
                                    in
                                 match uu____18958 with
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____19005)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____19006)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____19057)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____19058)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____19109)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____19110)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____19161)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____19162)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____19213,(arg,uu____19215))::(FStar_Pervasives_Native.Some
                                                                    (true
                                                                    ),uu____19216)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____19265)::(uu____19266,(arg,uu____19268))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____19317,(arg,uu____19319))::(FStar_Pervasives_Native.Some
                                                                    (false
                                                                    ),uu____19320)::[]
                                     ->
                                     let uu____19369 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____19369
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____19370)::(uu____19371,(arg,uu____19373))::[]
                                     ->
                                     let uu____19422 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____19422
                                 | (uu____19423,(p,uu____19425))::(uu____19426,
                                                                   (q,uu____19428))::[]
                                     ->
                                     let uu____19475 =
                                       FStar_Syntax_Util.term_eq p q  in
                                     (if uu____19475
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____19477 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____19491 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid
                                     in
                                  if uu____19491
                                  then
                                    let uu____19492 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify1)
                                       in
                                    match uu____19492 with
                                    | (FStar_Pervasives_Native.Some (true
                                       ),uu____19539)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false
                                       ),uu____19570)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____19601 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____19615 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid
                                        in
                                     if uu____19615
                                     then
                                       match args with
                                       | (t,uu____19617)::[] ->
                                           let uu____19634 =
                                             let uu____19635 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____19635.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____19634 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____19638::[],body,uu____19640)
                                                ->
                                                let uu____19667 = simp_t body
                                                   in
                                                (match uu____19667 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____19670 -> tm1)
                                            | uu____19673 -> tm1)
                                       | (ty,FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____19675))::(t,uu____19677)::[]
                                           ->
                                           let uu____19716 =
                                             let uu____19717 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____19717.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____19716 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____19720::[],body,uu____19722)
                                                ->
                                                let uu____19749 = simp_t body
                                                   in
                                                (match uu____19749 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false ) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____19752 -> tm1)
                                            | uu____19755 -> tm1)
                                       | uu____19756 -> tm1
                                     else
                                       (let uu____19766 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid
                                           in
                                        if uu____19766
                                        then
                                          match args with
                                          | (t,uu____19768)::[] ->
                                              let uu____19785 =
                                                let uu____19786 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____19786.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____19785 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____19789::[],body,uu____19791)
                                                   ->
                                                   let uu____19818 =
                                                     simp_t body  in
                                                   (match uu____19818 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____19821 -> tm1)
                                               | uu____19824 -> tm1)
                                          | (ty,FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____19826))::(t,uu____19828)::[]
                                              ->
                                              let uu____19867 =
                                                let uu____19868 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____19868.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____19867 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____19871::[],body,uu____19873)
                                                   ->
                                                   let uu____19900 =
                                                     simp_t body  in
                                                   (match uu____19900 with
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
                                                    | uu____19903 -> tm1)
                                               | uu____19906 -> tm1)
                                          | uu____19907 -> tm1
                                        else
                                          (let uu____19917 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid
                                              in
                                           if uu____19917
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____19918;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____19919;_},uu____19920)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____19937;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____19938;_},uu____19939)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____19956 -> tm1
                                           else
                                             (let uu____19966 =
                                                FStar_Syntax_Util.is_auto_squash
                                                  tm1
                                                 in
                                              match uu____19966 with
                                              | FStar_Pervasives_Native.Some
                                                  (FStar_Syntax_Syntax.U_zero
                                                   ,t)
                                                  when
                                                  FStar_Syntax_Util.is_sub_singleton
                                                    t
                                                  -> t
                                              | uu____19986 ->
                                                  reduce_equality cfg env
                                                    stack tm1))))))))
                  | FStar_Syntax_Syntax.Tm_refine (bv,t) ->
                      let uu____20001 = simp_t t  in
                      (match uu____20001 with
                       | FStar_Pervasives_Native.Some (true ) ->
                           bv.FStar_Syntax_Syntax.sort
                       | FStar_Pervasives_Native.Some (false ) -> tm1
                       | FStar_Pervasives_Native.None  -> tm1)
                  | FStar_Syntax_Syntax.Tm_match uu____20004 ->
                      let uu____20027 = is_const_match tm1  in
                      (match uu____20027 with
                       | FStar_Pervasives_Native.Some (true ) ->
                           w FStar_Syntax_Util.t_true
                       | FStar_Pervasives_Native.Some (false ) ->
                           w FStar_Syntax_Util.t_false
                       | FStar_Pervasives_Native.None  -> tm1)
                  | uu____20030 -> tm1))

and (rebuild :
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          log cfg
            (fun uu____20041  ->
               let uu____20042 = FStar_Syntax_Print.tag_of_term t  in
               let uu____20043 = FStar_Syntax_Print.term_to_string t  in
               let uu____20044 =
                 FStar_Util.string_of_int (FStar_List.length env)  in
               let uu____20051 =
                 let uu____20052 =
                   let uu____20055 = firstn (Prims.parse_int "4") stack  in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____20055
                    in
                 stack_to_string uu____20052  in
               FStar_Util.print4
                 ">>> %s\nRebuild %s with %s env elements and top of the stack %s \n"
                 uu____20042 uu____20043 uu____20044 uu____20051);
          (let t1 = maybe_simplify cfg env stack t  in
           match stack with
           | [] -> t1
           | (Debug (tm,time_then))::stack1 ->
               (if (cfg.debug).print_normalized
                then
                  (let time_now = FStar_Util.now ()  in
                   let uu____20086 =
                     let uu____20087 =
                       let uu____20088 =
                         FStar_Util.time_diff time_then time_now  in
                       FStar_Pervasives_Native.snd uu____20088  in
                     FStar_Util.string_of_int uu____20087  in
                   let uu____20093 = FStar_Syntax_Print.term_to_string tm  in
                   let uu____20094 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.print3 "Normalized (%s ms) %s\n\tto %s\n"
                     uu____20086 uu____20093 uu____20094)
                else ();
                rebuild cfg env stack1 t1)
           | (Cfg cfg1)::stack1 -> rebuild cfg1 env stack1 t1
           | (Meta (m,r))::stack1 ->
               let t2 = mk (FStar_Syntax_Syntax.Tm_meta (t1, m)) r  in
               rebuild cfg env stack1 t2
           | (MemoLazy r)::stack1 ->
               (set_memo cfg r (env, t1);
                log cfg
                  (fun uu____20148  ->
                     let uu____20149 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 "\tSet memo %s\n" uu____20149);
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
               let uu____20185 =
                 let uu___178_20186 = FStar_Syntax_Util.abs bs1 t1 lopt1  in
                 {
                   FStar_Syntax_Syntax.n =
                     (uu___178_20186.FStar_Syntax_Syntax.n);
                   FStar_Syntax_Syntax.pos = r;
                   FStar_Syntax_Syntax.vars =
                     (uu___178_20186.FStar_Syntax_Syntax.vars)
                 }  in
               rebuild cfg env stack1 uu____20185
           | (Arg (Univ uu____20187,uu____20188,uu____20189))::uu____20190 ->
               failwith "Impossible"
           | (Arg (Dummy ,uu____20193,uu____20194))::uu____20195 ->
               failwith "Impossible"
           | (UnivArgs (us,r))::stack1 ->
               let t2 = FStar_Syntax_Syntax.mk_Tm_uinst t1 us  in
               rebuild cfg env stack1 t2
           | (Arg (Clos (env_arg,tm,uu____20210,uu____20211),aq,r))::stack1
               when
               let uu____20261 = head_of t1  in
               FStar_Syntax_Util.is_fstar_tactics_by_tactic uu____20261 ->
               let t2 =
                 let uu____20265 =
                   let uu____20266 =
                     let uu____20267 = closure_as_term cfg env_arg tm  in
                     (uu____20267, aq)  in
                   FStar_Syntax_Syntax.extend_app t1 uu____20266  in
                 uu____20265 FStar_Pervasives_Native.None r  in
               rebuild cfg env stack1 t2
           | (Arg (Clos (env_arg,tm,m,uu____20273),aq,r))::stack1 ->
               (log cfg
                  (fun uu____20326  ->
                     let uu____20327 = FStar_Syntax_Print.term_to_string tm
                        in
                     FStar_Util.print1 "Rebuilding with arg %s\n" uu____20327);
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
                  (let uu____20337 = FStar_ST.op_Bang m  in
                   match uu____20337 with
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
                   | FStar_Pervasives_Native.Some (uu____20474,a) ->
                       let t2 =
                         FStar_Syntax_Syntax.extend_app t1 (a, aq)
                           FStar_Pervasives_Native.None r
                          in
                       rebuild cfg env_arg stack1 t2))
           | (App (env1,head1,aq,r))::stack' when should_reify cfg stack ->
               let t0 = t1  in
               let fallback msg uu____20521 =
                 log cfg
                   (fun uu____20525  ->
                      let uu____20526 = FStar_Syntax_Print.term_to_string t1
                         in
                      FStar_Util.print2 "Not reifying%s: %s\n" msg
                        uu____20526);
                 (let t2 =
                    FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                      FStar_Pervasives_Native.None r
                     in
                  rebuild cfg env1 stack' t2)
                  in
               let uu____20530 =
                 let uu____20531 = FStar_Syntax_Subst.compress t1  in
                 uu____20531.FStar_Syntax_Syntax.n  in
               (match uu____20530 with
                | FStar_Syntax_Syntax.Tm_meta
                    (t2,FStar_Syntax_Syntax.Meta_monadic (m,ty)) ->
                    do_reify_monadic (fallback " (1)") cfg env1 stack t2 m ty
                | FStar_Syntax_Syntax.Tm_meta
                    (t2,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,ty))
                    ->
                    let lifted =
                      let uu____20558 = closure_as_term cfg env1 ty  in
                      reify_lift cfg t2 msrc mtgt uu____20558  in
                    (log cfg
                       (fun uu____20562  ->
                          let uu____20563 =
                            FStar_Syntax_Print.term_to_string lifted  in
                          FStar_Util.print1 "Reified lift to (1): %s\n"
                            uu____20563);
                     (let uu____20564 = FStar_List.tl stack  in
                      norm cfg env1 uu____20564 lifted))
                | FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reflect uu____20565);
                       FStar_Syntax_Syntax.pos = uu____20566;
                       FStar_Syntax_Syntax.vars = uu____20567;_},(e,uu____20569)::[])
                    -> norm cfg env1 stack' e
                | FStar_Syntax_Syntax.Tm_app uu____20598 when
                    (cfg.steps).primops ->
                    let uu____20613 = FStar_Syntax_Util.head_and_args t1  in
                    (match uu____20613 with
                     | (hd1,args) ->
                         let uu____20650 =
                           let uu____20651 = FStar_Syntax_Util.un_uinst hd1
                              in
                           uu____20651.FStar_Syntax_Syntax.n  in
                         (match uu____20650 with
                          | FStar_Syntax_Syntax.Tm_fvar fv ->
                              let uu____20655 = find_prim_step cfg fv  in
                              (match uu____20655 with
                               | FStar_Pervasives_Native.Some
                                   { name = uu____20658; arity = uu____20659;
                                     auto_reflect =
                                       FStar_Pervasives_Native.Some n1;
                                     strong_reduction_ok = uu____20661;
                                     requires_binder_substitution =
                                       uu____20662;
                                     interpretation = uu____20663;_}
                                   when (FStar_List.length args) = n1 ->
                                   norm cfg env1 stack' t1
                               | uu____20676 -> fallback " (3)" ())
                          | uu____20679 -> fallback " (4)" ()))
                | uu____20680 -> fallback " (2)" ())
           | (App (env1,head1,aq,r))::stack1 ->
               let t2 =
                 FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                   FStar_Pervasives_Native.None r
                  in
               rebuild cfg env1 stack1 t2
           | (Match (env1,branches,cfg1,r))::stack1 ->
               (log cfg1
                  (fun uu____20701  ->
                     let uu____20702 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1
                       "Rebuilding with match, scrutinee is %s ...\n"
                       uu____20702);
                (let scrutinee = t1  in
                 let norm_and_rebuild_match uu____20707 =
                   log cfg1
                     (fun uu____20712  ->
                        let uu____20713 =
                          FStar_Syntax_Print.term_to_string scrutinee  in
                        let uu____20714 =
                          let uu____20715 =
                            FStar_All.pipe_right branches
                              (FStar_List.map
                                 (fun uu____20732  ->
                                    match uu____20732 with
                                    | (p,uu____20742,uu____20743) ->
                                        FStar_Syntax_Print.pat_to_string p))
                             in
                          FStar_All.pipe_right uu____20715
                            (FStar_String.concat "\n\t")
                           in
                        FStar_Util.print2
                          "match is irreducible: scrutinee=%s\nbranches=%s\n"
                          uu____20713 uu____20714);
                   (let whnf = (cfg1.steps).weak || (cfg1.steps).hnf  in
                    let cfg_exclude_iota_zeta =
                      let new_delta =
                        FStar_All.pipe_right cfg1.delta_level
                          (FStar_List.filter
                             (fun uu___91_20760  ->
                                match uu___91_20760 with
                                | FStar_TypeChecker_Env.Inlining  -> true
                                | FStar_TypeChecker_Env.Eager_unfolding_only 
                                    -> true
                                | uu____20761 -> false))
                         in
                      let uu___179_20762 = cfg1  in
                      {
                        steps =
                          (let uu___180_20765 = cfg1.steps  in
                           {
                             beta = (uu___180_20765.beta);
                             iota = (uu___180_20765.iota);
                             zeta = false;
                             weak = (uu___180_20765.weak);
                             hnf = (uu___180_20765.hnf);
                             primops = (uu___180_20765.primops);
                             no_delta_steps = (uu___180_20765.no_delta_steps);
                             unfold_until = (uu___180_20765.unfold_until);
                             unfold_only = (uu___180_20765.unfold_only);
                             unfold_attr = (uu___180_20765.unfold_attr);
                             unfold_tac = (uu___180_20765.unfold_tac);
                             pure_subterms_within_computations =
                               (uu___180_20765.pure_subterms_within_computations);
                             simplify = (uu___180_20765.simplify);
                             erase_universes =
                               (uu___180_20765.erase_universes);
                             allow_unbound_universes =
                               (uu___180_20765.allow_unbound_universes);
                             reify_ = (uu___180_20765.reify_);
                             compress_uvars = (uu___180_20765.compress_uvars);
                             no_full_norm = (uu___180_20765.no_full_norm);
                             check_no_uvars = (uu___180_20765.check_no_uvars);
                             unmeta = (uu___180_20765.unmeta);
                             unascribe = (uu___180_20765.unascribe)
                           });
                        tcenv = (uu___179_20762.tcenv);
                        debug = (uu___179_20762.debug);
                        delta_level = new_delta;
                        primitive_steps = (uu___179_20762.primitive_steps);
                        strong = true;
                        memoize_lazy = (uu___179_20762.memoize_lazy);
                        normalize_pure_lets =
                          (uu___179_20762.normalize_pure_lets)
                      }  in
                    let norm_or_whnf env2 t2 =
                      if whnf
                      then closure_as_term cfg_exclude_iota_zeta env2 t2
                      else norm cfg_exclude_iota_zeta env2 [] t2  in
                    let rec norm_pat env2 p =
                      match p.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_constant uu____20797 ->
                          (p, env2)
                      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                          let uu____20818 =
                            FStar_All.pipe_right pats
                              (FStar_List.fold_left
                                 (fun uu____20878  ->
                                    fun uu____20879  ->
                                      match (uu____20878, uu____20879) with
                                      | ((pats1,env3),(p1,b)) ->
                                          let uu____20970 = norm_pat env3 p1
                                             in
                                          (match uu____20970 with
                                           | (p2,env4) ->
                                               (((p2, b) :: pats1), env4)))
                                 ([], env2))
                             in
                          (match uu____20818 with
                           | (pats1,env3) ->
                               ((let uu___181_21052 = p  in
                                 {
                                   FStar_Syntax_Syntax.v =
                                     (FStar_Syntax_Syntax.Pat_cons
                                        (fv, (FStar_List.rev pats1)));
                                   FStar_Syntax_Syntax.p =
                                     (uu___181_21052.FStar_Syntax_Syntax.p)
                                 }), env3))
                      | FStar_Syntax_Syntax.Pat_var x ->
                          let x1 =
                            let uu___182_21071 = x  in
                            let uu____21072 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___182_21071.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___182_21071.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____21072
                            }  in
                          ((let uu___183_21086 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_var x1);
                              FStar_Syntax_Syntax.p =
                                (uu___183_21086.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_wild x ->
                          let x1 =
                            let uu___184_21097 = x  in
                            let uu____21098 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___184_21097.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___184_21097.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____21098
                            }  in
                          ((let uu___185_21112 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_wild x1);
                              FStar_Syntax_Syntax.p =
                                (uu___185_21112.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                          let x1 =
                            let uu___186_21128 = x  in
                            let uu____21129 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___186_21128.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___186_21128.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____21129
                            }  in
                          let t3 = norm_or_whnf env2 t2  in
                          ((let uu___187_21136 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_dot_term (x1, t3));
                              FStar_Syntax_Syntax.p =
                                (uu___187_21136.FStar_Syntax_Syntax.p)
                            }), env2)
                       in
                    let branches1 =
                      match env1 with
                      | [] when whnf -> branches
                      | uu____21146 ->
                          FStar_All.pipe_right branches
                            (FStar_List.map
                               (fun branch1  ->
                                  let uu____21160 =
                                    FStar_Syntax_Subst.open_branch branch1
                                     in
                                  match uu____21160 with
                                  | (p,wopt,e) ->
                                      let uu____21180 = norm_pat env1 p  in
                                      (match uu____21180 with
                                       | (p1,env2) ->
                                           let wopt1 =
                                             match wopt with
                                             | FStar_Pervasives_Native.None 
                                                 ->
                                                 FStar_Pervasives_Native.None
                                             | FStar_Pervasives_Native.Some w
                                                 ->
                                                 let uu____21205 =
                                                   norm_or_whnf env2 w  in
                                                 FStar_Pervasives_Native.Some
                                                   uu____21205
                                              in
                                           let e1 = norm_or_whnf env2 e  in
                                           FStar_Syntax_Util.branch
                                             (p1, wopt1, e1))))
                       in
                    let uu____21211 =
                      mk
                        (FStar_Syntax_Syntax.Tm_match (scrutinee, branches1))
                        r
                       in
                    rebuild cfg1 env1 stack1 uu____21211)
                    in
                 let rec is_cons head1 =
                   let uu____21216 =
                     let uu____21217 = FStar_Syntax_Subst.compress head1  in
                     uu____21217.FStar_Syntax_Syntax.n  in
                   match uu____21216 with
                   | FStar_Syntax_Syntax.Tm_uinst (h,uu____21221) ->
                       is_cons h
                   | FStar_Syntax_Syntax.Tm_constant uu____21226 -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____21227;
                         FStar_Syntax_Syntax.fv_delta = uu____21228;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Data_ctor );_}
                       -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____21229;
                         FStar_Syntax_Syntax.fv_delta = uu____21230;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Record_ctor uu____21231);_}
                       -> true
                   | uu____21238 -> false  in
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
                   let uu____21383 =
                     FStar_Syntax_Util.head_and_args scrutinee1  in
                   match uu____21383 with
                   | (head1,args) ->
                       (match p.FStar_Syntax_Syntax.v with
                        | FStar_Syntax_Syntax.Pat_var bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_wild bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_dot_term uu____21470 ->
                            FStar_Util.Inl []
                        | FStar_Syntax_Syntax.Pat_constant s ->
                            (match scrutinee1.FStar_Syntax_Syntax.n with
                             | FStar_Syntax_Syntax.Tm_constant s' when
                                 FStar_Const.eq_const s s' ->
                                 FStar_Util.Inl []
                             | uu____21509 ->
                                 let uu____21510 =
                                   let uu____21511 = is_cons head1  in
                                   Prims.op_Negation uu____21511  in
                                 FStar_Util.Inr uu____21510)
                        | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                            let uu____21536 =
                              let uu____21537 =
                                FStar_Syntax_Util.un_uinst head1  in
                              uu____21537.FStar_Syntax_Syntax.n  in
                            (match uu____21536 with
                             | FStar_Syntax_Syntax.Tm_fvar fv' when
                                 FStar_Syntax_Syntax.fv_eq fv fv' ->
                                 matches_args [] args arg_pats
                             | uu____21555 ->
                                 let uu____21556 =
                                   let uu____21557 = is_cons head1  in
                                   Prims.op_Negation uu____21557  in
                                 FStar_Util.Inr uu____21556))
                 
                 and matches_args out a p =
                   match (a, p) with
                   | ([],[]) -> FStar_Util.Inl out
                   | ((t2,uu____21626)::rest_a,(p1,uu____21629)::rest_p) ->
                       let uu____21673 = matches_pat t2 p1  in
                       (match uu____21673 with
                        | FStar_Util.Inl s ->
                            matches_args (FStar_List.append out s) rest_a
                              rest_p
                        | m -> m)
                   | uu____21722 -> FStar_Util.Inr false
                  in
                 let rec matches scrutinee1 p =
                   match p with
                   | [] -> norm_and_rebuild_match ()
                   | (p1,wopt,b)::rest ->
                       let uu____21828 = matches_pat scrutinee1 p1  in
                       (match uu____21828 with
                        | FStar_Util.Inr (false ) -> matches scrutinee1 rest
                        | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                        | FStar_Util.Inl s ->
                            (log cfg1
                               (fun uu____21868  ->
                                  let uu____21869 =
                                    FStar_Syntax_Print.pat_to_string p1  in
                                  let uu____21870 =
                                    let uu____21871 =
                                      FStar_List.map
                                        (fun uu____21881  ->
                                           match uu____21881 with
                                           | (uu____21886,t2) ->
                                               FStar_Syntax_Print.term_to_string
                                                 t2) s
                                       in
                                    FStar_All.pipe_right uu____21871
                                      (FStar_String.concat "; ")
                                     in
                                  FStar_Util.print2
                                    "Matches pattern %s with subst = %s\n"
                                    uu____21869 uu____21870);
                             (let env2 =
                                FStar_List.fold_left
                                  (fun env2  ->
                                     fun uu____21917  ->
                                       match uu____21917 with
                                       | (bv,t2) ->
                                           let uu____21940 =
                                             let uu____21947 =
                                               let uu____21950 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   bv
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 uu____21950
                                                in
                                             let uu____21951 =
                                               let uu____21952 =
                                                 let uu____21983 =
                                                   FStar_Util.mk_ref
                                                     (FStar_Pervasives_Native.Some
                                                        ([], t2))
                                                    in
                                                 ([], t2, uu____21983, false)
                                                  in
                                               Clos uu____21952  in
                                             (uu____21947, uu____21951)  in
                                           uu____21940 :: env2) env1 s
                                 in
                              let uu____22100 = guard_when_clause wopt b rest
                                 in
                              norm cfg1 env2 stack1 uu____22100)))
                    in
                 if (cfg1.steps).iota
                 then matches scrutinee branches
                 else norm_and_rebuild_match ())))

let (plugins :
  (primitive_step -> Prims.unit,Prims.unit -> primitive_step Prims.list)
    FStar_Pervasives_Native.tuple2)
  =
  let plugins = FStar_Util.mk_ref []  in
  let register p =
    let uu____22123 =
      let uu____22126 = FStar_ST.op_Bang plugins  in p :: uu____22126  in
    FStar_ST.op_Colon_Equals plugins uu____22123  in
  let retrieve uu____22224 = FStar_ST.op_Bang plugins  in
  (register, retrieve) 
let (register_plugin : primitive_step -> Prims.unit) =
  fun p  -> FStar_Pervasives_Native.fst plugins p 
let (retrieve_plugins : Prims.unit -> primitive_step Prims.list) =
  fun uu____22289  -> FStar_Pervasives_Native.snd plugins () 
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
               (fun uu___92_22322  ->
                  match uu___92_22322 with
                  | UnfoldUntil k -> [FStar_TypeChecker_Env.Unfold k]
                  | Eager_unfolding  ->
                      [FStar_TypeChecker_Env.Eager_unfolding_only]
                  | Inlining  -> [FStar_TypeChecker_Env.Inlining]
                  | UnfoldTac  -> [FStar_TypeChecker_Env.UnfoldTac]
                  | uu____22326 -> []))
           in
        let d1 =
          match d with
          | [] -> [FStar_TypeChecker_Env.NoDelta]
          | uu____22332 -> d  in
        let uu____22335 = to_fsteps s  in
        let uu____22336 =
          let uu____22337 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Norm")  in
          let uu____22338 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Primops")  in
          let uu____22339 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "380")  in
          let uu____22340 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "NormDelayed")
             in
          let uu____22341 =
            FStar_TypeChecker_Env.debug e
              (FStar_Options.Other "print_normalized_terms")
             in
          {
            gen = uu____22337;
            primop = uu____22338;
            b380 = uu____22339;
            norm_delayed = uu____22340;
            print_normalized = uu____22341
          }  in
        let uu____22342 =
          let uu____22345 =
            let uu____22348 = retrieve_plugins ()  in
            FStar_List.append uu____22348 psteps  in
          add_steps built_in_primitive_steps uu____22345  in
        let uu____22351 =
          (FStar_Options.normalize_pure_terms_for_extraction ()) ||
            (let uu____22353 =
               FStar_All.pipe_right s
                 (FStar_List.contains PureSubtermsWithinComputations)
                in
             Prims.op_Negation uu____22353)
           in
        {
          steps = uu____22335;
          tcenv = e;
          debug = uu____22336;
          delta_level = d1;
          primitive_steps = uu____22342;
          strong = false;
          memoize_lazy = true;
          normalize_pure_lets = uu____22351
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
      fun t  -> let uu____22411 = config s e  in norm_comp uu____22411 [] t
  
let (normalize_universe :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun u  ->
      let uu____22424 = config [] env  in norm_universe uu____22424 [] u
  
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
        let uu____22442 = norm cfg [] [] t  in
        FStar_Syntax_Util.non_informative uu____22442  in
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____22449 -> c
      | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
          let uu___188_22468 = c  in
          {
            FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
            FStar_Syntax_Syntax.pos =
              (uu___188_22468.FStar_Syntax_Syntax.pos);
            FStar_Syntax_Syntax.vars =
              (uu___188_22468.FStar_Syntax_Syntax.vars)
          }
      | FStar_Syntax_Syntax.Comp ct ->
          let l =
            FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
              ct.FStar_Syntax_Syntax.effect_name
             in
          let uu____22475 =
            (FStar_Syntax_Util.is_ghost_effect l) &&
              (non_info ct.FStar_Syntax_Syntax.result_typ)
             in
          if uu____22475
          then
            let ct1 =
              let uu____22477 =
                downgrade_ghost_effect_name
                  ct.FStar_Syntax_Syntax.effect_name
                 in
              match uu____22477 with
              | FStar_Pervasives_Native.Some pure_eff ->
                  let flags1 =
                    let uu____22484 =
                      FStar_Ident.lid_equals pure_eff
                        FStar_Parser_Const.effect_Tot_lid
                       in
                    if uu____22484
                    then FStar_Syntax_Syntax.TOTAL ::
                      (ct.FStar_Syntax_Syntax.flags)
                    else ct.FStar_Syntax_Syntax.flags  in
                  let uu___189_22488 = ct  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___189_22488.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name = pure_eff;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___189_22488.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___189_22488.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags = flags1
                  }
              | FStar_Pervasives_Native.None  ->
                  let ct1 =
                    FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c
                     in
                  let uu___190_22490 = ct1  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___190_22490.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name =
                      FStar_Parser_Const.effect_PURE_lid;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___190_22490.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___190_22490.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags =
                      (uu___190_22490.FStar_Syntax_Syntax.flags)
                  }
               in
            let uu___191_22491 = c  in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
              FStar_Syntax_Syntax.pos =
                (uu___191_22491.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___191_22491.FStar_Syntax_Syntax.vars)
            }
          else c
      | uu____22493 -> c
  
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
        let uu____22505 = norm cfg [] [] t  in
        FStar_Syntax_Util.non_informative uu____22505  in
      let uu____22512 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ)
         in
      if uu____22512
      then
        let uu____22513 =
          downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name  in
        match uu____22513 with
        | FStar_Pervasives_Native.Some pure_eff ->
            FStar_Syntax_Syntax.mk_lcomp pure_eff
              lc.FStar_Syntax_Syntax.res_typ lc.FStar_Syntax_Syntax.cflags
              (fun uu____22519  ->
                 let uu____22520 = FStar_Syntax_Syntax.lcomp_comp lc  in
                 ghost_to_pure env uu____22520)
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
            ((let uu____22537 =
                let uu____22542 =
                  let uu____22543 = FStar_Util.message_of_exn e  in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____22543
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____22542)  in
              FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____22537);
             t)
         in
      FStar_Syntax_Print.term_to_string' env.FStar_TypeChecker_Env.dsenv t1
  
let (comp_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string) =
  fun env  ->
    fun c  ->
      let c1 =
        try
          let uu____22554 = config [AllowUnboundUniverses] env  in
          norm_comp uu____22554 [] c
        with
        | e ->
            ((let uu____22567 =
                let uu____22572 =
                  let uu____22573 = FStar_Util.message_of_exn e  in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____22573
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____22572)  in
              FStar_Errors.log_issue c.FStar_Syntax_Syntax.pos uu____22567);
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
                   let uu____22610 =
                     let uu____22611 =
                       let uu____22618 = FStar_Syntax_Util.mk_conj phi1 phi
                          in
                       (y, uu____22618)  in
                     FStar_Syntax_Syntax.Tm_refine uu____22611  in
                   mk uu____22610 t01.FStar_Syntax_Syntax.pos
               | uu____22623 -> t2)
          | uu____22624 -> t2  in
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
        let uu____22664 = FStar_Syntax_Util.arrow_formals_comp t_e  in
        match uu____22664 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____22693 ->
                 let uu____22700 = FStar_Syntax_Util.abs_formals e  in
                 (match uu____22700 with
                  | (actuals,uu____22710,uu____22711) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____22725 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders
                            in
                         match uu____22725 with
                         | (binders,args) ->
                             let uu____22742 =
                               FStar_Syntax_Syntax.mk_Tm_app e args
                                 FStar_Pervasives_Native.None
                                 e.FStar_Syntax_Syntax.pos
                                in
                             FStar_Syntax_Util.abs binders uu____22742
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
      | uu____22750 ->
          let uu____22751 = FStar_Syntax_Util.head_and_args t  in
          (match uu____22751 with
           | (head1,args) ->
               let uu____22788 =
                 let uu____22789 = FStar_Syntax_Subst.compress head1  in
                 uu____22789.FStar_Syntax_Syntax.n  in
               (match uu____22788 with
                | FStar_Syntax_Syntax.Tm_uvar (uu____22792,thead) ->
                    let uu____22818 = FStar_Syntax_Util.arrow_formals thead
                       in
                    (match uu____22818 with
                     | (formals,tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____22860 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___196_22868 = env  in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___196_22868.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___196_22868.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___196_22868.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___196_22868.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___196_22868.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___196_22868.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___196_22868.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___196_22868.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___196_22868.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___196_22868.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___196_22868.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___196_22868.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___196_22868.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___196_22868.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___196_22868.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___196_22868.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___196_22868.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___196_22868.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___196_22868.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___196_22868.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___196_22868.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___196_22868.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___196_22868.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___196_22868.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                     =
                                     (uu___196_22868.FStar_TypeChecker_Env.qtbl_name_and_index);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___196_22868.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth_hook =
                                     (uu___196_22868.FStar_TypeChecker_Env.synth_hook);
                                   FStar_TypeChecker_Env.splice =
                                     (uu___196_22868.FStar_TypeChecker_Env.splice);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___196_22868.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___196_22868.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___196_22868.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___196_22868.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.dep_graph =
                                     (uu___196_22868.FStar_TypeChecker_Env.dep_graph)
                                 }) t
                               in
                            match uu____22860 with
                            | (uu____22869,ty,uu____22871) ->
                                eta_expand_with_type env t ty))
                | uu____22872 ->
                    let uu____22873 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___197_22881 = env  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___197_22881.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___197_22881.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___197_22881.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___197_22881.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___197_22881.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___197_22881.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___197_22881.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___197_22881.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___197_22881.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___197_22881.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___197_22881.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___197_22881.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___197_22881.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___197_22881.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___197_22881.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___197_22881.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___197_22881.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___197_22881.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.failhard =
                             (uu___197_22881.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___197_22881.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___197_22881.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___197_22881.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___197_22881.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___197_22881.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qtbl_name_and_index =
                             (uu___197_22881.FStar_TypeChecker_Env.qtbl_name_and_index);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___197_22881.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth_hook =
                             (uu___197_22881.FStar_TypeChecker_Env.synth_hook);
                           FStar_TypeChecker_Env.splice =
                             (uu___197_22881.FStar_TypeChecker_Env.splice);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___197_22881.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___197_22881.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___197_22881.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___197_22881.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.dep_graph =
                             (uu___197_22881.FStar_TypeChecker_Env.dep_graph)
                         }) t
                       in
                    (match uu____22873 with
                     | (uu____22882,ty,uu____22884) ->
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
      let uu___198_22941 = x  in
      let uu____22942 = elim_delayed_subst_term x.FStar_Syntax_Syntax.sort
         in
      {
        FStar_Syntax_Syntax.ppname =
          (uu___198_22941.FStar_Syntax_Syntax.ppname);
        FStar_Syntax_Syntax.index =
          (uu___198_22941.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = uu____22942
      }  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____22945 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_bvar uu____22970 -> t1
    | FStar_Syntax_Syntax.Tm_name uu____22971 -> t1
    | FStar_Syntax_Syntax.Tm_fvar uu____22972 -> t1
    | FStar_Syntax_Syntax.Tm_uinst uu____22973 -> t1
    | FStar_Syntax_Syntax.Tm_constant uu____22980 -> t1
    | FStar_Syntax_Syntax.Tm_type uu____22981 -> t1
    | FStar_Syntax_Syntax.Tm_lazy uu____22982 -> t1
    | FStar_Syntax_Syntax.Tm_unknown  -> t1
    | FStar_Syntax_Syntax.Tm_abs (bs,t2,rc_opt) ->
        let elim_rc rc =
          let uu___199_23010 = rc  in
          let uu____23011 =
            FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
              elim_delayed_subst_term
             in
          let uu____23018 =
            elim_delayed_subst_cflags rc.FStar_Syntax_Syntax.residual_flags
             in
          {
            FStar_Syntax_Syntax.residual_effect =
              (uu___199_23010.FStar_Syntax_Syntax.residual_effect);
            FStar_Syntax_Syntax.residual_typ = uu____23011;
            FStar_Syntax_Syntax.residual_flags = uu____23018
          }  in
        let uu____23021 =
          let uu____23022 =
            let uu____23039 = elim_delayed_subst_binders bs  in
            let uu____23046 = elim_delayed_subst_term t2  in
            let uu____23047 = FStar_Util.map_opt rc_opt elim_rc  in
            (uu____23039, uu____23046, uu____23047)  in
          FStar_Syntax_Syntax.Tm_abs uu____23022  in
        mk1 uu____23021
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____23076 =
          let uu____23077 =
            let uu____23090 = elim_delayed_subst_binders bs  in
            let uu____23097 = elim_delayed_subst_comp c  in
            (uu____23090, uu____23097)  in
          FStar_Syntax_Syntax.Tm_arrow uu____23077  in
        mk1 uu____23076
    | FStar_Syntax_Syntax.Tm_refine (bv,phi) ->
        let uu____23110 =
          let uu____23111 =
            let uu____23118 = elim_bv bv  in
            let uu____23119 = elim_delayed_subst_term phi  in
            (uu____23118, uu____23119)  in
          FStar_Syntax_Syntax.Tm_refine uu____23111  in
        mk1 uu____23110
    | FStar_Syntax_Syntax.Tm_app (t2,args) ->
        let uu____23142 =
          let uu____23143 =
            let uu____23158 = elim_delayed_subst_term t2  in
            let uu____23159 = elim_delayed_subst_args args  in
            (uu____23158, uu____23159)  in
          FStar_Syntax_Syntax.Tm_app uu____23143  in
        mk1 uu____23142
    | FStar_Syntax_Syntax.Tm_match (t2,branches) ->
        let rec elim_pat p =
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_var x ->
              let uu___200_23223 = p  in
              let uu____23224 =
                let uu____23225 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_var uu____23225  in
              {
                FStar_Syntax_Syntax.v = uu____23224;
                FStar_Syntax_Syntax.p =
                  (uu___200_23223.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_wild x ->
              let uu___201_23227 = p  in
              let uu____23228 =
                let uu____23229 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_wild uu____23229  in
              {
                FStar_Syntax_Syntax.v = uu____23228;
                FStar_Syntax_Syntax.p =
                  (uu___201_23227.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
              let uu___202_23236 = p  in
              let uu____23237 =
                let uu____23238 =
                  let uu____23245 = elim_bv x  in
                  let uu____23246 = elim_delayed_subst_term t0  in
                  (uu____23245, uu____23246)  in
                FStar_Syntax_Syntax.Pat_dot_term uu____23238  in
              {
                FStar_Syntax_Syntax.v = uu____23237;
                FStar_Syntax_Syntax.p =
                  (uu___202_23236.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
              let uu___203_23265 = p  in
              let uu____23266 =
                let uu____23267 =
                  let uu____23280 =
                    FStar_List.map
                      (fun uu____23303  ->
                         match uu____23303 with
                         | (x,b) ->
                             let uu____23316 = elim_pat x  in
                             (uu____23316, b)) pats
                     in
                  (fv, uu____23280)  in
                FStar_Syntax_Syntax.Pat_cons uu____23267  in
              {
                FStar_Syntax_Syntax.v = uu____23266;
                FStar_Syntax_Syntax.p =
                  (uu___203_23265.FStar_Syntax_Syntax.p)
              }
          | uu____23329 -> p  in
        let elim_branch uu____23351 =
          match uu____23351 with
          | (pat,wopt,t3) ->
              let uu____23377 = elim_pat pat  in
              let uu____23380 =
                FStar_Util.map_opt wopt elim_delayed_subst_term  in
              let uu____23383 = elim_delayed_subst_term t3  in
              (uu____23377, uu____23380, uu____23383)
           in
        let uu____23388 =
          let uu____23389 =
            let uu____23412 = elim_delayed_subst_term t2  in
            let uu____23413 = FStar_List.map elim_branch branches  in
            (uu____23412, uu____23413)  in
          FStar_Syntax_Syntax.Tm_match uu____23389  in
        mk1 uu____23388
    | FStar_Syntax_Syntax.Tm_ascribed (t2,a,lopt) ->
        let elim_ascription uu____23522 =
          match uu____23522 with
          | (tc,topt) ->
              let uu____23557 =
                match tc with
                | FStar_Util.Inl t3 ->
                    let uu____23567 = elim_delayed_subst_term t3  in
                    FStar_Util.Inl uu____23567
                | FStar_Util.Inr c ->
                    let uu____23569 = elim_delayed_subst_comp c  in
                    FStar_Util.Inr uu____23569
                 in
              let uu____23570 =
                FStar_Util.map_opt topt elim_delayed_subst_term  in
              (uu____23557, uu____23570)
           in
        let uu____23579 =
          let uu____23580 =
            let uu____23607 = elim_delayed_subst_term t2  in
            let uu____23608 = elim_ascription a  in
            (uu____23607, uu____23608, lopt)  in
          FStar_Syntax_Syntax.Tm_ascribed uu____23580  in
        mk1 uu____23579
    | FStar_Syntax_Syntax.Tm_let (lbs,t2) ->
        let elim_lb lb =
          let uu___204_23653 = lb  in
          let uu____23654 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbtyp  in
          let uu____23657 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbdef  in
          {
            FStar_Syntax_Syntax.lbname =
              (uu___204_23653.FStar_Syntax_Syntax.lbname);
            FStar_Syntax_Syntax.lbunivs =
              (uu___204_23653.FStar_Syntax_Syntax.lbunivs);
            FStar_Syntax_Syntax.lbtyp = uu____23654;
            FStar_Syntax_Syntax.lbeff =
              (uu___204_23653.FStar_Syntax_Syntax.lbeff);
            FStar_Syntax_Syntax.lbdef = uu____23657;
            FStar_Syntax_Syntax.lbattrs =
              (uu___204_23653.FStar_Syntax_Syntax.lbattrs);
            FStar_Syntax_Syntax.lbpos =
              (uu___204_23653.FStar_Syntax_Syntax.lbpos)
          }  in
        let uu____23660 =
          let uu____23661 =
            let uu____23674 =
              let uu____23681 =
                FStar_List.map elim_lb (FStar_Pervasives_Native.snd lbs)  in
              ((FStar_Pervasives_Native.fst lbs), uu____23681)  in
            let uu____23690 = elim_delayed_subst_term t2  in
            (uu____23674, uu____23690)  in
          FStar_Syntax_Syntax.Tm_let uu____23661  in
        mk1 uu____23660
    | FStar_Syntax_Syntax.Tm_uvar (uv,t2) ->
        let uu____23723 =
          let uu____23724 =
            let uu____23741 = elim_delayed_subst_term t2  in
            (uv, uu____23741)  in
          FStar_Syntax_Syntax.Tm_uvar uu____23724  in
        mk1 uu____23723
    | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
        let qi1 =
          FStar_Syntax_Syntax.on_antiquoted elim_delayed_subst_term qi  in
        let uu____23759 =
          let uu____23760 =
            let uu____23767 = elim_delayed_subst_term tm  in
            (uu____23767, qi1)  in
          FStar_Syntax_Syntax.Tm_quoted uu____23760  in
        mk1 uu____23759
    | FStar_Syntax_Syntax.Tm_meta (t2,md) ->
        let uu____23774 =
          let uu____23775 =
            let uu____23782 = elim_delayed_subst_term t2  in
            let uu____23783 = elim_delayed_subst_meta md  in
            (uu____23782, uu____23783)  in
          FStar_Syntax_Syntax.Tm_meta uu____23775  in
        mk1 uu____23774

and (elim_delayed_subst_cflags :
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun flags1  ->
    FStar_List.map
      (fun uu___93_23790  ->
         match uu___93_23790 with
         | FStar_Syntax_Syntax.DECREASES t ->
             let uu____23794 = elim_delayed_subst_term t  in
             FStar_Syntax_Syntax.DECREASES uu____23794
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
        let uu____23815 =
          let uu____23816 =
            let uu____23825 = elim_delayed_subst_term t  in
            (uu____23825, uopt)  in
          FStar_Syntax_Syntax.Total uu____23816  in
        mk1 uu____23815
    | FStar_Syntax_Syntax.GTotal (t,uopt) ->
        let uu____23838 =
          let uu____23839 =
            let uu____23848 = elim_delayed_subst_term t  in
            (uu____23848, uopt)  in
          FStar_Syntax_Syntax.GTotal uu____23839  in
        mk1 uu____23838
    | FStar_Syntax_Syntax.Comp ct ->
        let ct1 =
          let uu___205_23853 = ct  in
          let uu____23854 =
            elim_delayed_subst_term ct.FStar_Syntax_Syntax.result_typ  in
          let uu____23857 =
            elim_delayed_subst_args ct.FStar_Syntax_Syntax.effect_args  in
          let uu____23866 =
            elim_delayed_subst_cflags ct.FStar_Syntax_Syntax.flags  in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___205_23853.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___205_23853.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ = uu____23854;
            FStar_Syntax_Syntax.effect_args = uu____23857;
            FStar_Syntax_Syntax.flags = uu____23866
          }  in
        mk1 (FStar_Syntax_Syntax.Comp ct1)

and (elim_delayed_subst_meta :
  FStar_Syntax_Syntax.metadata -> FStar_Syntax_Syntax.metadata) =
  fun uu___94_23869  ->
    match uu___94_23869 with
    | FStar_Syntax_Syntax.Meta_pattern args ->
        let uu____23881 = FStar_List.map elim_delayed_subst_args args  in
        FStar_Syntax_Syntax.Meta_pattern uu____23881
    | FStar_Syntax_Syntax.Meta_monadic (m,t) ->
        let uu____23914 =
          let uu____23921 = elim_delayed_subst_term t  in (m, uu____23921)
           in
        FStar_Syntax_Syntax.Meta_monadic uu____23914
    | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,t) ->
        let uu____23929 =
          let uu____23938 = elim_delayed_subst_term t  in
          (m1, m2, uu____23938)  in
        FStar_Syntax_Syntax.Meta_monadic_lift uu____23929
    | m -> m

and (elim_delayed_subst_args :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun args  ->
    FStar_List.map
      (fun uu____23961  ->
         match uu____23961 with
         | (t,q) ->
             let uu____23972 = elim_delayed_subst_term t  in (uu____23972, q))
      args

and (elim_delayed_subst_binders :
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun bs  ->
    FStar_List.map
      (fun uu____23992  ->
         match uu____23992 with
         | (x,q) ->
             let uu____24003 =
               let uu___206_24004 = x  in
               let uu____24005 =
                 elim_delayed_subst_term x.FStar_Syntax_Syntax.sort  in
               {
                 FStar_Syntax_Syntax.ppname =
                   (uu___206_24004.FStar_Syntax_Syntax.ppname);
                 FStar_Syntax_Syntax.index =
                   (uu___206_24004.FStar_Syntax_Syntax.index);
                 FStar_Syntax_Syntax.sort = uu____24005
               }  in
             (uu____24003, q)) bs

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
            | (uu____24081,FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c))
                  FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
            | (uu____24087,FStar_Util.Inl t) ->
                let uu____24093 =
                  let uu____24096 =
                    let uu____24097 =
                      let uu____24110 = FStar_Syntax_Syntax.mk_Total t  in
                      (binders, uu____24110)  in
                    FStar_Syntax_Syntax.Tm_arrow uu____24097  in
                  FStar_Syntax_Syntax.mk uu____24096  in
                uu____24093 FStar_Pervasives_Native.None
                  t.FStar_Syntax_Syntax.pos
             in
          let uu____24114 = FStar_Syntax_Subst.open_univ_vars univ_names t
             in
          match uu____24114 with
          | (univ_names1,t1) ->
              let t2 = remove_uvar_solutions env t1  in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2  in
              let t4 = elim_delayed_subst_term t3  in
              let uu____24142 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t4))
                | uu____24197 ->
                    let uu____24198 =
                      let uu____24207 =
                        let uu____24208 = FStar_Syntax_Subst.compress t4  in
                        uu____24208.FStar_Syntax_Syntax.n  in
                      (uu____24207, tc)  in
                    (match uu____24198 with
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inr uu____24233) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inl uu____24270) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____24309,FStar_Util.Inl uu____24310) ->
                         ([], (FStar_Util.Inl t4))
                     | uu____24333 -> failwith "Impossible")
                 in
              (match uu____24142 with
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
          let uu____24438 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl t)  in
          match uu____24438 with
          | (univ_names1,binders1,tc) ->
              let uu____24496 = FStar_Util.left tc  in
              (univ_names1, binders1, uu____24496)
  
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
          let uu____24531 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr c)  in
          match uu____24531 with
          | (univ_names1,binders1,tc) ->
              let uu____24591 = FStar_Util.right tc  in
              (univ_names1, binders1, uu____24591)
  
let rec (elim_uvars :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt)
  =
  fun env  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univ_names,binders,typ,lids,lids') ->
          let uu____24624 = elim_uvars_aux_t env univ_names binders typ  in
          (match uu____24624 with
           | (univ_names1,binders1,typ1) ->
               let uu___207_24652 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___207_24652.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___207_24652.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___207_24652.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___207_24652.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
          let uu___208_24673 = s  in
          let uu____24674 =
            let uu____24675 =
              let uu____24684 = FStar_List.map (elim_uvars env) sigs  in
              (uu____24684, lids)  in
            FStar_Syntax_Syntax.Sig_bundle uu____24675  in
          {
            FStar_Syntax_Syntax.sigel = uu____24674;
            FStar_Syntax_Syntax.sigrng =
              (uu___208_24673.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___208_24673.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___208_24673.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___208_24673.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_datacon (lid,univ_names,typ,lident,i,lids) ->
          let uu____24701 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____24701 with
           | (univ_names1,uu____24719,typ1) ->
               let uu___209_24733 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___209_24733.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___209_24733.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___209_24733.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___209_24733.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univ_names,typ) ->
          let uu____24739 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____24739 with
           | (univ_names1,uu____24757,typ1) ->
               let uu___210_24771 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___210_24771.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___210_24771.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___210_24771.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___210_24771.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____24805 =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs
                       in
                    match uu____24805 with
                    | (opening,lbunivs) ->
                        let elim t =
                          let uu____24828 =
                            let uu____24829 =
                              let uu____24830 =
                                FStar_Syntax_Subst.subst opening t  in
                              remove_uvar_solutions env uu____24830  in
                            FStar_Syntax_Subst.close_univ_vars lbunivs
                              uu____24829
                             in
                          elim_delayed_subst_term uu____24828  in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp  in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef  in
                        let uu___211_24833 = lb  in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___211_24833.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___211_24833.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___211_24833.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___211_24833.FStar_Syntax_Syntax.lbpos)
                        }))
             in
          let uu___212_24834 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids));
            FStar_Syntax_Syntax.sigrng =
              (uu___212_24834.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___212_24834.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___212_24834.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___212_24834.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_main t ->
          let uu___213_24846 = s  in
          let uu____24847 =
            let uu____24848 = remove_uvar_solutions env t  in
            FStar_Syntax_Syntax.Sig_main uu____24848  in
          {
            FStar_Syntax_Syntax.sigel = uu____24847;
            FStar_Syntax_Syntax.sigrng =
              (uu___213_24846.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___213_24846.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___213_24846.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___213_24846.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_assume (l,us,t) ->
          let uu____24852 = elim_uvars_aux_t env us [] t  in
          (match uu____24852 with
           | (us1,uu____24870,t1) ->
               let uu___214_24884 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___214_24884.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___214_24884.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___214_24884.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___214_24884.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____24885 ->
          failwith "Impossible: should have been desugared already"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____24887 =
            elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature
             in
          (match uu____24887 with
           | (univs1,binders,signature) ->
               let uu____24915 =
                 let uu____24924 = FStar_Syntax_Subst.univ_var_opening univs1
                    in
                 match uu____24924 with
                 | (univs_opening,univs2) ->
                     let uu____24951 =
                       FStar_Syntax_Subst.univ_var_closing univs2  in
                     (univs_opening, uu____24951)
                  in
               (match uu____24915 with
                | (univs_opening,univs_closing) ->
                    let uu____24968 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders
                         in
                      let uu____24974 =
                        FStar_Syntax_Subst.opening_of_binders binders1  in
                      let uu____24975 =
                        FStar_Syntax_Subst.closing_of_binders binders1  in
                      (uu____24974, uu____24975)  in
                    (match uu____24968 with
                     | (b_opening,b_closing) ->
                         let n1 = FStar_List.length univs1  in
                         let n_binders = FStar_List.length binders  in
                         let elim_tscheme uu____24997 =
                           match uu____24997 with
                           | (us,t) ->
                               let n_us = FStar_List.length us  in
                               let uu____25015 =
                                 FStar_Syntax_Subst.open_univ_vars us t  in
                               (match uu____25015 with
                                | (us1,t1) ->
                                    let uu____25026 =
                                      let uu____25031 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      let uu____25038 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      (uu____25031, uu____25038)  in
                                    (match uu____25026 with
                                     | (b_opening1,b_closing1) ->
                                         let uu____25051 =
                                           let uu____25056 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us)
                                              in
                                           let uu____25065 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us)
                                              in
                                           (uu____25056, uu____25065)  in
                                         (match uu____25051 with
                                          | (univs_opening1,univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____25081 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1
                                                   in
                                                FStar_Syntax_Subst.subst
                                                  univs_opening1 uu____25081
                                                 in
                                              let uu____25082 =
                                                elim_uvars_aux_t env [] [] t2
                                                 in
                                              (match uu____25082 with
                                               | (uu____25103,uu____25104,t3)
                                                   ->
                                                   let t4 =
                                                     let uu____25119 =
                                                       let uu____25120 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3
                                                          in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
                                                         uu____25120
                                                        in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____25119
                                                      in
                                                   (us1, t4)))))
                            in
                         let elim_term t =
                           let uu____25125 =
                             elim_uvars_aux_t env univs1 binders t  in
                           match uu____25125 with
                           | (uu____25138,uu____25139,t1) -> t1  in
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
                             | uu____25199 ->
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_abs
                                      ((a.FStar_Syntax_Syntax.action_params),
                                        body, FStar_Pervasives_Native.None))
                                   FStar_Pervasives_Native.None
                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                              in
                           let destruct_action_body body =
                             let uu____25216 =
                               let uu____25217 =
                                 FStar_Syntax_Subst.compress body  in
                               uu____25217.FStar_Syntax_Syntax.n  in
                             match uu____25216 with
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,(FStar_Util.Inl
                                        typ,FStar_Pervasives_Native.None ),FStar_Pervasives_Native.None
                                  )
                                 -> (defn, typ)
                             | uu____25276 -> failwith "Impossible"  in
                           let destruct_action_typ_templ t =
                             let uu____25305 =
                               let uu____25306 =
                                 FStar_Syntax_Subst.compress t  in
                               uu____25306.FStar_Syntax_Syntax.n  in
                             match uu____25305 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (pars,body,uu____25327) ->
                                 let uu____25348 = destruct_action_body body
                                    in
                                 (match uu____25348 with
                                  | (defn,typ) -> (pars, defn, typ))
                             | uu____25393 ->
                                 let uu____25394 = destruct_action_body t  in
                                 (match uu____25394 with
                                  | (defn,typ) -> ([], defn, typ))
                              in
                           let uu____25443 =
                             elim_tscheme
                               ((a.FStar_Syntax_Syntax.action_univs),
                                 action_typ_templ)
                              in
                           match uu____25443 with
                           | (action_univs,t) ->
                               let uu____25452 = destruct_action_typ_templ t
                                  in
                               (match uu____25452 with
                                | (action_params,action_defn,action_typ) ->
                                    let a' =
                                      let uu___215_25493 = a  in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___215_25493.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___215_25493.FStar_Syntax_Syntax.action_unqualified_name);
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
                           let uu___216_25495 = ed  in
                           let uu____25496 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ret_wp  in
                           let uu____25497 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_wp  in
                           let uu____25498 =
                             elim_tscheme ed.FStar_Syntax_Syntax.if_then_else
                              in
                           let uu____25499 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ite_wp  in
                           let uu____25500 =
                             elim_tscheme ed.FStar_Syntax_Syntax.stronger  in
                           let uu____25501 =
                             elim_tscheme ed.FStar_Syntax_Syntax.close_wp  in
                           let uu____25502 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assert_p  in
                           let uu____25503 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assume_p  in
                           let uu____25504 =
                             elim_tscheme ed.FStar_Syntax_Syntax.null_wp  in
                           let uu____25505 =
                             elim_tscheme ed.FStar_Syntax_Syntax.trivial  in
                           let uu____25506 =
                             elim_term ed.FStar_Syntax_Syntax.repr  in
                           let uu____25507 =
                             elim_tscheme ed.FStar_Syntax_Syntax.return_repr
                              in
                           let uu____25508 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_repr
                              in
                           let uu____25509 =
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions
                              in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___216_25495.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___216_25495.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs = univs1;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp = uu____25496;
                             FStar_Syntax_Syntax.bind_wp = uu____25497;
                             FStar_Syntax_Syntax.if_then_else = uu____25498;
                             FStar_Syntax_Syntax.ite_wp = uu____25499;
                             FStar_Syntax_Syntax.stronger = uu____25500;
                             FStar_Syntax_Syntax.close_wp = uu____25501;
                             FStar_Syntax_Syntax.assert_p = uu____25502;
                             FStar_Syntax_Syntax.assume_p = uu____25503;
                             FStar_Syntax_Syntax.null_wp = uu____25504;
                             FStar_Syntax_Syntax.trivial = uu____25505;
                             FStar_Syntax_Syntax.repr = uu____25506;
                             FStar_Syntax_Syntax.return_repr = uu____25507;
                             FStar_Syntax_Syntax.bind_repr = uu____25508;
                             FStar_Syntax_Syntax.actions = uu____25509;
                             FStar_Syntax_Syntax.eff_attrs =
                               (uu___216_25495.FStar_Syntax_Syntax.eff_attrs)
                           }  in
                         let uu___217_25512 = s  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___217_25512.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___217_25512.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___217_25512.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___217_25512.FStar_Syntax_Syntax.sigattrs)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___95_25529 =
            match uu___95_25529 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (us,t) ->
                let uu____25556 = elim_uvars_aux_t env us [] t  in
                (match uu____25556 with
                 | (us1,uu____25580,t1) ->
                     FStar_Pervasives_Native.Some (us1, t1))
             in
          let sub_eff1 =
            let uu___218_25599 = sub_eff  in
            let uu____25600 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp  in
            let uu____25603 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift  in
            {
              FStar_Syntax_Syntax.source =
                (uu___218_25599.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___218_25599.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____25600;
              FStar_Syntax_Syntax.lift = uu____25603
            }  in
          let uu___219_25606 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___219_25606.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___219_25606.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___219_25606.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___219_25606.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,univ_names,binders,comp,flags1) ->
          let uu____25616 = elim_uvars_aux_c env univ_names binders comp  in
          (match uu____25616 with
           | (univ_names1,binders1,comp1) ->
               let uu___220_25650 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___220_25650.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___220_25650.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___220_25650.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___220_25650.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____25661 -> s
      | FStar_Syntax_Syntax.Sig_splice uu____25662 -> s
  
let (erase_universes :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  -> normalize [EraseUniverses; AllowUnboundUniverses] env t
  